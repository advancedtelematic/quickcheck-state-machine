{-# OPTIONS_GHC -Wno-orphans #-}

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ExplicitNamespaces  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Test.StateMachine.Markov
  ( Markov(..)
  , runMarkov
  , MarkovTable(..)
  , Continue(..)
  , markovTable
  , checkStochastic
  , markovToDot
  , lookupMarkov
  , transitionMatrix
  , ToState(..)
  , SomeMatrix(..)
  , ppSomeMatrix
  , results
  , maybeToRight
  , CompatibleMatrices(..)
  , compatibleMatrices
  )
  where

import           Control.Arrow
                   (first)
import           Control.Monad.Fail
                   (MonadFail(..))
import           Data.Bifunctor
                   (bimap)
import           Data.Either
                   (partitionEithers)
import           Data.GraphViz
                   (graphElemsToDot, quickParams)
import           Data.GraphViz.Commands
                   (GraphvizOutput(Pdf), addExtension, runGraphviz)
import           Data.GraphViz.Exception
                   (GraphvizException, handle)
import           Data.Map
                   (Map)
import qualified Data.Map                           as Map
import           Data.Maybe
                   (fromMaybe)
import           Data.Proxy
                   (Proxy(Proxy))
import           Data.String
                   (IsString, fromString)
import           Data.Tuple
                   (swap)
import           Data.Type.Equality
                   ((:~:)(..))
import           Generic.Data
                   (FiniteEnum, GBounded, GEnum, gfiniteEnumFromTo,
                   gfromFiniteEnum, gmaxBound, gminBound)
import           GHC.Generics
                   (Generic, Rep)
import           GHC.TypeLits
                   (type (-), type (<=), KnownNat, SomeNat(SomeNat),
                   natVal, sameNat, someNatVal)
import           GHC.TypeLits.Compare
                   ((:<=?)(..), (%<=?))
import           Numeric.LinearAlgebra.Static
                   (L, Sq, matrix)
import           Prelude
import           System.Random
                   (RandomGen, mkStdGen, randomR)
import           Test.QuickCheck.Gen
                   (Gen, chooseAny)
import           Unsafe.Coerce
                   (unsafeCoerce)

import           Test.StateMachine.Types.References
                   (Symbolic)

------------------------------------------------------------------------

type ConstructorName = String

data Continue model state cmd
  = Stop
  | Continue ConstructorName (model Symbolic -> Gen (cmd Symbolic)) state

data Markov model state cmd = Markov
  { unMarkov :: state -> [(Int, Continue model state cmd)] }

newtype MarkovTable model state cmd = MarkovTable
  { unMarkovTable :: [(state, [(Int, Continue model state cmd)])] }

markovTable :: (Generic s, GEnum FiniteEnum (Rep s), GBounded (Rep s))
            => Markov m s a -> MarkovTable m s a
markovTable (Markov f) = MarkovTable
  [ (s, f s) | s <- gfiniteEnumFromTo gminBound gmaxBound ]

checkStochastic :: MarkovTable model state cmd -> Bool
checkStochastic = all (\is -> all (>= 0) is && sum is == 100)
                . filter (not . null)
                . map (map fst)
                . map snd
                . unMarkovTable

runMarkov :: forall model state cmd. Generic state
          => (GEnum FiniteEnum (Rep state), GBounded (Rep state))
          => Markov model state cmd -> model Symbolic -> state
          -> Gen (Maybe (cmd Symbolic, state))
runMarkov markov m s
  | checkStochastic (markovTable markov) = pickGen (unMarkov markov s)
  | otherwise                            = error "The probabilities don't add up to 100."
  where
    pickGen :: [(Int, Continue model state cmd)]
            -> Gen (Maybe (cmd Symbolic, state))
    pickGen gens = do
      stdGen <- mkStdGen <$> chooseAny
      frequencyR [ (prob, go gen) | (prob, gen) <- gens ] stdGen
      where
        go :: Continue model state cmd -> Gen (Maybe (cmd Symbolic, state))
        go Stop               = return Nothing
        go (Continue _c k s') = fmap (\x -> Just (x, s')) (k m)

    frequencyR :: RandomGen g => [(Int, b)] -> g -> b
    frequencyR []  _ = error "There are paths in the Markov chain which contain no generators."
    frequencyR xs0 g =
      let
        (n, _g') = randomR (1, 100) g
      in
        lookupRange n (makeRanges xs0)
      where
        makeRanges :: [(Int, b)] -> [((Int, Int), b)]
        makeRanges = go 1
          where
            go _   []               = []
            go low [(_, x)]         = [((low, 100), x)]
            go low ((high, x) : xs) = ((low, low + high), x) : go (low + high) xs

        lookupRange :: Int -> [((Int, Int), b)] -> b
        lookupRange needle = go
          where
            go [] = error "lookupRange: number not in any range"
            go (((low, high), x) : xs)
              | low <= needle && needle <= high = x
              | otherwise                       = go xs

lookupMarkov :: Markov model state cmd -> state -> ConstructorName
             -> Maybe state
lookupMarkov (Markov markov) state conName = go (map snd (markov state))
  where
    go [] = Nothing
    go (Continue conName' _gen state' : cs)
      | conName == conName' = Just state'
      | otherwise           = go cs
    go (Stop : cs) = go cs

------------------------------------------------------------------------

type Node = String

markovToDot :: (Show state, Generic state)
            => (GEnum FiniteEnum (Rep state), GBounded (Rep state))
            => Markov model state cmd -> state -> FilePath -> IO (Either String FilePath)
markovToDot markov start fp =
  handle (\(e :: GraphvizException) -> return (Left (show e))) $ do
    let gr :: ([(Node, String)], [(Node, Node, ConstructorName)])
        gr = markovToGraphElems markov start
    Right <$> addExtension (runGraphviz (uncurry (graphElemsToDot quickParams) gr)) Pdf fp

markovToGraphElems :: (Show state, Generic state)
                   => (GEnum FiniteEnum (Rep state), GBounded (Rep state))
                   => Markov model state cmd -> state
                   -> ([(Node, String)], [(Node, Node, ConstructorName)])
markovToGraphElems markov _start = (nodes, edges)
  where
    table = markovTable markov
    exit  = "Exit"
    nodes = (exit, exit)
          : map (\e -> let s = show (fst e) in (s, s)) (unMarkovTable table)
    edges = concatMap (\(s, es) ->
                          map (\(freq, cont) -> let (s', a) = f freq cont in (show s, s', a))
                              es)
                      (unMarkovTable table)
      where
        f freq Stop                   = (exit, " Exit\n(" ++ show freq ++ "%)")
        f freq (Continue con _gen s') = (show s', ' ' : con ++ "\n(" ++ show freq ++ "%)")

------------------------------------------------------------------------

transitionMatrix :: forall model state cmd. (Eq state, Generic state)
                 => (GEnum FiniteEnum (Rep state), GBounded (Rep state))
                 => Markov model state cmd -> SomeMatrix
transitionMatrix markov = fromMaybe (error "results: impossible") $ do
  SomeNat pn@(Proxy :: Proxy n) <- someNatVal dimension
  return (SomeMatrix pn pn (matrix values :: Sq n))
  where
    dimension = toInteger (length states + 1) -- + 1 for the stop/exit/sink state.

    states :: [state]
    states = gfiniteEnumFromTo gminBound gmaxBound

    values :: [Double]
    values = [ 0.01 * fromIntegral (lookupFrequency markov from to)
             | from <- map Just states ++ [Nothing]
             , to   <- map Just states ++ [Nothing]
             ]

lookupFrequency :: forall model state cmd. Eq state
                => (Generic state, GEnum FiniteEnum (Rep state), GBounded (Rep state))
                => Markov model state cmd -> Maybe state -> Maybe state -> Int
lookupFrequency _markov Nothing Nothing = 0 -- From stop to stop.
lookupFrequency _markov Nothing (Just to)
  | gfromFiniteEnum to == 0 = 100 -- Recurrent Markov chain, always connect exit to start state.
  | otherwise               = 0   -- The exit state isn't connected to any other state.
lookupFrequency markov (Just from) to =
  case lookup from (unMarkovTable (markovTable markov)) of
    Nothing -> error "lookupFrequency: impossible."
    Just es -> go es
  where
    go :: [(Int, Continue model state cmd)] -> Int
    go []                  = 0
    go ((freq, Stop) : es) = case to of
      Nothing -> freq
      Just _  -> go es
    go ((freq, Continue _conName _gen state') : es)
      | to == Just state' = freq
      | otherwise         = go es

------------------------------------------------------------------------

-- | We can transition into a state successful or not, or the it can
-- actually be the sink/stop state.
data ToState state
  = Successful state
  | Failed state
  | Sink
  deriving (Show, Read)

data SomeMatrix where
  SomeMatrix :: forall m n. (KnownNat m, KnownNat n) =>
    Proxy m -> Proxy n -> L m n -> SomeMatrix

ppSomeMatrix :: SomeMatrix -> String
ppSomeMatrix (SomeMatrix _ _ mat) = show mat

results :: forall state proxy. (Read state, Ord state)
        => (Generic state, GEnum FiniteEnum (Rep state), GBounded (Rep state))
        => proxy state -> Map String (Map String Int)
        -> (SomeMatrix, SomeMatrix)
results _ = bimap go go . readTables @state
  where
    go = fromMaybe (error "results: impossible") . toMatrix

readTables :: (Read state, Ord state)
           => Map String (Map String Int)
           -> (Map (state, Maybe state) Double, Map (state, Maybe state) Double)
readTables m = bimap Map.fromList Map.fromList $ swap $
  partitionEithers
    [ case read es' of
        Successful s' -> Right ((s, Just s'), fromIntegral n)
        Failed     s' -> Left  ((s, Just s'), fromIntegral n)
        Sink          -> Right ((s, Nothing), fromIntegral n)
        -- ^ Transitioning into a sink never fails.
    | (s, m')  <- map (first read) (Map.toList m)
    , (es', n) <- Map.toList m'
    ]

toMatrix :: forall state. Ord state
         => (Generic state, GEnum FiniteEnum (Rep state), GBounded (Rep state))
         => Map (state, Maybe state) Double -> Maybe SomeMatrix
toMatrix m = do
  SomeNat pm@(Proxy :: Proxy m) <- someNatVal (dimension - 1)
  SomeNat pn@(Proxy :: Proxy n) <- someNatVal dimension
  return (SomeMatrix pm pn (matrix values :: L m n))
  where
    dimension = toInteger (length states) + 1 -- We add one for the stop/sink state.

    states :: [state]
    states = gfiniteEnumFromTo gminBound gmaxBound

    values :: [Double]
    values = [ fromMaybe 0.0 (Map.lookup (s, s') m)
             | s  <- states
             , s' <- map Just states ++ [Nothing]
             ]

------------------------------------------------------------------------

instance IsString str => MonadFail (Either str) where
  fail = Left . fromString

maybeToRight :: Maybe a -> String -> Either String a
maybeToRight Nothing msg = Left $ "validation error: " ++ msg
maybeToRight (Just x) _  = Right x

data CompatibleMatrices n where
  CompatibleMatrices ::
    ( KnownNat n, KnownNat (n - 1)
    , KnownNat (n - (n - 1))
    , KnownNat ((n - 1) - (n - 1))
    , 1 <= (n - 1)
    , (n - 1) <= n
    , (n - (n - 1)) ~ 1
    ) => Proxy n -> Sq n -> L (n - 1) n -> L (n - 1) n -> CompatibleMatrices n

compatibleMatrices :: KnownNat n => Proxy n -> SomeMatrix -> (SomeMatrix, SomeMatrix)
                   -> Either String (CompatibleMatrices n)
compatibleMatrices pn (SomeMatrix po pp p) (SomeMatrix pm pq s, SomeMatrix pr ps f) = do
  Refl <- maybeToRight (sameNat pn po) "sameNat pn po"
  Refl <- maybeToRight (sameNat pn pp) "sameNat pn pp"
  Refl <- maybeToRight (sameNat pn pq) "sameNat pn pq"
  Refl <- maybeToRight (sameNat pn ps) "sameNat pn ps"

  Refl <- maybeToRight (lemma0 pm pn)  "lemma0 pm pn"
  Refl <- maybeToRight (lemma0 pr pn)  "lemma0 pr pn"
  LE Refl <- maybeToRight (lemma1 pn)  "lemma1 pn"
  Refl <- maybeToRight (lemma2 pn)     "lemma2 pn"
  LE Refl <- maybeToRight (lemma3 pn)  "lemma3 pn"
  Refl <- maybeToRight (lemma4 pm)     "lemma4 pm"

  return (CompatibleMatrices pn p s f)

  where
    lemma0 :: (KnownNat m, KnownNat n) => Proxy m -> Proxy n -> Maybe (m :~: (n - 1))
    lemma0 m n
      | natVal m == pred (natVal n) = Just (unsafeCoerce Refl)
      | otherwise                   = Nothing

    lemma1 :: forall n. KnownNat (n - 1) => Proxy n -> Maybe (1 :<=? (n - 1))
    lemma1 _ = pure $ (Proxy @1) %<=? (Proxy @(n - 1))

    lemma2 :: Proxy n -> Maybe ((n - (n - 1)) :~: 1)
    lemma2 _ = pure $ unsafeCoerce Refl

    lemma3 :: forall n. (KnownNat n, KnownNat (n - 1)) => Proxy n -> Maybe ((n - 1) :<=? n)
    lemma3 p' = pure $ (Proxy @(n - 1)) %<=? p'

    lemma4 :: Proxy n -> Maybe ((n - n) :~: 0)
    lemma4 _ = pure $ unsafeCoerce Refl
