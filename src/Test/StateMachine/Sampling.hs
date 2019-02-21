{-# OPTIONS_GHC -Wno-orphans #-}

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ExplicitNamespaces  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Test.StateMachine.Sampling
  ( ToState(..)
  , SomeMatrix(..)
  , ppSomeMatrix
  , usage
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
import           Data.Map
                   (Map)
import qualified Data.Map                     as Map
import           Data.Maybe
                   (fromJust, fromMaybe)
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
                   gmaxBound, gminBound)
import           GHC.Generics
                   (Generic, Rep)
import           GHC.TypeLits
                   (type (-), type (<=), KnownNat, SomeNat(SomeNat),
                   natVal, sameNat, someNatVal)
import           GHC.TypeLits.Compare
                   ((:<=?)(..), (%<=?))
import           Numeric.LinearAlgebra
                   (fromRows)
import           Numeric.LinearAlgebra.Static
                   (L, R, create, linspace, matrix, norm_1, toRows,
                   unwrap)
import           Prelude
import           Unsafe.Coerce
                   (unsafeCoerce)

------------------------------------------------------------------------

--- | We can transition into a state successful or not, or the it can
--- actually be the sink/stop state.
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

probabilisticNormalize :: SomeMatrix -> SomeMatrix
probabilisticNormalize (SomeMatrix pm pn m) =
  let f = fromJust . create . fromRows . map (unwrap . normalizeV) . toRows
  in SomeMatrix pm pn (f m)

normalizeV :: KnownNat n => R n -> R n
normalizeV v = v / linspace (norm_1 v, norm_1 v)

usage
  :: forall state proxy. (Read state, Ord state)
  => (Generic state, GEnum FiniteEnum (Rep state), GBounded (Rep state))
  => proxy state -> Map String Int
  -> SomeMatrix
usage _ = probabilisticNormalize . go . fst . readTable @state
  where
    go = fromMaybe (error "usage: impossible") . toMatrix

results
  :: forall state proxy. (Read state, Ord state)
  => (Generic state, GEnum FiniteEnum (Rep state), GBounded (Rep state))
  => proxy state -> Map String Int
  -> (SomeMatrix, SomeMatrix)
results _ = bimap go go . readTable @state
  where
    go = fromMaybe (error "results: impossible") . toMatrix

readTable :: (Read state, Ord state)
           => Map String Int
           -> (Map (state, Maybe state) Double, Map (state, Maybe state) Double)
readTable m = bimap Map.fromList Map.fromList $ swap $
  partitionEithers
    [ case s' of
        Successful s'' -> Right ((s, Just s''), fromIntegral n)
        Failed     s'' -> Left  ((s, Just s''), fromIntegral n)
        Sink           -> Right ((s, Nothing),  fromIntegral n)
        -- ^ Transitioning into a sink never fails.
    | ((s, s'), n)  <- map (first read) (Map.toList m)
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
    ) => Proxy n -> L (n - 1) n -> L (n - 1) n -> L (n - 1) n -> CompatibleMatrices n

compatibleMatrices :: KnownNat n => Proxy n -> SomeMatrix -> (SomeMatrix, SomeMatrix)
                   -> Either String (CompatibleMatrices n)
compatibleMatrices pn (SomeMatrix po pp p) (SomeMatrix pm pq s, SomeMatrix pr ps f) = do
  Refl <- maybeToRight (lemma0  po pn) "lemma0 pn po"
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
