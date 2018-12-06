{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.StateMachine.Markov
  ( Markov(..)
  , runMarkov
  , MarkovTable(..)
  , Continue(..)
  , tabulate
  , checkStochastic
  , prettyPrintTable
  )
  where

import           Generic.Data
                   (FiniteEnum, GBounded, GEnum, gfiniteEnumFromTo,
                   gmaxBound, gminBound)
import           GHC.Generics
                   (Generic, Rep)
import           Prelude
import           System.Random
                   (RandomGen, mkStdGen, randomR)
import           Test.QuickCheck.Gen
                   (Gen, chooseAny)

------------------------------------------------------------------------

data Continue a = Stop | Continue a
  deriving Show

data Markov model submodel cmd = Markov
  { unMarkov :: submodel -> [(Int, Continue (model -> Gen cmd, submodel))] }

newtype MarkovTable model submodel cmd = MarkovTable
  { unMarkovTable :: [(submodel, [(Int, Continue (model -> Gen cmd, submodel))])] }

tabulate :: (Generic s, GEnum FiniteEnum (Rep s), GBounded (Rep s))
         => Markov m s a -> MarkovTable m s a
tabulate (Markov f) = MarkovTable
  [ (s, f s) | s <- gfiniteEnumFromTo gminBound gmaxBound ]

checkStochastic :: MarkovTable model submodel cmd -> Bool
checkStochastic = all (\is -> all (>= 0) is && sum is == 100)
                . filter (not . null)
                . map (map fst)
                . map snd
                . unMarkovTable

runMarkov :: forall m s a. (Generic s, GEnum FiniteEnum (Rep s), GBounded (Rep s))
          => Markov m s a -> m -> s -> Gen (Continue (a, s))
runMarkov markov m s | checkStochastic (tabulate markov) = pickGen (unMarkov markov s)
                     | otherwise                         = error "The probabilities don't add up to 100."
  where
    pickGen :: [(Int, Continue (m -> Gen a, s))] -> Gen (Continue (a, s))
    pickGen gens = do
      stdGen <- mkStdGen <$> chooseAny
      frequencyR [ (prob, go gen) | (prob, gen) <- gens ] stdGen
      where
        go :: Continue (m -> Gen a, s) -> Gen (Continue (a, s))
        go Stop               = return Stop
        go (Continue (k, s')) = fmap (\x -> Continue (x, s')) (k m)

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

prettyPrintTable :: Show s => MarkovTable m s a -> String
prettyPrintTable (MarkovTable ps) = unlines
  [ show x ++ "\n     -- " ++ show (fst y) ++ " --> \n" ++ ppContinue (snd y) ++ "\n"
  | (x, xs) <- ps
  , y       <- xs
  ]
  where
    ppContinue :: Show s => Continue (m -> Gen a, s) -> String
    ppContinue Stop                 = "Stop"
    ppContinue (Continue (_gen, s)) = show s
