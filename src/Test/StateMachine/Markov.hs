{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.StateMachine.Markov
  ( Markov(..)
  , runMarkov
  , MarkovTable(..)
  , Continue(..)
  , tabulate
  , prettyPrintTable
  )
  where

import           Control.Monad
                   (unless)
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
  (model -> submodel)
  (submodel -> [(Int, Continue (model -> Gen cmd, submodel))])

newtype MarkovTable m s a = MarkovTable
  [(s, [(Int, Continue (m -> Gen a, s))])]

tabulate :: (Generic s, GEnum FiniteEnum (Rep s), GBounded (Rep s))
         => Markov m s a -> MarkovTable m s a
tabulate (Markov _ f) = MarkovTable
  [ (s, f s) | s <- gfiniteEnumFromTo gminBound gmaxBound ]

runMarkov :: forall m s a. Markov m s a -> m -> Gen (Continue (a, s))
runMarkov (Markov classify dist) m = pickGen (dist (classify m))
  where
    pickGen :: [(Int, Continue (m -> Gen a, s))] -> Gen (Continue (a, s))
    pickGen gens = do
      let probs = map fst gens
      !_ <- unless (all (\p -> 0 <= p && p <= 100) probs && sum probs == 100) $
        error "The probabilites don't add up to 100."
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
