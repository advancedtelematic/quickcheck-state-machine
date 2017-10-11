-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Internal.Utils
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-----------------------------------------------------------------------------

module Test.StateMachine.Internal.Utils where

import           Data.List
                   (group, sort)
import           Test.QuickCheck
                   (Property, chatty, counterexample, property,
                   stdArgs, whenFail)
import           Test.QuickCheck.Counterexamples
                   (PropertyOf)
import qualified Test.QuickCheck.Counterexamples as CE
import           Test.QuickCheck.Monadic
                   (PropertyM(MkPropertyM), monadicIO, run)
import           Test.QuickCheck.Property
                   ((.&&.), (.||.))

------------------------------------------------------------------------

-- | Lifts 'Prelude.any' to properties.
anyP :: (a -> Property) -> [a] -> Property
anyP p = foldr (\x ih -> p x .||. ih) (property False)

-- | Lifts a plain property into a monadic property.
liftProperty :: Monad m => Property -> PropertyM m ()
liftProperty prop = MkPropertyM (\k -> fmap (prop .&&.) <$> k ())

-- | Lifts 'whenFail' to 'PropertyM'.
whenFailM :: Monad m => IO () -> Property -> PropertyM m ()
whenFailM m prop = liftProperty (m `whenFail` prop)

-- | A property that tests @prop@ repeatedly @n@ times, failing as soon as any
--   of the tests of @prop@ fails.
alwaysP :: Int -> Property -> Property
alwaysP n prop
  | n <= 0    = error "alwaysP: expected positive integer."
  | n == 1    = prop
  | otherwise = prop .&&. alwaysP (n - 1) prop

-- | Write a metaproperty on the output of QuickChecking a property using a
--   boolean predicate on the output.
shrinkPropertyHelperC :: Show a => PropertyOf a -> (a -> Bool) -> Property
shrinkPropertyHelperC prop p = shrinkPropertyHelperC' prop (property . p)

-- | Same as above, but using a property predicate.
shrinkPropertyHelperC' :: Show a => PropertyOf a -> (a -> Property) -> Property
shrinkPropertyHelperC' prop p = monadicIO $ do
  ce_ <- run $ CE.quickCheckWith (stdArgs {chatty = False}) prop
  case ce_ of
    Nothing -> return ()
    Just ce -> liftProperty $
      counterexample ("failed: " ++ show ce) $ p ce

-- | Given shrinkers for the components of a pair we can shrink the pair.
shrinkPair' :: (a -> [a]) -> (b -> [b]) -> ((a, b) -> [(a, b)])
shrinkPair' shrinkerA shrinkerB (x, y) =
  [ (x', y) | x' <- shrinkerA x ] ++
  [ (x, y') | y' <- shrinkerB y ]

-- | Same above, but for homogeneous pairs.
shrinkPair :: (a -> [a]) -> ((a, a) -> [(a, a)])
shrinkPair shrinker = shrinkPair' shrinker shrinker

------------------------------------------------------------------------

-- | Remove duplicate elements from a list.
nub :: Ord a => [a] -> [a]
nub = fmap head . group . sort

-- | Drop last 'n' elements of a list.
dropLast :: Int -> [a] -> [a]
dropLast n xs = zipWith const xs (drop n xs)

-- | Indexing starting from the back of a list.
toLast :: Int -> [a] -> a
toLast n = last . dropLast n
