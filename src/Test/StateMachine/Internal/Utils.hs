{-# LANGUAGE TypeOperators #-}

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

import           Control.Concurrent.STM
                   (atomically)
import           Control.Concurrent.STM.TChan
                   (TChan, tryReadTChan)
import           Data.List
                   (group, sort)
import           Test.QuickCheck
                   (Gen, Property, Testable, again, chatty,
                   counterexample, property, shrinking, stdArgs,
                   whenFail)
import           Test.QuickCheck.Counterexamples
                   ((:&:)(..), Counterexample, PropertyOf)
import qualified Test.QuickCheck.Counterexamples as CE
import           Test.QuickCheck.Gen.Unsafe
                   (promote)
import           Test.QuickCheck.Monadic
                   (PropertyM(MkPropertyM), run)
import           Test.QuickCheck.Property
                   (Prop(MkProp), Property(MkProperty), ioRose, unProp,
                   unProperty)
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

oldMonadic :: Monad m => (m Property -> Property) -> PropertyM m a -> Property
oldMonadic runner m0 = property (fmap runner (go m0))
  where
  go :: Monad m => PropertyM m a -> Gen (m Property)
  go (MkPropertyM m) = m (const (return (return (property True))))

oldMonadicIO :: PropertyM IO a -> Property
oldMonadicIO = oldMonadic oldIoProperty

oldIoProperty :: Testable prop => IO prop -> Property
oldIoProperty = MkProperty . fmap (MkProp . ioRose . fmap unProp) .
  promote . fmap (unProperty . property)

-- | Write a metaproperty on the output of QuickChecking a property using a
--   boolean predicate on the output.
shrinkPropertyHelperC :: Show a => PropertyOf a -> (a -> Bool) -> Property
shrinkPropertyHelperC prop p = oldMonadicIO $ do
  ce_ <- run $ CE.quickCheckWith (stdArgs {chatty = False}) prop
  case ce_ of
    Nothing -> return False
    Just ce -> return (p ce)

-- | Same as above, but using a property predicate.
shrinkPropertyHelperC' :: Show a => PropertyOf a -> (a -> Property) -> Property
shrinkPropertyHelperC' prop p = oldMonadicIO $ do
  ce_ <- run $ CE.quickCheckWith (stdArgs {chatty = False}) prop
  case ce_ of
    Nothing -> return ()
    Just ce -> liftProperty $
      counterexample ("shrinkPropertyHelper: " ++ show ce) $ p ce

-- | Given shrinkers for the components of a pair we can shrink the pair.
shrinkPair' :: (a -> [a]) -> (b -> [b]) -> ((a, b) -> [(a, b)])
shrinkPair' shrinkerA shrinkerB (x, y) =
  [ (x', y) | x' <- shrinkerA x ] ++
  [ (x, y') | y' <- shrinkerB y ]

-- | Same above, but for homogeneous pairs.
shrinkPair :: (a -> [a]) -> ((a, a) -> [(a, a)])
shrinkPair shrinker = shrinkPair' shrinker shrinker

-- | A variant of 'Test.QuickCheck.Monadic.forAllShrink' with an explicit show
--   function.
forAllShrinkShow
  :: Testable prop
  => Gen a -> (a -> [a]) -> (a -> String) -> (a -> prop) -> Property
forAllShrinkShow gen shrinker shower pf =
  again $
  MkProperty $
  gen >>= \x ->
    unProperty $
    shrinking shrinker x $ \x' ->
      counterexample (shower x') (pf x')

forAllShrinkShowC
  :: CE.Testable prop
  => Gen a -> (a -> [a]) -> (a -> String) -> (a -> prop) -> PropertyOf (a :&: Counterexample prop)
forAllShrinkShowC arb shr shower prop =
  CE.MkProperty $ \f ->
    forAllShrinkShow arb shr shower $ \x ->
      CE.unProperty (CE.property (prop x)) (\y -> f (x :&: y))

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

------------------------------------------------------------------------

getChanContents :: TChan a -> IO [a]
getChanContents chan = reverse <$> atomically (go [])
  where
  go acc = do
    mx <- tryReadTChan chan
    case mx of
      Just x  -> go $ x : acc
      Nothing -> return acc
