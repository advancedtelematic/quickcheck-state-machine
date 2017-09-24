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
-- This module exports some QuickCheck utility functions. Some of these should
-- perhaps be upstreamed.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Internal.Utils
  ( anyP
  , liftProperty
  , whenFailM
  , bracketP
  , shrinkPropertyHelper
  , shrinkPropertyHelper'
  , shrinkPair
  , shrinkPair'
  ) where

import           Control.Exception
                   (bracketOnError)
import           Test.QuickCheck
                   (Property, Result(Failure), chatty, counterexample,
                   ioProperty, output, property, quickCheckWithResult,
                   stdArgs, whenFail)
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

whenFailM :: Monad m => IO () -> Property -> PropertyM m ()
whenFailM m prop = liftProperty (m `whenFail` prop)

bracketP :: IO a -> (a -> IO b) -> (a -> Property) -> Property
bracketP up down prop = ioProperty $
  bracketOnError up down (return . prop)

-- | A property that tests @prop@ repeatedly @n@ times, failing as soon as any
--   of the tests of @prop@ fails.
alwaysP :: Int -> Property -> Property
alwaysP n prop
  | n <= 0    = error "alwaysP: expected positive integer."
  | n == 1    = prop
  | otherwise = prop .&&. alwaysP (n - 1) prop

-- | Write a metaproperty on the output of QuickChecking a property using a
--   boolean predicate on the output.
shrinkPropertyHelper :: Property -> (String -> Bool) -> Property
shrinkPropertyHelper prop p = shrinkPropertyHelper' prop (property . p)

-- | Same as above, but using a property predicate.
shrinkPropertyHelper' :: Property -> (String -> Property) -> Property
shrinkPropertyHelper' prop p = monadicIO $ do
  result <- run $ quickCheckWithResult (stdArgs {chatty = False}) prop
  case result of
    Failure { output = outputLines } -> liftProperty $
      counterexample ("failed: " ++ outputLines) $ p outputLines
    _                                -> return ()

-- | Given shrinkers for the components of a pair we can shrink the pair.
shrinkPair' :: (a -> [a]) -> (b -> [b]) -> ((a, b) -> [(a, b)])
shrinkPair' shrinkerA shrinkerB (x, y) =
  [ (x', y) | x' <- shrinkerA x ] ++
  [ (x, y') | y' <- shrinkerB y ]

-- | Same above, but for homogeneous pairs.
shrinkPair :: (a -> [a]) -> ((a, a) -> [(a, a)])
shrinkPair shrinker = shrinkPair' shrinker shrinker
