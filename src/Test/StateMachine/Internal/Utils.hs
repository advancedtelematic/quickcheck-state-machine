{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE TypeInType                #-}
{-# LANGUAGE TypeOperators             #-}

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
  ( Shrinker
  , genFromMaybe
  , anyP
  , forAllShrinkShow
  , forAllShow
  , liftProperty
  , shrinkPropertyHelper
  , shrinkPropertyHelper'
  , shrinkPair
  ) where

import           Control.Monad.State
                   (StateT)
import           Test.QuickCheck
                   (Gen, Property, Result(Failure), Testable, again,
                   chatty, counterexample, output, property,
                   quickCheckWithResult, shrinking, stdArgs)
import           Test.QuickCheck.Monadic
                   (PropertyM(MkPropertyM), monadicIO, run)
import           Test.QuickCheck.Property
                   (Property(MkProperty), unProperty, (.&&.), (.||.))

------------------------------------------------------------------------

-- | The type of a shrinker function.
type Shrinker a = a -> [a]

-- | Keep generating until we actually get a value.
genFromMaybe :: StateT s (StateT t Gen) (Maybe a) -> StateT s (StateT t Gen) a
genFromMaybe g = do
  mx <- g
  case mx of
    Nothing -> genFromMaybe g
    Just x  -> return x

-- | Lifts 'Prelude.any' to properties.
anyP :: (a -> Property) -> [a] -> Property
anyP p = foldr (\x ih -> p x .||. ih) (property False)

-- | A variant of 'Test.QuickCheck.Monadic.forAllShrink' with an explicit show
--   function.
forAllShrinkShow
  :: Testable prop
  => Gen a -> Shrinker a -> (a -> String) -> (a -> prop) -> Property
forAllShrinkShow gen shrinker shower pf =
  again $
  MkProperty $
  gen >>= \x ->
    unProperty $
    shrinking shrinker x $ \x' ->
      counterexample (shower x') (pf x')

-- | Same as above, but without shrinking.
forAllShow
  :: Testable prop
  => Gen a -> (a -> String) -> (a -> prop) -> Property
forAllShow gen = forAllShrinkShow gen (const [])

-- | Lifts a plain property into a monadic property.
liftProperty :: Monad m => Property -> PropertyM m ()
liftProperty prop = MkPropertyM (\k -> fmap (prop .&&.) <$> k ())

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
shrinkPair :: Shrinker a -> Shrinker b -> Shrinker (a, b)
shrinkPair shrinkerA shrinkerB (x, y) =
  [ (x', y) | x' <- shrinkerA x ] ++
  [ (x, y') | y' <- shrinkerB y ]
