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

type Shrinker a = a -> [a]

genFromMaybe :: StateT s (StateT t Gen) (Maybe a) -> StateT s (StateT t Gen) a
genFromMaybe g = do
  mx <- g
  case mx of
    Nothing -> genFromMaybe g
    Just x  -> return x

anyP :: (a -> Property) -> [a] -> Property
anyP p = foldr (\x ih -> p x .||. ih) (property False)

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

forAllShow
  :: Testable prop
  => Gen a -> (a -> String) -> (a -> prop) -> Property
forAllShow gen = forAllShrinkShow gen (const [])


liftProperty :: Monad m => Property -> PropertyM m ()
liftProperty prop = MkPropertyM (\k -> fmap (prop .&&.) <$> k ())

shrinkPropertyHelper :: Property -> (String -> Bool) -> Property
shrinkPropertyHelper prop p = shrinkPropertyHelper' prop (property . p)

shrinkPropertyHelper' :: Property -> (String -> Property) -> Property
shrinkPropertyHelper' prop p = monadicIO $ do
  result <- run $ quickCheckWithResult (stdArgs {chatty = False}) prop
  case result of
    Failure { output = outputLines } -> liftProperty $
      counterexample ("failed: " ++ outputLines) $ p outputLines
    _                                -> return ()

shrinkPair :: (a -> [a]) -> (b -> [b]) -> (a, b) -> [(a, b)]
shrinkPair shrinkerA shrinkerB (x, y) =
  [ (x', y) | x' <- shrinkerA x ] ++
  [ (x, y') | y' <- shrinkerB y ]
