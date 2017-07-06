{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Rank2Types       #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- The main module for state machine based testing, it contains the
-- sequential and parallel property helpers.
--
-----------------------------------------------------------------------------

module Test.StateMachine
  ( -- * ForAll combinator for program
    forAllProgram
  , forAllParallelProgram
    -- * Run sequential program, and check model
  , runSequentialProgram
  , runSequentialProgram'
    -- * Run parallel program
  , runParallelProgram
  , runParallelProgram'
  , checkParallelInvariant
  , module Test.StateMachine.Types
  , ParallelProgram
  , Program
  ) where

import           Control.Monad.State
                   (evalStateT, replicateM_)
import           Test.QuickCheck.Monadic
                   (PropertyM, monadic, monadicIO, run)
import           Test.QuickCheck.Property
                   (Property, forAllShrink, ioProperty)

import           Test.StateMachine.Internal.Parallel
import           Test.StateMachine.Internal.Sequential
import           Test.StateMachine.Internal.Types
                   (ParallelProgram, Program)
import           Test.StateMachine.Internal.Types.Environment
import           Test.StateMachine.Internal.Utils
                   (liftProperty)
import           Test.StateMachine.Types

------------------------------------------------------------------------

-- | This function is like a `forAllShrink` for `Program act`.
forAllProgram
  :: Show (Untyped act)
  => HFoldable act
  => Generator model act
  -> Shrinker act
  -> Precondition model act
  -> Transition model act
  -> InitialModel model
  -> (Program act -> Property)
  -> Property
forAllProgram gen shrinker precond trans m =
  forAllShrink
    (fst <$> liftGen gen precond trans m 0)
    (liftShrink shrinker precond trans m)

-- | This function is like a `forAllShrink` for `ParallelProgram act`,
--   which is a concurrent program.
forAllParallelProgram
  :: Show (Untyped act)
  => HFoldable act
  => Generator model act
  -> Shrinker act
  -> Precondition model act
  -> Transition model act
  -> InitialModel model
  -> (ParallelProgram act -> Property)
  -> Property
forAllParallelProgram gen shrinker precond trans initial =
  forAllShrink
    (liftGenParallelProgram gen precond trans initial)
    (liftShrinkParallelProgram shrinker precond trans initial)

-- | Run a `Program act` sequentially and check if your model agrees
--   with your semantics.
runSequentialProgram
  :: Monad m
  => HFunctor act
  => Precondition model act
  -> Transition model act
  -> Postcondition model act
  -> InitialModel model
  -> Semantics act m
  -> (m Property -> Property)
  -> Program act
  -> Property
runSequentialProgram precond trans postcond m sem runner =
  runSequentialProgram' precond trans postcond m sem (return ()) (const runner) (const (return ()))

-- | Same as above, except with the possibility to setup some resource
--   for the runner to use. The resource could be a database connection
--   for example.
runSequentialProgram'
  :: Monad m
  => HFunctor act
  => Precondition model act
  -> Transition model act
  -> Postcondition model act
  -> InitialModel model
  -> Semantics act m
  -> IO setup
  -> (setup -> m Property -> Property)
  -> (setup -> IO ())
  -> Program act
  -> Property
runSequentialProgram' precond trans postcond m sem setup runner cleanup acts =
  monadic (ioProperty . runnerWithSetup)
    (checkProgram precond trans postcond m m sem acts)
  where
  runnerWithSetup mp = do
    s <- setup
    let prop = runner s (evalStateT mp emptyEnvironment)
    cleanup s
    return prop

-- | Run a parallel program `ParallelProgram act` which provides
--   a history.
runParallelProgram
  :: Show (Untyped act)
  => HTraversable act
  => Semantics act IO
  -> ParallelProgram act
  -> (History act -> Property)
  -> Property
runParallelProgram sem = runParallelProgram' (return ()) (const sem) (const (return ()))

-- | Same as above, but with the possibility of setting up some resource.
runParallelProgram'
  :: Show (Untyped act)
  => HTraversable act
  => IO setup
  -> (setup -> Semantics act IO)
  -> (setup -> IO ())
  -> ParallelProgram act
  -> (History act -> Property)
  -> Property
runParallelProgram' setup sem clean fork checkhistory = monadicIO $ do
  res <- run setup
  replicateM_ 10 $ do
    hist <- run $ liftSemParallelProgram (sem res) fork
    run (clean res)
    liftProperty $ checkhistory hist
