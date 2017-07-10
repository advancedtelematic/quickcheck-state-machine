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
-- The main module for state machine based testing, it contains
-- combinators that help you build sequential and parallel properties.
--
-----------------------------------------------------------------------------

module Test.StateMachine

  ( -- * Sequential property combinators
    Program
  , forAllProgram
  , runAndCheckProgram
  , runAndCheckProgram'

    -- * Parallel property combinators
  , ParallelProgram
  , forAllParallelProgram
  , History
  , runParallelProgram
  , runParallelProgram'
  , checkParallelProgram

    -- * Types
  , module Test.StateMachine.Types
  ) where

import           Control.Monad.State
                   (evalStateT, replicateM_)
import           Test.QuickCheck.Monadic
                   (monadic, monadicIO, run)
import           Test.QuickCheck.Property
                   (Property, forAllShrink, ioProperty)

import           Test.StateMachine.Internal.Parallel
import           Test.StateMachine.Internal.Sequential
import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Internal.Types.Environment
import           Test.StateMachine.Internal.Utils
                   (liftProperty)
import           Test.StateMachine.Types

------------------------------------------------------------------------

-- | This function is like a 'forAllShrink' for sequential programs.
forAllProgram
  :: Show (Untyped act)
  => HFoldable act
  => Generator model act
  -> Shrinker act
  -> Precondition model act
  -> Transition   model act
  -> InitialModel model
  -> (Program act -> Property)  -- ^ Predicate that should hold for all
                                --   programs.
  -> Property
forAllProgram generator shrinker precondition transition model =
  forAllShrink
    (evalStateT (generateProgram generator precondition transition 0) model)
    (shrinkProgram shrinker precondition transition model)

-- | Run a sequential program and check if your model agrees with your
--   semantics.
runAndCheckProgram
  :: Monad m
  => HFunctor act
  => Precondition model act
  -> Transition model act
  -> Postcondition model act
  -> InitialModel model
  -> Semantics act m
  -> (m Property -> Property)  -- ^ Runner
  -> Program act
  -> Property
runAndCheckProgram precond trans postcond m sem runner =
  runAndCheckProgram' precond trans postcond m sem (return ()) (const runner) (const (return ()))

-- | Same as above, except with the possibility to setup some resource
--   for the runner to use. The resource could be a database connection
--   for example.
runAndCheckProgram'
  :: Monad m
  => HFunctor act
  => Precondition model act
  -> Transition model act
  -> Postcondition model act
  -> InitialModel model
  -> Semantics act m
  -> IO setup                           -- ^ Setup a resource.
  -> (setup -> m Property -> Property)
  -> (setup -> IO ())                   -- ^ Tear down the resource.
  -> Program act
  -> Property
runAndCheckProgram' precond trans postcond m sem setup runner cleanup acts =
  monadic (ioProperty . runnerWithSetup)
    (checkProgram precond trans postcond m m sem acts)
  where
  runnerWithSetup mp = do
    s <- setup
    let prop = runner s (evalStateT mp emptyEnvironment)
    cleanup s
    return prop

------------------------------------------------------------------------

-- | This function is like a 'forAllShrink' for parallel programs.
forAllParallelProgram
  :: Show (Untyped act)
  => HFoldable act
  => Generator model act
  -> Shrinker act
  -> Precondition model act
  -> Transition   model act
  -> InitialModel model
  -> (ParallelProgram act -> Property) -- ^ Predicate that should hold
                                       --   for all parallel programs.
  -> Property
forAllParallelProgram generator shrinker precondition transition model =
  forAllShrink
    (generateParallelProgram generator precondition transition model)
    (shrinkParallelProgram shrinker precondition transition model)

-- | Run a parallel program and collect the history of the execution.
runParallelProgram
  :: Show (Untyped act)
  => HTraversable act
  => Semantics act IO
  -> ParallelProgram act
  -> (History act -> Property) -- ^ Predicate that should hold for the
                               --   execution history.
  -> Property
runParallelProgram sem = runParallelProgram' (return ()) (const sem) (const (return ()))

-- | Same as above, but with the possibility of setting up some resource.
runParallelProgram'
  :: Show (Untyped act)
  => HTraversable act
  => IO setup                     -- ^ Setup a resource.
  -> (setup -> Semantics act IO)
  -> (setup -> IO ())             -- ^ Tear down the resource.
  -> ParallelProgram act
  -> (History act -> Property)
  -> Property
runParallelProgram' setup sem clean fork checkhistory = monadicIO $ do
  res <- run setup
  replicateM_ 10 $ do
    hist <- run (executeParallelProgram (sem res) fork)
    run (clean res)
    liftProperty (checkhistory hist)
