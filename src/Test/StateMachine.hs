{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}

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
-- The main module for state machine based testing.
--
-----------------------------------------------------------------------------

module Test.StateMachine
  ( -- * Sequential property helper
    sequentialProperty
  , sequentialProperty'
    -- * Parallel property helper
  , parallelProperty
  , parallelProperty'
  , module Test.StateMachine.Types
  ) where

import           Control.Monad.State
                   (evalStateT, replicateM_)
import qualified Data.Map                              as M
import           Test.QuickCheck
                   (Gen)
import           Test.QuickCheck.Monadic
                   (monadic, monadicIO, run)
import           Test.QuickCheck.Property
                   (Property, forAllShrink, ioProperty)

import qualified Test.StateMachine.Internal.IxMap      as IxM
import           Test.StateMachine.Internal.Parallel
import           Test.StateMachine.Internal.Sequential
import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Internal.Utils
import           Test.StateMachine.Types

------------------------------------------------------------------------

-- | This function builds a property that tests if your model is agrees
--   with your semantics when running commands sequentially.
sequentialProperty
  :: CommandConstraint ix cmd
  => Monad m
  => Show (model ConstIntRef)
  => StateMachineModel model cmd                             -- ^ Model
  -> Gen (Untyped cmd (RefPlaceholder ix))                   -- ^ Generator
  -> (forall resp refs'. Shrinker (cmd refs' resp))          -- ^ Shrinker
  -> (forall resp. cmd refs resp -> m (Response_ refs resp)) -- ^ Semantics
  -> (m Property -> Property)
  -> Property
sequentialProperty smm gen shrinker sem runner =
  sequentialProperty' smm (liftGenerator gen) shrinker (const (const sem))
    (return ()) (const runner) (const (return ()))

-- | Same as above, except it provides more flexibility.
sequentialProperty'
  :: CommandConstraint ix cmd
  => Show (model ConstIntRef)
  => Monad m
  => StateMachineModel model cmd
  -> Generator ix cmd gstate
  -> (forall resp refs'. Shrinker (cmd refs' resp))
  -> (forall resp. model ConstIntRef ->
        MayResponse_ ConstIntRef resp ->
        cmd refs resp ->
        m (Response_ refs resp))                             -- ^ Semantics
  -> IO setup                                                -- ^ Setup
  -> (setup -> m Property -> Property)
  -> (setup -> IO ())                                        -- ^ Cleanup
  -> Property
sequentialProperty' model gen shrinker semantics setup runner cleanup =
  forAllShrink
    (fst <$> liftGen gen 0 M.empty)
    (liftShrink gen shrinker)
    $ \cmds -> collectStats cmds $
        monadic (ioProperty . runnerWithSetup)
          (checkSequentialInvariant model
             (initialModel model) semantics cmds)
  where
  runnerWithSetup mp = do
    s <- setup
    let prop = runner s (evalStateT mp IxM.empty)
    cleanup s
    return prop

------------------------------------------------------------------------

-- | This function builds a property that tests your semantics for race
--   conditions, by runnings commands in parallel and then trying to
--   linearise the resulting history.
--
-- /Note:/ Make sure that your model passes the sequential property first.
parallelProperty
  :: CommandConstraint ix cmd
  => StateMachineModel model cmd                              -- ^ Model
  -> Gen (Untyped cmd (RefPlaceholder ix))                    -- ^ Generator
  -> (forall resp refs'. Shrinker (cmd refs' resp))           -- ^ Shrinker
  -> (forall resp. cmd refs resp -> IO (Response_ refs resp)) -- ^ Semantics
  -> Property
parallelProperty smm gen shrinker sem
  = parallelProperty' smm (liftGenerator gen) shrinker (return ())
      (const sem) (const (return ()))

-- | Same as above, but with the possibility of stateful generation, and
--   setting up and tearing down some resource used by the semantics.
--   The latter can be useful for connecting to a database for example.
parallelProperty'
  :: CommandConstraint ix cmd
  => StateMachineModel model cmd                              -- ^ Model
  -> Generator ix cmd gstate
  -> (forall resp refs'. Shrinker (cmd refs' resp))           -- ^ Shrinker
  -> IO setup                                                 -- ^ Setup
  -> (forall resp. setup -> cmd refs resp ->
        IO (Response_ refs resp))                             -- ^ Semantics
  -> (setup -> IO ())                                         -- ^ Cleanup
  -> Property
parallelProperty' smm gen shrinker setup sem clean
  = forAllShrink
      (liftGenFork gen)
      (liftShrinkFork gen shrinker) $ \fork -> monadicIO $ do
        res <- run setup
        replicateM_ 10 $ do
          hist <- run $ liftSemFork (sem res) fork
          run (clean res)
          checkParallelInvariant smm hist
