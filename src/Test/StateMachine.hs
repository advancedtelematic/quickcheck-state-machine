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
                   (StateT, evalStateT, lift, replicateM_)
import qualified Data.Map                              as M
import           Test.QuickCheck
                   (Gen)
import           Test.QuickCheck.Monadic
                   (monadic, monadicIO, run)
import           Test.QuickCheck.Property
                   (Property)

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
sequentialProperty smm gen shrinker sem runM =
  sequentialProperty' smm (lift gen) () shrinker (const (const sem)) runM

-- | Same as above, except it provides more flexibility.
sequentialProperty'
  :: CommandConstraint ix cmd
  => Show (model ConstIntRef)
  => Monad m
  => StateMachineModel model cmd                             -- ^ Model
  -> StateT s Gen (Untyped cmd (RefPlaceholder ix))          -- ^ Generator
  -> s                                                       -- ^ Generator state
  -> (forall resp refs'. Shrinker (cmd refs' resp))          -- ^ Shrinker
  -> (forall resp. model ConstIntRef ->
        MayResponse_ ConstIntRef resp ->
        cmd refs resp ->
        m (Response_ refs resp))                             -- ^ Semantics
  -> (m Property -> Property)
  -> Property
sequentialProperty' smm gen s shrinker sem runM =
  forAllShrinkShow
    (fst . fst <$> liftGen' gen s 0 M.empty)
    (liftShrink shrinker)
    show
    $ \cmds -> collectStats cmds $
        monadic (runM . flip evalStateT IxM.empty) $
          checkSequentialInvariant smm (initialModel smm) sem cmds

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
  = parallelProperty' smm (lift gen) () shrinker sem (return ())

parallelProperty'
  :: CommandConstraint ix cmd
  => StateMachineModel model cmd                              -- ^ Model
  -> StateT genState Gen (Untyped cmd (RefPlaceholder ix))    -- ^ Generator
  -> genState
  -> (forall resp refs'. Shrinker (cmd refs' resp))           -- ^ Shrinker
  -> (forall resp. cmd refs resp -> IO (Response_ refs resp)) -- ^ Semantics
  -> IO ()                                                    -- ^ Cleanup
  -> Property
parallelProperty' smm gen genState shrinker sem clean
  = forAllShrinkShow
      (liftGenFork' gen genState)
      (liftShrinkFork shrinker)
      show
      $ \fork -> monadicIO $ replicateM_ 10 $ do
          run clean
          hist <- run $ liftSemFork sem fork
          checkParallelInvariant smm hist
