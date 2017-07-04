{-# LANGUAGE FlexibleContexts      #-}
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
import           Test.QuickCheck.Monadic
                   (monadic, monadicIO, run)
import           Test.QuickCheck.Property
                   (Property, forAllShrink, ioProperty)

import           Test.StateMachine.Internal.Parallel
import           Test.StateMachine.Internal.Sequential
import           Test.StateMachine.Internal.Types.Environment
import           Test.StateMachine.Types

------------------------------------------------------------------------

-- | This function builds a property that tests if your model is agrees
--   with your semantics when running commands sequentially.
sequentialProperty
  :: Monad m
  => Show (Internal act)
  => HFunctor act
  => HFoldable act
  => Generator model act
  -> (forall resp v. act v resp -> [act v resp])   -- ^ Shrinker
  -> Precondition model act
  -> Transition    model act
  -> Postcondition model act
  -> (forall v. model v)                           -- ^ Initial model
  -> (forall resp. act Concrete resp -> m resp)    -- ^ Semantics
  -> (m Property -> Property)                      -- ^ Runner
  -> Property
sequentialProperty gen shrinker precond trans postcond m sem runner =
  sequentialProperty' gen shrinker precond trans postcond m
    sem (return ()) (const runner) (const (return ()))

-- | Same as above, except it provides more flexibility.
sequentialProperty'
  :: Monad m
  => Show (Internal act)
  => HFunctor act
  => HFoldable act
  => Generator model act
  -> (forall resp v. act v resp -> [act v resp])   -- ^ Shrinker
  -> Precondition model act
  -> Transition    model act
  -> Postcondition model act
  -> (forall v. model v)                           -- ^ Initial model
  -> (forall resp. act Concrete resp -> m resp)    -- ^ Semantics
  -> IO setup                                      -- ^ Setup some resource
  -> (setup -> m Property -> Property)             -- ^ Runner
  -> (setup -> IO ())                              -- ^ Cleanup the resource
  -> Property
sequentialProperty' gen shrinker precond trans postcond m sem setup runner cleanup =
  forAllShrink
  (fst <$> liftGen gen precond trans m 0)
  (liftShrink shrinker precond trans m)
  $ \acts ->
    monadic (ioProperty . runnerWithSetup)
      (liftModel m m acts precond sem trans postcond)
  where
  runnerWithSetup mp = do
    s <- setup
    let prop = runner s (evalStateT mp emptyEnvironment)
    cleanup s
    return prop

------------------------------------------------------------------------

-- | This function builds a property that tests your semantics for race
--   conditions, by runnings commands in parallel and then trying to
--   linearise the resulting history.
--
-- /Note:/ Make sure that your model passes the sequential property first.
parallelProperty
  :: ShowAction act
  => Show (Internal act) -- used by the forAllShrink
  => HTraversable act
  => Generator model act
  -> (forall resp v. act v resp -> [act v resp])          -- ^ Shrinker
  -> Precondition  model act
  -> Transition    model act
  -> Postcondition model act
  -> (forall v. model v)                                  -- ^ Initial model
  -> (forall resp. act Concrete resp -> IO resp)          -- ^ Semantics
  -> Property
parallelProperty gen shrinker precond trans postcond initial sem =
  parallelProperty' gen shrinker precond trans postcond
    initial (return ()) (const sem) (const (return ()))

-- | Same as above, but with the possibility of stateful generation, and
--   setting up and tearing down some resource used by the semantics.
--   The latter can be useful for connecting to a database for example.
parallelProperty'
  :: ShowAction act
  => Show (Internal act) -- used by the forAllShrink
  => HTraversable act
  => Generator model act
  -> (forall resp v. act v resp -> [act v resp])          -- ^ Shrinker
  -> Precondition  model act
  -> Transition    model act
  -> Postcondition model act
  -> (forall v. model v)                                  -- ^ Initial model
  -> IO setup                                             -- ^ Setup
  -> (forall resp. setup -> act Concrete resp -> IO resp) -- ^ Semantics
  -> (setup -> IO ())                                     -- ^ Cleanup
  -> Property
parallelProperty' gen shrinker precond trans postcond initial setup sem clean =
  forAllShrink
    (liftGenFork gen precond trans initial)
    (liftShrinkFork shrinker precond trans initial) $ \fork -> monadicIO $ do
      res <- run setup
      replicateM_ 10 $ do
        hist <- run $ liftSemFork (sem res) fork
        run (clean res)
        checkParallelInvariant trans postcond initial fork hist
