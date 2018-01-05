{-# OPTIONS_GHC -Wno-orphans #-}

{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}

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
  , programLength
  , forAllProgram
  , monadicSequential
  , runProgram
  , prettyProgram
  , actionNames
  , checkActionNames

    -- * Parallel property combinators
  , ParallelProgram
  , History
  , monadicParallel
  , runParallelProgram
  , runParallelProgram'
  , runParallelProgramIncomplete
  , prettyParallelProgram

    -- * With counterexamples
  , forAllProgramC
  , monadicSequentialC
  , monadicParallelC

    -- * Without shrinking
  , monadicSequentialNoShrink
  , monadicParallelNoShrink

    -- * Types
  , module Test.StateMachine.Types

    -- * Reexport
  , Test.QuickCheck.quickCheck
  ) where

import           Control.Monad.IO.Class
                   (MonadIO)
import           Control.Monad.State
                   (evalStateT, replicateM)
import           Control.Monad.Trans.Control
                   (MonadBaseControl)
import           Data.Functor.Classes
                   (Show1)
import           Data.Map
                   (Map)
import qualified Data.Map                              as M
import           Data.Typeable
                   (Typeable)
import           Test.QuickCheck
                   (Property, Testable, collect, cover, forAll,
                   ioProperty, property)
import qualified Test.QuickCheck
import           Test.QuickCheck.Counterexamples
                   ((:&:)(..), PropertyOf)
import qualified Test.QuickCheck.Counterexamples       as CE
import           Test.QuickCheck.Monadic
                   (PropertyM, monadic, run)
#if !MIN_VERSION_QuickCheck(2,10,0)
import           Test.QuickCheck.Property
                   (succeeded)
#endif

import           Test.StateMachine.Internal.Parallel
import           Test.StateMachine.Internal.Sequential
import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Internal.Utils
                   (forAllShow, forAllShrinkShowC, whenFailM)
import           Test.StateMachine.Types
import           Test.StateMachine.Types.History

------------------------------------------------------------------------

-- | This function is like a 'forAllShrink' for sequential programs.
forAllProgram
  :: HFoldable act
  => Generator model act
  -> Shrinker act
  -> Precondition model act
  -> Transition' model act err
  -> InitialModel model
  -> (Program act -> Property)  -- ^ Predicate that should hold for all
                                --   programs.
  -> Property
forAllProgram generator shrinker precondition transition model =
  property
  . forAllProgramC generator shrinker precondition transition model
  . \prop p -> CE.property (prop p)

-- | Variant of 'forAllProgram' which returns the generated and shrunk
-- program if the property fails.
forAllProgramC
  :: HFoldable act
  => Generator model act
  -> Shrinker act
  -> Precondition model act
  -> Transition' model act err
  -> InitialModel model
  -> (Program act -> PropertyOf a)  -- ^ Predicate that should hold for all
                                    --   programs.
  -> PropertyOf (Program act :&: a)
forAllProgramC generator shrinker precondition transition model =
  forAllShrinkShowC
    (evalStateT (generateProgram generator precondition transition 0) model)
    (shrinkProgram shrinker precondition transition model)
    (const "")

-- | Wrapper around 'forAllProgram' using the 'StateMachine' specification
-- to generate and shrink sequential programs.
monadicSequential
  :: Monad m
  => HFoldable act
  => Testable a
  => StateMachine' model act m err
  -> (Program act -> PropertyM m a)
     -- ^ Predicate that should hold for all programs.
  -> Property
monadicSequential sm = property . monadicSequentialC sm

-- | Variant of 'monadicSequential' with counterexamples.
monadicSequentialC
  :: Monad m
  => HFoldable act
  => Testable a
  => StateMachine' model act m err
  -> (Program act -> PropertyM m a)
     -- ^ Predicate that should hold for all programs.
  -> PropertyOf (Program act)
monadicSequentialC StateMachine {..} predicate
  = fmap (\(prog :&: ()) -> prog)
  . forAllProgramC generator' shrinker' precondition' transition' model'
  $ CE.property
  . monadic (ioProperty . runner')
  . predicate

#if !MIN_VERSION_QuickCheck(2,10,0)
instance Testable () where
  property = property . liftUnit
    where
    liftUnit () = succeeded
#endif

-- | Testable property of sequential programs derived from a
-- 'StateMachine' specification.
runProgram
  :: MonadBaseControl IO m
  => Show1 (act Symbolic)
  => Show err
  => Typeable err
  => HTraversable act
  => StateMachine' model act m err
     -- ^
  -> Program act
  -> PropertyM m (History act err, model Concrete, Reason)
runProgram sm = run . executeProgram sm

-- | Takes the output of running a program and pretty prints a
--   counterexample if the run failed.
prettyProgram
  :: MonadIO m
  => Show (model Concrete)
  => Show err
  => StateMachine' model act m err
  -> History act err
  -> Property
  -> PropertyM m ()
prettyProgram StateMachine{..} hist prop =
  putStrLn (ppHistory model' transition' hist) `whenFailM` prop

-- | Print distribution of actions and fail if some actions have not been
--   executed.
checkActionNames :: Constructors act => Program act -> Property -> Property
checkActionNames prog
  = collect names
  . cover (length names == numOfConstructors) 1 "coverage"
  where
    names = actionNames prog
    numOfConstructors = nConstructors prog

-- | Returns the frequency of actions in a program.
actionNames :: forall act. Constructors act => Program act -> [(Constructor, Int)]
actionNames = M.toList . foldl go M.empty . unProgram
  where
  go :: Map Constructor Int -> Internal act -> Map Constructor Int
  go ih (Internal act _) = M.insertWith (+) (constructor act) 1 ih

------------------------------------------------------------------------

-- | This function is like a 'forAllShrink' for parallel programs.
forAllParallelProgramC
  :: Show1 (act Symbolic)
  => Eq (Untyped act)
  => HFoldable act
  => Generator model act
  -> Shrinker act
  -> Precondition model act
  -> Transition'  model act err
  -> InitialModel model
  -> (ParallelProgram act -> PropertyOf a) -- ^ Predicate that should hold
                                           --   for all parallel programs.
  -> PropertyOf (ParallelProgram act :&: a)
forAllParallelProgramC generator shrinker precondition transition model =
  forAllShrinkShowC
    (generateParallelProgram generator precondition transition model)
    (shrinkParallelProgram shrinker precondition transition model)
    (const "")

-- | Wrapper around 'forAllParallelProgram using the 'StateMachine'
-- specification to generate and shrink parallel programs.
monadicParallel
  :: MonadBaseControl IO m
  => Eq (Untyped act)
  => Show1 (act Symbolic)
  => HFoldable act
  => StateMachine' model act m err
  -> (ParallelProgram act -> PropertyM m ())
     -- ^ Predicate that should hold for all parallel programs.
  -> Property
monadicParallel sm = property . monadicParallelC sm

-- | Variant of 'monadicParallel' with counterexamples.
monadicParallelC
  :: MonadBaseControl IO m
  => Eq (Untyped act)
  => Show1 (act Symbolic)
  => HFoldable act
  => StateMachine' model act m err
  -> (ParallelProgram act -> PropertyM m ())
     -- ^ Predicate that should hold for all parallel programs.
  -> PropertyOf (ParallelProgram act)
monadicParallelC StateMachine{..} predicate
  = fmap (\(prog :&: ()) -> prog)
  . forAllParallelProgramC generator' shrinker' precondition' transition' model'
  $ CE.property
  . monadic (ioProperty . runner')
  . predicate

-- | Testable property of parallel programs derived from a
--   'StateMachine' specification.
runParallelProgram
  :: MonadBaseControl IO m
  => Show1 (act Symbolic)
  => Show err
  => HTraversable act
  => StateMachine' model act m err
     -- ^
  -> ParallelProgram act
  -> PropertyM m [(History act err, Property)]
runParallelProgram = runParallelProgram' 10

runParallelProgram'
  :: MonadBaseControl IO m
  => Show1 (act Symbolic)
  => Show err
  => HTraversable act
  => Int -- ^ How many times to execute the parallel program.
  -> StateMachine' model act m err
     -- ^
  -> ParallelProgram act
  -> PropertyM m [(History act err, Property)]
runParallelProgram' n sm@StateMachine{..} prog =
  replicateM n $ do
    (hist, _reason) <- run (executeParallelProgram sm prog)
    return (hist, linearise transition' postcondition' model' hist)

runParallelProgramIncomplete
  :: MonadBaseControl IO m
  => Show1 (act Symbolic)
  => HTraversable act
  => Int -- ^ How many times to execute the parallel program.
  -> StateMachine' model act m err
     -- ^
  -> (forall resp. Typeable resp => act Concrete resp -> model Concrete -> resp)
  -> err
  -> ParallelProgram act
  -> PropertyM m [(History act err, Property)]
runParallelProgramIncomplete _n StateMachine{..} _mock _err _prog =
  undefined
  {-
  replicateM n $ do
    hist <- run (executeParallelProgram semantics' prog)
    return (hist, linearise' transition' postcondition' model' mock err hist)
-}

-- | Takes the output of a parallel program runs and pretty prints a
--   counter example if any of the runs fail.
prettyParallelProgram
  :: MonadIO m
  => HFoldable act
  => Show (Untyped act)
  => ParallelProgram act
  -> [(History act err, Property)] -- ^ Output of 'runParallelProgram.
  -> PropertyM m ()
prettyParallelProgram prog
  = mapM_ (\(hist, prop) ->
              print (toBoxDrawings prog hist) `whenFailM` prop)

------------------------------------------------------------------------

monadicSequentialNoShrink
  :: Monad m
  => Testable a
  => Show (Untyped act)
  => HFoldable act
  => StateMachine' model act m err
  -> (Program act -> PropertyM m a)
     -- ^ Predicate that should hold for all programs.
  -> Property
monadicSequentialNoShrink StateMachine{..} predicate
  = forAllProgramNoShrink generator' precondition' transition' model'
  $ monadic (ioProperty . runner')
  . predicate

forAllProgramNoShrink
  :: Show (Untyped act)
  => HFoldable act
  => Generator model act
  -> Precondition model act
  -> Transition'  model act err
  -> InitialModel model
  -> (Program act -> Property)  -- ^ Predicate that should hold for all
                                --   programs.
  -> Property
forAllProgramNoShrink generator precondition transition model =
  forAll (evalStateT (generateProgram generator precondition transition 0) model)

monadicParallelNoShrink
  :: MonadBaseControl IO m
  => Eq (Untyped act)
  => Show1 (act Symbolic)
  => HFoldable act
  => StateMachine' model act m err
  -> (ParallelProgram act -> PropertyM m ())
     -- ^ Predicate that should hold for all parallel programs.
  -> Property
monadicParallelNoShrink StateMachine{..} predicate
  = forAllParallelProgramNoShrink generator' precondition' transition' model'
  $ monadic (ioProperty . runner')
  . predicate

forAllParallelProgramNoShrink
  :: HFoldable act
  => Generator model act
  -> Precondition model act
  -> Transition'  model act err
  -> InitialModel model
  -> (ParallelProgram act -> Property)  -- ^ Predicate that should hold for all
                                        --   parallel programs.
  -> Property
forAllParallelProgramNoShrink generator precondition transition model =
  forAllShow
    (generateParallelProgram generator precondition transition model)
    (const "")
