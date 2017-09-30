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
  , forAllProgramC
  , monadicSequential
  , monadicSequentialC
  , runProgram
  , prettyProgram
  , actionNames
  , checkActionNames

    -- * Parallel property combinators
  , ParallelProgram
  , forAllParallelProgram
  , forAllParallelProgramC
  , History
  , monadicParallel
  , monadicParallelC
  , runParallelProgram
  , runParallelProgram'
  , prettyParallelProgram

    -- * Types
  , module Test.StateMachine.Generics
  , module Test.StateMachine.Types

    -- * Reexport
  , bracketP
  , bracketPC
  , Test.QuickCheck.quickCheck
  ) where

import           Control.Monad.IO.Class
                   (MonadIO)
import           Control.Monad.State
                   (evalStateT, replicateM)
import           Control.Monad.Trans.Control
                   (MonadBaseControl)
import           Data.Map
                   (Map)
import qualified Data.Map                              as M
import           Test.QuickCheck
                   (Property, collect, cover, ioProperty, property)
import qualified Test.QuickCheck
import           Test.QuickCheck.Counterexamples
                   ((:&:)(..), PropertyOf, forAllShrink)
import qualified Test.QuickCheck.Counterexamples       as CE
import           Test.QuickCheck.Monadic
                   (PropertyM, monadic, run)

import           Test.StateMachine.Generics
import           Test.StateMachine.Internal.Parallel
import           Test.StateMachine.Internal.Sequential
import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Internal.Utils
                   (bracketP, bracketPC, whenFailM)
import           Test.StateMachine.Types
import           Test.StateMachine.Types.History

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
  property
  . forAllProgramC generator shrinker precondition transition model
  . \prop p -> CE.property (prop p)

forAllProgramC
  :: Show (Untyped act)
  => HFoldable act
  => Generator model act
  -> Shrinker act
  -> Precondition model act
  -> Transition   model act
  -> InitialModel model
  -> (Program act -> PropertyOf a)  -- ^ Predicate that should hold for all
                                    --   programs.
  -> PropertyOf (Program act :&: a)
forAllProgramC generator shrinker precondition transition model =
  forAllShrink
    (evalStateT (generateProgram generator precondition transition 0) model)
    (shrinkProgram shrinker precondition transition model)

monadicSequential
  :: Monad m
  => Show (Untyped act)
  => HFoldable act
  => StateMachine model act m
  -> (Program act -> PropertyM m a)
  -> Property
monadicSequential sm = property . monadicSequentialC sm

monadicSequentialC
  :: Monad m
  => Show (Untyped act)
  => HFoldable act
  => StateMachine model act m
  -> (Program act -> PropertyM m a)
  -> PropertyOf (Program act)
monadicSequentialC StateMachine {..} predicate
  = fmap (\(prog :&: ()) -> prog)
  . forAllProgramC generator' shrinker' precondition' transition' model'
  $ CE.property
  . monadic (ioProperty . runner')
  . predicate

runProgram
  :: forall m act model
  .  Monad m
  => Show (Untyped act)
  => HFunctor act
  => StateMachine  model act m
  -> Program act
  -> PropertyM m (History act, model Concrete, Property)
runProgram sm = run . executeProgram sm

prettyProgram
  :: MonadIO m
  => Program act -> History act -> model Concrete -> Property -> PropertyM m ()
prettyProgram _ hist _ prop = putStrLn (ppHistory hist) `whenFailM` prop

actionNames :: forall act. Constructors act => Program act -> [(Constructor, Int)]
actionNames = M.toList . foldl go M.empty . unProgram
  where
  go :: Map Constructor Int -> Internal act -> Map Constructor Int
  go ih (Internal act _) = M.insertWith (+) (constructor act) 1 ih

-- | Print distribution of actions and fail if some actions have not been
--   executed.
checkActionNames :: Constructors act => Program act -> Property -> Property
checkActionNames prog
  = collect names
  . cover (length names == numOfConstructors) 1 "coverage"
  where
    names = actionNames prog
    numOfConstructors = nConstructors prog

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
  property
  . forAllParallelProgramC generator shrinker precondition transition model
  . \prop p -> CE.property (prop p)

forAllParallelProgramC
  :: Show (Untyped act)
  => HFoldable act
  => Generator model act
  -> Shrinker act
  -> Precondition model act
  -> Transition   model act
  -> InitialModel model
  -> (ParallelProgram act -> PropertyOf a) -- ^ Predicate that should hold
                                           --   for all parallel programs.
  -> PropertyOf (ParallelProgram act :&: a)
forAllParallelProgramC generator shrinker precondition transition model =
  forAllShrink
    (generateParallelProgram generator precondition transition model)
    (shrinkParallelProgram shrinker precondition transition model)

monadicParallel
  :: MonadBaseControl IO m
  => Show (Untyped act)
  => HFoldable act
  => StateMachine model act m
  -> (ParallelProgram act -> PropertyM m ())
  -> Property
monadicParallel sm = property . monadicParallelC sm

monadicParallelC
  :: MonadBaseControl IO m
  => Show (Untyped act)
  => HFoldable act
  => StateMachine model act m
  -> (ParallelProgram act -> PropertyM m ())
  -> PropertyOf (ParallelProgram act)
monadicParallelC StateMachine {..} predicate
  = fmap (\(prog :&: ()) -> prog)
  . forAllParallelProgramC generator' shrinker' precondition' transition' model'
  $ CE.property
  . monadic (ioProperty . runner')
  . predicate

runParallelProgram
  :: MonadBaseControl IO m
  => Show (Untyped act)
  => HTraversable act
  => StateMachine model act m
  -> ParallelProgram act
  -> PropertyM m [(History act, Property)]
runParallelProgram = runParallelProgram' 10

runParallelProgram'
  :: MonadBaseControl IO m
  => Show (Untyped act)
  => HTraversable act
  => Int
  -> StateMachine model act m
  -> ParallelProgram act
  -> PropertyM m [(History act, Property)]
runParallelProgram' n StateMachine {..} prog =
  replicateM n $ do
    hist <- run (executeParallelProgram semantics' prog)
    return (hist, linearise transition' postcondition' model' hist)

prettyParallelProgram
  :: MonadIO m
  => HFoldable act
  => ParallelProgram act -> [(History act, Property)] -> PropertyM m ()
prettyParallelProgram prog
  = mapM_ (\(hist, prop) ->
              print (toBoxDrawings prog hist) `whenFailM` prop)

