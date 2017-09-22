{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}

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
  , runAndCheckProgram
  , runAndCheckProgram'
  , StateMachine(..)
  , monadicSequential
  , runCommands
  , prettyCommands
  , commandNames
  , checkCommandNames

    -- * Parallel property combinators
  , ParallelProgram
  , forAllParallelProgram
  , History
  , runParallelProgram
  , runParallelProgram'
  , checkParallelProgram
  , monadicParallel
  , runParallelCommands
  , runParallelCommands'
  , prettyParallelCommands
  , prettyParallelCommands'

    -- * Types
  , module Test.StateMachine.Types

    -- * Rexport
  , bracketP
  , Test.QuickCheck.quickCheck
  ) where

import           Control.Monad
                   (foldM)
import           Control.Monad.IO.Class
                   (MonadIO)
import           Control.Monad.State
                   (evalStateT, replicateM, replicateM_)
import           Control.Monad.Trans.Control
                   (MonadBaseControl)
import           Data.Dynamic
                   (toDyn)
import           Data.Map
                   (Map)
import qualified Data.Map                                     as M
import           Data.Monoid
                   ((<>))
import qualified Test.QuickCheck                              as Test.QuickCheck
import           Test.QuickCheck.Monadic
                   (PropertyM, monadic, monadicIO, run)
import           Test.QuickCheck.Property
                   (Property, collect, counterexample, cover,
                   forAllShrink, ioProperty, property, (.&&.))

import           Test.StateMachine.Internal.Parallel
import           Test.StateMachine.Internal.Sequential
import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Internal.Types.Environment
import           Test.StateMachine.Internal.Utils
                   (liftProperty, whenFailM, bracketP)
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

data StateMachine model act m = StateMachine
  { generator'     :: Generator model act
  , shrinker'      :: Shrinker  act
  , precondition'  :: Precondition model act
  , transition'    :: Transition   model act
  , postcondition' :: Postcondition model act
  , model'         :: InitialModel model
  , semantics'     :: Semantics act m
  , runner'        :: m Property -> IO Property
  }

monadicSequential
  :: Monad m
  => Show (Untyped act)
  => HFoldable act
  => StateMachine model act m
  -> (Program act -> PropertyM m a)
  -> Property
monadicSequential StateMachine {..} predicate
  = forAllProgram generator' shrinker' precondition' transition' model'
  $ monadic (ioProperty . runner')
  . predicate

runCommands
  :: forall m act model
  .  Monad m
  => Show (Untyped act)
  => HFunctor act
  => StateMachine  model act m
  -> Program act
  -> PropertyM m (History act, model Concrete, Property)
runCommands sm = run . runCommands' sm

runCommands'
  :: forall m act model
  .  Monad m
  => Show (Untyped act)
  => HFunctor act
  => StateMachine  model act m
  -> Program act
  -> m (History act, model Concrete, Property)
runCommands' StateMachine {..}
  = fmap (\(hist, _, cmodel, _, prop) -> (hist, cmodel, prop))
  . foldM go (mempty, model', model', emptyEnvironment, property True)
  . unProgram
  where
  go :: (History act, model Symbolic, model Concrete, Environment, Property)
     -> Internal act
     -> m (History act, model Symbolic, model Concrete, Environment, Property)
  go (hist, smodel, cmodel, env, prop) (Internal act sym@(Symbolic var)) = do
    if not (precondition' smodel act)
    then
      return ( hist
             , smodel
             , cmodel
             , env
             , counterexample ("precondition failed for: " ++ show (Untyped act)) prop
             )
    else do
      let cact = hfmap (fromSymbolic env) act
      resp <- semantics' cact
      let cresp = Concrete resp
          hist' = History
            [ InvocationEvent (UntypedConcrete cact) (show (Untyped act)) var (Pid 0)
            , ResponseEvent (toDyn cresp) (show resp) (Pid 0)
            ]
      return ( hist <> hist'
             , transition' smodel act sym
             , transition' cmodel cact cresp
             , insertConcrete sym cresp env
             , prop .&&. postcondition' cmodel cact resp
             )
    where
    fromSymbolic :: Environment -> Symbolic v ->  Concrete v
    fromSymbolic env' sym' = case reifyEnvironment env' sym' of
      Left  err -> error (show err)
      Right con -> con

prettyCommands
  :: MonadIO m
  => Program act -> History act -> model Concrete -> Property -> PropertyM m ()
prettyCommands _ hist _ prop = putStrLn (ppHistory hist) `whenFailM` prop

commandNames :: forall act. Show (Untyped act) => Program act -> [(String, Int)]
commandNames = M.toList . foldl go M.empty . unProgram
  where
  go :: Map String Int -> Internal act -> Map String Int
  go ih (Internal act _) = M.insertWith (+) (name act) 1 ih
    where
    -- XXX: This will fail for infix constructors, we need template Haskell to
    -- do this properly...
    name = takeWhile (/= ' ') . show . Untyped

-- | Print distribution of commands and fail if some commands have not been
--   executed.
checkCommandNames :: Show (Untyped act) => Program act -> Int -> Property -> Property
checkCommandNames prog numOfConstructors
  = collect names
  . cover (length names == numOfConstructors) 1 "coverage"
  where
  names = commandNames prog

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

monadicParallel
  :: MonadBaseControl IO m
  => Show (Untyped act)
  => HFoldable act
  => StateMachine model act m
  -> (ParallelProgram act -> PropertyM m ())
  -> Property
monadicParallel StateMachine {..} predicate
  = forAllParallelProgram generator' shrinker' precondition' transition' model'
  $ monadic (ioProperty . runner')
  . predicate

runParallelCommands
  :: MonadBaseControl IO m
  => Show (Untyped act)
  => HTraversable act
  => StateMachine model act m
  -> ParallelProgram act
  -> PropertyM m (History act, Property)
runParallelCommands StateMachine {..} prog = do
  hist <- run (executeParallelProgram' semantics' prog)
  return (hist, linearise transition' postcondition' model' hist)

runParallelCommands'
  :: MonadBaseControl IO m
  => Show (Untyped act)
  => HTraversable act
  => StateMachine model act m
  -> ParallelProgram act
  -> PropertyM m [(History act, Property)]
runParallelCommands' StateMachine {..} prog =
  replicateM 10 $ do
    hist <- run (executeParallelProgram' semantics' prog)
    return (hist, linearise transition' postcondition' model' hist)

prettyParallelCommands
  :: MonadIO m
  => HFoldable act
  => ParallelProgram act -> History act -> Property -> PropertyM m ()
prettyParallelCommands prog hist prop
  = print (toBoxDrawings' prog hist) `whenFailM` prop

prettyParallelCommands'
  :: MonadIO m
  => HFoldable act
  => ParallelProgram act -> [(History act, Property)] -> PropertyM m ()
prettyParallelCommands' prog
  = mapM_ (\(hist, prop) ->
              print (toBoxDrawings' prog hist) `whenFailM` prop)

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
