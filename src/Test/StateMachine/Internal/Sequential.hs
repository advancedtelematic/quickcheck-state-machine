{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Internal.Sequential
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains helpers for generating, shrinking, and checking
-- sequential programs.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Internal.Sequential
  ( generateProgram
  , generateProgram'
  , filterInvalid
  , getUsedVars
  , liftShrinkInternal
  , validProgram
  , shrinkProgram
  , ExecutionEnv(..)
  , executeProgram
  , executeProgram'
  )
  where

import           Control.Concurrent.STM.TChan
                   (TChan, newTChanIO)
import           Control.Exception.Lifted
                   (SomeException, catch)
import           Control.Monad
                   (filterM, when)
import           Control.Monad.State
                   (State, StateT, evalStateT, get, lift, put, runStateT)
import           Control.Monad.Trans.Control
                   (MonadBaseControl, liftBaseWith)
import           Data.Dynamic
                   (toDyn)
import           Data.Functor.Classes
                   (Show1, showsPrec1)
import           Data.Set
                   (Set)
import qualified Data.Set                                     as S
import           Test.QuickCheck
                   (Gen, choose, shrinkList, sized, suchThat)

import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Internal.Types.Environment
import           Test.StateMachine.Internal.Utils
                   (writeTChanMBC, getChanContents)
import           Test.StateMachine.Types
import           Test.StateMachine.Types.History

------------------------------------------------------------------------

-- | Generate programs whose actions all respect their pre-conditions.
generateProgram
  :: forall model act err
  .  Generator    model act
  -> Precondition model act
  -> Transition'  model act err
  -> Int                     -- ^ Name supply for symbolic variables.
  -> StateT (model Symbolic) Gen (Program act)
generateProgram generator precondition transition index = do
  size <- lift (sized (\k -> choose (0, k)))
  Program <$> go size index
  where
  go :: Int -> Int -> StateT (model Symbolic) Gen [Internal act]
  go 0  _  = return []
  go sz ix = do
    model <- get
    Untyped act <- lift (generator model `suchThat`
      \(Untyped act) -> precondition model act)
    let sym = Symbolic (Var ix)
    put (transition model act (Success sym))
    acts <- go (sz - 1) (ix + 1)
    return (Internal act sym : acts)

generateProgram'
  :: Generator    model act
  -> Precondition model act
  -> Transition'  model act err
  -> model Symbolic
  -> Gen (Program act)
generateProgram' g p t = evalStateT (generateProgram g p t 0)

-- | Filter out invalid actions from a program. An action is invalid if
--   either its pre-condition doesn't hold, or it uses references that
--   are not in scope.
filterInvalid
  :: HFoldable act
  => Precondition model act
  -> Transition'  model act err
  -> Program act
  -> State (model Symbolic, Set Var) (Program act) -- ^ Where @Set Var@
                                                   --   is the scope.
filterInvalid precondition transition
  = fmap Program
  . filterM go
  . unProgram
  where
  go (Internal act sym@(Symbolic var)) = do
    (model, scope) <- get
    let valid = precondition model act && getUsedVars act `S.isSubsetOf` scope
    when valid (put (transition model act (Success sym), S.insert var scope))
    return valid

-- | Returns the set of references an action uses.
getUsedVars :: HFoldable act => act Symbolic a -> Set Var
getUsedVars = hfoldMap (\(Symbolic v) -> S.singleton v)

-- | Given a shrinker of typed actions we can lift it to a shrinker of
--   internal actions.
liftShrinkInternal :: Shrinker act -> (Internal act -> [Internal act])
liftShrinkInternal shrinker (Internal act sym) =
  [ Internal act' sym | act' <- shrinker act ]

validProgram
  :: forall act model err
  .  HFoldable act
  => Precondition model act
  -> Transition' model act err
  -> model Symbolic
  -> Program act
  -> Bool
validProgram precondition transition model0 = go model0 S.empty . unProgram
  where
  go :: model Symbolic -> Set Var -> [Internal act] -> Bool
  go _     _     []                                     = True
  go model scope (Internal act sym@(Symbolic var) : is) =
    valid && go (transition model act (Success sym)) (S.insert var scope) is
    where
    valid = precondition model act && getUsedVars act `S.isSubsetOf` scope

-- | Shrink a program in a pre-condition and scope respecting way.
shrinkProgram
  :: HFoldable act
  => Shrinker  act
  -> Precondition model act
  -> Transition'  model act err
  -> model Symbolic
  ->  Program act             -- ^ Program to shrink.
  -> [Program act]
shrinkProgram shrinker precondition transition model
  = filter (validProgram precondition transition model)
  . map Program
  . shrinkList (liftShrinkInternal shrinker)
  . unProgram

-- | Execute a program and return a history, the final model and a result which
--   contains the information of whether the execution respects the state
--   machine model or not.
executeProgram
  :: MonadBaseControl IO m
  => Show1 (act Symbolic)
  => HTraversable act
  => Show err
  => StateMachine' model act m err
  -> Program act
  -> m (History act err, model Concrete, Reason)
executeProgram sm@StateMachine{..} prog = do
  hchan <- liftBaseWith (const newTChanIO)
  let eenv = ExecutionEnv emptyEnvironment model' model'
  (reason, eenv') <- runStateT (executeProgram' sm hchan (Pid 0) True prog) eenv
  hist <- liftBaseWith (const (getChanContents hchan))
  return (History hist, cmodel eenv', reason)

data ExecutionEnv model = ExecutionEnv
  { env    :: Environment
  , smodel :: model Symbolic
  , cmodel :: model Concrete
  }

executeProgram'
  :: MonadBaseControl IO m
  => Show1 (act Symbolic)
  => HTraversable act
  => Show err
  => StateMachine' model act m err
  -> TChan (HistoryEvent (UntypedConcrete act) err)
  -> Pid
  -> Bool -- ^ Check post-condition?
  -> Program act
  -> StateT (ExecutionEnv model) m Reason
executeProgram' StateMachine{..} hchan pid check = go . unProgram
  where
  go []                                        = return Ok
  go (Internal act sym@(Symbolic var) : iacts) = do

    ExecutionEnv{..} <- get

    if not (precondition' smodel act)
    then
      return PreconditionFailed
    else do
      let Right cact = reify env act

      writeTChanMBC hchan
        (InvocationEvent (UntypedConcrete cact) (showsPrec1 10 act "") var pid)

      mresp <- lift (semantics' cact
                 `catch` (\(e :: SomeException) -> return (Info (show e))))

      writeTChanMBC hchan
        (ResponseEvent (fmap toDyn mresp) (ppResult mresp) pid)

      if check && not (postcondition' cmodel cact mresp)
      then
        return PostconditionFailed
      else do
        case mresp of

          Fail err     -> do
            put (ExecutionEnv
                   { smodel = transition' smodel  act (Fail err)
                   , cmodel = transition' cmodel cact (Fail err)
                   , ..
                   })
            go iacts

          Success resp -> do
            put (ExecutionEnv
                   { smodel = transition' smodel  act (Success sym)
                   , cmodel = transition' cmodel cact (fmap Concrete mresp)
                   , env    = insertConcrete sym (Concrete resp) env
                   })
            go iacts

          Info info    -> return (ExceptionThrown info)
