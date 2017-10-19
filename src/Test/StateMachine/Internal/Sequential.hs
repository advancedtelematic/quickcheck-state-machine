{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
  , filterInvalid
  , getUsedVars
  , liftShrinkInternal
  , shrinkProgram
  , executeProgram
  , executeProgram'
  )
  where

import           Control.Monad
                   (filterM, foldM, when)
import           Control.Monad.State
                   (State, StateT, evalState, get, lift, put)
import           Data.Dynamic
                   (toDyn)
import           Data.Functor.Classes
                   (Show1, showsPrec1)
import           Data.Monoid
                   ((<>))
import           Data.Set
                   (Set)
import qualified Data.Set                                     as S
import           Data.Void
                   (Void)
import           Test.QuickCheck
                   (Gen, Property, choose, counterexample, property,
                   shrinkList, sized, suchThat, (.&&.))

import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Internal.Types.Environment
import           Test.StateMachine.Types
import           Test.StateMachine.Types.History

------------------------------------------------------------------------

-- | Generate programs whose actions all respect their pre-conditions.
generateProgram
  :: forall model act
  .  Generator    model act
  -> Precondition model act
  -> Transition   model act
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
    put (transition model act sym)
    acts <- go (sz - 1) (ix + 1)
    return (Internal act sym : acts)

-- | Filter out invalid actions from a program. An action is invalid if
--   either its pre-condition doesn't hold, or it uses references that
--   are not in scope.
filterInvalid
  :: HFoldable act
  => Precondition model act
  -> Transition   model act
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
    when valid (put (transition model act sym, S.insert var scope))
    return valid

-- | Returns the set of references an action uses.
getUsedVars :: HFoldable act => act Symbolic a -> Set Var
getUsedVars = hfoldMap (\(Symbolic v) -> S.singleton v)

-- | Given a shrinker of typed actions we can lift it to a shrinker of
--   internal actions.
liftShrinkInternal :: Shrinker act -> (Internal act -> [Internal act])
liftShrinkInternal shrinker (Internal act sym) =
  [ Internal act' sym | act' <- shrinker act ]

-- | Shrink a program in a pre-condition and scope respecting way.
shrinkProgram
  :: HFoldable act
  => Shrinker  act
  -> Precondition model act
  -> Transition   model act
  -> model Symbolic
  ->  Program act             -- ^ Program to shrink.
  -> [Program act]
shrinkProgram shrinker precondition transition model
  = map ( flip evalState (model, S.empty)
        . filterInvalid precondition transition
        . Program
        )
  . shrinkList (liftShrinkInternal shrinker)
  . unProgram

-- | Execute a program and return a history, the final model and a property
--   which contains the information of whether the execution respects the state
--   machine model or not.
executeProgram
  :: forall m act err model
  .  Monad m
  => Show (Untyped act)
  => HTraversable act
  => StateMachine' model act err m
  -> Program act
  -> m (History act err, model Concrete, Property)
executeProgram StateMachine {..}
  = fmap (\(hist, _, cmodel, _, prop) -> (hist, cmodel, prop))
  . foldM go (mempty, model', model', emptyEnvironment, property True)
  . unProgram
  where
  go :: (History act err, model Symbolic, model Concrete, Environment, Property)
     -> Internal act
     -> m (History act err, model Symbolic, model Concrete, Environment, Property)
  go (hist, smodel, cmodel, env, prop) (Internal act sym@(Symbolic var)) =
    if not (precondition' smodel act)
    then
      return ( hist
             , smodel
             , cmodel
             , env
             , counterexample ("precondition failed for: " ++ show (Untyped act)) prop
             )
    else
      case reify env act of

                      -- This means that the reference that the action uses
                      -- failed to be created, so we do nothing.
        Left _     -> return (hist, smodel, cmodel, env, prop)

        Right cact -> do
          mresp <- semantics' cact
          case mresp of
            Fail err -> do
              let hist' = History
                    [ InvocationEvent (UntypedConcrete cact) (show (Untyped act)) var (Pid 0)
                    , ResponseEvent (Fail err) "<fail>" (Pid 0)
                    ]
              return ( hist <> hist'
                     , smodel
                     , cmodel
                     , env
                     , prop .&&. postcondition' cmodel cact (Fail err)
                     )
            OkResponse resp  -> do
              let cresp = Concrete resp
                  hist' = History
                    [ InvocationEvent (UntypedConcrete cact) (show (Untyped act)) var (Pid 0)
                    , ResponseEvent (OkResponse (toDyn cresp)) (show resp) (Pid 0)
                    ]
              return ( hist <> hist'
                     , transition' smodel act sym
                     , transition' cmodel cact cresp
                     , insertConcrete sym cresp env
                     , prop .&&. postcondition' cmodel cact (OkResponse resp)
                     )

executeProgram'
  :: forall m act model
  .  Monad m
  => Show1 (act Symbolic)
  => HTraversable act
  => StateMachine'' model act m
  -> Program act
  -> m (History act Void, model Concrete, Reason)
executeProgram' StateMachine'' {..}
  = fmap (\(hist, _, cmodel, _, reason) -> (hist, cmodel, reason))
  . go (mempty, model'', model'', emptyEnvironment)
  . unProgram
  where
  go :: (History act err, model Symbolic, model Concrete, Environment)
     -> [Internal act]
     -> m (History act err, model Symbolic, model Concrete, Environment, Reason)
  go (hist, smodel, cmodel, env)  []                                       =
    return (hist, smodel, cmodel, env, Ok)
  go (hist, smodel, cmodel, env)  (Internal act sym@(Symbolic var) : acts) =
    if not (precondition'' smodel act)
    then
      return ( hist
             , smodel
             , cmodel
             , env
             , PreconditionFailed
             )
    else
      case reify env act of

                      -- This means that the reference that the action uses
                      -- failed to be created, so we do nothing.
        Left _     -> return (hist, smodel, cmodel, env, ReferenceFailed)

        Right cact -> do
          resp <- semantics'' cact
          let hist' = hist <> History
                [ InvocationEvent (UntypedConcrete cact) (showsPrec1 10 act "") var (Pid 0)
                , ResponseEvent (OkResponse (toDyn resp)) (show resp) (Pid 0)
                ]
          if not (postcondition'' cmodel cact resp)
          then
            return ( hist'
                   , smodel
                   , cmodel
                   , env
                   , PostconditionFailed
                   )
          else do
            let cresp = Concrete resp
            go ( hist'
               , transition'' smodel act sym
               , transition'' cmodel cact cresp
               , insertConcrete sym cresp env
               )
               acts
