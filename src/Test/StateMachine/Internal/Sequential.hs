{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE Rank2Types          #-}
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
  , checkProgram
  )
  where

import           Control.Monad
                   (filterM, foldM_, when)
import           Control.Monad.State
                   (State, StateT, get, lift, modify, put, evalState)
import           Data.Set
                   (Set)
import qualified Data.Set                                     as S
import           Test.QuickCheck
                   (Gen, shrinkList, sized, choose, suchThat)
import           Test.QuickCheck.Monadic
                   (PropertyM, pre, run)

import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Internal.Types.Environment
import           Test.StateMachine.Internal.Utils
import           Test.StateMachine.Types

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

-- | For each action in a program, check that if the pre-condition holds
--   for the action, then so does the post-condition.
checkProgram
  :: Monad m
  => HFunctor act
  => Precondition  model act
  -> Transition    model act
  -> Postcondition model act
  -> model Symbolic  -- ^ The model with symbolic references is used to
                     -- check pre-conditions against.
  -> model Concrete  -- ^ While the one with concrete referenes is used
                     -- for checking post-conditions.
  -> Semantics act m
  -> Program   act
  -> PropertyM (StateT Environment m) ()
checkProgram precondition transition postcondition smodel0 cmodel0 semantics
  = foldM_ go (smodel0, cmodel0)
  . unProgram
  where
  go (smodel, cmodel) (Internal act sym) = do
    pre (precondition smodel act)
    env <- run get
    let cact = hfmap (fromSymbolic env) act
    resp <- run (lift (semantics cact))
    liftProperty (postcondition cmodel cact resp)
    let cresp = Concrete resp
    run (modify (insertConcrete sym cresp))
    return (transition smodel act sym, transition cmodel cact cresp)
    where
    fromSymbolic :: Environment -> Symbolic v ->  Concrete v
    fromSymbolic env sym' = case reifyEnvironment env sym' of
      Left  err -> error (show err)
      Right con -> con
