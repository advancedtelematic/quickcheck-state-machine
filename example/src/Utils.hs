{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Utils
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module provides a couple of helpers for writing properties about
-- state machine properties.
--
-----------------------------------------------------------------------------

module Utils
  ( minimalShrinkHelper
  , alphaEq
  , structuralSubset
  , scopeCheck
  , scopeCheckParallel
  , possibleShrinks'
  )
  where

import           Control.Arrow
                   ((&&&))
import           Control.Monad
                   (foldM)
import           Control.Monad.State
                   (State, evalState, get, modify, runState)
import           Data.List
                   (intersect)
import           Data.Map
                   (Map)
import qualified Data.Map                              as M
import           Data.Set
                   (Set)
import qualified Data.Set                              as S
import           Data.Tree
                   (Tree(Node), unfoldTree)
import           Test.QuickCheck
                   (Property)
import           Test.QuickCheck.Counterexamples
                   (PropertyOf)

import           Test.StateMachine.Internal.Parallel
                   (shrinkParallelProgram)
import           Test.StateMachine.Internal.Sequential
                   (getUsedVars)
import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Internal.Utils
import           Test.StateMachine.Types

------------------------------------------------------------------------

minimalShrinkHelper
  :: forall act model err
  .  Eq   (Untyped act)
  => Show (Untyped act)
  => HFoldable act
  => Shrinker  act
  -> Precondition model act
  -> Transition'  model act err
  -> model Symbolic
  -> PropertyOf (ParallelProgram act)
  -> (ParallelProgram act -> Bool)
  -> Property
minimalShrinkHelper shrinker precondition transition model prop isMinimal
  = shrinkPropertyHelperC prop $ \ce ->
      isMinimal ce || hasMinimalShrink ce
  where
  hasMinimalShrink :: ParallelProgram act -> Bool
  hasMinimalShrink
    = anyTree isMinimal
    . possibleShrinks
    where
    anyTree :: (a -> Bool) -> Tree a -> Bool
    anyTree p = foldTree (\x ih -> p x || or ih)
      where
      -- `foldTree` is part of `Data.Tree` in later versions of `containers`.
      foldTree :: (a -> [b] -> b) -> Tree a -> b
      foldTree f = go where
        go (Node x ts) = f x (map go ts)

  possibleShrinks :: ParallelProgram act -> Tree (ParallelProgram act)
  possibleShrinks = possibleShrinks'
    (shrinkParallelProgram shrinker precondition transition model)

possibleShrinks' :: (a -> [a]) -> a -> Tree a
possibleShrinks' shr = unfoldTree (id &&& shr)

------------------------------------------------------------------------

-- | Check if two lists of actions are equal modulo
--   \(\alpha\)-conversion.
alphaEq
  :: (HFunctor act, Eq (Program act))
  => Program act -> Program act     -- ^ The two input programs.
  -> Bool
alphaEq acts1 acts2 = canonical acts1 == canonical acts2

canonical :: HFunctor act => Program act -> Program act
canonical = Program . fst . flip runState M.empty . canonical' . unProgram

canonical' :: HFunctor act => [Internal act] -> State (Map Var Var) [Internal act]
canonical' []                                   = return []
canonical' (Internal act (Symbolic var) : acts) = do
  env     <- get
  let act' = hfmap (\(Symbolic v) -> Symbolic (env M.! v)) act
      var' = Var (M.size env)
      sym' = Symbolic var'
  modify (M.insert var var')
  ih      <- canonical' acts
  return (Internal act' sym' : ih)

structuralSubset
  :: (Eq (Untyped act), HFunctor act)
  => [Untyped act] -> [Untyped act] -> ParallelProgram act -> Bool
structuralSubset prefix suffixes (ParallelProgram prefix' suffixes'0)
  =  prefix   ==           toUntyped (Program prefix'')
  && suffixes `isSubsetOf` toUntyped (Program (mconcat suffixes''))
  where
  suffixes'     = parallelProgramToList suffixes'0
  (prefix'', m) = runState (canonical' (unProgram prefix')) M.empty
  suffixes''    = evalState (go (map unProgram suffixes')) m
    where
    go = foldM (\ih iacts -> (:) <$> canonical' iacts <*> pure ih) []

  isSubsetOf :: Eq a => [a] -> [a] -> Bool
  r `isSubsetOf` s = r == r `intersect` s

  toUntyped :: Program act -> [Untyped act]
  toUntyped = map (\(Internal act _) -> Untyped act) . unProgram

------------------------------------------------------------------------

-- | Scope-check a program, i.e. make sure that no action uses a
--   reference that doesn't exist.
scopeCheck :: forall act. HFoldable act => Program act -> Bool
scopeCheck = go S.empty . unProgram
  where
  go :: Set Var -> [Internal act] -> Bool
  go _     []                                    = True
  go known (Internal act (Symbolic var) : iacts) =
    getUsedVars act `S.isSubsetOf` known && go (S.insert var known) iacts

-- | Same as above, but for parallel programs.
scopeCheckParallel :: HFoldable act => ParallelProgram act -> Bool
scopeCheckParallel = scopeCheck . flattenParallelProgram
