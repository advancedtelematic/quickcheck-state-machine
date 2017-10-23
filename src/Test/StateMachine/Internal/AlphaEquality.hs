{-# LANGUAGE FlexibleContexts #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Internal.AlphaEquality
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module provides \(\alpha\)-equality for internal actions. This
-- functionality isn't used anywhere in the library, but can be useful
-- for writing
-- <https://github.com/advancedtelematic/quickcheck-state-machine/blob/master/example/src/MutableReference/Prop.hs metaproperties>.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Internal.AlphaEquality
  ( alphaEq
  , alphaEqFork
  , alphaEqParallel
  ) where

import           Control.Monad
                   (foldM)
import           Control.Monad.State
                   (State, evalState, get, modify, runState)
import           Data.Map
                   (Map)
import qualified Data.Map                         as M

import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Types

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

-- | Check if two forks of actions are equal modulo
--   \(\alpha\)-conversion.
alphaEqFork
  :: (HFunctor act, Eq (Program act))
  => Fork (Program act) -> Fork (Program act) -- ^ The two input forks.
  -> Bool
alphaEqFork f1 f2 = canonicalFork f1 == canonicalFork f2

canonicalFork :: HFunctor act => Fork (Program act) -> Fork (Program act)
canonicalFork (Fork l p r) = Fork (Program l') (Program p') (Program r')
  where
  (p', m) = runState  (canonical' (unProgram p)) M.empty
  l'      = evalState (canonical' (unProgram l)) m
  r'      = evalState (canonical' (unProgram r)) m

alphaEqParallel
  :: (HFunctor act, Eq (Untyped act))
  => ParallelProgram' act -> ParallelProgram' act -- ^ The two input programs.
  -> Bool
alphaEqParallel f1 f2 = canonicalParallel f1 == canonicalParallel f2

canonicalParallel :: HFunctor act => ParallelProgram' act -> ParallelProgram' act
canonicalParallel (ParallelProgram' prefix suffixes)
  = ParallelProgram' (Program prefix') (map Program suffixes')
  where
  (prefix', m) = runState (canonical' (unProgram prefix)) M.empty
  suffixes'    = evalState (go (map unProgram suffixes)) m
    where
    go = foldM (\ih iacts -> (:) <$> canonical' iacts <*> pure ih) []
