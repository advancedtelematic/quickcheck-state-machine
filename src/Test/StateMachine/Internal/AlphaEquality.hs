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
-- This module provides \(\alpha\)-equality for internal commands. This
-- functionality isn't used anywhere in the library, but can be useful
-- for writing
-- <https://github.com/advancedtelematic/quickcheck-state-machine/blob/master/example/src/MutableReference/Prop.hs metaproperties>.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Internal.AlphaEquality
  ( alphaEq
  , alphaEqFork
  ) where

import           Control.Monad.State
                   (State, get, modify, evalState, runState)
import           Data.Map
                   (Map)
import qualified Data.Map                    as M

import           Test.StateMachine.Prototype

------------------------------------------------------------------------

-- | Check if two lists of actions are equal modulo
--   \(\alpha\)-conversion.
alphaEq
  :: (HFunctor act, Eq (Internal act))
  => [Internal act] -> [Internal act]     -- ^ The two input lists.
  -> Bool
alphaEq acts1 acts2 = canonical acts1 == canonical acts2

canonical :: HFunctor act => [Internal act] -> [Internal act]
canonical = fst . flip runState M.empty . canonical'

canonical' :: HFunctor act => [Internal act] -> State (Map Var Var) [Internal act]
canonical' []                                   = return []
canonical' (Internal act (Symbolic var) : acts) = do
  env     <- get
  let act' = hfmap (\(Symbolic var) -> Symbolic (env M.! var)) act
      var' = Var (M.size env)
      sym' = Symbolic var'
  modify (M.insert var var')
  ih      <- canonical' acts
  return (Internal act' sym' : ih)

-- | Check if two forks of commands are equal modulo
--   \(\alpha\)-conversion.
alphaEqFork
  :: (HFunctor act, Eq (Internal act))
  => Fork [Internal act] -> Fork [Internal act] -- ^ The two input forks.
  -> Bool
alphaEqFork f1 f2 = canonicalFork f1 == canonicalFork f2

canonicalFork :: HFunctor act => Fork [Internal act] -> Fork [Internal act]
canonicalFork (Fork l p r) = Fork l' p' r'
  where
  (p', m) = runState  (canonical' p) M.empty
  l'      = evalState (canonical' l) m
  r'      = evalState (canonical' r) m
