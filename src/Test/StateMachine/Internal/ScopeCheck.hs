{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Internal.ScopeCheck
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module provides scope-checking for internal commands. This
-- functionality isn't used anywhere in the library, but can be useful
-- for writing
-- <https://github.com/advancedtelematic/quickcheck-state-machine/blob/master/example/src/MutableReference/Prop.hs metaproperties>.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Internal.ScopeCheck
  ( scopeCheck
  , scopeCheckFork
  ) where

import           Data.Set
                   (Set)
import qualified Data.Set                    as S

import           Test.StateMachine.Prototype

------------------------------------------------------------------------

-- | Scope-check a list of internal actions, i.e. make sure that no
--   action uses a reference that doesn't exist.
scopeCheck :: forall act. HFoldable act => [Internal act] -> Bool
scopeCheck = go S.empty
  where
  go :: Set Var -> [Internal act] -> Bool
  go _     []                                        = True
  go known (Internal act sym@(Symbolic var) : iacts) =
    getUsedVars act `S.isSubsetOf` known && go (S.insert var known) iacts

-- | Same as above, but for forks rather than lists.
scopeCheckFork :: HFoldable act => Fork [Internal act] -> Bool
scopeCheckFork (Fork l p r) =
  scopeCheck (p ++ l) && scopeCheck (p ++ r)
