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

import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Types

------------------------------------------------------------------------

-- | Scope-check a list of untyped internal commands, i.e. make sure
--   that no command uses a reference that doesn't exist.
scopeCheck
  :: forall cmd. (IxFoldable cmd, HasResponse cmd)
  => [IntRefed cmd] -> Bool
scopeCheck = go []
  where
  go :: [IntRef] -> [IntRefed cmd] -> Bool
  go _    []                      = True
  go refs (IntRefed c miref : cs) = case response c of
    SReference _  ->
      all (\(Ex _ ref) -> ref `elem` refs) (itoList c) &&
      go (miref : refs) cs
    SResponse     ->
      all (\(Ex _ ref) -> ref `elem` refs) (itoList c) &&
      go refs cs

-- | Same as above, but for forks rather than lists.
scopeCheckFork
  :: (IxFoldable cmd, HasResponse cmd)
  => Fork [IntRefed cmd] -> Bool
scopeCheckFork (Fork l p r) =
  scopeCheck (p ++ l) &&
  scopeCheck (p ++ r)
