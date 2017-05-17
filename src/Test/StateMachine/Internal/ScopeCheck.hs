{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.StateMachine.Internal.ScopeCheck
  ( scopeCheck
  , scopeCheckFork
  ) where

import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Types
import           Test.StateMachine.Utils

------------------------------------------------------------------------

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

scopeCheckFork
  :: (IxFoldable cmd, HasResponse cmd)
  => Fork [IntRefed cmd] -> Bool
scopeCheckFork (Fork l p r) =
  scopeCheck (p ++ l) &&
  scopeCheck (p ++ r)
