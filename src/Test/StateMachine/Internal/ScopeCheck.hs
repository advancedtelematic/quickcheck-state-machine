{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.StateMachine.Internal.ScopeCheck
  ( scopeCheck
  , scopeCheckFork
  ) where

import           Test.StateMachine.Types
import           Test.StateMachine.Utils

------------------------------------------------------------------------

scopeCheck
  :: forall cmd. (IxFoldable cmd, HasResponse cmd)
  => [(Pid, IntRefed cmd)] -> Bool
scopeCheck = go []
  where
  go :: [IntRef] -> [(Pid, IntRefed cmd)] -> Bool
  go _    []                           = True
  go refs ((_, IntRefed c miref) : cs) = case response c of
    SReference _  ->
      let refs' = miref : refs in
      all (\(Ex _ ref) -> ref `elem` refs) (itoList c) &&
      go refs' cs
    SResponse     ->
      all (\(Ex _ ref) -> ref `elem` refs) (itoList c) &&
      go refs cs

scopeCheckFork
  :: (IxFoldable cmd, HasResponse cmd)
  => Fork [IntRefed cmd] -> Bool
scopeCheckFork (Fork l p r) =
  let p' = zip (repeat 0) p in
  scopeCheck (p' ++ zip (repeat 1) l) &&
  scopeCheck (p' ++ zip (repeat 2) r)
