{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE Rank2Types          #-}

module Test.StateMachine.Types.AlphaEquality
  ( alphaEq
  , alphaEqFork
  ) where

import           Control.Monad                    (forM)
import           Control.Monad.State              (get, put, runState)
import           Data.Singletons.Decide           (SDecide)
import           Data.Singletons.Prelude          (Proxy (..))

import           Test.StateMachine.Internal.IxMap (IxMap)
import qualified Test.StateMachine.Internal.IxMap as IxM
import           Test.StateMachine.Types
import           Test.StateMachine.Utils

------------------------------------------------------------------------

canonical'
  :: SDecide ix
  => IxTraversable cmd
  => (forall resp refs. cmd resp refs -> SResponse ix resp)
  -> IxMap ix IntRef ConstIntRef
  -> [IntRefed cmd]
  -> ([IntRefed cmd], IxMap ix IntRef ConstIntRef)
canonical' returns im = flip runState im . go
  where
  go xs = forM xs $ \(Untyped' cmd ref) -> do
    cmd' <- ifor (Proxy :: Proxy ConstIntRef) cmd $ \ ix iref -> do
      (IxM.! (ix, iref)) <$> get
    ref' <- case returns cmd of
      SResponse    -> return ()
      SReference i -> do
        m <- get
        let ref' = IntRef (Ref $ IxM.size i m) (Pid 0)
        put $ IxM.insert i ref ref' m
        return $ ref'
    return $ Untyped' cmd' ref'

canonical
  :: SDecide ix
  => IxTraversable cmd
  => (forall resp refs. cmd resp refs -> SResponse ix resp)
  -> [IntRefed cmd]
  -> [IntRefed cmd]
canonical returns = fst . canonical' returns IxM.empty

canonicalFork
  :: SDecide ix
  => IxTraversable cmd
  => (forall resp refs. cmd resp refs -> SResponse ix resp)
  -> Fork [IntRefed cmd]
  -> Fork [IntRefed cmd]
canonicalFork returns (Fork l p r) = Fork l' p' r'
  where
  (p', im') = canonical' returns IxM.empty p
  l'        = fst $ canonical' returns im' l
  r'        = fst $ canonical' returns im' r

alphaEq
  :: SDecide ix
  => IxTraversable cmd
  => Eq (IntRefed cmd)
  => (forall resp refs. cmd resp refs -> SResponse ix resp)
  -> [IntRefed cmd]
  -> [IntRefed cmd]
  -> Bool
alphaEq returns c0 c1
  = canonical returns c0 == canonical returns c1

alphaEqFork
  :: SDecide ix
  => IxTraversable cmd
  => Eq (IntRefed cmd)
  => (forall resp refs. cmd resp refs -> SResponse ix resp)
  -> Fork [IntRefed cmd]
  -> Fork [IntRefed cmd]
  -> Bool
alphaEqFork returns f1 f2
  = canonicalFork returns f1 == canonicalFork returns f2
