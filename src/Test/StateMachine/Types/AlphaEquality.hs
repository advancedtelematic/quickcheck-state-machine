{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ExplicitNamespaces  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeInType          #-}

module Test.StateMachine.Types.AlphaEquality
  ( alphaEq
  , alphaEqFork
  ) where

import           Control.Monad                    (forM)
import           Control.Monad.State              (State, get, put, runState)
import           Data.Kind                        (type (*))
import           Data.Singletons.Decide           (SDecide)
import           Data.Singletons.Prelude          (Proxy (..))

import           Test.StateMachine.Internal.IxMap (IxMap)
import qualified Test.StateMachine.Internal.IxMap as IxM
import           Test.StateMachine.Types
import           Test.StateMachine.Utils

------------------------------------------------------------------------

canonical'
  :: forall (ix :: *) (cmd :: Signature ix)
  .  SDecide ix
  => IxTraversable cmd
  => HasResponse   cmd
  => IxMap ix IntRef ConstIntRef
  -> [IntRefed cmd]
  -> ([IntRefed cmd], IxMap ix IntRef ConstIntRef)
canonical' im = flip runState im . go
  where
  go :: [IntRefed cmd] -> State (IxMap ix IntRef ConstIntRef) [IntRefed cmd]
  go xs = forM xs $ \(IntRefed cmd ref) -> do
    cmd' <- ifor (Proxy :: Proxy ConstIntRef) cmd $ \ix iref -> do
      (IxM.! (ix, iref)) <$> get
    ref' <- case response cmd of
      SResponse    -> return ()
      SReference i -> do
        m <- get
        let ref' = IntRef (Ref $ IxM.size i m) (Pid 0)
        put $ IxM.insert i ref ref' m
        return ref'
    return $ IntRefed cmd' ref'

canonical
  :: forall ix (cmd :: Signature ix)
  .  SDecide ix
  => IxTraversable cmd
  => HasResponse   cmd
  => [IntRefed cmd]
  -> [IntRefed cmd]
canonical = fst . canonical' IxM.empty

canonicalFork
  :: forall ix (cmd :: Signature ix)
  .  SDecide ix
  => IxTraversable cmd
  => HasResponse   cmd
  => Fork [IntRefed cmd]
  -> Fork [IntRefed cmd]
canonicalFork (Fork l p r) = Fork l' p' r'
  where
  (p', im') = canonical' IxM.empty p
  l'        = fst $ canonical' im' l
  r'        = fst $ canonical' im' r

alphaEq
  :: forall ix (cmd :: Signature ix)
  .  SDecide ix
  => IxTraversable cmd
  => HasResponse   cmd
  => Eq (IntRefed cmd)
  => [IntRefed cmd]
  -> [IntRefed cmd]
  -> Bool
alphaEq c0 c1 = canonical c0 == canonical c1

alphaEqFork
  :: forall ix (cmd :: Signature ix)
  .  SDecide ix
  => IxTraversable cmd
  => HasResponse   cmd
  => Eq (IntRefed  cmd)
  => Fork [IntRefed cmd]
  -> Fork [IntRefed cmd]
  -> Bool
alphaEqFork f1 f2 = canonicalFork f1 == canonicalFork f2
