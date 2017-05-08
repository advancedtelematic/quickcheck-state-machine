{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ExplicitNamespaces  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module Test.StateMachine.Types.AlphaEquality
  ( alphaEq
  , alphaEqFork
  )
  where

import           Control.Monad                    (forM)
import           Control.Monad.State              (State, get, put, runState)
import           Data.Kind                        (type (*))
import           Data.Singletons.Decide           (SDecide)
import           Data.Singletons.Prelude          (type (@@), ConstSym1,
                                                   Proxy (..), Sing, TyFun)

import           Test.StateMachine.Internal.IxMap (IxMap)
import qualified Test.StateMachine.Internal.IxMap as IxM
import           Test.StateMachine.Types

------------------------------------------------------------------------

canonical'
  :: forall
     (ix   :: *)
     (cmd  :: Response ix -> (TyFun ix * -> *) -> *)
  .  SDecide ix
  => (forall resp refs. cmd resp refs -> SResponse ix resp)
  -> (forall f p q resp. Applicative f
        => Proxy q
        -> cmd resp p
        -> (forall (x :: ix). Sing x -> p @@ x -> f (q @@ x))
        -> f (cmd resp q))
  -> IxMap ix IntRef ConstIntRef
  -> [Untyped' cmd ConstIntRef]
  -> ([Untyped' cmd ConstIntRef], IxMap ix IntRef ConstIntRef)
canonical' returns ixfor im = flip runState im . go
  where
  go :: [Untyped' cmd ConstIntRef]
     -> State (IxMap ix IntRef ConstIntRef) [Untyped' cmd ConstIntRef]
  go xs = forM xs $ \(Untyped' cmd ref) -> do
    cmd' <- ixfor (Proxy :: Proxy ConstIntRef) cmd $ \ ix iref -> do
      (IxM.! (ix, iref)) <$> Control.Monad.State.get
    ref' <- case returns cmd of
      SResponse -> return ()
      SReference i -> do
        m <- Control.Monad.State.get
        let ref' = IntRef (Ref $ IxM.size i m) (Pid 0)
        put $ IxM.insert i ref ref' m
        return $ ref'
    return $ Untyped' cmd' ref'

canonical
  :: forall
     (ix   :: *)
     (cmd  :: Response ix -> (TyFun ix * -> *) -> *)
  .  SDecide ix
  => (forall resp refs. cmd resp refs -> SResponse ix resp)
  -> (forall f p q resp. Applicative f
        => Proxy q
        -> cmd resp p
        -> (forall (x :: ix). Sing x -> p @@ x -> f (q @@ x))
        -> f (cmd resp q))
  -> [Untyped' cmd ConstIntRef]
  -> [Untyped' cmd ConstIntRef]
canonical returns ixfor = fst . canonical' returns ixfor IxM.empty

canonicalFork
  :: forall
     (ix   :: *)
     (cmd  :: Response ix -> (TyFun ix * -> *) -> *)
  .  SDecide ix
  => (forall resp refs. cmd resp refs -> SResponse ix resp)
  -> (forall f p q resp. Applicative f
        => Proxy q
        -> cmd resp p
        -> (forall (x :: ix). Sing x -> p @@ x -> f (q @@ x))
        -> f (cmd resp q))
  -> Fork [Untyped' cmd ConstIntRef]
  -> Fork [Untyped' cmd ConstIntRef]
canonicalFork returns ixfor (Fork l p r) = Fork l' p' r'
  where
  (p', im') = canonical' returns ixfor IxM.empty p
  l'        = fst $ canonical' returns ixfor im' l
  r'        = fst $ canonical' returns ixfor im' r

alphaEq
  :: forall
     (ix   :: *)
     (cmd  :: Response ix -> (TyFun ix * -> *) -> *)
  .  SDecide ix
  => Eq (Untyped' cmd ConstIntRef)
  => (forall resp refs. cmd resp refs -> SResponse ix resp)
  -> (forall f p q resp. Applicative f
        => Proxy q
        -> cmd resp p
        -> (forall (x :: ix). Sing x -> p @@ x -> f (q @@ x))
        -> f (cmd resp q))
  -> [Untyped' cmd ConstIntRef]
  -> [Untyped' cmd ConstIntRef]
  -> Bool
alphaEq returns ixfor c0 c1
  = canonical returns ixfor c0 == canonical returns ixfor c1

alphaEqFork
  :: forall
     (ix   :: *)
     (cmd  :: Response ix -> (TyFun ix * -> *) -> *)
  .  SDecide ix
  => Eq (Untyped' cmd ConstIntRef)
  => (forall resp refs. cmd resp refs -> SResponse ix resp)
  -> (forall f p q resp. Applicative f
        => Proxy q
        -> cmd resp p
        -> (forall (x :: ix). Sing x -> p @@ x -> f (q @@ x))
        -> f (cmd resp q))
  -> Fork [Untyped' cmd ConstIntRef]
  -> Fork [Untyped' cmd ConstIntRef]
  -> Bool
alphaEqFork returns ixfor f1 f2
  = canonicalFork returns ixfor f1 == canonicalFork returns ixfor f2
