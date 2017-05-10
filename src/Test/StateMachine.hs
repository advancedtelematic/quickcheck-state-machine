{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE ExplicitNamespaces         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module Test.StateMachine
  ( sequentialProperty
  , parallelProperty
  ) where

import           Control.Monad.State
import           Data.Kind                             (type (*))
import qualified Data.Map                              as M
import           Data.Singletons.Prelude               (ConstSym1)
import           Data.Singletons.TH
import           Test.QuickCheck
import           Test.QuickCheck.Monadic
import           Test.QuickCheck.Property              (Property (..))

import           Test.StateMachine.Internal.IxMap      (IxMap)
import qualified Test.StateMachine.Internal.IxMap      as IxM
import           Test.StateMachine.Internal.Parallel
import           Test.StateMachine.Internal.Sequential
import           Test.StateMachine.Types
import           Test.StateMachine.Utils

------------------------------------------------------------------------

sequentialProperty
  :: forall
     (ix    :: *)
     (cmd   :: Response ix -> (TyFun ix * -> *) -> *)
     (refs  :: TyFun ix * -> *)
     (model :: (TyFun ix * -> *) -> *)
     (m     :: * -> *)
  .  Monad m
  => IxFunctor1 cmd
  => Show (Untyped' cmd ConstIntRef)
  => IxFoldable (Untyped' cmd)
  => IxTraversable (Untyped cmd)
  => Ord       ix
  => SDecide   ix
  => SingKind  ix
  => DemoteRep ix ~ ix
  => StateMachineModel model cmd
  -> [(Int, Gen (Untyped cmd (IxRefs ix)))]
  -> (forall refs'. Shrinker (Untyped' cmd refs'))
  -> (forall resp refs'. cmd resp refs' -> SResponse ix resp)
  -> (forall resp. cmd resp refs -> m (Response_ refs resp))
  -> (forall f p q resp. Applicative f
        => Proxy q
        -> cmd resp p
        -> (forall (x :: ix). Sing x -> p @@ x -> f (q @@ x))
        -> f (cmd resp q))
  -> (m Property -> Property)
  -> Property
sequentialProperty StateMachineModel {..} gens shrinker returns sem ixFor runM =
  forAllShrink
    (fst <$> liftGen gens 0 M.empty returns)
    (liftShrink returns shrinker)
    $ \cmds ->
      let len = length cmds in
      classify (len == 0)              "0     commands" $
      classify (len >= 1  && len < 15) "1-15  commands" $
      classify (len >= 15 && len < 30) "15-30 commands" $
      classify (len >= 30)             "30+   commands" $
        monadic (runM . flip evalStateT IxM.empty) $ go initialModel cmds
  where
  go :: model ConstIntRef -> [Untyped' cmd ConstIntRef]
     -> PropertyM (StateT (IxMap ix IntRef refs) m) ()
  go _ []                                 = return ()
  go m (cmd@(Untyped' cmd' miref) : cmds) = do
    let s = takeWhile (/= ' ') $ show cmd
    monitor $ label s
    pre $ precondition m cmd'
    resp <- run $ liftSem sem returns cmd' miref
    liftProperty $
      counterexample ("The post-condition for `" ++ s ++ "' failed!") $
        postcondition m cmd' resp
    go (transition m cmd' resp) cmds

------------------------------------------------------------------------

parallelProperty
  :: forall
     (ix    :: *)
     (cmd   :: Response ix -> (TyFun ix * -> *) -> *)
     (refs  :: TyFun ix * -> *)
     (model :: (TyFun ix * -> *) -> *)
  .  IxFunctor1 cmd
  => IxFoldable (Untyped' cmd)
  => IxTraversable (Untyped cmd)
  => Show (Untyped' cmd ConstIntRef)
  => ShowCmd cmd
  => Ord (Untyped' cmd ConstIntRef)
  => Ord       ix
  => SDecide   ix
  => SingKind  ix
  => DemoteRep ix ~ ix
  => StateMachineModel model cmd
  -> [(Int, Gen (Untyped cmd (IxRefs ix)))]
  -> (forall refs'. Shrinker (Untyped' cmd refs'))
  -> (forall resp refs'. cmd resp refs' -> SResponse ix resp)
  -> (forall resp. cmd resp refs -> IO (Response_ refs resp))
  -> (forall f p q resp. Applicative f
        => Proxy q
        -> cmd resp p
        -> (forall (x :: ix). Sing x -> p @@ x -> f (q @@ x))
        -> f (cmd resp q))
  -> Property
parallelProperty smm gen shrinker returns sem ifor
  = forAllShrink
      (liftGenFork gen returns)
      (liftShrinkFork returns shrinker)
      $ \fork -> monadicIO $ replicateM_ 10 $ do
          hist <- run $ liftSemFork sem returns fork
          checkParallelInvariant smm hist
