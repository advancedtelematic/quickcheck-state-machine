{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE DerivingStrategies        #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}

module Test.StateMachine.Lockstep.Simple (
    -- * Test type-level parameters
    MockState
  , Cmd
  , Resp
  , RealHandle
  , MockHandle
  , Test
    -- * Test term-level parameters
  , StateMachineTest(..)
    -- * Handle instantiation
  , At(..)
  , (:@)
    -- * Model state
  , Model(..)
    -- * Running the tests
  , prop_sequential
  , prop_parallel
    -- * Translate to n-ary model model
  , fromSimple
  ) where

import           Data.Bifunctor
import           Data.Functor.Classes
import           Data.Kind
                   (Type)
import           Data.SOP
import           Data.Typeable
import           Prelude
import           Test.QuickCheck
import           Test.StateMachine
import           Test.StateMachine.Lockstep.Auxiliary
import           Test.StateMachine.Lockstep.NAry
                   (MockState)

import qualified Test.StateMachine.Lockstep.NAry      as NAry

{-------------------------------------------------------------------------------
  Top-level parameters
-------------------------------------------------------------------------------}

data family Cmd        t :: Type -> Type
data family Resp       t :: Type -> Type
data family RealHandle t :: Type
data family MockHandle t :: Type

{-------------------------------------------------------------------------------
  Default handle instantiation
-------------------------------------------------------------------------------}

type family Test (f :: Type -> Type) :: Type where
  Test (Cmd  t) = t
  Test (Resp t) = t

-- @f@ will be instantiated with @Cmd@ or @Resp@
-- @r@ will be instantiated with 'Symbolic' or 'Concrete'
newtype At f r = At { unAt :: f (Reference (RealHandle (Test f)) r) }
type    f :@ r = At f r

{-------------------------------------------------------------------------------
  Simplified model
-------------------------------------------------------------------------------}

data Model t r = Model {
      modelState :: MockState t
    , modelRefs  :: [(Reference (RealHandle t) r, MockHandle t)]
    }

modelToSimple :: NAry.Model (Simple t) r -> Model t r
modelToSimple NAry.Model{modelRefss = NAry.Refss (NAry.Refs rs :* Nil), ..} = Model {
      modelState = modelState
    , modelRefs  = map (second unSimpleToMock) rs
    }

{-------------------------------------------------------------------------------
  Wrap and unwrap
-------------------------------------------------------------------------------}

cmdAtFromSimple :: Functor (Cmd t)
                => Cmd t :@ Symbolic -> NAry.Cmd (Simple t) NAry.:@ Symbolic
cmdAtFromSimple = NAry.At . SimpleCmd . fmap NAry.FlipRef . unAt

cmdAtToSimple :: Functor (Cmd t)
              => NAry.Cmd (Simple t) NAry.:@ Symbolic -> Cmd t :@ Symbolic
cmdAtToSimple = At . fmap (NAry.unFlipRef) . unSimpleCmd . NAry.unAt

cmdMockToSimple :: Functor (Cmd t)
                => NAry.Cmd (Simple t) (NAry.MockHandle (Simple t)) '[RealHandle t]
                -> Cmd t (MockHandle t)
cmdMockToSimple = fmap unSimpleToMock . unSimpleCmd

cmdRealToSimple :: Functor (Cmd t)
                => NAry.Cmd (Simple t) I '[RealHandle t]
                -> Cmd t (RealHandle t)
cmdRealToSimple = fmap unI . unSimpleCmd

respMockFromSimple :: Functor (Resp t)
                   => Resp t (MockHandle t)
                   -> NAry.Resp (Simple t) (NAry.MockHandle (Simple t)) '[RealHandle t]
respMockFromSimple = SimpleResp . fmap SimpleToMock

respRealFromSimple :: Functor (Resp t)
                   => Resp t (RealHandle t)
                   -> NAry.Resp (Simple t) I '[RealHandle t]
respRealFromSimple = SimpleResp . fmap I

{-------------------------------------------------------------------------------
  User defined values
-------------------------------------------------------------------------------}

data StateMachineTest t =
    ( Typeable t
      -- Response
    , Eq   (Resp t (MockHandle t))
    , Show (Resp t (Reference (RealHandle t) Symbolic))
    , Show (Resp t (Reference (RealHandle t) Concrete))
    , Show (Resp t (MockHandle t))
    , Traversable (Resp t)
      -- Command
    , Show (Cmd t (Reference (RealHandle t) Symbolic))
    , Show (Cmd t (Reference (RealHandle t) Concrete))
    , Traversable (Cmd t)
      -- Real handles
    , Eq     (RealHandle t)
    , Show   (RealHandle t)
    , ToExpr (RealHandle t)
      -- Mock handles
    , Eq     (MockHandle t)
    , Show   (MockHandle t)
    , ToExpr (MockHandle t)
      -- Mock state
    , Show   (MockState t)
    , ToExpr (MockState t)
    ) => StateMachineTest {
      runMock    :: Cmd t (MockHandle t) -> MockState t -> (Resp t (MockHandle t), MockState t)
    , runReal    :: Cmd t (RealHandle t) -> IO (Resp t (RealHandle t))
    , initMock   :: MockState t
    , newHandles :: forall h. Resp t h -> [h]
    , generator  :: Model t Symbolic -> Maybe (Gen (Cmd t :@ Symbolic))
    , shrinker   :: Model t Symbolic -> Cmd t :@ Symbolic -> [Cmd t :@ Symbolic]
    , cleanup    :: Model t Concrete -> IO ()
    }

data Simple t

type instance NAry.MockState   (Simple t) = MockState t
type instance NAry.RealHandles (Simple t) = '[RealHandle t]
type instance NAry.RealMonad   (Simple _) = IO

data instance NAry.Cmd (Simple _) _f _hs where
    SimpleCmd :: Cmd t (f h) -> NAry.Cmd (Simple t) f '[h]

data instance NAry.Resp (Simple _) _f _hs where
    SimpleResp :: Resp t (f h) -> NAry.Resp (Simple t) f '[h]

newtype instance NAry.MockHandle (Simple t) (RealHandle t) =
    SimpleToMock { unSimpleToMock :: MockHandle t }

unSimpleCmd :: NAry.Cmd (Simple t) f '[h] -> Cmd t (f h)
unSimpleCmd (SimpleCmd cmd) = cmd

unSimpleResp :: NAry.Resp (Simple t) f '[h] -> Resp t (f h)
unSimpleResp (SimpleResp resp) = resp

instance ( Functor (Resp t)
         , Eq (Resp t (MockHandle t))
         , Eq (MockHandle t)
         ) => Eq (NAry.Resp (Simple t) (NAry.MockHandle (Simple t)) '[RealHandle t]) where
  SimpleResp r == SimpleResp r' = (unSimpleToMock <$> r) == (unSimpleToMock <$> r')

instance ( Functor (Resp t)
         , Show (Resp t (MockHandle t))
         ) => Show (NAry.Resp (Simple t) (NAry.MockHandle (Simple t)) '[RealHandle t]) where
  show (SimpleResp r) = show (unSimpleToMock <$> r)

instance ( Functor (Resp t)
         , Show (Resp t (Reference (RealHandle t) r))
         , Show1 r
         ) => Show (NAry.Resp (Simple t) (NAry.FlipRef r) '[RealHandle t]) where
  show (SimpleResp r) = show (NAry.unFlipRef <$> r)

instance ( Functor (Cmd t)
         , Show (Cmd t (Reference (RealHandle t) r))
         , Show1 r
         ) => Show (NAry.Cmd (Simple t) (NAry.FlipRef r) '[RealHandle t]) where
  show (SimpleCmd r) = show (NAry.unFlipRef <$> r)

deriving stock instance Eq   (MockHandle t) => Eq   (NAry.MockHandle (Simple t) (RealHandle t))
deriving stock instance Show (MockHandle t) => Show (NAry.MockHandle (Simple t) (RealHandle t))

instance Traversable (Resp t) => NTraversable (NAry.Resp (Simple t)) where
  nctraverse _ f (SimpleResp x) = SimpleResp <$> traverse (f ElemHead) x

instance Traversable (Cmd t) => NTraversable (NAry.Cmd (Simple t)) where
  nctraverse _ f (SimpleCmd x) = SimpleCmd <$> traverse (f ElemHead) x

instance ToExpr (MockHandle t)
      => ToExpr (NAry.MockHandle (Simple t) (RealHandle t)) where
  toExpr (SimpleToMock h) = toExpr h

fromSimple :: StateMachineTest t -> NAry.StateMachineTest (Simple t)
fromSimple StateMachineTest{..} = NAry.StateMachineTest {
      runMock    = \cmd st -> first respMockFromSimple (runMock (cmdMockToSimple cmd) st)
    , runReal    = \cmd -> respRealFromSimple <$> (runReal (cmdRealToSimple cmd))
    , initMock   = initMock
    , newHandles = \r -> Comp (newHandles (unSimpleResp r)) :* Nil
    , generator  = \m     -> fmap cmdAtFromSimple <$> generator (modelToSimple m)
    , shrinker   = \m cmd ->      cmdAtFromSimple <$> shrinker  (modelToSimple m) (cmdAtToSimple cmd)
    , cleanup    = cleanup   . modelToSimple
    }

{-------------------------------------------------------------------------------
  Running the tests
-------------------------------------------------------------------------------}

prop_sequential :: StateMachineTest t
                -> Maybe Int   -- ^ (Optional) minimum number of commands
                -> Property
prop_sequential = NAry.prop_sequential . fromSimple

prop_parallel :: StateMachineTest t
              -> Maybe Int   -- ^ (Optional) minimum number of commands
              -> Property
prop_parallel = NAry.prop_parallel . fromSimple
