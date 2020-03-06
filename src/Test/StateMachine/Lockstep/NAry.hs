{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module Test.StateMachine.Lockstep.NAry (
    -- * Test type-level parameters
    MockState
  , Cmd
  , Resp
  , RealHandles
  , MockHandle
  , RealMonad
  , Test
    -- * Test term-level parameters
  , StateMachineTest(..)
    -- * Handle instantiation
  , At(..)
  , (:@)
    -- * Model state
  , Model(..)
  , Refs(..)
  , Refss(..)
  , FlipRef(..)
    -- * Running the tests
  , prop_sequential
  , prop_parallel
  ) where

import Prelude
import Data.Functor.Classes
import Data.Kind (Type)
import Data.Maybe (fromJust)
import Data.SOP
import Data.Typeable
import GHC.Generics (Generic)
import Test.QuickCheck
import Test.QuickCheck.Monadic
import Test.StateMachine

#if !MIN_VERSION_base(4,11,0)
import Data.Semigroup (Semigroup(..))
#endif

import qualified Data.Monoid                   as M
import qualified Data.TreeDiff                 as TD
import qualified Test.StateMachine.Types       as QSM
import qualified Test.StateMachine.Types.Rank2 as Rank2

import Test.StateMachine.Lockstep.Auxiliary

{-------------------------------------------------------------------------------
  Test type-level parameters
-------------------------------------------------------------------------------}

type family MockState   t   :: Type
data family Cmd         t   :: (Type -> Type) -> [Type] -> Type
data family Resp        t   :: (Type -> Type) -> [Type] -> Type
type family RealHandles t   :: [Type]
data family MockHandle  t a :: Type
type family RealMonad   t   :: Type -> Type

{-------------------------------------------------------------------------------
  Reference environments
-------------------------------------------------------------------------------}

-- | Relation between real and mock references for single handle type @a@
newtype Refs t r a = Refs { unRefs :: [(Reference a r, MockHandle t a)] }
  deriving (Semigroup, Monoid, Generic)

deriving instance (Show1 r, Show a, Show (MockHandle t a)) => Show (Refs t r a)
deriving instance (ToExpr a, ToExpr (MockHandle t a)) => ToExpr (Refs t Concrete a)

-- | Relation between real and mock references for /all/ handle types
newtype Refss t r = Refss { unRefss :: NP (Refs t r) (RealHandles t) }

instance ( Show1 r
         , All (And Show (Compose Show (MockHandle t))) (RealHandles t)
         ) => Show (Refss t r) where
  show = unlines
       . hcollapse
       . hcmap (Proxy @(And Show (Compose Show (MockHandle t)))) showOne
       . unRefss
    where
      showOne :: (Show a, Show (MockHandle t a))
              => Refs t r a -> K String a
      showOne = K . show

instance All (And ToExpr (Compose ToExpr (MockHandle t))) (RealHandles t)
      => ToExpr (Refss t Concrete) where
  toExpr = TD.Lst
         . hcollapse
         . hcmap (Proxy @(And ToExpr (Compose ToExpr (MockHandle t)))) toExprOne
         . unRefss
    where
      toExprOne :: (ToExpr a, ToExpr (MockHandle t a))
                => Refs t Concrete a -> K (TD.Expr) a
      toExprOne = K . toExpr

instance SListI (RealHandles t) => Semigroup (Refss t r) where
  Refss rss <> Refss rss' = Refss $ hzipWith (<>) rss rss'

instance SListI (RealHandles t) => Monoid (Refss t r) where
  mempty = Refss $ hpure (Refs mempty)

{-------------------------------------------------------------------------------
  Default instantiation to handles
-------------------------------------------------------------------------------}

type family Test (f :: (Type -> Type) -> [Type] -> Type) :: Type where
  Test (Cmd  t) = t
  Test (Resp t) = t

newtype FlipRef r h = FlipRef { unFlipRef :: Reference h r }
  deriving (Show)

-- @f@ will be instantiated with @Cmd@ or @Resp@
-- @r@ will be instantiated with 'Symbolic' or 'Concrete'
newtype At f r = At { unAt :: f (FlipRef r) (RealHandles (Test f)) }
type    f :@ r = At f r

deriving instance (Show (f (FlipRef r) (RealHandles (Test f)))) => Show (At f r)

{-------------------------------------------------------------------------------
  Model
-------------------------------------------------------------------------------}

data Model t r = Model {
      modelState :: MockState t
    , modelRefss :: Refss t r
    }
  deriving (Generic)

deriving instance ( Show1 r
                  , Show (MockState t)
                  , All (And Show (Compose Show (MockHandle t))) (RealHandles t)
                  ) => Show (Model t r)

instance ( ToExpr (MockState t)
         , All (And ToExpr (Compose ToExpr (MockHandle t))) (RealHandles t)
         ) => ToExpr (Model t Concrete)

initModel :: StateMachineTest t -> Model t r
initModel StateMachineTest{..} = Model initMock (Refss (hpure (Refs [])))

{-------------------------------------------------------------------------------
  High level API
-------------------------------------------------------------------------------}

data StateMachineTest t =
    ( Monad (RealMonad t)
    -- Requirements on the handles
    , All Typeable                                     (RealHandles t)
    , All Eq                                           (RealHandles t)
    , All (And Show   (Compose Show   (MockHandle t))) (RealHandles t)
    , All (And ToExpr (Compose ToExpr (MockHandle t))) (RealHandles t)
    -- Response
    , NTraversable (Resp t)
    , Eq   (Resp t (MockHandle t)     (RealHandles t))
    , Show (Resp t (MockHandle t)     (RealHandles t))
    , Show (Resp t (FlipRef Symbolic) (RealHandles t))
    , Show (Resp t (FlipRef Concrete) (RealHandles t))
    -- Command
    , NTraversable (Cmd t)
    , Show (Cmd t (FlipRef Symbolic) (RealHandles t))
    , Show (Cmd t (FlipRef Concrete) (RealHandles t))
    -- MockState
    , Show   (MockState t)
    , ToExpr (MockState t)
    ) => StateMachineTest {
      runMock    :: Cmd t (MockHandle t) (RealHandles t) -> MockState t -> (Resp t (MockHandle t) (RealHandles t), MockState t)
    , runReal    :: Cmd t I              (RealHandles t) -> RealMonad t (Resp t I (RealHandles t))
    , initMock   :: MockState t
    , newHandles :: forall f. Resp t f (RealHandles t) -> NP ([] :.: f) (RealHandles t)
    , generator  :: Model t Symbolic -> Maybe (Gen (Cmd t :@ Symbolic))
    , shrinker   :: Model t Symbolic -> Cmd t :@ Symbolic -> [Cmd t :@ Symbolic]
    , cleanup    :: Model t Concrete -> RealMonad t ()
    }

semantics :: StateMachineTest t
          -> Cmd t :@ Concrete
          -> RealMonad t (Resp t :@ Concrete)
semantics StateMachineTest{..} (At c) =
    (At . ncfmap (Proxy @Typeable) (const wrapConcrete)) <$>
      runReal (nfmap (const unwrapConcrete) c)

unwrapConcrete :: FlipRef Concrete a -> I a
unwrapConcrete = I . concrete . unFlipRef

wrapConcrete :: Typeable a => I a -> FlipRef Concrete a
wrapConcrete = FlipRef . reference  . unI

-- | Turn @Cmd@ or @Resp@ in terms of (symbolic or concrete) references to
-- real handles into a command in terms of mock handles.
--
-- This is isomorphic to
--
-- > toMock :: Refss t Symbolic
--          -> Cmd (FlipRef r) (Handles t)
--          -> Cmd  ToMock     (Handles t)
toMockHandles :: (NTraversable f, t ~ Test f, All Eq (RealHandles t), Eq1 r)
              => Refss t r -> f :@ r -> f (MockHandle t) (RealHandles t)
toMockHandles rss (At fr) =
    ncfmap (Proxy @Eq) (\pf -> find (unRefss rss) pf . unFlipRef) fr
  where
    find :: (Eq a, Eq1 r)
         => NP (Refs t r) (RealHandles t)
         -> Elem (RealHandles t) a
         -> Reference a r -> MockHandle t a
    find refss ix r = unRefs (npAt refss ix) ! r

step :: Eq1 r
     => StateMachineTest t
     -> Model t r
     -> Cmd t :@ r
     -> (Resp t (MockHandle t) (RealHandles t), MockState t)
step StateMachineTest{..} (Model st rss) cmd =
    runMock (toMockHandles rss cmd) st

data Event t r = Event {
      before   :: Model t    r
    , cmd      :: Cmd   t :@ r
    , after    :: Model t    r
    , mockResp :: Resp t (MockHandle t) (RealHandles t)
    }

lockstep :: forall t r. Eq1 r
         => StateMachineTest t
         -> Model t    r
         -> Cmd   t :@ r
         -> Resp  t :@ r
         -> Event t    r
lockstep sm@StateMachineTest{..} m@(Model _ rss) c (At resp) = Event {
      before   = m
    , cmd      = c
    , after    = Model st' (rss <> rss')
    , mockResp = resp'
    }
  where
    (resp', st') = step sm m c

    rss' :: Refss t r
    rss' = zipHandles (newHandles resp) (newHandles resp')

transition :: Eq1 r
           => StateMachineTest t
           -> Model t    r
           -> Cmd   t :@ r
           -> Resp  t :@ r
           -> Model t    r
transition sm m c = after . lockstep sm m c

postcondition :: StateMachineTest t
              -> Model t    Concrete
              -> Cmd   t :@ Concrete
              -> Resp  t :@ Concrete
              -> Logic
postcondition sm@StateMachineTest{} m c r =
    toMockHandles (modelRefss $ after e) r .== mockResp e
  where
    e = lockstep sm m c r

symbolicResp :: StateMachineTest t
             -> Model t Symbolic
             -> Cmd t :@ Symbolic
             -> GenSym (Resp t :@ Symbolic)
symbolicResp sm@StateMachineTest{} m c =
    At <$> nctraverse (Proxy @Typeable) (\_ _ -> FlipRef <$> genSym) resp
  where
    (resp, _mock') = step sm m c

precondition :: forall t. (NTraversable (Cmd t), All Eq (RealHandles t))
             => Model t Symbolic
             -> Cmd t :@ Symbolic
             -> Logic
precondition (Model _ (Refss hs)) (At c) =
    Boolean (M.getAll $ nfoldMap check c) .// "No undefined handles"
  where
    check :: Elem (RealHandles t) a -> FlipRef Symbolic a -> M.All
    check ix (FlipRef a) = M.All $ any (sameRef a) $ map fst (unRefs (hs `npAt` ix))

    -- TODO: Patch QSM
    sameRef :: Reference a Symbolic -> Reference a Symbolic -> Bool
    sameRef (QSM.Reference (QSM.Symbolic v)) (QSM.Reference (QSM.Symbolic v')) = v == v'

toStateMachine :: StateMachineTest t
               -> StateMachine (Model t) (At (Cmd t)) (RealMonad t) (At (Resp t))
toStateMachine sm@StateMachineTest{} = StateMachine {
      initModel     = initModel     sm
    , transition    = transition    sm
    , precondition  = precondition
    , postcondition = postcondition sm
    , generator     = generator     sm
    , shrinker      = shrinker      sm
    , semantics     = semantics     sm
    , mock          = symbolicResp  sm
    , cleanup       = cleanup       sm
    , invariant     = Nothing
    }

prop_sequential :: RealMonad t ~ IO
                => StateMachineTest t
                -> Maybe Int   -- ^ (Optional) minimum number of commands
                -> Property
prop_sequential sm@StateMachineTest{} mMinSize =
    forAllCommands sm' mMinSize $ \cmds ->
      monadicIO $ do
        (hist, _model, res) <- runCommands sm' cmds
        prettyCommands sm' hist
          $ res === Ok
  where
    sm' = toStateMachine sm

prop_parallel :: RealMonad t ~ IO
              => StateMachineTest t
              -> Maybe Int   -- ^ (Optional) minimum number of commands
              -> Property
prop_parallel sm@StateMachineTest{} mMinSize =
    forAllParallelCommands sm' mMinSize $ \cmds ->
      monadicIO $
            prettyParallelCommands cmds
        =<< runParallelCommands sm' cmds
  where
    sm' = toStateMachine sm

{-------------------------------------------------------------------------------
  Rank2 instances
-------------------------------------------------------------------------------}

instance (NTraversable (Cmd t), SListI (RealHandles t))
      => Rank2.Functor (At (Cmd t)) where
  fmap :: forall p q. (forall a. p a -> q a) -> At (Cmd t) p -> At (Cmd t) q
  fmap f (At cmd) = At $ nfmap (const f') cmd
    where
      f' :: FlipRef p a -> FlipRef q a
      f' = FlipRef . Rank2.fmap f . unFlipRef

instance (NTraversable (Cmd t), SListI (RealHandles t))
      => Rank2.Foldable (At (Cmd t)) where
  foldMap :: forall p m. Monoid m => (forall a. p a -> m) -> At (Cmd t) p -> m
  foldMap f (At cmd) = nfoldMap (const f') cmd
    where
      f' :: FlipRef p a -> m
      f' = Rank2.foldMap f . unFlipRef

instance (NTraversable (Cmd t), SListI (RealHandles t))
      => Rank2.Traversable (At (Cmd t)) where
  traverse :: forall f p q. Applicative f
           => (forall a. p a -> f (q a)) -> At (Cmd t) p -> f (At (Cmd t) q)
  traverse f (At cmd) = At <$> ntraverse (const f') cmd
    where
      f' :: FlipRef p a -> f (FlipRef q a)
      f' = fmap FlipRef . Rank2.traverse f . unFlipRef

instance (NTraversable (Resp t), SListI (RealHandles t))
      => Rank2.Functor (At (Resp t)) where
  fmap :: forall p q. (forall a. p a -> q a) -> At (Resp t) p -> At (Resp t) q
  fmap f (At cmd) = At $ nfmap (const f') cmd
    where
      f' :: FlipRef p a -> FlipRef q a
      f' = FlipRef . Rank2.fmap f . unFlipRef

instance (NTraversable (Resp t), SListI (RealHandles t))
      => Rank2.Foldable (At (Resp t)) where
  foldMap :: forall p m. Monoid m => (forall a. p a -> m) -> At (Resp t) p -> m
  foldMap f (At cmd) = nfoldMap (const f') cmd
    where
      f' :: FlipRef p a -> m
      f' = Rank2.foldMap f . unFlipRef

instance (NTraversable (Resp t), SListI (RealHandles t))
      => Rank2.Traversable (At (Resp t)) where
  traverse :: forall f p q. Applicative f
           => (forall a. p a -> f (q a)) -> At (Resp t) p -> f (At (Resp t) q)
  traverse f (At cmd) = At <$> ntraverse (const f') cmd
    where
      f' :: FlipRef p a -> f (FlipRef q a)
      f' = fmap FlipRef . Rank2.traverse f . unFlipRef

{-------------------------------------------------------------------------------
  Auxiliary
-------------------------------------------------------------------------------}

(!) :: Eq k => [(k, a)] -> k -> a
env ! r = fromJust (lookup r env)

zipHandles :: SListI (RealHandles t)
           => NP ([] :.: FlipRef r)    (RealHandles t)
           -> NP ([] :.: MockHandle t) (RealHandles t)
           -> Refss t r
zipHandles = \real mock -> Refss $ hzipWith zip' real mock
  where
    zip' :: (:.:) [] (FlipRef r) a -> (:.:) [] (MockHandle t) a -> Refs t r a
    zip' (Comp real) (Comp mock) = Refs $ zip (map unFlipRef real) mock
