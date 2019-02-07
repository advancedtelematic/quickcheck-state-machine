{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE RecordWildCards        #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeOperators          #-}

module Modular where

import           Data.Functor.Classes
                   (Ord1, Show1)
import           Data.Functor.Const
                   (Const(Const))
import           Data.Kind
                   (Type)
import           Data.Proxy
                   (Proxy(Proxy))
import           GHC.Records
                   (HasField, getField)
import           Prelude
import           Test.QuickCheck
                   (Gen, elements, generate, oneof, suchThat)

import           Test.StateMachine.Logic
                   (Logic(..), boolean)
import qualified Test.StateMachine.Logic            as Logic
import           Test.StateMachine.Sequential
                   (getUsedVars)
import           Test.StateMachine.Types
                   (Command(Command), Commands(Commands), GenSym,
                   genSym, newCounter, runGenSym)
import qualified Test.StateMachine.Types.Rank2      as Rank2
import           Test.StateMachine.Types.References
                   (Reference, Symbolic)

------------------------------------------------------------------------

data ((l :: (Type -> Type) -> Type) :+: r) x = Inl (l x) | Inr (r x)
  deriving Show

instance (Rank2.Foldable l, Rank2.Foldable r) => Rank2.Foldable (l :+: r) where
  foldMap f (Inl x) = Rank2.foldMap f x
  foldMap f (Inr x) = Rank2.foldMap f x

data ((l :: (Type -> Type) -> Type) :*: r) x = Pair (l x) (r x)

instance Rank2.Foldable (Const a) where
  foldMap _ _ = mempty

------------------------------------------------------------------------

class InitModel (model :: (Type -> Type) -> Type) where
  initModel :: forall r. model r

instance (InitModel model1, InitModel model2) => InitModel (model1 :*: model2) where
  initModel = initModel `Pair` initModel


class Transition model cmd resp where
  transition :: (Ord1 r, Show1 r) => model r -> cmd r -> resp r -> model r

instance (Transition model cmd1 resp1, Transition model cmd2 resp2) =>
          Transition model (cmd1 :+: cmd2) (resp1 :+: resp2) where
  transition = undefined

class Precondition model cmd where
  precondition :: model Symbolic -> cmd Symbolic -> Logic

instance (Precondition model cmd1,
          Precondition model cmd2) => Precondition model (cmd1 :+: cmd2) where
  precondition model (Inl cmd1) = precondition model cmd1
  precondition model (Inr cmd2) = precondition model cmd2

class Generator model cmd where
  generator :: model Symbolic -> Gen (cmd Symbolic)

instance (Generator model cmd1,
          Generator model cmd2) => Generator model (cmd1 :+: cmd2) where
  generator model = oneof
    [ Inl <$> generator model
    , Inr <$> generator model
    ]

class Mock model cmd resp where
  mock :: model Symbolic -> cmd Symbolic -> GenSym (resp Symbolic)

instance (Mock model cmd1 resp1,
          Mock model cmd2 resp2) => Mock model (cmd1 :+: cmd2) (resp1 :+: resp2) where
  mock model (Inl cmd1) = Inl <$> mock model cmd1
  mock model (Inr cmd2) = Inr <$> mock model cmd2

type StateMachine model cmd resp =
  ( InitModel model
  , Transition model cmd resp
  , Precondition model cmd
  , Generator model cmd
  , Mock model cmd resp
  )

generateCommands :: forall model cmd resp. StateMachine model cmd resp
                 => Rank2.Foldable resp
                 => Proxy model -> Gen (Commands cmd resp)
generateCommands _proxy = do
  let model :: model Symbolic
      model = initModel
  cmd <- generator model `suchThat` (boolean . precondition model)
  let (resp, counter') = runGenSym (mock model cmd) newCounter
  return (Commands [Command cmd resp (getUsedVars resp)])

------------------------------------------------------------------------

-- * Spawn

data Spawn (r :: Type -> Type) = Spawn
  deriving Show

data SpawnModel r = SpawnModel
  { processes :: [Reference Int r]
  }

-- XXX: Can we use GHC.Records.HasField?
class HasProcesses m where
  getProcesses :: m r -> [Reference Int r]
  setProcesses :: [Reference Int r] -> m r -> m r

  modifyProcesses :: ([Reference Int r] -> [Reference Int r]) -> m r -> m r
  modifyProcesses f m = setProcesses (f (getProcesses m)) m

instance HasProcesses m1 => HasProcesses (m1 :*: m2) where
  getProcesses (Pair m1 _m2) = getProcesses m1

instance HasProcesses SpawnModel where
  getProcesses                    = processes
  setProcesses ps SpawnModel {..} = SpawnModel { processes = ps, ..}

instance InitModel SpawnModel where
  initModel = SpawnModel []

instance Precondition model Spawn where
  precondition _model Spawn = Top

instance HasProcesses model => Transition model Spawn (Reference Int) where
  transition model Spawn r = modifyProcesses (r :) model

instance Generator model Spawn where
  generator _model = return Spawn

instance Mock model Spawn (Reference Int) where
  mock _model Spawn = genSym

-- * Kill

data Kill r = Kill (Reference Int r)
  deriving Show

data KillModel r = KillModel
  { killed :: [Reference Int r]
  }

instance InitModel KillModel where
  initModel = KillModel []

class HasKilled m where
  getKilled :: m r -> [Reference Int r]
  setKilled :: [Reference Int r] -> m r -> m r

  modifyKilled :: ([Reference Int r] -> [Reference Int r]) -> m r -> m r
  modifyKilled f m = setKilled (f (getKilled m)) m

instance HasKilled m2 => HasKilled (m1 :*: m2) where
  getKilled (Pair _m1 m2) = getKilled m2

instance HasKilled KillModel where
  getKilled = killed
  setKilled ps KillModel {..} = KillModel { killed = ps }

instance HasKilled model => Transition model Kill (Const ()) where
  transition m (Kill r) (Const ()) = modifyKilled (++ [r]) m

instance HasProcesses model => Precondition model Kill where
  precondition m (Kill pid) = pid `Logic.elem` getProcesses m

instance HasProcesses model => Generator model Kill where
  generator m = Kill <$> elements (getProcesses m)

instance Mock model Kill (Const ()) where
  mock _model Kill{} = pure (Const ())

------------------------------------------------------------------------

g :: IO (Commands (Spawn :+: Kill) (Reference Int :+: Const ()))
g = generate (generateCommands (Proxy @(SpawnModel :*: KillModel)))

test :: IO ()
test = print =<< g
