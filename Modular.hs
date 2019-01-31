{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}

module Modular where

import           Data.Functor.Classes
                   (Ord1, Show1)
import           Data.Functor.Const
                   (Const(Const))
import           Data.Kind
                   (Type)
import           Data.Proxy
                   (Proxy(Proxy))
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

data Model r = Model
  { processes :: [Reference Int r]
  }

class HasProcesses a where
  getProcesses :: a r -> [Reference Int r]
  putProcesses :: [Reference Int r] -> a r

  modifyProcesses :: ([Reference Int r] -> [Reference Int r]) -> a r -> a r
  modifyProcesses f = putProcesses . f . getProcesses

instance HasProcesses Model where
  getProcesses = processes

instance InitModel Model where
  initModel = Model []

data Spawn (r :: Type -> Type) = Spawn
  deriving Show

instance Precondition model Spawn where
  precondition _model Spawn = Top

instance HasProcesses model => Transition model Spawn (Reference Int) where
  transition model Spawn r = modifyProcesses (r :) model

instance Generator model Spawn where
  generator _model = return Spawn

instance Mock model Spawn (Reference Int) where
  mock _model Spawn = genSym

data Kill r = Kill (Reference Int r)
  deriving Show

instance Transition Model Kill (Const ()) where
  transition Model {..} (Kill r) (Const ()) =
    Model { processes = filter (/= r) processes, .. }

instance Precondition Model Kill where
  precondition Model {..} (Kill pid) = pid `Logic.elem` processes

instance Generator Model Kill where
  generator Model{..} = Kill <$> elements processes

instance Mock model Kill (Const ()) where
  mock _model Kill{} = pure (Const ())

g :: IO (Commands (Spawn :+: Kill) (Reference Int :+: Const ()))
g = generate (generateCommands (Proxy @Model))

test :: IO ()
test = print =<< g
