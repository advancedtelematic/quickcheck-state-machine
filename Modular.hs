{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Modular where

import           Data.Functor.Classes
                   (Ord1, Show1, liftShowsPrec)
import           Data.Functor.Const
                   (Const(Const))
import           Data.Functor.Product
                   (Product(Pair))
import           Data.Functor.Sum
                   (Sum(InL, InR))
import           Data.Kind
                   (Type)
import           Data.Proxy
                   (Proxy(Proxy))
import           GHC.Records
                   (HasField, getField)
import           Haskus.Utils.Variant
import           Haskus.Utils.VariantF
import           Prelude
import           Test.QuickCheck
                   (Gen, elements, generate, oneof, suchThat)
import           Text.Show.Pretty
                   (pPrint)

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
                   (Concrete(Concrete), Reference(Reference), Symbolic(Symbolic), Var(Var))

------------------------------------------------------------------------
-- Look into:

-- https://docs.haskus.org/variant.html
-- https://hsyl20.fr/home/posts/2018-05-22-extensible-adt.html
-- https://hackage.haskell.org/package/haskus-utils-variant

------------------------------------------------------------------------

infixr 1 :+:
type (:+:) = Sum

instance (Show (l a), Show (r a)) => Show ((l :+: r) a) where
  show (InL x) = "InL " ++ show x
  show (InR y) = "InR " ++ show y

type (:*:) = Product

------------------------------------------------------------------------

class InitModel (model :: (Type -> Type) -> Type) where
  initModel :: model r

instance (InitModel model1, InitModel model2) => InitModel (model1 :*: model2) where
  initModel = Pair initModel initModel

class Transition model cmd resp where
  transition         :: (Ord1 r, Show1 r) => model r -> cmd r -> resp r -> model r
  default transition :: model r -> cmd r -> resp r -> model r
  transition model _cmd _resp = model

instance (Transition model1 cmd1 resp1, Transition model2 cmd2 resp2) =>
          Transition (model1 :*: model2) (cmd1 :+: cmd2) (resp1 :+: resp2) where
  transition (Pair model1 model2) (InL cmd1) (InL resp1) =
    Pair (transition model1 cmd1 resp1) model2
  transition (Pair model1 model2) (InR cmd2) (InR resp2) =
    Pair (model1) (transition model2 cmd2 resp2)
  transition (Pair _ _) (InL _) (InR _) = error "transition: impossible, InL InR"
  transition (Pair _ _) (InR _) (InL _) = error "transition: impossible, InR InL"

class Precondition model cmd where
  precondition :: model Symbolic -> cmd Symbolic -> Logic

instance Precondition model (VariantF '[]) where
  precondition = undefined

instance ( Precondition model cmd
         , Precondition model (VariantF cmds)
         ) => Precondition model (VariantF (cmd ': cmds)) where
  precondition m v = case popVariantFHead v of
    Right u -> precondition m u
    Left  w -> precondition m w

instance (Precondition model cmd1,
          Precondition model cmd2) => Precondition model (cmd1 :+: cmd2) where
  precondition model (InL cmd1) = precondition model cmd1
  precondition model (InR cmd2) = precondition model cmd2

-- instance (Precondition model1 cmd1,
          -- Precondition model2 cmd2) => Precondition (model1 :*: model2)
                                                    -- (cmd1   :+: cmd2) where
  -- precondition (Pair model1 _model2) (InL cmd1) = precondition model1 cmd1
  -- precondition (Pair _model1 model2) (InR cmd2) = precondition model2 cmd2

class Postcondition model cmd resp where
  postcondition         :: model Concrete -> cmd Concrete -> resp Concrete -> Logic
  default postcondition :: model Concrete -> cmd Concrete -> resp Concrete -> Logic
  postcondition _model _cmd _resp = Top

instance ( Postcondition model cmd1 resp1
         , Postcondition model cmd2 resp2
         ) => Postcondition model (cmd1 :+: cmd2) (resp1 :+: resp2) where
  postcondition model  (InL cmd1) (InL resp1) = postcondition model cmd1 resp1
  postcondition model  (InR cmd2) (InR resp2) = postcondition model cmd2 resp2
  postcondition _model (InL _)    (InR _)     = error "postcondition: impossible, InL InR"
  postcondition _model (InR _)    (InL _)     = error "postcondition: impossible, InR InL"

class Generator model cmd where
  generator :: model Symbolic -> Gen (cmd Symbolic)

instance (Generator model cmd1,
          Generator model cmd2) => Generator model (cmd1 :+: cmd2) where
  generator model = oneof
    [ InL <$> generator model
    , InR <$> generator model
    ]

class Shrinker model cmd where
  shrinker :: model Symbolic -> cmd Symbolic -> [cmd Symbolic]

class Invariant model where
  invariant :: model Concrete -> Logic

class Semantics cmd m resp where
  semantics :: cmd Concrete -> m (resp Concrete)

instance ( Monad m
         , Semantics cmd1 m resp1
         , Semantics cmd2 m resp2
         ) => Semantics (cmd1 :+: cmd2) m (resp1 :+: resp2) where
  semantics (InL cmd1) = InL <$> semantics cmd1
  semantics (InR cmd2) = InR <$> semantics cmd2

class Mock model cmd resp where
  mock :: model Symbolic -> cmd Symbolic -> GenSym (resp Symbolic)

instance (Mock model cmd1 resp1,
          Mock model cmd2 resp2) => Mock model (cmd1 :+: cmd2) (resp1 :+: resp2) where
  mock model (InL cmd1) = InL <$> mock model cmd1
  mock model (InR cmd2) = InR <$> mock model cmd2

type StateMachine model cmd m resp =
  ( InitModel model
  , Transition model cmd resp
  , Precondition model cmd
  , Postcondition model cmd resp
  , Semantics cmd m resp
  , Generator model cmd
  , Mock model cmd resp
  )

generateCommands :: forall model cmd m resp. StateMachine model cmd m resp
                 => Rank2.Foldable resp
                 => Proxy model -> Proxy m -> Gen (Commands cmd resp)
generateCommands _proxy _m = do
  let model :: model Symbolic
      model = initModel
  cmd <- generator model `suchThat` (boolean . precondition model)
  let (resp, counter') = runGenSym (mock model cmd) newCounter
      model'           = transition model cmd resp
  cmd' <- generator model' `suchThat` (boolean . precondition model')
  let (resp', _counter'') = runGenSym (mock model' cmd') counter'
  return (Commands [ Command cmd resp (getUsedVars resp)
                   , Command cmd' resp' (getUsedVars resp')
                   ])

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
  getProcesses    (Pair m1 _m2) = getProcesses m1
  setProcesses ps (Pair m1  m2) = Pair (setProcesses ps m1) m2

instance HasProcesses SpawnModel where
  getProcesses                    = processes
  setProcesses ps SpawnModel {..} = SpawnModel { processes = ps, ..}

instance InitModel SpawnModel where
  initModel = SpawnModel []

instance Precondition model Spawn where
  precondition _model Spawn = Top

instance (HasProcesses model, Transition model Spawn (Reference Int)) =>
          Postcondition model Spawn (Reference Int) where
  postcondition model Spawn ref  = ref `Logic.elem` getProcesses (transition model Spawn ref)

instance HasProcesses model => Transition model Spawn (Reference Int) where
  transition model Spawn r = modifyProcesses (r :) model

instance Generator model Spawn where
  generator _model = return Spawn

instance Semantics Spawn IO (Reference Int) where
  semantics Spawn = return (Reference (Concrete 0))

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
  getKilled    (Pair _m1 m2) = getKilled m2
  setKilled ps (Pair m1  m2) = Pair m1 (setKilled ps m2)

instance HasKilled KillModel where
  getKilled = killed
  setKilled ps KillModel {..} = KillModel { killed = ps }

instance HasKilled model => Transition model Kill (Const ()) where
  transition m (Kill r) (Const ()) = modifyKilled (++ [r]) m

instance HasProcesses model => Precondition model Kill where
  precondition m (Kill pid) = pid `Logic.elem` getProcesses m

instance (HasProcesses model, HasKilled model) => Postcondition model Kill (Const ()) where
  postcondition m (Kill pid) unit =
    pid `Logic.notElem` getProcesses (transition m (Kill pid) unit)

instance HasProcesses model => Generator model Kill where
  generator m = Kill <$> elements (getProcesses m)

instance Semantics Kill IO (Const ()) where
  semantics (Kill _) = return (Const ())

instance Mock model Kill (Const ()) where
  mock _model Kill{} = pure (Const ())

------------------------------------------------------------------------

type Model = SpawnModel :*: KillModel
type Cmds  = Spawn :+: Kill
type Resp  = Reference Int :+: Const ()

g :: IO (Commands Cmds Resp)
g = generate (generateCommands (Proxy @Model) (Proxy @IO))

test :: IO ()
test = pPrint =<< g

test2 :: IO ()
test2 = do
  let cmd :: VariantF '[Kill, Spawn] Symbolic
      cmd = FV @(Spawn Symbolic) Spawn

      cmd2 :: VariantF '[Kill, Spawn] Symbolic
      cmd2 = FV @(Kill Symbolic) (Kill (Reference (Symbolic (Var 0))))

  print $ boolean $ precondition (initModel :: SpawnModel Symbolic) cmd
  print $ boolean $ precondition (Pair initModel initModel :: Model Symbolic) cmd2


------------------------------------------------------------------------
-- Bank example
--
-- https://github.com/advancedtelematic/quickcheck-state-machine/pull/182/commits/3532f19a3fcb8081b761d0d80d3bc79cc18eb884

-- https://hooktube.com/watch?v=fSWZWXx5ixc

-- CONTEXT c0:
-- ACT, PRS : Set

-- MACHINE bank0 sees c0 (7:01):
-- act \subseteq ACT
-- owner : act -> PRS
-- bal : act -> Nat

-- init:
-- act, owner, bal := \emptyset

-- open (p : PRS, a : ACT), where a \nin act
-- owner(a) := p
-- bal(a) := 0
-- act := act \union {a}  <-- forgotten in first iteration

-- close (a : ACT), where a \in act and bal(a) = 0
-- owner := {a} <-| owner
-- bal := {a} <-| bal
-- act := act \ {a}  <-- forgotten in first iteration

-- deposit (a : ACT, q : Nat) where a \in act
-- bal := bal(a) + q

-- withdraw (a : ACT, q : Nat) where a \in act and bal(a) >= q
-- bal := bal(a) - q

----

-- bank1

-- inbank : act <-> Nat

-- move1 (b : ACT) refines withdraw, where b \in act and b /= a
-- inbank := inbank \union {b \mapsto q}

-- close refined with a \nin dom(inbank)

----

-- c1: KIND = { normal, savings} extends c0

-- MACHINE bank2 sees c1 (28:45)

-- kind : act -> KIND (init := \emptyset)

-- save (p : PRS) refines move1, where owner(a) = p and owner(b) = p
--   and kind(a) = normal and kind(b) = savings

-- open (k : KIND) refines open
-- kind(a) := k

-- close refines close
-- kind := {a} <-| kind

----


-- bank3 refines bank2 sees c2
-- file : act -> PRS \x N \x KIND
-- invariant forall a : act. file(a) = (owner(a), bal(a), kind(a))

------------------------------------------------------------------------

data Account = Account
  deriving (Eq, Show)
data Person  = Person
  deriving (Eq, Show)
type Money   = Int

data Open     r = Open Person Account
data Close    r = Close Account
data Deposit  r = Deposit Account Money
data Withdraw r = Withdraw Account Money

type Bank0 = Open :+: Close :+: Deposit :+: Withdraw

data Model0 r = Model0
  { accounts :: [Account]
  , owner    :: Account -> Money
  , balance  :: Account -> Money
  }

class HasAccounts model where
  getAccounts :: model r -> [Account]

instance HasAccounts m1 => HasAccounts (m1 :*: m2) where
  getAccounts = undefined

instance HasAccounts Model0 where
  getAccounts = accounts

instance Precondition Model0 Open where
  precondition = undefined

instance Precondition Model0 Close where
  precondition = undefined

instance Precondition Model0 Deposit where
  precondition = undefined

instance HasAccounts model => Precondition model Withdraw where
  precondition = undefined

----

data Move1 r = Move1 Account (Withdraw r)

type Bank1 = Bank0 :+: Move1

data InBank r = InBank { inbank :: [(Account, Money)] }

class HasInBank model where
  getInBank :: model r -> [(Account, Money)]

instance HasInBank InBank where
  getInBank = inbank

instance HasInBank m2 => HasInBank (m1 :*: m2) where
  getInBank = undefined

type Model1 = Model0 :*: InBank

instance (HasAccounts model, HasInBank model) => Precondition model Move1 where
  precondition model (Move1 a w) =
    precondition model w Logic..&&
    a `Logic.elem` getAccounts model

instance Precondition Model1 Bank1 where
  precondition (Pair model0 (InBank b)) (InL bank0) = precondition model0 bank0 Logic..&&
    case bank0 of
      -- This is the only new part:
      InR (InL (Close a)) -> a `Logic.notElem` map fst b
  precondition model1 (InR move1) = precondition model1 move1

----

data Kind = Normal | Savings

data BankKind r = BankKind { kind :: Account -> Kind }



-- kind : act -> KIND (init := \emptyset)

-- save (p : PRS) refines move1, where owner(a) = p and owner(b) = p
--   and kind(a) = normal and kind(b) = savings

-- open (k : KIND) refines open
-- kind(a) := k

-- close refines close
-- kind := {a} <-| kind
