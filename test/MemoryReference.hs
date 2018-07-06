{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE ExplicitNamespaces   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE MonoLocalBinds       #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}

module MemoryReference where

import           Data.Functor.Classes
                   (Eq1, Show1)
import           Data.IORef
                   (IORef, newIORef, readIORef, writeIORef)
import           Data.TreeDiff
                   (ToExpr)
import           GHC.Generics
                   (Generic, Generic1)
import           Test.QuickCheck
                   (Gen, Property, arbitrary, elements, (===))
import           Test.QuickCheck.Monadic
                   (monadicIO)

import           Test.StateMachine
import qualified Test.StateMachine.Types.Rank2 as Rank2
import           Test.StateMachine.Z

------------------------------------------------------------------------

data Command r
  = Create
  | Read  (Reference (Opaque (IORef Int)) r)
  | Write (Reference (Opaque (IORef Int)) r) Int
  deriving (Generic1, Rank2.Functor, Rank2.Foldable, Rank2.Traversable)

deriving instance Show (Command Symbolic)
deriving instance Show (Command Concrete)

data Response r
  = Created (Reference (Opaque (IORef Int)) r)
  | ReadValue Int
  | Written
  deriving (Generic1, Rank2.Foldable)

deriving instance Show (Response Symbolic)
deriving instance Show (Response Concrete)

newtype Model r = Model (Fun (Reference (Opaque (IORef Int)) r) Int)
  deriving Generic

instance ToExpr (Model Symbolic)
instance ToExpr (Model Concrete)

initModel :: Model r
initModel = Model empty

transition :: Eq1 r => Model r -> Command r -> Response r -> Model r
transition m@(Model model) cmd resp = case (cmd, resp) of
  (Create, Created ref)  -> Model (model .! ref .= 0)
  (Read _, ReadValue _)  -> m
  (Write ref x, Written) -> Model (model .! ref .= x)
  _                      -> error "transition: impossible."

precondition :: Model Symbolic -> Command Symbolic -> Bool
precondition (Model m) cmd = case cmd of
  Create      -> True
  Read  ref   -> ref `elem` domain m
  Write ref _ -> ref `elem` domain m

postcondition :: (Show1 r, Eq1 r) => Model r -> Command r -> Response r -> Bool
postcondition (Model m) cmd resp = case (cmd, resp) of
  (Create,        Created ref) -> m' ! ref == 0
    where
      Model m' = transition (Model m) cmd resp
  (Read ref,      ReadValue v) -> v == m ! ref
  (Write _ref _x, Written)     -> True
  _                            -> False

semantics :: Command Concrete -> IO (Response Concrete)
semantics cmd = case cmd of
  Create      -> Created   <$> (reference . Opaque <$> newIORef 0)
  Read ref    -> ReadValue <$> readIORef  (opaque ref)
  Write ref x -> Written   <$  writeIORef (opaque ref) (if x == 5 then x + 0 else x)

mock :: Model Symbolic -> Command Symbolic -> GenSym (Response Symbolic)
mock (Model m) cmd = case cmd of
  Create    -> Created   <$> genSym
  Read ref  -> ReadValue <$> pure (m ! ref)
  Write _ _ -> pure Written

generator :: Model Symbolic -> [Gen (Command Symbolic)]
generator (Model model) =
  [ pure Create
  , Read  <$> elements (domain model)
  , Write <$> elements (domain model) <*> arbitrary
  ]

weight :: Model Symbolic -> Command Symbolic -> Int
weight (Model model) Create | null model = 10
                            | otherwise  = 5
weight (Model model) _      | null model = 0
                            | otherwise  = 5

shrinker :: Command Symbolic -> [Command Symbolic]
shrinker _ = []

sm :: StateMachine Model Command IO Response
sm = StateMachine initModel transition precondition postcondition Nothing
       generator (Just weight) shrinker semantics id mock

prop_modelCheck :: Property
prop_modelCheck = forAllShrinkCommands sm Nothing $ \cmds -> monadicIO $ do
  res <- undefined -- modelCheck sm cmds
  -- prettyPrintHistory sm hist `whenFailM` (res === Ok)
  return (res === Ok)

prop_sequential :: Property
prop_sequential = forAllShrinkCommands sm Nothing $ \cmds -> monadicIO $ do
  (hist, _model, res) <- runCommands sm cmds
  prettyCommands sm hist (checkCommandNames cmds (res === Ok))
