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

import           Data.Constraint
                   (type (:-)(Sub), Dict(Dict))
import           Data.Constraint.Forall
                   (ForallF, instF)
import           Data.IORef
                   (IORef, newIORef, readIORef, writeIORef)
import           Data.Map
                   (Map)
import qualified Data.Map                as M
import           Data.TreeDiff
                   (ToExpr)
import           GHC.Generics
                   (Generic, Generic1)
import           Test.QuickCheck
import           Test.QuickCheck.Monadic
                   (monadicIO)

import qualified Test.StateMachine.Types.Rank2 as Rank2
import           Test.StateMachine

------------------------------------------------------------------------

data Command r
  = Create
  | Read  (Reference (IORef Int) r)
  | Write (Reference (IORef Int) r) Int
  deriving (Generic1, Rank2.Functor, Rank2.Foldable, Rank2.Traversable)

deriving instance Show (Command Symbolic)
deriving instance Show (Command Concrete)

data Response r
  = Created (Reference (IORef Int) r)
  | ReadValue Int
  | Written
  deriving (Generic1, Rank2.Foldable)

deriving instance Show (Response Symbolic)
deriving instance Show (Response Concrete)

newtype Model r = Model (Map (Reference (IORef Int) r) Int)
  deriving (Generic)

deriving instance Show (r (IORef Int)) => Show (Model r)

instance ToExpr (Model Concrete)

initModel :: Model r
initModel = Model M.empty

transition :: forall r. ForallF Ord r => Model r -> Command r -> Response r -> Model r
transition m@(Model model) cmd resp = case (cmd, resp) of
  (Create, Created ref)  -> case instF of
                              Sub (Dict :: Dict (Ord (r (IORef Int)))) ->
                                Model (M.insert ref 0 model)
  (Read _, ReadValue _)  -> m
  (Write ref x, Written) -> case instF of
                              Sub (Dict :: Dict (Ord (r (IORef Int)))) ->
                                Model (M.insert ref x model)
  _                      -> error "transition: impossible."

precondition :: Model Symbolic -> Command Symbolic -> Bool
precondition (Model m) cmd = case cmd of
  Create      -> True
  Read  ref   -> M.member ref m
  Write ref _ -> M.member ref m

postcondition :: forall r. ForallF Ord r => Model r -> Command r -> Response r -> Bool
postcondition (Model m) cmd resp = case (cmd, resp) of
  (Create,        Created ref) -> case instF of
                                    Sub (Dict :: Dict (Ord (r (IORef Int)))) ->
                                      m' M.! ref == 0
    where
      Model m' = transition (Model m) cmd resp
  (Read ref,      ReadValue v) -> case instF of
                                    Sub (Dict :: Dict (Ord (r (IORef Int)))) ->
                                      v == m M.! ref
  (Write _ref _x, Written)     -> True
  _                            -> False

semantics :: Command Concrete -> IO (Response Concrete)
semantics cmd = case cmd of
  Create      -> Created   <$> (reference =<< newIORef 0)
  Read ref    -> ReadValue <$> readIORef  (concrete ref)
  Write ref x -> Written   <$  writeIORef (concrete ref) (if x == 5 then x + 0 else x)

mock :: Model Symbolic -> Command Symbolic -> GenSym (Response Symbolic)
mock (Model m) cmd = case cmd of
  Create    -> Created   <$> genSym
  Read ref  -> ReadValue <$> pure (m M.! ref)
  Write _ _ -> pure Written

generator :: Model Symbolic -> [Gen (Command Symbolic)]
generator (Model model) =
  [ pure Create
  , Read  <$> elements (M.keys model)
  , Write <$> elements (M.keys model) <*> arbitrary
  ]

weight :: Model Symbolic -> Command Symbolic -> Int
weight (Model model) Create | M.null model = 10
                            | otherwise    = 1
weight (Model model) _      | M.null model = 0
                            | otherwise    = 5

shrinker :: Command Symbolic -> [Command Symbolic]
shrinker _ = []

sm :: StateMachine Model Command IO Response
sm = StateMachine initModel transition precondition postcondition Nothing
       generator (Just weight) shrinker semantics id mock

prop_modelCheck :: Property
prop_modelCheck = forAllShrinkCommands sm $ \cmds -> monadicIO $ do
  res <- modelCheck sm cmds
  -- prettyPrintHistory sm hist `whenFailM` (res === Ok)
  return (res === Ok)

prop_sequential :: Property
prop_sequential = forAllShrinkCommands sm $ \cmds -> monadicIO $ do
  (hist, _model, res) <- runCommands sm cmds
  prettyCommands sm hist (checkActionNames cmds (res === Ok))
