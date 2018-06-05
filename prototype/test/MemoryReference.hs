{-# LANGUAGE ExplicitNamespaces  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}

module MemoryReference where

import           Data.Constraint
                   (type (:-)(Sub), Dict(Dict))
import           Data.Constraint.Forall
                   (ForallF, instF)
import           Data.IORef
import           Data.Map
                   (Map)
import qualified Data.Map                as M
import qualified Rank2
import           Test.QuickCheck
import           Test.QuickCheck.Monadic
                   (monadicIO)

import           Lib
import           Types
                   (Concrete, GenSym, Reference(..), Result(Ok),
                   StateMachine(StateMachine), Symbolic, concrete,
                   genSym, reference)

------------------------------------------------------------------------

data Command r
  = Create
  | Read  (Reference (IORef Int) r)
  | Write (Reference (IORef Int) r) Int

deriving instance Show (Command Symbolic)

instance Rank2.Foldable Command where
  foldMap _ Create        = mempty
  foldMap f (Read ref)    = Rank2.foldMap f ref
  foldMap f (Write ref _) = Rank2.foldMap f ref

data Response r
  = Created (Reference (IORef Int) r)
  | ReadValue Int
  | Written

deriving instance Show (Response Symbolic)

instance Rank2.Foldable Response where
  foldMap f (Created ref) = Rank2.foldMap f ref
  foldMap _ (ReadValue _) = mempty
  foldMap _ Written       = mempty

newtype Model r = Model (Map (Reference (IORef Int) r) Int)

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
  Write ref x -> Written   <$  writeIORef (concrete ref) x

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

sm :: StateMachine Model Command Response
sm = StateMachine initModel transition precondition postcondition Nothing
       generator (Just weight) shrinker semantics mock

prop_modelCheck :: Property
prop_modelCheck = forAllShrinkCommands sm $ \cmds -> monadicIO $ do
  res <- modelCheck sm cmds
  -- prettyPrintHistory sm hist `whenFailM` (res === Ok)
  return (res === Ok)
