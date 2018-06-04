{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

module MemoryReference where

import           Data.IORef
import           Data.Map                (Map)
import qualified Data.Map                as M
import           Test.QuickCheck
import           Test.QuickCheck.Monadic (monadicIO)

import           Lib
import           Types                   (Concrete, GenSym, Reference (..),
                                          Result (Ok),
                                          StateMachine (StateMachine), Symbolic,
                                          concrete, genSym, reference)

------------------------------------------------------------------------

data Command r
  = Create
  | Read  (Reference r (IORef Int))
  | Write (Reference r (IORef Int)) Int

deriving instance Show (Command Symbolic)

data Response r
  = Created (Reference r (IORef Int))
  | ReadValue Int
  | Written

newtype Model r = Model (Map (Reference r (IORef Int)) Int)

initModel :: Model r
initModel = Model M.empty

transition :: Ord (r (IORef Int)) => Model r -> Command r -> Response r -> Model r
transition m@(Model model) cmd resp = case (cmd, resp) of
  (Create, Created ref)  -> Model (M.insert ref 0 model)
  (Read _, ReadValue _)  -> m
  (Write ref x, Written) -> Model (M.insert ref x model)

precondition :: Model Symbolic -> Command Symbolic -> Bool
precondition (Model m) cmd = case cmd of
  Create      -> True
  Read  ref   -> M.member ref m
  Write ref _ -> M.member ref m

postcondition :: Ord (r (IORef Int)) => Model r -> Command r -> Response r -> Bool
postcondition (Model m) cmd resp = case (cmd, resp) of
  (Create,        Created _ref) -> True
  (Read ref,      ReadValue v)  -> v == m M.! ref
  (Write _ref _x, Written)      -> True
  _                             -> False

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
shrinker = undefined

sm :: StateMachine Model Command Response
sm = StateMachine initModel undefined precondition undefined Nothing
       generator (Just weight) shrinker semantics mock

prop_modelCheck :: Property
prop_modelCheck = forAllShrinkCommands sm $ \cmds -> monadicIO $ do
  res <- modelCheck sm cmds
  -- prettyPrintHistory sm hist `whenFailM` (res === Ok)
  return (res === Ok)

