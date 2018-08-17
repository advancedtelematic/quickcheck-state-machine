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

module MemoryReference
  ( prop_sequential
  , prop_parallel
  , prop_modelCheck
  , Bug(..)
  )
  where

import           Control.Concurrent
                   (threadDelay)
import           Data.Functor.Classes
                   (Eq1, Show1)
import           Data.IORef
                   (IORef, atomicModifyIORef', newIORef, readIORef,
                   writeIORef)
import           Data.TreeDiff
                   (ToExpr)
import           GHC.Generics
                   (Generic, Generic1)
import           Prelude                       hiding
                   (elem)
import qualified Prelude
import           System.Random
                   (randomRIO)
import           Test.QuickCheck
                   (Gen, Property, arbitrary, collect, elements,
                   frequency, (===))
import           Test.QuickCheck.Monadic
                   (monadicIO, monitor)

import           Test.StateMachine
import qualified Test.StateMachine.Types.Rank2 as Rank2
import           Test.StateMachine.Z

------------------------------------------------------------------------

data Command r
  = Create
  | Read  (Reference (Opaque (IORef Int)) r)
  | Write (Reference (Opaque (IORef Int)) r) Int
  | Increment (Reference (Opaque (IORef Int)) r)
  deriving (Eq, Generic1, Rank2.Functor, Rank2.Foldable, Rank2.Traversable)

deriving instance Show (Command Symbolic)
deriving instance Show (Command Concrete)

data Response r
  = Created (Reference (Opaque (IORef Int)) r)
  | ReadValue Int
  | Written
  | Incremented
  deriving (Generic1, Rank2.Foldable)

deriving instance Show (Response Symbolic)
deriving instance Show (Response Concrete)

newtype Model r = Model (Fun (Reference (Opaque (IORef Int)) r) Int)
  deriving (Generic, Show)

instance ToExpr (Model Symbolic)
instance ToExpr (Model Concrete)

initModel :: Model r
initModel = Model empty

transition :: (Show1 r, Eq1 r) => Model r -> Command r -> Response r -> Model r
transition m@(Model model) cmd resp = case (cmd, resp) of
  (Create, Created ref)        -> Model (model .! ref .= 0)
  (Read _, ReadValue _)        -> m
  (Write ref x, Written)       -> Model (model .! ref .= x)
  (Increment ref, Incremented) -> Model (model .! ref .% succ)
  _                            -> error "transition: impossible."

precondition :: Model Symbolic -> Command Symbolic -> Logic
precondition (Model m) cmd = case cmd of
  Create        -> Top
  Read  ref     -> ref `elem` domain m
  Write ref _   -> ref `elem` domain m
  Increment ref -> ref `elem` domain m

postcondition :: (Show1 r, Eq1 r) => Model r -> Command r -> Response r -> Logic
postcondition (Model m) cmd resp = case (cmd, resp) of
  (Create,        Created ref) -> m' ! ref .== 0 .// "Create"
    where
      Model m' = transition (Model m) cmd resp
  (Read ref,      ReadValue v)  -> v .== m ! ref .// "Read"
  (Write _ref _x, Written)      -> Top
  (Increment _ref, Incremented) -> Top
  _                             -> Bot

data Bug
  = None
  | Logic
  | Race
  deriving Eq

semantics :: Bug -> Command Concrete -> IO (Response Concrete)
semantics bug cmd = case cmd of
  Create        -> Created     <$> (reference . Opaque <$> newIORef 0)
  Read ref      -> ReadValue   <$> readIORef  (opaque ref)
  Write ref i   -> Written     <$  writeIORef (opaque ref) i'
    where
    -- One of the problems is a bug that writes a wrong value to the
    -- reference.
      i' | i `Prelude.elem` [5..10] = if bug == Logic then i + 1 else i
         | otherwise                = i
  Increment ref -> do
    -- The other problem is that we introduce a possible race condition
    -- when incrementing.
    if bug == Race
    then do
      i <- readIORef (opaque ref)
      threadDelay =<< randomRIO (0, 5000)
      writeIORef (opaque ref) (i + 1)
    else
      atomicModifyIORef' (opaque ref) (\i -> (i + 1, ()))
    return Incremented

mock :: Model Symbolic -> Command Symbolic -> GenSym (Response Symbolic)
mock (Model m) cmd = case cmd of
  Create      -> Created   <$> genSym
  Read ref    -> ReadValue <$> pure (m ! ref)
  Write _ _   -> pure Written
  Increment _ -> pure Incremented

generator :: Model Symbolic -> Gen (Command Symbolic)
generator (Model model) = frequency
  [ (1, pure Create)
  , (4, Read  <$> elements (domain model))
  , (4, Write <$> elements (domain model) <*> arbitrary)
  , (4, Increment <$> elements (domain model))
  ]

shrinker :: Command Symbolic -> [Command Symbolic]
shrinker _ = []

sm :: Bug -> StateMachine Model Command IO Response
sm bug = StateMachine initModel transition precondition postcondition
           (Just postcondition) Nothing
           generator Nothing shrinker (semantics bug) id mock

prop_modelCheck :: Bug -> Property
prop_modelCheck bug = forAllCommands sm' Nothing $ \cmds -> monadicIO $ do
  res <- modelCheck sm' cmds
  return (res === Ok)
    where
      sm' = sm bug

prop_sequential :: Bug -> Property
prop_sequential bug = forAllCommands sm' Nothing $ \cmds -> monadicIO $ do
  (hist, _model, res) <- runCommands sm' cmds
  prettyCommands sm' hist (checkCommandNames cmds (res === Ok))
    where
      sm' = sm bug

prop_parallel :: Bug -> Property
prop_parallel bug = forAllParallelCommands sm' $ \cmds -> monadicIO $ do
  monitor (collect cmds)
  prettyParallelCommands cmds =<< runParallelCommands sm' cmds
    where
      sm' = sm bug
