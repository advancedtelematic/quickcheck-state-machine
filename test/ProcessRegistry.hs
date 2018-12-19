{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RecordWildCards            #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ProcessRegistry
-- Copyright   :  (C) 2017, Jacob Stanley; 2018, Stevan Andjelkovic
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan.andjelkovic@here.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains the process registry example that is commonly
-- used in the papers on Erlang QuickCheck, e.g. "Finding Race
-- Conditions in Erlang with QuickCheck and PULSE". Parts of the code
-- are stolen from an example in Hedgehog.
--
-----------------------------------------------------------------------------

module ProcessRegistry
  ( prop_processRegistry
  , markovGood
  , markovDeadlock
  , markovNotStochastic1
  , markovNotStochastic2
  , markovNotStochastic3
  , sm
  , initFiniteModel
  )
  where

import           Control.Monad
                   (when)
import           Control.Monad.IO.Class
                   (MonadIO(..))
import           Data.Foldable
                   (traverse_)
import qualified Data.HashTable.IO             as HashTable
import           Data.IORef
                   (IORef)
import qualified Data.IORef                    as IORef
import           Data.Map
                   (Map)
import qualified Data.Map.Strict               as Map
import           Data.Maybe
                   (isJust, isNothing)
import           Data.TreeDiff
                   (ToExpr)
import           GHC.Generics
                   (Generic, Generic1)
import           Prelude                       hiding
                   (elem, notElem)
import           System.IO.Unsafe
                   (unsafePerformIO)
import           Test.QuickCheck
                   (Arbitrary, Gen, Property, arbitrary, elements,
                   (===))
import           Test.QuickCheck.Monadic
                   (monadicIO)

import           Test.StateMachine
import qualified Test.StateMachine.Types.Rank2 as Rank2

------------------------------------------------------------------------
-- Implementation
--
-- The following code is stolen from an Hedgehog example:
--
-- Fake Process Registry
--
-- /These are global to simulate some kind of external system we're
-- testing./
--

newtype Name = Name String
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (ToExpr)

newtype Pid = Pid Int
  deriving newtype (Num)
  deriving stock (Eq, Generic, Show)
  deriving anyclass (ToExpr)

type ProcessTable = HashTable.CuckooHashTable String Int

pidRef :: IORef Pid
pidRef =
  unsafePerformIO $ IORef.newIORef 0
{-# NOINLINE pidRef #-}

procTable :: ProcessTable
procTable =
  unsafePerformIO $ HashTable.new
{-# NOINLINE procTable #-}

ioReset :: IO ()
ioReset = do
  IORef.writeIORef pidRef 0
  ks <- fmap fst <$> HashTable.toList procTable
  traverse_ (HashTable.delete procTable) ks

ioSpawn :: IO Pid
ioSpawn = do
  pid <- IORef.readIORef pidRef
  IORef.writeIORef pidRef (pid + 1)
  pure pid

ioRegister :: Name -> Pid -> IO ()
ioRegister (Name name) (Pid pid) = do
  m <- HashTable.lookup procTable name

  when (isJust m) $
    fail "ioRegister: already registered"

  HashTable.insert procTable name pid

ioUnregister :: Name -> IO ()
ioUnregister (Name name) = do
  m <- HashTable.lookup procTable name

  when (isNothing m) $
    fail "ioUnregister: not registered"

  HashTable.delete procTable name

-- Here we extend the Hedgehog example with a looking up names in the
-- registry.
ioWhereIs :: Name -> IO Pid
ioWhereIs (Name name) = do
  mpid <- HashTable.lookup procTable name

  case mpid of
    Nothing  -> fail "ioWhereIs: not registered"
    Just pid -> return (Pid pid)

------------------------------------------------------------------------
-- Specification

data Action (r :: * -> *)
  = Spawn
  | Kill (Reference Pid r)
  | Register Name (Reference Pid r)
  | Unregister Name
  | WhereIs Name
  deriving (Show, Generic1, Rank2.Functor, Rank2.Foldable, Rank2.Traversable)

data Response (r :: * -> *)
  = Spawned (Reference Pid r)
  | Killed
  | Registered
  | Unregistered
  | HereIs (Reference Pid r)
  deriving (Show, Generic1, Rank2.Foldable)

data Model (r :: * -> *) = Model
  { pids     :: [Reference Pid r]
  , registry :: Map Name (Reference Pid r)
  , killed   :: [Reference Pid r]
  }
  deriving (Show, Generic)

instance ToExpr (Model Concrete)

initModel :: Model r
initModel = Model [] Map.empty []

transition :: Model r -> Action r -> Response r -> Model r
transition Model {..} act resp = case (act, resp) of

  (Spawn, Spawned pid) ->
    Model { pids = pids ++ [pid], .. }

  (Kill pid, Killed) ->
    Model { killed = killed ++ [pid], .. }

  (Register name pid, Registered) ->
    Model { registry = Map.insert name pid registry, .. }

  (Unregister name, Unregistered) ->
    Model { registry = Map.delete name registry, .. }

  (WhereIs _name, HereIs _pid) ->
    Model {..}

  (_, _) -> error "transition"

precondition :: Model Symbolic -> Action Symbolic -> Logic
precondition Model {..} act = case act of
  Spawn             -> Top
  Kill pid          -> pid `elem` pids
  Register name pid -> pid `elem` pids
                   .&& name `notElem` Map.keys registry
  Unregister name   -> name `elem` Map.keys registry
  WhereIs name      -> name `elem` Map.keys registry

postcondition :: Model Concrete -> Action Concrete -> Response Concrete -> Logic
postcondition Model {..} act resp = case (act, resp) of
  (Spawn, Spawned _pid)             -> Top
  (Kill _pid, Killed)               -> Top
  (Register _name _pid, Registered) -> Top
  (Unregister _name, Unregistered)  -> Top
  (WhereIs name, HereIs pid)        -> registry Map.! name .== pid
  (_, _)                            -> Bot

semantics :: Action Concrete -> IO (Response Concrete)
semantics Spawn               = Spawned . reference <$> ioSpawn
semantics (Kill _pid)         = pure Killed
semantics (Register name pid) = Registered <$ ioRegister name (concrete pid)
semantics (Unregister name)   = Unregistered <$ ioUnregister name
semantics (WhereIs name)      = HereIs . reference <$> ioWhereIs name

data Fin2
  = Zero
  | One
  | Two
  deriving (Enum, Bounded, Show, Eq)

type FiniteModel = (Fin2, Fin2)

initFiniteModel :: FiniteModel
initFiniteModel = (Zero, Zero)

instance Arbitrary Name where
  arbitrary = elements (map Name ["A", "B", "C"])

markovGood :: Markov Model FiniteModel Action
markovGood = Markov f
  where
    f :: FiniteModel -> [(Int, Continue Model FiniteModel Action)]
    f (Zero, Zero) = [ (100, Continue "Spawn" (const (pure Spawn)) (One, Zero)) ]

    f (One,  Zero) = [ (40,  Continue "Spawn" (const (pure Spawn)) (Two, Zero))
                     , (40,  Continue "Register" (\m -> Register <$> arbitrary <*> elements (pids m)) (One, One))
                     , (20,  Continue "Kill" (\m -> Kill <$> elements (pids m)) (Zero, Zero))
                     ]
    f (One,  One)  = [ (50,  Continue "Spawn" (const (pure Spawn)) (Two, One))
                     , (20,  Continue "Unregister" (\m -> Unregister <$> elements (Map.keys (registry m))) (One, Zero))
                     , (30,  Continue "WhereIs" (\m -> WhereIs <$> elements (Map.keys (registry m))) (One, One))
                     ]
    f (Two, Zero)  = [ (80, Continue "Register" (\m -> Register <$> arbitrary <*> elements (pids m)) (Two, One))
                     , (20, Continue "Kill" (\m -> Kill <$> elements (pids m)) (One, Zero))
                     ]

    f (Two, One)   = [ (40, Continue "Register" (\m -> Register <$> arbitrary <*> elements (pids m)) (Two, Two))
                     , (10, Continue "Kill" (\m -> Kill <$> elements (pids m)) (One, One))
                     , (20, Continue "Unregister" (\m -> Unregister <$> elements (Map.keys (registry m))) (Two, Zero))
                     , (20, Continue "WhereIs" (\m -> WhereIs <$> elements (Map.keys (registry m))) (Two, One))
                     , (10, Stop)
                     ]
    f (Two, Two)   = [ (30, Stop)
                     , (20, Continue "Unregister" (\m -> Unregister <$> elements (Map.keys (registry m))) (Two, One))
                     , (50, Continue "WhereIs" (\m -> WhereIs <$> elements (Map.keys (registry m))) (Two, Two))
                     ]
    f _            = []

markovDeadlock :: Markov Model FiniteModel Action
markovDeadlock = Markov f
  where
    nameGen :: Gen Name
    nameGen = return (Name "A")

    f :: FiniteModel -> [(Int, Continue Model FiniteModel Action)]
    f (Zero, Zero) = [ (100, Continue "Spawn" (const (pure Spawn)) (One, Zero)) ]
    f (One,  Zero) = [ (100, Continue "Spawn" (const (pure Spawn)) (Two, Zero)) ]
    f (Two, Zero)  = [ (100, Continue "Register"
                               (\m -> Register <$> nameGen
                                               <*> elements (pids m)) (Two, One)) ]
    f (Two, One)   = [ (100, Continue "Register"
                               (\m -> Register <$> nameGen
                                               <*> elements (pids m)) (Two, Two)) ]
    f (Two, Two)   = [ (100, Stop) ]
    f _            = []

markovNotStochastic1 :: Markov Model FiniteModel Action
markovNotStochastic1 = Markov f
  where
    f (Zero, Zero) = [ (90, Continue "Spawn" (const (pure Spawn)) (One, Zero)) ]
    f (One, Zero)  = [ (100, Stop) ]
    f _            = []

markovNotStochastic2 :: Markov Model FiniteModel Action
markovNotStochastic2 = Markov f
  where
    f (Zero, Zero) = [ (110, Continue "Spawn" (const (pure Spawn)) (One, Zero))
                     , (-10, Stop)
                     ]
    f (One, Zero)  = [ (100, Stop) ]
    f _            = []

markovNotStochastic3 :: Markov Model FiniteModel Action
markovNotStochastic3 = Markov f
  where
    f (Zero, Zero) = [ (90, Continue "Spawn" (const (pure Spawn)) (One, Zero))
                     , (10, Stop)
                     ]
    f (One, Zero)  = [ (100, Stop) ]
    f (Two, Two)   = [ (90, Stop) ]
    f _            = []

shrinker :: Action Symbolic -> [Action Symbolic]
shrinker _act = []

mock :: Model Symbolic -> Action Symbolic -> GenSym (Response Symbolic)
mock _m act = case act of
  Spawn               -> Spawned <$> genSym
  Kill _pid           -> pure Killed
  Register _name _pid -> pure Registered
  Unregister _name    -> pure Unregistered
  WhereIs _name       -> HereIs <$> genSym

sm :: Markov Model FiniteModel Action
   -> AdvancedStateMachine Model FiniteModel Action IO Response
sm chain = StateMachine initModel transition precondition postcondition
       Nothing undefined (Just (chain, (Zero, Zero))) shrinker semantics mock
               -- ^ XXX: Either Generator Markov? Would be a breaking change...

prop_processRegistry :: Markov Model FiniteModel Action -> Property
prop_processRegistry chain = forAllCommands sm' Nothing $ \cmds -> monadicIO $ do
  liftIO ioReset
  (hist, _model, res) <- runCommands sm' cmds
  tabulateState sm' hist
  prettyCommands sm' hist (checkCommandNames cmds (res === Ok))
    where
      sm' = sm chain
