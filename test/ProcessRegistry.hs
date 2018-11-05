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
  , markovTransitionMismatch
  , markovNotStochastic
  , markovNotStochastic'
  , sm
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

instance Arbitrary Name where
  arbitrary = elements (map Name ["A", "B", "C"])

finiteModel :: Model Symbolic -> FiniteModel
finiteModel Model {..} =
  ( toEnum (length pids - length killed)
  , toEnum (length (Map.toList registry))
  )

markovGood :: Markov (Model Symbolic) FiniteModel (Action Symbolic)
markovGood = Markov finiteModel g
  where
    g :: FiniteModel
      -> [(Int, Continue (Model Symbolic -> Gen (Action Symbolic), FiniteModel))]
    g (Zero, Zero) = [ (100, Continue (const (pure Spawn), (One, Zero))) ]

    g (One,  Zero) = [ (10,  Stop)
                     , (30,  Continue (const (pure Spawn), (Two, Zero)))
                     , (40,  Continue (\m -> Register <$> arbitrary <*> elements (pids m), (One, One)))
                     , (20,  Continue (\m -> Kill <$> elements (pids m), (Zero, Zero)))
                     ]
    g (One,  One)  = [ (10,  Stop)
                     , (50,  Continue (const (pure Spawn), (Two, One)))
                     , (20,  Continue (\m -> Unregister <$> elements (Map.keys (registry m)), (One, Zero)))
                     , (20,  Continue (\m -> WhereIs <$> elements (Map.keys (registry m)), (One, One)))
                     ]
    g (Two, Zero)  = [ (30, Stop)
                     , (50, Continue (\m -> Register <$> arbitrary <*> elements (pids m), (Two, One)))
                     , (20, Continue (\m -> Kill <$> elements (pids m), (One, Zero)))
                     ]

    g (Two, One)   = [ (30, Stop)
                     , (20, Continue (\m -> Register <$> arbitrary <*> elements (pids m), (Two, Two)))
                     , (10, Continue (\m -> Kill <$> elements (pids m), (One, One)))
                     , (20, Continue (\m -> Unregister <$> elements (Map.keys (registry m)), (Two, Zero)))
                     , (20, Continue (\m -> WhereIs <$> elements (Map.keys (registry m)), (Two, One)))
                     ]
    g (Two, Two)   = [ (30, Stop)
                     , (20, Continue (\m -> Unregister <$> elements (Map.keys (registry m)), (Two, One)))
                     , (50, Continue (\m -> WhereIs <$> elements (Map.keys (registry m)), (Two, Two)))
                     ]
    g _            = []

markovDeadlock :: Markov (Model Symbolic) FiniteModel (Action Symbolic)
markovDeadlock = Markov finiteModel g
  where
    nameGen :: Gen Name
    nameGen = return (Name "A")

    g :: FiniteModel
      -> [(Int, Continue (Model Symbolic -> Gen (Action Symbolic), FiniteModel))]
    g (Zero, Zero) = [ (100, Continue (const (pure Spawn), (One, Zero))) ]
    g (One,  Zero) = [ (100, Continue (const (pure Spawn), (Two, Zero))) ]
    g (Two, Zero)  = [ (100, Continue (\m -> Register <$> nameGen
                                                      <*> elements (pids m), (Two, One))) ]
    g (Two, One)   = [ (100, Continue (\m -> Register <$> nameGen
                                                      <*> elements (pids m), (Two, Two))) ]
    g (Two, Two)   = [ (100, Stop) ]
    g _            = []

markovTransitionMismatch :: Markov (Model Symbolic) FiniteModel (Action Symbolic)
markovTransitionMismatch = Markov finiteModel g
  where
    g (Zero, Zero) = [ (100, Continue (const (pure Spawn), (Zero, Zero))) ]
    g (_, _)       = []

markovNotStochastic :: Markov (Model Symbolic) FiniteModel (Action Symbolic)
markovNotStochastic = Markov finiteModel g
  where
    g (Zero, Zero) = [ (90, Continue (const (pure Spawn), (One, Zero))) ]
    g (One, Zero)  = [ (100, Stop) ]
    g _            = []

markovNotStochastic' :: Markov (Model Symbolic) FiniteModel (Action Symbolic)
markovNotStochastic' = Markov finiteModel g
  where
    g (Zero, Zero) = [ (110, Continue (const (pure Spawn), (One, Zero)))
                     , (-10, Stop)
                     ]
    g (One, Zero)  = [ (100, Stop) ]
    g _            = []

shrinker :: Action Symbolic -> [Action Symbolic]
shrinker _act = []

mock :: Model Symbolic -> Action Symbolic -> GenSym (Response Symbolic)
mock _m act = case act of
  Spawn               -> Spawned <$> genSym
  Kill _pid           -> pure Killed
  Register _name _pid -> pure Registered
  Unregister _name    -> pure Unregistered
  WhereIs _name       -> HereIs <$> genSym

sm :: Markov (Model Symbolic) FiniteModel (Action Symbolic)
   -> AdvancedStateMachine Model FiniteModel Action IO Response
sm chain = StateMachine initModel transition precondition postcondition
       Nothing undefined (Just chain) shrinker semantics mock
               -- ^ XXX: Either Generator Markov? Would be a breaking change...

prop_processRegistry :: Markov (Model Symbolic) FiniteModel (Action Symbolic)
                     -> Property
prop_processRegistry chain = forAllCommands sm' Nothing $ \cmds -> monadicIO $ do
  liftIO ioReset
  (hist, _model, res) <- runCommands sm' cmds
  prettyCommands sm' hist (checkCommandNames cmds (res === Ok))
    where
      sm' = sm chain
