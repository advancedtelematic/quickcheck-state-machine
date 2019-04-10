{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}

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
  , prop_processRegistry'
  , markovGood
  , markovDeadlock
  , markovNotStochastic1
  , markovNotStochastic2
  , markovNotStochastic3
  , sm
  , initState
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
import           Data.Kind
                   (Type)
import           Data.Map
                   (Map)
import qualified Data.Map.Strict               as Map
import           Data.Maybe
                   (isJust, isNothing)
import           GHC.Generics
                   (Generic, Generic1)
import           Prelude                       hiding
                   (elem, notElem)
import           System.IO.Unsafe
                   (unsafePerformIO)
import           System.Random
                   (randomRIO)
import           Test.QuickCheck
                   (Arbitrary, Gen, Property, arbitrary, elements,
                   frequency, (===))
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

  die <- randomRIO (1, 6) :: IO Int
  if die == -1
  then error "ioSpawn"
  else pure pid

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

data Action (r :: Type -> Type)
  = Spawn
  | Kill (Reference Pid r)
  | Register Name (Reference Pid r)
  | Unregister Name
  | WhereIs Name
  | Exit
  deriving (Show, Generic1, Rank2.Functor, Rank2.Foldable, Rank2.Traversable,
            CommandNames)

data Action_
  = Spawn_
  | Kill_
  | Register_
  | Unregister_
  | WhereIs_
  | Exit_
  deriving Show

constructor :: Action r -> Action_
constructor act = case act of
  Spawn      {} -> Spawn_
  Kill       {} -> Kill_
  Register   {} -> Register_
  Unregister {} -> Unregister_
  WhereIs    {} -> WhereIs_
  Exit       {} -> Exit_

data Response (r :: Type -> Type)
  = Spawned (Reference Pid r)
  | Killed
  | Registered
  | Unregistered
  | HereIs (Reference Pid r)
  | Exited
  deriving (Show, Generic1, Rank2.Foldable)

data Model (r :: Type -> Type) = Model
  { pids     :: [Reference Pid r]
  , registry :: Map Name (Reference Pid r)
  , killed   :: [Reference Pid r]
  , stop     :: Bool
  }
  deriving (Show, Generic)

instance ToExpr (Model Concrete)

initModel :: Model r
initModel = Model [] Map.empty [] False

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

  (Exit, Exited) ->
    Model { stop = True, .. }

  (_, _) -> error "transition"

precondition :: Model Symbolic -> Action Symbolic -> Logic
precondition Model {..} act = case act of
  Spawn             -> Top
  Kill pid          -> pid `member` pids
  Register name pid -> pid `member` pids
                   .&& name `notMember` Map.keys registry
  Unregister name   -> name `member` Map.keys registry
  WhereIs name      -> name `member` Map.keys registry
  Exit              -> Top

postcondition :: Model Concrete -> Action Concrete -> Response Concrete -> Logic
postcondition Model {..} act resp = case (act, resp) of
  (Spawn, Spawned _pid)             -> Top
  (Kill _pid, Killed)               -> Top
  (Register _name _pid, Registered) -> Top
  (Unregister _name, Unregistered)  -> Top
  (WhereIs name, HereIs pid)        -> registry Map.! name .== pid
  (Exit, Exited)                    -> Top
  (_, _)                            -> Bot

semantics :: Action Concrete -> IO (Response Concrete)
semantics Spawn               = Spawned . reference <$> ioSpawn
semantics (Kill _pid)         = pure Killed
semantics (Register name pid) = Registered <$ ioRegister name (concrete pid)
semantics (Unregister name)   = Unregistered <$ ioUnregister name
semantics (WhereIs name)      = HereIs . reference <$> ioWhereIs name
semantics Exit                = return Exited

data Fin2
  = Zero
  | One
  | Two
  deriving (Enum, Bounded, Show, Eq, Read, Ord)

type State = (Fin2, Fin2)

partition :: Model r -> State
partition Model {..} = ( toEnum (length pids - length killed)
                       , toEnum (length (Map.keys registry))
                       )

initState :: State
initState = (Zero, Zero)

instance Arbitrary Name where
  arbitrary = elements (map Name ["A", "B", "C"])

markovGood :: Markov Model State Action
markovGood = Markov f
  where
    f :: State -> [(Int, Continue Model State Action)]
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

genSpawn, genKill, genRegister, genUnregister, genWhereIs, genExit
  :: Model Symbolic -> Gen (Action Symbolic)

genSpawn     _model = return Spawn
genKill       model = Kill       <$> elements (pids model)
genRegister   model = Register   <$> arbitrary <*> elements (pids model)
genUnregister model = Unregister <$> elements (Map.keys (registry model))
genWhereIs    model = WhereIs    <$> elements (Map.keys (registry model))
genExit      _model = return Exit

generator :: Model Symbolic -> Maybe (Gen (Action Symbolic))
generator model
  | stop model = Nothing
  | otherwise  = Just $ case partition model of
      (Zero, Zero) -> genSpawn model
      (One,  Zero) -> frequency
                        [ (40, genSpawn model)
                        , (40, genRegister model)
                        , (20, genKill model)
                        ]
      (One,  One)  -> frequency
                        [ (50, genSpawn model)
                        , (20, genUnregister model)
                        , (30, genWhereIs model)
                        ]
      (Two, Zero)  -> frequency
                        [ (80, genRegister model)
                        , (20, genKill model)
                        ]

      (Two, One)   -> frequency
                        [ (40, genRegister model)
                        , (10, genKill model)
                        , (20, genUnregister model)
                        , (20, genWhereIs model)
                        , (10, genExit model)
                        ]
      (Two, Two)   -> frequency
                        [ (30, genExit model)
                        , (20, genUnregister model)
                        , (50, genWhereIs model)
                        ]
      _            -> error "generator: illegal state"


markovDeadlock :: Markov Model State Action
markovDeadlock = Markov f
  where
    nameGen :: Gen Name
    nameGen = return (Name "A")

    f :: State -> [(Int, Continue Model State Action)]
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

markovNotStochastic1 :: Markov Model State Action
markovNotStochastic1 = Markov f
  where
    f (Zero, Zero) = [ (90, Continue "Spawn" (const (pure Spawn)) (One, Zero)) ]
    f (One, Zero)  = [ (100, Stop) ]
    f _            = []

markovNotStochastic2 :: Markov Model State Action
markovNotStochastic2 = Markov f
  where
    f (Zero, Zero) = [ (110, Continue "Spawn" (const (pure Spawn)) (One, Zero))
                     , (-10, Stop)
                     ]
    f (One, Zero)  = [ (100, Stop) ]
    f _            = []

markovNotStochastic3 :: Markov Model State Action
markovNotStochastic3 = Markov f
  where
    f (Zero, Zero) = [ (90, Continue "Spawn" (const (pure Spawn)) (One, Zero))
                     , (10, Stop)
                     ]
    f (One, Zero)  = [ (100, Stop) ]
    f (Two, Two)   = [ (90, Stop) ]
    f _            = []

shrinker :: Model Symbolic -> Action Symbolic -> [Action Symbolic]
shrinker _model _act = []

mock :: Model Symbolic -> Action Symbolic -> GenSym (Response Symbolic)
mock _m act = case act of
  Spawn               -> Spawned <$> genSym
  Kill _pid           -> pure Killed
  Register _name _pid -> pure Registered
  Unregister _name    -> pure Unregistered
  WhereIs _name       -> HereIs <$> genSym
  Exit                -> pure Exited

sm :: StateMachine Model Action IO Response
sm = StateMachine initModel transition precondition postcondition
       Nothing generator shrinker semantics mock

prop_processRegistry :: Markov Model State Action -> Property
prop_processRegistry chain = forAllMarkov sm chain initState $ \cmds -> monadicIO $ do
  liftIO ioReset
  (hist, _model, res) <- runCommands sm cmds
  prettyCommands sm hist (checkCommandNames cmds (res === Ok))

prop_processRegistry' :: Property
prop_processRegistry' = forAllCommands sm (Just 100000) $ \cmds -> monadicIO $ do
  liftIO ioReset
  (hist, _model, res) <- runCommands sm cmds

  prettyCommands sm hist
    $ coverTransitions
        [ (Zero, Zero) -< (Spawn_, 1) >- (One, Zero)

        , (One,  Zero) -< (Spawn_,    0.4) >- (Two, Zero)
        , (One,  Zero) -< (Register_, 0.4) >- (One, One)
        , (One,  Zero) -< (Kill_,     0.2) >- (Zero, Zero)

        , (One,  One)  -< (Spawn_,      0.5) >- (Two, One)
        , (One,  One)  -< (Unregister_, 0.2) >- (One, Zero)
        , (One,  One)  -< (WhereIs_,    0.3) >- (One, One)

        , (Two, Zero)  -< (Register_, 0.8) >- (Two, One)
        , (Two, Zero)  -< (Kill_,     0.2) >- (One, Zero)

        , (Two, One)   -< (Register_,   0.4) >- (Two, Two)
        , (Two, One)   -< (Kill_,       0.1) >- (One, One)
        , (Two, One)   -< (Unregister_, 0.2) >- (Two, Zero)
        , (Two, One)   -< (WhereIs_,    0.2) >- (Two, One)
        , (Two, One)   -< (Exit_,       0.1) >- (Two, One)

        , (Two, Two)   -< (Exit_,       0.3) >- (Two, Two)
        , (Two, Two)   -< (Unregister_, 0.2) >- (Two, One)
        , (Two, Two)   -< (WhereIs_,    0.5) >- (Two, Two)
        ]
    $ tabulateMarkov sm partition constructor cmds
    $ res === Ok
