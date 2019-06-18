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
  , printLabelledExamples
  )
  where

import           Control.Exception
                   (catch)
import           Control.Monad
                   (when)
import           Control.Monad.IO.Class
                   (MonadIO(..))
import           Data.Foldable
                   (traverse_)
import           Data.Functor.Classes
                   (Ord1)
import           Data.Hashable
                   (Hashable)
import qualified Data.HashTable.IO             as HashTable
import           Data.IORef
                   (IORef)
import qualified Data.IORef                    as IORef
import           Data.Kind
                   (Type)
import           Data.List
                   ((\\))
import           Data.Map
                   (Map)
import qualified Data.Map.Strict               as Map
import           Data.Maybe
                   (isJust, isNothing)
import           Data.Set
                   (Set)
import qualified Data.Set                      as Set
import           Data.Tuple
                   (swap)
import           GHC.Generics
                   (Generic, Generic1)
import           Prelude
import           System.IO.Error
                   (IOError, ioeGetErrorString)
import           System.IO.Unsafe
                   (unsafePerformIO)
import           System.Random
                   (randomRIO)
import           Test.QuickCheck
                   (Arbitrary, Gen, Property, arbitrary, elements,
                   tabulate, (.&&.), (===))
import           Test.QuickCheck.Monadic
                   (monadicIO)

import           Test.StateMachine
import           Test.StateMachine.Labelling
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
  deriving stock (Eq, Ord, Generic, Show)
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

killedPidsRef :: IORef [Pid]
killedPidsRef =
  unsafePerformIO $ IORef.newIORef []
{-# NOINLINE killedPidsRef #-}

ioReset :: IO ()
ioReset = do
  IORef.writeIORef pidRef 0
  ks <- fmap fst <$> HashTable.toList procTable
  traverse_ (HashTable.delete procTable) ks
  IORef.writeIORef killedPidsRef []

ioSpawn :: IO Pid
ioSpawn = do
  pid <- IORef.readIORef pidRef
  IORef.writeIORef pidRef (pid + 1)

  die <- randomRIO (1, 6) :: IO Int
  if die == -1
  then error "ioSpawn"
  else pure pid

ioKill :: Pid -> IO ()
ioKill pid = do
  IORef.modifyIORef killedPidsRef (pid :)

reverseLookup :: (Eq k, Eq v, Hashable k, Hashable v)
              => HashTable.CuckooHashTable k v -> v -> IO (Maybe k)
reverseLookup tbl val = do
  lbt <- swapTable tbl
  HashTable.lookup lbt val
  where
    -- Swap the keys and values in a hashtable.
    swapTable :: (Eq k, Eq v, Hashable k, Hashable v)
              => HashTable.CuckooHashTable k v -> IO (HashTable.CuckooHashTable v k)
    swapTable t = HashTable.fromList =<< fmap (map swap) (HashTable.toList t)

ioRegister :: Name -> Pid -> IO ()
ioRegister (Name name) pid'@(Pid pid) = do

  mpid <- HashTable.lookup procTable name
  when (isJust mpid) $
    fail "ioRegister: name already registered"

  mname <- reverseLookup procTable pid
  when (isJust mname) $
    fail "ioRegister: pid already registered"

  killedPids <- IORef.readIORef killedPidsRef

  when (pid' `elem` killedPids) $
    fail "ioRegister: pid is dead"

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
  | BadRegister Name (Reference Pid r)
  | Unregister Name
  | BadUnregister Name
  | WhereIs Name
  | Exit
  deriving (Show, Generic1, Rank2.Functor, Rank2.Foldable, Rank2.Traversable,
            CommandNames)

data Action_
  = Spawn_
  | Kill_
  | Register_
  | BadRegister_
  | Unregister_
  | BadUnregister_
  | WhereIs_
  | Exit_
  deriving (Show, Eq, Ord, Generic)

constructor :: Action r -> Action_
constructor act = case act of
  Spawn         {} -> Spawn_
  Kill          {} -> Kill_
  Register      {} -> Register_
  BadRegister   {} -> BadRegister_
  Unregister    {} -> Unregister_
  BadUnregister {} -> BadUnregister_
  WhereIs       {} -> WhereIs_
  Exit          {} -> Exit_

newtype Response (r :: Type -> Type) = Response
  { _getResponse :: Either Error (Success r) }
  deriving stock (Show, Generic1)
  deriving anyclass Rank2.Foldable

data Success (r :: Type -> Type)
  = Spawned (Reference Pid r)
  | Killed
  | Registered
  | Unregistered
  | HereIs (Reference Pid r)
  | Exited
  deriving (Show, Generic1, Rank2.Foldable)

data Error
  = NameAlreadyRegisteredError
  | PidAlreadyRegisteredError
  | PidDeadRegisterError
  | NameNotRegisteredError
  | UnknownError
  deriving Show

success :: Success r -> Response r
success = Response . Right

failure :: Error -> Response r
failure = Response . Left

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
transition m          act (Response (Left _err))  = case act of
  BadRegister   {} -> m
  BadUnregister {} -> m
  _otherwise       -> error "transition: good command throws error"
transition Model {..} act (Response (Right resp)) = case (act, resp) of

  (Spawn, Spawned pid) ->
    Model { pids = pids ++ [pid], .. }

  (Kill pid, Killed) ->
    Model { killed = killed ++ [pid], .. }

  (Register name pid, Registered) ->
    Model { registry = Map.insert name pid registry, .. }

  (BadRegister _name _pid, _) -> error "transition: BadRegister"

  (Unregister name, Unregistered) ->
    Model { registry = Map.delete name registry, .. }

  (BadUnregister _name, _) -> error "transition: BadUnregister"

  (WhereIs _name, HereIs _pid) ->
    Model {..}

  (Exit, Exited) ->
    Model { stop = True, .. }

  (_, _) -> error "transition"

precondition :: Model Symbolic -> Action Symbolic -> Logic
precondition Model {..} act = case act of
  Spawn                -> Top
  Kill pid             -> pid `member` pids
  Register name pid    -> pid `member` pids
                      .&& name `notMember` Map.keys  registry
                      .&& pid  `notMember` Map.elems registry
  BadRegister name pid -> pid `member` killed
                      .|| name `member` Map.keys  registry
                      .|| pid  `member` Map.elems registry
  Unregister name      -> name `member` Map.keys registry
  BadUnregister name   -> name `notMember` Map.keys registry
  WhereIs name         -> name `member` Map.keys registry
  Exit                 -> Top

postcondition :: Model Concrete -> Action Concrete -> Response Concrete -> Logic
postcondition Model {..} act (Response (Left err))   = case act of
  BadRegister _name _pid -> Top
  BadUnregister _name    -> Top
  _                      -> Bot .// show err
postcondition Model {..} act (Response (Right resp)) = case (act, resp) of
  (Spawn, Spawned _pid)             -> Top
  (Kill _pid, Killed)               -> Top
  (Register _name _pid, Registered) -> Top
  (Unregister _name, Unregistered)  -> Top
  (WhereIs name, HereIs pid)        -> registry Map.! name .== pid
  (Exit, Exited)                    -> Top
  (_, _)                            -> Bot

semantics' :: Action Concrete -> IO (Success Concrete)
semantics' Spawn                  = Spawned . reference <$> ioSpawn
semantics' (Kill pid)             = Killed <$ ioKill (concrete pid)
semantics' (Register name pid)    = Registered <$ ioRegister name (concrete pid)
semantics' (BadRegister name pid) = Registered <$ ioRegister name (concrete pid)
semantics' (Unregister name)      = Unregistered <$ ioUnregister name
semantics' (BadUnregister name)   = Unregistered <$ ioUnregister name
semantics' (WhereIs name)         = HereIs . reference <$> ioWhereIs name
semantics' Exit                   = return Exited

semantics :: Action Concrete -> IO (Response Concrete)
semantics act = fmap success (semantics' act)
                `catch`
                  (return . failure . handler)
  where
    handler :: IOError -> Error
    handler err = case ioeGetErrorString err of
      "ioRegister: name already registered" -> NameAlreadyRegisteredError
      "ioRegister: pid already registered"  -> PidAlreadyRegisteredError
      "ioRegister: pid is dead"             -> PidDeadRegisterError
      "ioUnregister: not registered"        -> NameNotRegisteredError
      _ -> UnknownError

data Fin2
  = Zero
  | One
  | Two
  deriving (Enum, Bounded, Show, Eq, Read, Ord)

data State = Fin2 :*: Fin2 | Stop
  deriving (Show, Eq, Ord, Generic)

partition :: Model r -> State
partition Model {..}
  | stop      = Stop
  | otherwise = (   toEnum (length pids - length killed)
                :*: toEnum (length (Map.keys registry))
                )

sinkState :: State -> Bool
sinkState = (== Stop)

_initState :: State
_initState = Zero :*: Zero

allNames :: [Name]
allNames = map Name ["A", "B", "C"]

instance Arbitrary Name where
  arbitrary = elements allNames

genSpawn, genKill, genRegister, genBadRegister, genUnregister, genBadUnregister,
  genWhereIs, genExit :: Model Symbolic -> Gen (Action Symbolic)

genSpawn        _model = return Spawn
genKill          model = Kill        <$> elements (pids model)
genRegister      model = Register    <$> arbitrary <*> elements (pids model \\ killed model)
genBadRegister   model = BadRegister <$> arbitrary <*> elements (pids model ++ killed model)
genUnregister    model = Unregister  <$> elements (Map.keys (registry model))
genBadUnregister model = BadUnregister <$> elements (allNames \\ Map.keys (registry model))
genWhereIs       model = WhereIs       <$> elements (Map.keys (registry model))
genExit         _model = return Exit

gens :: Map Action_ (Model Symbolic -> Gen (Action Symbolic))
gens = Map.fromList
  [ (Spawn_,         genSpawn)
  , (Kill_,          genKill)
  , (Register_,      genRegister)
  , (BadRegister_,   genBadRegister)
  , (Unregister_,    genUnregister)
  , (BadUnregister_, genBadUnregister)
  , (WhereIs_,       genWhereIs)
  , (Exit_,          genExit)
  ]

generator :: Model Symbolic -> Maybe (Gen (Action Symbolic))
generator = markovGenerator markov gens partition sinkState

shrinker :: Model Symbolic -> Action Symbolic -> [Action Symbolic]
shrinker _model _act = []

mock :: Model Symbolic -> Action Symbolic -> GenSym (Response Symbolic)
mock m act = case act of
  Spawn                  -> success . Spawned <$> genSym
  Kill _pid              -> pure (success Killed)
  Register _name _pid    -> pure (success Registered)
  BadRegister name pid
    | name `elem` Map.keys  (registry m) -> pure (failure NameAlreadyRegisteredError)
    | pid  `elem` Map.elems (registry m) -> pure (failure PidAlreadyRegisteredError)
    | pid  `elem` killed m               -> pure (failure PidDeadRegisterError)
    | otherwise                          -> error "mock: BadRegister"
  Unregister _name       -> pure (success Unregistered)
  BadUnregister _name    -> pure (failure NameNotRegisteredError)
  WhereIs _name          -> success . HereIs <$> genSym
  Exit                   -> pure (success Exited)

sm :: StateMachine Model Action IO Response
sm = StateMachine initModel transition precondition postcondition
       Nothing generator shrinker semantics mock

markov :: Markov State Action_ Double
markov = makeMarkov
  [ Zero :*: Zero -< [ Spawn_ /- One :*: Zero ]

  , One :*: Zero -< [ Spawn_             /- Two :*: Zero
                    , Register_          /- One :*: One
                    , (BadRegister_, 10) >- One :*: Zero
                    , (Kill_, 20)        >- Zero :*: Zero
                    ]

  , One :*: One  -< [ (Spawn_,      40) >- Two :*: One
                    , BadRegister_      /- One :*: One
                    , (Unregister_, 20) >- One :*: Zero
                    , BadUnregister_    /- One :*: One
                    , (WhereIs_,    20) >- One :*: One
                    ]

  , Two :*: Zero  -< [ (Register_, 80) >- Two :*: One
                     , (Kill_,     20) >- One :*: Zero
                     ]

  , Two :*: One   -< [ (Register_,      30) >- Two :*: Two
                     , (Kill_,          10) >- One :*: One
                     , (Unregister_,    20) >- Two :*: Zero
                     , (BadUnregister_, 10) >- Two :*: One
                     , (WhereIs_,       20) >- Two :*: One
                     , (Exit_,          10) >- Stop
                     ]

  , Two :*: Two   -< [ (Exit_,       30) >- Stop
                     , (Unregister_, 20) >- Two :*: One
                     , (WhereIs_,    50) >- Two :*: Two
                     ]
  ]

------------------------------------------------------------------------

-- Requirements from the paper "How well are your requirements tested?"
-- (2016) by Arts and Hughes.
data Req
  = RegisterNewNameAndPid_REG001
  | RegisterExistingName_REG002
  | RegisterExistingPid_REG003
  | RegisterDeadPid_REG004
  | UnregisterRegisteredName_UNR001
  | UnregisterNotRegisteredName_UNR002
  | WHE001
  | WHE002
  | DIE001
  deriving (Eq, Ord, Show, Generic, ToExpr)

type EventPred r = Predicate (Event Model Action Response r) Req

-- Convenience combinator for creating classifiers for successful commands.
successful :: (Event Model Action Response r -> Success r -> Either Req (EventPred r))
           -> EventPred r
successful f = predicate $ \ev ->
                 case eventResp ev of
                   Response (Left  _ ) -> Right $ successful f
                   Response (Right ok) -> f ev ok

tag :: forall r. Ord1 r => [Event Model Action Response r] -> [Req]
tag = classify
  [ tagRegisterNewNameAndPid
  , tagRegisterExistingName Set.empty
  , tagRegisterExistingPid  Set.empty
  , tagRegisterDeadPid      Set.empty
  , tagUnregisterRegisteredName    Set.empty
  , tagUnregisterNotRegisteredName Set.empty
  ]
  where
    tagRegisterNewNameAndPid :: EventPred r
    tagRegisterNewNameAndPid = successful $ \ev _ -> case eventCmd ev of
      Register _ _ -> Left RegisterNewNameAndPid_REG001
      _otherwise   -> Right tagRegisterNewNameAndPid

    tagRegisterExistingName :: Set Name -> EventPred r
    tagRegisterExistingName existingNames = predicate $ \ev ->
      case (eventCmd ev, eventResp ev) of
        (Register name _pid, Response (Right Registered)) ->
          Right (tagRegisterExistingName (Set.insert name existingNames))
        (BadRegister name _pid, Response (Left NameAlreadyRegisteredError))
          | name `Set.member` existingNames -> Left RegisterExistingName_REG002
        _otherwise
          -> Right (tagRegisterExistingName existingNames)

    tagRegisterExistingPid :: Set (Reference Pid r) -> EventPred r
    tagRegisterExistingPid existingPids = predicate $ \ev ->
      case (eventCmd ev, eventResp ev) of
        (Register _name pid, Response (Right Registered)) ->
          Right (tagRegisterExistingPid (Set.insert pid existingPids))
        (BadRegister _name pid, Response (Left PidAlreadyRegisteredError))
          | pid `Set.member` existingPids -> Left RegisterExistingPid_REG003
        _otherwise
          -> Right (tagRegisterExistingPid existingPids)

    tagRegisterDeadPid :: Set (Reference Pid r) -> EventPred r
    tagRegisterDeadPid killedPids = predicate $ \ev ->
      case (eventCmd ev, eventResp ev) of
        (Kill pid, Response (Right Killed)) ->
          Right (tagRegisterDeadPid (Set.insert pid killedPids))
        (BadRegister _name pid, Response (Left PidDeadRegisterError))
          | pid `Set.member` killedPids -> Left RegisterDeadPid_REG004
        _otherwise
          -> Right (tagRegisterDeadPid killedPids)

    tagUnregisterRegisteredName :: Set Name -> EventPred r
    tagUnregisterRegisteredName registeredNames = successful $ \ev resp ->
      case (eventCmd ev, resp) of
        (Register name _pid, Registered) ->
          Right (tagUnregisterRegisteredName (Set.insert name registeredNames))
        (Unregister name, Unregistered)
          | name `Set.member` registeredNames -> Left UnregisterRegisteredName_UNR001
        _otherwise
          -> Right (tagUnregisterRegisteredName registeredNames)

    tagUnregisterNotRegisteredName :: Set Name -> EventPred r
    tagUnregisterNotRegisteredName registeredNames = predicate $ \ev ->
      case (eventCmd ev, eventResp ev) of
        (Register name _pid, Response (Right Registered)) ->
          Right (tagUnregisterNotRegisteredName (Set.insert name registeredNames))
        (BadUnregister name, Response (Left NameNotRegisteredError))
          | name `Set.notMember` registeredNames -> Left UnregisterNotRegisteredName_UNR002
        _otherwise
          -> Right (tagUnregisterNotRegisteredName registeredNames)

printLabelledExamples :: IO ()
printLabelledExamples = showLabelledExamples sm tag

------------------------------------------------------------------------

prop_processRegistry :: StatsDb IO -> Property
prop_processRegistry sdb = forAllCommands sm (Just 100000) $ \cmds -> monadicIO $ do
  liftIO ioReset
  (hist, _model, res) <- runCommands sm cmds

  let observed = historyObservations sm markov partition constructor hist
      reqs     = tag (execCmds sm cmds)

  persistStats sdb observed

  prettyCommands' sm tag cmds hist
    $ tabulate "_Requirements" (map show reqs)
    $ coverMarkov markov
    $ tabulateMarkov sm partition constructor cmds
    $ printReliability sdb (transitionMatrix markov) observed
    $ res === Ok .&&. reqs === tag (execHistory sm hist)
