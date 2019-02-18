{-# OPTIONS_GHC -fno-warn-orphans  #-}

{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

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
  , prop_parallelProcessRegistry
  , sm
  )
  where

import           Control.Exception
                   (Exception(..), catch, throwIO)
import           Control.Monad
                   (when)
import           Control.Monad.IO.Class
                   (MonadIO(..))
import           Data.Bifunctor
                   (first)
import           Data.Either
                   (isLeft, isRight)
import           Data.Foldable
                   (toList)
import           Data.Foldable
                   (traverse_)
import           Data.Functor.Classes
                   (Eq1, Show1)
import           Data.Hashable
                   (Hashable(..))
import qualified Data.HashTable.IO             as HashTable
import qualified Data.List                     as List
import           Data.Map
                   (Map)
import qualified Data.Map                      as Map
import           Data.Maybe
                   (fromJust, isJust, isNothing)
import           Data.Proxy
                   (Proxy(..))
import           Data.TreeDiff
                   (ToExpr(..), defaultExprViaShow)
import           GHC.Generics
                   (Generic)
import           Prelude                       hiding
                   (elem, notElem)
import qualified Prelude                       as P
import           System.IO.Unsafe
                   (unsafePerformIO)
import           System.Posix.Types
                   (CPid(..))
import qualified System.Process                as Proc
import           System.Random
                   (randomRIO)
import           Test.QuickCheck
                   (Gen, Property, elements, noShrinking, oneof,
                   tabulate, (===))
import           Test.QuickCheck.Monadic
                   (monadicIO)
import           Test.Tasty
                   (defaultMain)

import           Test.StateMachine             hiding
                   (ToState(..))
import           Test.StateMachine.Types
                   (Command(..), Commands(..), History(..),
                   Operation(..), Reference(..), makeOperations)
import qualified Test.StateMachine.Types.Rank2 as Rank2
import           Test.Tasty.QuickCheckSM

------------------------------------------------------------------------
-- Domain

data Mock = Mock
  { registry :: Map Pname Pid
  , pids     :: [Pid]
  , next     :: Pid
  } deriving (Show, Generic)

newtype Pname = Pname String
  deriving stock (Eq, Ord, Show, Generic)

newtype Pid = Pid Int
  deriving newtype (Num, Enum)
  deriving stock (Eq, Generic, Show)

emptyMock :: Mock
emptyMock = Mock mempty mempty 0

data Err = PidNotFound | AlreadyRegistered | NotRegistered | UnknownError
  deriving (Eq, Show)

instance Exception Err

data Success r = Unit () | Got r
  deriving (Eq, Show, Functor, Foldable, Traversable)

newtype Resp r = Resp { getResp :: Either Err (Success r) }
  deriving (Eq, Show, Functor, Foldable, Traversable)

type MockOp a = Mock -> (Either Err a, Mock)

mSpawn :: MockOp Pid
mSpawn Mock{..} =
  let pid = next
  in (Right pid, Mock{ pids = pid:pids, next = succ next, .. })

mKill :: Pid -> MockOp ()
mKill pid Mock{..}
  | pid `P.notElem` pids = (Left PidNotFound, Mock{..})
  | otherwise = (Right (), Mock{ pids = List.delete pid pids, ..})

mRegister :: Pname -> Pid -> MockOp ()
mRegister pname pid Mock{..}
  | pid `P.notElem` pids = (Left PidNotFound, Mock{..})
  | Just _ <- Map.lookup pname registry = (Left AlreadyRegistered, Mock{..})
  | otherwise = (Right (), Mock{ registry = Map.insert pname pid registry, .. })

mUnregister :: Pname -> MockOp ()
mUnregister pname Mock{..}
  | Nothing <- Map.lookup pname registry = (Left NotRegistered, Mock{..})
  | otherwise = (Right (), Mock{ registry = Map.delete pname registry, ..})

mWhereIs :: Pname -> MockOp Pid
mWhereIs pname Mock{..}
  | Just pid <- Map.lookup pname registry = (Right pid, Mock{..})
  | otherwise = (Left NotRegistered, Mock{..})

data Cmd r
  = Spawn
  | Kill r
  | Register Pname r
  | Unregister Pname
  | WhereIs Pname
  | Bad (Cmd r)
  deriving (Show, Functor, Foldable, Traversable)

runMock :: Cmd Pid -> Mock -> (Resp Pid, Mock)
runMock Spawn = first (Resp . fmap Got) . mSpawn
runMock (Register pname pid) = first (Resp . fmap Unit) . mRegister pname pid
runMock (Unregister pname) = first (Resp . fmap Unit) . mUnregister pname
runMock (Kill pid) = first (Resp . fmap Unit) . mKill pid
runMock (WhereIs pname) = first (Resp . fmap Got) . mWhereIs pname
runMock (Bad cmd)       = runMock cmd

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

instance Hashable Pname

instance Hashable Proc.Pid where
  hashWithSalt salt (CPid pid) = hashWithSalt salt pid

type PidTable = HashTable.CuckooHashTable Proc.Pid Proc.ProcessHandle

pidTable :: PidTable
pidTable =
  unsafePerformIO $ HashTable.new
{-# NOINLINE pidTable #-}

type ProcessTable = HashTable.CuckooHashTable Pname Proc.Pid

procTable :: ProcessTable
procTable =
  unsafePerformIO $ HashTable.new
{-# NOINLINE procTable #-}

ioReset :: IO ()
ioReset = do
  pids <- fmap fst <$> HashTable.toList pidTable
  traverse_ (HashTable.delete pidTable) pids

  pnames <- fmap fst <$> HashTable.toList procTable
  traverse_ (HashTable.delete procTable) pnames

ioSpawn :: IO Proc.Pid
ioSpawn = do
  die <- randomRIO (1, 6) :: IO Int
  when (die == -1) $
    throwIO UnknownError
  ph <- Proc.spawnCommand "true"
  mpid <- Proc.getPid ph
  case mpid of
    Nothing  -> throwIO PidNotFound
    Just pid -> do
      HashTable.insert pidTable pid ph
      return pid

ioRegister :: Pname -> Proc.Pid -> IO ()
ioRegister name pid = do
  mpid <- HashTable.lookup pidTable pid
  when (isNothing mpid) $
    throwIO PidNotFound
  mp <- HashTable.lookup procTable name
  when (isJust mp) $
    throwIO AlreadyRegistered
  HashTable.insert procTable name pid

ioUnregister :: Pname -> IO ()
ioUnregister pname = do
  mp <- HashTable.lookup procTable pname
  when (isNothing mp) $
    throwIO NotRegistered
  HashTable.delete procTable pname

ioKill :: Proc.Pid -> IO ()
ioKill pid = do
  m <- HashTable.lookup pidTable pid
  when (isNothing m) $
    throwIO PidNotFound
  HashTable.delete pidTable pid

ioWhereIs :: Pname -> IO Proc.Pid
ioWhereIs name = do
  mpid <- HashTable.lookup procTable name
  case mpid of
    Nothing  -> throwIO NotRegistered
    Just pid -> pure pid

catchErr :: IO (Success h) -> IO (Resp h)
catchErr act = catch (Resp . Right <$> act) handler
  where
    handler :: Err -> IO (Resp h)
    handler e = pure $ Resp (Left e)

runIO :: Cmd Proc.Pid -> IO (Resp Proc.Pid)
runIO = catchErr . go
  where
    go :: Cmd Proc.Pid -> IO (Success Proc.Pid)
    go Spawn                = Got  <$> ioSpawn
    go (Register pname pid) = Unit <$> ioRegister pname pid
    go (Unregister pname)   = Unit <$> ioUnregister pname
    go (Kill pid)           = Unit <$> ioKill pid
    go (WhereIs pname)      = Got  <$> ioWhereIs pname
    go (Bad cmd)            = go cmd

------------------------------------------------------------------------
-- Model

newtype At f r = At (f (Reference Proc.Pid r))
type    f :@ r = At f r

deriving stock instance Show (f (Reference Proc.Pid r)) => Show (At f r)

semantics :: Cmd :@ Concrete -> IO (Resp :@ Concrete)
semantics (At c) = (At . fmap reference) <$> runIO (concrete <$> c)

type PidRefs r = [(Reference Proc.Pid r, Pid)]

(!) :: Eq k => [(k, a)] -> k -> a
env ! r = fromJust (lookup r env)

data Model r = Model Mock (PidRefs r)
  deriving Generic

deriving instance Show1 r => Show (Model r)

initModel :: Model r
initModel = Model emptyMock []

toMock :: (Functor f, Eq1 r) => Model r -> f :@ r -> f Pid
toMock (Model _ pids) (At fr) = (pids !) <$> fr

step :: Eq1 r => Model r -> Cmd :@ r -> (Resp Pid, Mock)
step m@(Model mock _) c = runMock (toMock m c) mock

data Event r = Event
  { before   :: Model  r
  , cmd      :: Cmd :@ r
  , after    :: Model  r
  , mockResp :: Resp Pid
  } deriving Show

lockstep :: Eq1 r
         => Model   r
         -> Cmd  :@ r
         -> Resp :@ r
         -> Event   r
lockstep m@(Model _ hs) c (At resp) = Event
  { before   = m
  , cmd      = c
  , after    = Model mock' (hs <> hs')
  , mockResp = resp'
  }
  where
    (resp', mock') = step m c
    hs' = zip (toList resp) (toList resp')

transition :: Eq1 r => Model r -> Cmd :@ r -> Resp :@ r -> Model r
transition m c = after . lockstep m c

precondition :: Model Symbolic -> Cmd :@ Symbolic -> Logic
precondition model@(Model _ refs) cmd@(At cmd')
  = forall (toList cmd') (`elem` map fst refs)
  .&& case cmd' of
        Bad (Bad _) -> Bot .// "impossible: Bad (Bad ...)"
        Bad _cmd    -> Boolean (isLeft  resp) .// "Bad command doesn't throw error"
        _cmd        -> Boolean (isRight resp) .// "Good command throws error"
  where
    resp = getResp (fst (step model cmd))

postcondition
  :: Model   Concrete
  -> Cmd  :@ Concrete
  -> Resp :@ Concrete
  -> Logic
postcondition m c r = toMock (after e) r .== mockResp e
  where
    e = lockstep m c r

symbolicResp
  :: Model Symbolic
  -> Cmd :@ Symbolic
  -> GenSym (Resp :@ Symbolic)
symbolicResp m c = At <$> traverse (const genSym) resp
  where
    (resp, _mock') = step m c

generator :: Model Symbolic -> Gen (Cmd :@ Symbolic)
generator (Model _ refs) = oneof
  [ genSpawn
  , genRegister
  , genUnregister
  , genKill
  , genWhereIs

  , genBadSpawn
  , genBadRegister
  , genBadUnregister
  , genBadKill
  , genBadWhereIs
  ]
  where
    genName = elements (map Pname ["A", "B", "C"])

    genSpawn      = At <$> pure Spawn
    genRegister   = At <$> (Register <$> genName <*> genRef)
    genUnregister = At . Unregister <$> genName
    genKill       = At . Kill <$> genRef
    genWhereIs    = At . WhereIs <$> genName

    genBadSpawn      = At <$> pure (Bad Spawn)
    genBadRegister   = At . Bad <$> (Register <$> genName <*> genRef)
    genBadUnregister = At . Bad . Unregister <$> genName
    genBadKill       = At . Bad . Kill <$> genRef
    genBadWhereIs    = At . Bad . WhereIs <$> genName

    genRef  = elements (map fst refs)

shrinker :: Model Symbolic -> Cmd :@ Symbolic -> [Cmd :@ Symbolic]
shrinker _ _ = []

sm :: StateMachine Model (At Cmd) IO (At Resp)
sm =
  StateMachine
    initModel
    transition
    precondition
    postcondition
    Nothing
    (Just . generator)
    Nothing
    shrinker
    semantics
    symbolicResp

------------------------------------------------------------------------
-- additional class instances

instance CommandNames (At Cmd) where
  cmdName (At cmd0) = conName cmd0
    where
      conName cmd = case cmd of
        Spawn {}      -> "Spawn"
        Register {}   -> "Register"
        Unregister {} -> "Unregister"
        Kill {}       -> "Kill"
        WhereIs {}    -> "WhereIs"
        Bad cmd'      -> "Bad" ++ conName cmd'
  cmdNames _ = cmds ++ map ("Bad" ++) cmds
    where
      cmds = ["Spawn", "Register", "Unregister", "Kill", "WhereIs"]

instance Functor f => Rank2.Functor (At f) where
  fmap = \f (At x) -> At $ fmap (lift f) x
    where
      lift :: (r x -> r' x) -> Reference x r -> Reference x r'
      lift f (Reference x) = Reference (f x)

instance Foldable f => Rank2.Foldable (At f) where
  foldMap = \f (At x) -> foldMap (lift f) x
    where
      lift :: (r x -> m) -> Reference x r -> m
      lift f (Reference x) = f x

instance Traversable t => Rank2.Traversable (At t) where
  traverse = \f (At x) -> At <$> traverse (lift f) x
    where
      lift :: Functor f
           => (r x -> f (r' x)) -> Reference x r -> f (Reference x r')
      lift f (Reference x) = Reference <$> f x

deriving instance ToExpr (Model Concrete)
deriving instance ToExpr Mock
deriving newtype instance ToExpr Pid
deriving newtype instance ToExpr Pname

instance ToExpr Proc.Pid where
  toExpr = defaultExprViaShow

------------------------------------------------------------------------

prop_processRegistry :: Property
prop_processRegistry = noShrinking $
  forAllCommands sm Nothing $ \cmds ->
    monadicIO $ do
      liftIO ioReset
      (hist, _model, res) <- runCommands sm cmds
      prettyCommands sm hist
        $ checkCommandNames cmds
        $ tabulate "Usage"        (map show $ tag $ replayCmds cmds)
        $ tabulate "Observations" (map show $ replayHist hist)
        $ res === Ok

prop_parallelProcessRegistry :: Property
prop_parallelProcessRegistry = noShrinking $
  forAllParallelCommands sm $ \cmds -> monadicIO $ do
  liftIO ioReset
  -- If we run more than once below we'll end up with (already registered)
  -- errors. Perhaps 'runParallelCommandsNTimes' needs to be parametrised by a
  -- clean up function? Also see
  -- https://github.com/advancedtelematic/quickcheck-state-machine/issues/83 .
  prettyParallelCommands cmds =<< runParallelCommandsNTimes 1 sm cmds

------------------------------------------------------------------------
-- Usage analysis

data Fin2
  = Zero
  | One
  | TwoOrMore
  deriving (Enum, Bounded, Show, Eq, Read, Ord)

type ModelState = (Fin2, Fin2)

abstract :: Model r -> ModelState
abstract (Model Mock{..} _) =
  let spawned = case length pids of
        0 -> Zero
        1 -> One
        _ -> TwoOrMore
      registered = case length (Map.keys registry) of
        0 -> Zero
        1 -> One
        _ -> TwoOrMore
   in (spawned, registered)

tag :: [Event Symbolic] -> [(ModelState, ToState ModelState)]
tag evs = case foldr f (Nothing, mempty) evs of
  (Nothing, _)      -> mempty
  (Just last', akk) -> (last', Sink):akk
  where
    f (Event{..}) (_, akk) =
      let current = abstract after
      in (Just current, (abstract before, Successful $ abstract after):akk)

replayCmd :: Model Symbolic
        -> Command (At Cmd) (At Resp)
        -> Event Symbolic
replayCmd model (Command cmd resp _) =
  lockstep model cmd resp

replayCmds :: Commands (At Cmd) (At Resp) -> [Event Symbolic]
replayCmds (Commands cs) = go initModel cs
  where
    go :: Model Symbolic
       -> [Command (At Cmd) (At Resp)]
       -> [Event Symbolic]
    go _ []         = []
    go m (c : cs') = e : go (after e) cs'
      where
        e = replayCmd m c

-----------------------------------------------------------------------------
-- Observations

replayOp :: Model Concrete
       -> Operation (At Cmd) (At Resp)
       -> (Model Concrete, ModelState, ToState ModelState)
replayOp model (Operation cmd resp _) =
  let success = toMock model' resp == mockResp e
      from    = abstract model
      to      = (if success then Successful else Failed)
                  (abstract model')
  in (model', from, to)
  where
    e      = lockstep model cmd resp
    model' = after e
replayOp model (Crash _ _ _) =
  let state = abstract model
  in (model, state, Failed state)

replayOps :: [Operation (At Cmd) (At Resp)] -> [(ModelState, ToState ModelState)]
replayOps ops = map (\(_, from, to) -> (from, to)) (go initModel ops)
  where
    go :: Model Concrete
       -> [Operation (At Cmd) (At Resp)]
       -> [(Model Concrete, ModelState, ToState ModelState)]
    go m []         = [(m, abstract m, Sink)] -- XXX Successful -> Failed -> Sink
    go m (c : ops') = (m, from, to) : go m' ops'
      where
        (m', from, to) = replayOp m c

replayHist :: History (At Cmd) (At Resp) -> [(ModelState, ToState ModelState)]
replayHist = replayOps . makeOperations . unHistory

-----------------------------------------------------------------------------

_t :: IO ()
_t =
  defaultMain $
    testProperty "test" (Proxy :: Proxy ModelState) prop_processRegistry
