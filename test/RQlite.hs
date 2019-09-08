{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE PackageImports       #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}

module RQlite (
      Level (..)
    , prop_sequential_rqlite
    , prop_parallel_rqlite
    , prop_nparallel_rqlite
    , runCmds
    ) where

import           Control.Concurrent
                   (threadDelay)
import           Control.Concurrent.MVar
import           Control.Exception (bracketOnError, try)
import           Control.Monad (void, when)
import           Control.Monad.IO.Class  (liftIO)
import           Data.Aeson hiding (Result)
import           Data.Foldable
import           Data.Functor.Classes
import           Data.Kind
import           Data.List
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe
import           Data.TreeDiff
import           GHC.Generics
import           Prelude
import "hs-rqlite" Rqlite
import "hs-rqlite" Rqlite.Status
import           System.Directory
import           System.IO
import           System.Process
import           System.Random
import           Test.QuickCheck hiding (Result)
import           Test.QuickCheck.Monadic
import           Test.StateMachine
import           Test.StateMachine.DotDrawing
import           Test.StateMachine.Types (ParallelCommandsF(..),
                     History(..), interleavings)
import qualified Test.StateMachine.Types.Rank2 as Rank2
import           Test.StateMachine.Types.References

newtype At t r = At {unAt :: t (NodeRef r)}
  deriving (Generic)

instance Show (t (NodeRef r)) => Show (At t r) where
    show = show . unAt

data Person = Person {
    name :: String
  , age  :: Int
} deriving (Show, Read, Eq, Generic)

-- HTTP requests utilities

instance FromJSON Person where
    parseJSON j = do
        (n, a) <- parseJSON j
        return $ Person n a

createQ :: String
createQ =  "CREATE TABLE Person (name text, age Int)"

insertQuery :: String -> Person -> IO PostResult
insertQuery host Person{..} =
    postQuery True host $ "INSERT INTO Person(name, age) VALUES('" ++ name ++ "', " ++ show age ++ ")"

selectQuery :: Maybe Level -> String -> IO (GetResult Person)
selectQuery lvl host = do
    putStrLnM $ "querying " ++ host
    getQuery lvl host True "SELECT * FROM Person"

createQuery :: String -> IO PostResult
createQuery host = postQuery True host createQ

------------------------

-- Docker utilities

data Container = Container {
        counter  :: Int
      , cn       :: Int
      , nodeName :: String
      , cport    :: Int
} deriving (Generic)

instance Eq Container where
    n1 == n2 = counter n1 == counter n2

instance Show Container where
    show Container{..} = "Node@" ++ show cport

instance ToExpr Container where
    toExpr Container{..} = App ("Node@" ++ show cport) []

ignoreIOError :: IO a -> IO ()
ignoreIOError action = do
    (_ :: Either IOError a) <- try action
    return ()

stopContainer :: String -> IO ()
stopContainer ndName = do
    stdErr <- openFile "/dev/null" AppendMode
    -- stopping or removing a non-existing container should be a no-op
    ignoreIOError $ readCreateProcess (proc "docker"
      [ "stop"
      , ndName
      ]) {std_err = UseHandle stdErr}
      ""
    ignoreIOError $ readCreateProcess (proc "docker"
      [ "rm"
      , ndName
      ]) {std_err = UseHandle stdErr}
      ""

mkNodeTime :: Int -> Int -> Timeout -> Timeout -> Maybe Int -> IO Container
mkNodeTime c n timeout elTimeout mjoin = do
    (ndName, p) <- setupNode n timeout elTimeout mjoin
    return $ Container c n ndName p

stopNode :: Container -> IO ()
stopNode Container {..} = stopContainer nodeName

setupNode :: Int -> Timeout -> Timeout -> Maybe Int -> IO (String, Int)
setupNode n timeout elTimeout mjoin = do
  r :: Word <- randomIO
  let p   = leaderPort + 2 * n
      p'  = 4002 + 2 * n
      ip  = "172.19.0." ++ show (10 + n) -- http
      ip' = "172.18.0." ++ show (10 + n)
      mjoin' = fmap (\j -> "http://" ++ httpHost j) mjoin
      ndName = mkNodeName r
      jls = case mjoin' of
        Nothing   -> []
        Just join -> ["-join", join]
  stopContainer ndName

  void $ readProcess "docker"
        ([ "create"
        , "--net"
        , "rqlite-http"
        , "--ip"
        , ip
        , "-p"
        , show p ++ ":" ++ show p
        , "--name"
        , ndName
        , "rqlite/rqlite"
        , "-http-addr"
        , ip ++ ":" ++ show p
        , "-raft-addr"
        , ip' ++ ":" ++ show p'
        , "-raft-timeout"
        , show timeout
        , "-raft-election-timeout"
        , show elTimeout
        ] ++ jls) ""

  -- connect the container to the rqlite network.
  void $ readProcess "docker"
        [ "network"
        , "connect"
        , "--ip"
        , ip'
        , "rqlite-network"
        , ndName
        ] ""

  stdOut' <- openFile (testPath ++ "/out-" ++ show n) AppendMode
  stdErr' <- openFile (testPath ++ "/err-" ++ show n) AppendMode
  stdIn'  <- openFile "/dev/null" ReadMode
  -- we don't use readProcess here, because we don't want to block.
  void $ createProcess (proc "docker"
        [ "start"
        , "-a" -- this attaches the stdout and stderr to the one we specify.
        , ndName
        ]) {std_in = UseHandle stdIn', std_out = UseHandle stdOut', std_err = UseHandle stdErr'}

  putStrLnM "RAN"
  return (ndName, p)


pauseNode :: Container -> IO ()
pauseNode Container{..} =
    void $ readProcess "docker"
        [ "pause"
        , nodeName
        ] ""

unPauseNode :: Container -> IO ()
unPauseNode Container{..} =
    void $ readProcess "docker"
        [ "unpause"
        , nodeName
        ] ""

mkNodeName :: Word -> String
mkNodeName n = "rqlite-node-" ++ show n

disconnectNode :: String -> IO ()
disconnectNode ndName =
    void $ readProcess "docker"
        [ "network"
        , "disconnect"
        , "rqlite-network"
        , ndName
        ] ""

connectNode :: Container -> IO ()
connectNode Container {..} =
    void $ readProcess "docker"
        [ "network"
        , "connect"
        , "--ip"
        , "172.18.0." ++ show (10 + cn)
        , "rqlite-network"
        , nodeName
        ] ""

createRQNetworks :: IO ()
createRQNetworks = do
    -- this way we don't "polute" test output with messages (i.e. network
    -- may already be present).
    stdErr  <- openFile "/dev/null" AppendMode
    void $ ignoreIOError $ readCreateProcess (proc "docker"
        [ "network"
        , "create"
        , "--subnet"
        , "172.19.0.0/16"
        , "rqlite-http"]) {std_err = UseHandle stdErr}
        ""
    void $ ignoreIOError $ readCreateProcess (proc "docker"
        [ "network"
        , "create"
        , "--subnet"
        , "172.18.0.0/16"
        , "rqlite-network"]) {std_err = UseHandle stdErr}
        ""

-- retryUntilElections :: IO a -> IO a
-- retryUntilElections action = go 20
--     where
--     go n = do
--         res <- try action
--         let retry e = if n > 0 then do
--                 putStrLnM "LeadershipLost. Retrying"
--                 threadDelay 500000
--                 go (n-1)
--             else throwIO e
--         case res of
--             Right a -> return a
--             Left e@(LeadershipLost _) -> retry e
--             Left e@NotLeader -> retry e
--             Left e -> throwIO e


------------------------

sameElements :: Eq a => [a] -> [a] -> Bool
sameElements x y = null (x \\ y) && null (y \\ x)

type NodeRef =  Reference Container

data Model r = Model {
        dbModel :: DBModel
      , nodes   :: [(NodeRef r, Int)]
} deriving (Generic, Show)

data DBModel = DBModel {
      persons   :: [Person]
    , nodeState :: Map Int NodeState
    , cutLines  :: [(Int, Int)]
    , cWhere    :: Int
    , cRef      :: Int
    } deriving (Generic, Show)

type Join = Maybe Int

data Timeout =
      Ms Int
    | Sec Int

instance Show Timeout where
    show (Ms n) = show n ++ "ms"
    show (Sec n) = show n ++ "s"

data Cmd node =
      Spawn Int Timeout Timeout Join
    | ReSpawn Int Int Timeout Timeout Join
    | Disconnect node
    | Connect node
    | Stop node
    | Insert node Person
    | Get node (Maybe Level)
    | Pause node
    | UnPause node
    | Delay Int
    deriving (Generic, Show, Functor, Foldable, Traversable)

newtype Resp node = Resp (Either SomeError (Success node))
    deriving (Show, Eq, Functor, Foldable, Traversable, Generic)

newtype SomeError = SomeError String
    deriving (Show, Eq)

data Success node =
      Unit
    | Spawned node
    | Got [Person]
    deriving (Show, Functor, Foldable, Traversable, Generic)

deriving instance Generic1          (At Cmd)
deriving instance Rank2.Functor     (At Cmd)
deriving instance Rank2.Foldable    (At Cmd)
deriving instance Rank2.Traversable (At Cmd)

deriving instance ToExpr DBModel
deriving instance ToExpr (Model Concrete)
deriving instance ToExpr Person

deriving instance Generic1          (At Resp)
deriving instance Rank2.Functor     (At Resp)
deriving instance Rank2.Foldable    (At Resp)
deriving instance Rank2.Traversable (At Resp)

instance Eq node => Eq (Success node) where
    Unit == Unit          = True
    (Got ps) == (Got ps') = sameElements ps ps'
    Spawned n == Spawned n' = n == n'
    _ == _                = False

instance CommandNames (At Cmd) where
    cmdName (At Spawn {})      = "Spawn"
    cmdName (At ReSpawn {})    = "ReSpawn"
    cmdName (At Connect {})    = "Connect"
    cmdName (At Disconnect {}) = "Disconnect"
    cmdName (At Stop {})       = "Stop"
    cmdName (At Insert {})     = "Insert"
    cmdName (At Get {})        = "Get"
    cmdName (At Pause {})      = "Pause"
    cmdName (At UnPause {})    = "UnPause"
    cmdName (At Delay {})      = "Delay"

unitResp :: Resp node
unitResp = Resp (Right Unit)

data Event (r :: Type -> Type) = Event
  { eventBefore   :: Model  r
  , eventCmd      :: At Cmd r
  , eventAfter    :: Model  r
  , eventMockResp :: Resp Int
  }

lockstep :: forall  (r :: Type -> Type).
            (Eq1 r, Show1 r)
         => Model   r
         -> At Cmd  r
         -> At Resp r
         -> Event   r
lockstep model@Model {..} cmd (At resp) = Event
    { eventBefore   = model
    , eventCmd      = cmd
    , eventAfter    = model'
    , eventMockResp = mockResp
    }
  where
    (mockResp, dbModel') = step model cmd
    newNodes = zip (toList resp) (toList mockResp)
    model' = Model {
          dbModel = dbModel'
        , nodes   = nodes `union'` newNodes
        }

union' :: forall k v. (Eq k, Eq v, Show k, Show v)
              => [(k, v)] -- Mapping known to have duplicate keys
              -> [(k, v)] -- With potential duplicates
              -> [(k, v)]
union' acc []             = acc
union' acc ((k, v) : kvs) =
    case lookup k acc of
      Just v' | v /= v' -> error $ renderError v'
      _otherwise        -> union' ((k, v) : acc) kvs
  where
    renderError :: v -> String
    renderError v' = unwords [
          "Key"
        , show k
        , "with two different values"
        , show v
        , "and"
        , show v'
        ]

(!) :: Eq1 r => [(NodeRef r, v)] -> NodeRef r -> v
env ! r = case lookup r env of
            Just a  -> a
            Nothing -> error "(!): key not found"

step :: Eq1 r => Model r -> At Cmd r -> (Resp Int, DBModel)
step (Model m@DBModel{..} nodes) (At cmd) = case cmd of
    Insert _ p      -> (unitResp, m {persons = p : persons})
    Get _ _         -> (Resp $ Right $ Got $ persons, m)
    Spawn wh _ _ _  -> ( Resp $ Right $ Spawned cRef, m {
                          nodeState = M.insert cRef (Running wh) nodeState
                        , cWhere = wh + 1 -- while shrinking, node locations may not be consecutive.
                        , cRef = cRef + 1
                        })
    ReSpawn pRef wh _ _ _ ->
                        ( Resp $ Right $ Spawned cRef, m {
                          nodeState = M.union (M.fromList [(cRef, Running wh), (pRef, Done)]) nodeState
                        , cRef = cRef + 1
                        })
    Connect ref       -> (unitResp, m {
                          nodeState = M.update connectST (nodes ! ref) nodeState
                        })
    Disconnect ref    -> (unitResp, m {
                          nodeState = M.update disconnectST (nodes ! ref) nodeState
                        })
    Stop ref          -> (unitResp, m {
                          nodeState = M.update stopST (nodes ! ref) nodeState
                        })
    Pause ref         -> (unitResp, m {
                          nodeState = M.update pauseST (nodes ! ref) nodeState
                        })
    UnPause ref         -> (unitResp, m {
                          nodeState = M.update unPauseST (nodes ! ref) nodeState
                        })
    Delay _           -> (unitResp, m)

data NodeState = Running Int
               | Disconnected Int
               | Stopped Int
               | Paused Int
               | Done
               deriving (Show, Generic, ToExpr)

connectST :: NodeState -> Maybe NodeState
connectST (Disconnected wh) = Just $ Running wh
connectST st = error $ "is not dicsonnected but " ++ show st

disconnectST :: NodeState -> Maybe NodeState
disconnectST (Running wh) = Just $ Disconnected wh
disconnectST st = error $ "is not running but " ++ show st

stopST :: NodeState -> Maybe NodeState
stopST (Running wh) = Just $ Stopped wh
stopST st = error $ "is not running but " ++ show st

pauseST :: NodeState -> Maybe NodeState
pauseST (Running wh) = Just $ Paused wh
pauseST st = error $ "is not running but " ++ show st

unPauseST :: NodeState -> Maybe NodeState
unPauseST (Paused wh) = Just $ Running wh
unPauseST st = error $ "is not paused but " ++ show st

runsMp :: Int -> Map Int NodeState -> Bool
runsMp n mp = case M.lookup n mp of
    Just (Running _) -> True
    _                -> False

pausedMP :: Int -> Map Int NodeState -> Bool
pausedMP n mp = case M.lookup n mp of
    Just (Paused _) -> True
    _               -> False

disconnectedMP :: Int -> Map Int NodeState -> Bool
disconnectedMP n mp = case M.lookup n mp of
    Just (Disconnected _) -> True
    _                     -> False

stoppedMp :: Int -> Map Int NodeState -> Bool
stoppedMp n mp = case M.lookup n mp of
    Just (Stopped _) -> True
    _                -> False

getRunning :: Map Int NodeState -> [(Int, Int)]
getRunning = mapMaybe f . M.toList
    where
        f (a, Running wh) = Just (a, wh)
        f _               = Nothing

getNotRunning :: Map Int NodeState -> [Int]
getNotRunning = mapMaybe f . M.toList
    where
        f (a, Stopped _)      = Just a
        f (a, Done)           = Just a
        f (a, Disconnected _) = Just a
        f (a, Paused _)       = Just a
        f _                   = Nothing

isStopped :: NodeState -> Bool
isStopped (Stopped _) = True
isStopped _           = False

isDisconnected :: NodeState -> Bool
isDisconnected (Disconnected _) = True
isDisconnected _              = False

initModel :: Model r
initModel = Model (DBModel [] M.empty [] 0 0) []

transition :: forall r. (Eq1 r, Show1 r) => Model r -> At Cmd r -> At Resp r -> Model r
transition model cmd =  eventAfter . lockstep model cmd

precondition :: Model Symbolic -> At Cmd Symbolic -> Logic
precondition (Model DBModel{..} nodes) (At cmd) = case cmd of
    Spawn n _ _ j
               -> Boolean $ length (getRunning nodeState) <= 2
                         && (not (null (getRunning nodeState)) || n == 0)
                         && joinsRunning j nodeState
                         && n < 3
    ReSpawn prevRef _ _ _ j
               -> Boolean $ elem prevRef (snd <$> nodes)
                         && stoppedMp prevRef nodeState
                         && length (getRunning nodeState) <= 2
                         && joinsRunning j nodeState
    Stop n     -> Boolean $ elem n (fst <$> nodes)
                         && runsMp (nodes ! n) nodeState
                         && nodes ! n /= 0
                         && null (getNotRunning nodeState)
                         && length (getRunning nodeState) == 3
    Disconnect n
               -> Boolean $ elem n (fst <$> nodes)
                         && runsMp (nodes ! n) nodeState
                         && null (getNotRunning nodeState)
                         && nodes ! n /= 0
                         && length (getRunning nodeState) == 3
    Connect n  -> Boolean $ elem n (fst <$> nodes)
                         && disconnectedMP (nodes ! n) nodeState
    Insert n _ -> Boolean $ elem n (fst <$> nodes)
                         && runsMp (nodes ! n) nodeState
    Get n _    -> Boolean $ elem n (fst <$> nodes)
                         && runsMp (nodes ! n) nodeState
    Pause n    -> Boolean $ elem n (fst <$> nodes)
                         && runsMp (nodes ! n) nodeState
    UnPause n  -> Boolean $ elem n (fst <$> nodes)
                         && pausedMP (nodes ! n) nodeState
    Delay _    -> Top

postcondition :: Model Concrete -> At Cmd Concrete -> At Resp Concrete -> Logic
postcondition m@Model{..} cmd resp =
    toMock (eventAfter ev) resp .== eventMockResp ev
    where
        ev = lockstep m cmd resp

toMock :: Eq1 r => Model r -> At Resp r ->  Resp Int
toMock Model{..} (At r) = fmap
    (\n -> fromMaybe (error "could not find person ref") $ Prelude.lookup n nodes) r

shrinker :: Model Symbolic -> At Cmd Symbolic -> [At Cmd Symbolic]
shrinker _ _ = []

semantics :: MVar Int -> At Cmd Concrete -> IO (At Resp Concrete)
semantics counter (At cmd) = At . Resp <$> case cmd of
    Insert node p -> do
        _ <- insertQuery (httpHost $ cn $ concrete node) p
        return $ Right Unit
    Get node lvl -> do
        res <- selectQuery lvl $ httpHost $ cn $ concrete node
        return $ case res of
            GetResult p -> Right $ Got p
            GetError e  -> Left $ SomeError $ show e
    Spawn n t elt join -> do
            putStrLnM $ "Starting at " ++ show n ++ " joining " ++ show join
            c <- modifyMVar counter $ \m -> return (m + 1, m)
            bracketOnError (mkNodeTime c n t elt join)
                            stopNode
                            $ \rqNode -> do
                threadDelay 500000
                _ <- retryUntilAlive $ httpHost n
                _ <- createQuery $ httpHost n
                return $ Right $ Spawned $ reference rqNode
    ReSpawn n _ t elt join -> do
            putStrLnM $ "Restarting at " ++ show n ++ " joining " ++ show join
            c <- modifyMVar counter $ \m -> return (m + 1, m)
            bracketOnError (mkNodeTime c n t elt join)
                            stopNode
                            $ \rqNode -> do
                threadDelay 500000
                _ <- retryUntilAlive $ httpHost n
                return $ Right $ Spawned $ reference rqNode
    Stop node -> do
        putStrLnM $ "Stopping at " ++ show (cport $ concrete node)
        stopNode $ concrete node
        return $ Right Unit
    Disconnect node -> do
        disconnectNode $ nodeName $ concrete node
        return $ Right Unit
    Connect node -> do
        connectNode $ concrete node
        _ <- retryUntilAlive $ httpHost $ cn $ concrete node
        return $ Right Unit
    Pause node -> do
        pauseNode $ concrete node
        return $ Right Unit
    UnPause node -> do
        unPauseNode $ concrete node
        return $ Right Unit
    Delay n -> do
        threadDelay n
        return $ Right Unit

httpHost :: Int -> String
httpHost n = "172.19.0." ++ show (10 + n) ++ ":" ++ show (leaderPort + 2 * n)

mock :: Model Symbolic -> At Cmd Symbolic -> GenSym (At Resp Symbolic)
mock (Model DBModel{..} _) (At cmd) = At <$> case cmd of
    Spawn {}      -> Resp . Right . Spawned <$> genSym
    ReSpawn {}    -> Resp . Right . Spawned <$> genSym
    Stop {}       -> return unitResp
    Disconnect {} -> return unitResp
    Connect {}    -> return unitResp
    Insert {}     -> return unitResp
    Get {}        -> return $ Resp $ Right $ Got persons
    Pause {}      -> return unitResp
    UnPause {}    -> return unitResp
    Delay {}      -> return unitResp

sm :: MVar Int -> Maybe Level -> StateMachine Model (At Cmd) IO (At Resp)
sm counter lvl = StateMachine initModel transition precondition postcondition
    Nothing (generatorImpl lvl) shrinker (semantics counter) mock garbageCollect

prop_sequential_rqlite :: Maybe Level -> Property
prop_sequential_rqlite lvl =
    forAllCommands (sm undefined lvl) (Just 7) $ \cmds -> checkCommandNames cmds $ monadicIO $ do
        liftIO $ do
            createRQNetworks
            removePathForcibly testPath
            createDirectory testPath
            threadDelay 10000
        c <- liftIO $ newMVar 0
        (hist, _, res) <- runCommands (sm c lvl) cmds
        prettyCommands (sm undefined lvl) hist $ res === Ok

prop_parallel_rqlite :: Maybe Level -> Property
prop_parallel_rqlite lvl =
    forAllParallelCommands (sm undefined lvl) (Just 7) $ \cmds -> checkCommandNamesParallel cmds $ monadicIO $ do
        liftIO $ do
            createRQNetworks
            removePathForcibly testPath
            createDirectory testPath
            threadDelay 10000
        c <- liftIO $ newMVar 0
        prettyParallelCommandsWithOpts cmds (Just $ GraphOptions "rqlite.png" Png)
                =<< runParallelCommandsNTimes 2 (sm c lvl) cmds

prop_nparallel_rqlite :: Int -> Maybe Level -> Property
prop_nparallel_rqlite np lvl =
    forAllNParallelCommands (sm undefined lvl) np $ \cmds ->
      monadicIO $ do
        liftIO $ do
            removePathForcibly testPath
            createDirectory testPath
            threadDelay 10000
        c <- liftIO $ newMVar 0
        prettyNParallelCommandsWithOpts cmds (Just $ GraphOptions "rqlite.png" Png)
                =<< runNParallelCommandsNTimes 1 (sm c lvl) cmds


runCmds :: ParallelCommandsF [] (At Cmd) (At Resp) -> Property
runCmds cmds = withMaxSuccess 1 $ noShrinking $ monadicIO $ do
    liftIO $ do
            removePathForcibly testPath
            createDirectory testPath
    c <- liftIO $ newMVar 0
    ls <- runNParallelCommandsNTimes 1 (sm c $ Just Weak) cmds
    prettyNParallelCommandsWithOpts cmds (Just $ GraphOptions "rqlite.png" Png) ls
    liftIO $ print $ fst $ head ls
    liftIO $ print $ interleavings $ unHistory $ fst $ head ls

garbageCollect :: Model Concrete -> IO ()
garbageCollect (Model _ nodes) =
    forM_ nodes $ \(Reference (Concrete node), p) -> do
        putStrLnM $ "stopping " ++ show p
        stopNode node

generatorImpl :: Maybe Level -> Model Symbolic -> Maybe (Gen (At Cmd Symbolic))
generatorImpl _ (Model _ [])    = Just $ return $ At initCmd
generatorImpl lvl (Model DBModel{..} nodes) = Just $ At <$> do
    node <- fst <$> elements nodes
    let
        reconnect :: (Int, Gen (Cmd (NodeRef Symbolic)))
        reconnect = case find (isDisconnected . snd) (M.toList nodeState) of
            (Just (_, Disconnected _)) ->
                (100, return $ Connect node)
            _                       -> (0, undefined)
    frequency
        [ (5, Insert node <$> arbitrary)
        , (5, return $ Get node lvl)
        , (if cWhere <= 3 then 20 else 0, return $ mkSpawn Nothing cWhere $ joinNode False nodeState)
        , (if cWhere == 3 then 20 else 0, return $ Stop node)
        , (if cWhere == 3 then 20 else 0, return $ Disconnect node)
        , respawn
        , reconnect]
        where

        respawn :: (Int, Gen (Cmd (NodeRef Symbolic)))
        respawn = case find (isStopped . snd) (M.toList nodeState) of
            (Just (ref, Stopped n)) ->
                (100, return $ mkSpawn (Just ref) n $ joinNode True nodeState)
            _                       -> (0, undefined)

joinNode :: Bool -> Map Int NodeState -> Maybe Int
joinNode avoid0 ndState =
    case snd <$> getRunning ndState of
        [] -> Nothing
        rs -> Just $ case (elem 0 rs, delete 0 rs, avoid0) of
            (False, _, _)     -> head rs
            (True, _, False)  -> 0
            (True, rs', True) -> head rs'

joinsRunning :: Maybe Int -> Map Int NodeState -> Bool
joinsRunning Nothing _ = True
joinsRunning (Just n) mp = elem n $ snd <$> getRunning mp

initCmd :: Cmd node
initCmd = Spawn 0 (Sec 1) (Sec 1) Nothing

mkSpawn :: Maybe Int -> Int -> Maybe Int -> Cmd node
mkSpawn respawm n =
    (case respawm of
        Nothing -> Spawn
        Just ref -> ReSpawn ref) n (Sec 1) (Sec 1)

testPath :: String
testPath = "rqlite-test"

names :: [String]
names = ["John", "Stevan", "Kostas", "Curry", "Robert"]

leaderPort :: Int
leaderPort = 4001

instance Arbitrary Person where
    arbitrary = do
        n <- elements names
        a <- choose (0, 100)
        return $ Person n a

putStrLnM :: String -> IO ()
putStrLnM str = when isDebugging $ putStrLn str

isDebugging :: Bool
isDebugging = False
