{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
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
    ) where

import           Control.Concurrent
                   (threadDelay)
import           Control.Concurrent.MVar
import           Control.Exception (bracketOnError)
import           Control.Monad.IO.Class  (liftIO)
import           Data.Aeson hiding (Result)
import           Data.Dynamic
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
import           Rqlite
import           Rqlite.Status
import           System.Directory
import           System.IO
import           System.Process
import           Test.QuickCheck hiding (Result)
import           Test.QuickCheck.Monadic
import           Test.StateMachine
import           Test.StateMachine.DotDrawing
import           Test.StateMachine.Types (ParallelCommandsF(..), 
                     Commands(..), History(..), takeResponses)
import           Test.StateMachine.Types.Environment
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
selectQuery lvl host = getQuery lvl host True "SELECT * FROM Person"

createQuery :: String -> IO PostResult
createQuery host = postQuery True host $ createQ

------------------------

-- RQlite utilities

data RqNode = RqNode {
        counter :: Int
      , pHandle :: ProcessHandle
      , port    :: Int
} deriving (Generic)

instance Eq RqNode where
    n1 == n2 = counter n1 == counter n2

instance Show RqNode where
    show RqNode{..} = "Node@" ++ show port

instance ToExpr RqNode where
    toExpr RqNode{..} = App ("Node@" ++ show port) []

nodeHost :: RqNode -> String
nodeHost RqNode{..} = "localhost:" ++ show port

runRqlited :: Int -> String -> Int -> Maybe String -> IO RqNode
runRqlited counter path port mjoin = do
    let args =  case mjoin of
          Nothing ->
            [ "-http-addr"
            , "localhost:" ++ show port
            , "-raft-addr"
            , "localhost:" ++ (show $ port + 1)
            , path
            ]
          Just join ->
            [ "-http-addr"
            , "localhost:" ++ show port
            , "-raft-addr"
            , "localhost:" ++ (show $ port + 1)
            , "-join"
            , join
            , path
            ]
    stdOut <- openFile "/dev/null" WriteMode
    stdErr <- openFile "/dev/null" WriteMode
    stdIn  <- openFile "/dev/null" ReadMode
    (_, _, _, hd) <-
        createProcess
            (proc "/home/kostas/rqlite-v4.5.0-linux-amd64/rqlited" args)
            {std_in = UseHandle stdIn, std_out = UseHandle stdOut, std_err = UseHandle stdErr
            , new_session = True, create_group = True}
    return $ RqNode counter hd port

stopNode :: RqNode -> IO ()
stopNode RqNode{..} = putStrLn ("stopping " ++ show port) >> terminateProcess pHandle

------------------------

sameElements :: Eq a => [a] -> [a] -> Bool
sameElements x y = null (x \\ y) && null (y \\ x)

type NodeRef =  Reference RqNode

data Model r = Model {
        dbModel :: DBModel
      , nodes   :: [(NodeRef r, Int)]
} deriving (Generic, Show)

data DBModel = DBModel {
      persons   :: [Person]
    , nodeState :: Map Int NodeState
    , cWhere    :: Int
    , cRef      :: Int
    } deriving (Generic, Show)

type Port = Int
type Path = String
type Join = Maybe Int

data Cmd node =
      Spawn Int Port Path Join
    | ReSpawn Int Int Port Path Join
    | Stop node
    | Insert node Person
    | Get node (Maybe Level)
    deriving (Generic, Show, Functor, Foldable, Traversable)

newtype Resp node = Resp {getResp :: Either SomeError (Success node)}
    deriving (Show, Eq, Functor, Foldable, Traversable, Generic)

data SomeError = SomeError String
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

deriving instance ToExpr (DBModel)
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
    cmdName (At (Spawn {}))   = "Spawn"
    cmdName (At (ReSpawn {})) = "ReSpawn"
    cmdName (At (Stop {}))    = "Stop"
    cmdName (At (Insert {}))  = "Insert"
    cmdName (At (Get {}))     = "Get"

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
    renderError v' = intercalate " " [
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
    Stop ref          -> (unitResp, m {
                          nodeState = M.update (\(Running wh) -> Just $ Stopped wh) (nodes ! ref) nodeState
                        })

data NodeState = Running Int
               | Stopped Int
               | Done
               deriving (Show, Generic, ToExpr)

runsMp :: Int -> Map Int NodeState -> Bool
runsMp n mp = case M.lookup n mp of
    Just (Running _) -> True
    _                -> False

stoppedMp :: Int -> Map Int NodeState -> Bool
stoppedMp n mp = case M.lookup n mp of
    Just (Stopped _) -> True
    _                -> False

getRunning :: Map Int NodeState -> [(Int, Int)]
getRunning = mapMaybe f . M.toList
    where
        f (a, Running wh) = Just (a, wh)
        f _               = Nothing

isStopped :: NodeState -> Bool
isStopped (Stopped _) = True
isStopped _           = False

initModel :: Model r
initModel = Model (DBModel [] M.empty 0 0) []

transition :: forall r. (Eq1 r, Show1 r) => Model r -> At Cmd r -> At Resp r -> Model r
transition model cmd =  eventAfter . lockstep model cmd

precondition :: Model Symbolic -> At Cmd Symbolic -> Logic
precondition (Model DBModel{..} nodes) (At cmd) = case cmd of
    Spawn n _ _ j
               -> Boolean $ (length (getRunning nodeState) <= 2)
                         && (not (null (getRunning nodeState)) || n == 0)
                         && (joinsRunning j nodeState)
    ReSpawn prevRef _ _ _ j
               -> Boolean $ (elem prevRef (snd <$> nodes))
                         && (stoppedMp prevRef nodeState)
                         && (length (getRunning nodeState) <= 2)
                         && (joinsRunning j nodeState)
    Stop n     -> Boolean $ (elem n (fst <$> nodes))
                         && (runsMp (nodes ! n) nodeState)
                         && (nodes ! n /= 0)
                         && (length (getRunning nodeState) == 3)
    Insert n _ -> Boolean $ (elem n (fst <$> nodes))
                         && (runsMp (nodes ! n) nodeState)
    Get n _    -> Boolean $ (elem n (fst <$> nodes))
                         && (runsMp (nodes ! n) nodeState)

postcondition :: Model Concrete -> At Cmd Concrete -> At Resp Concrete -> Logic
postcondition m@(Model{..}) cmd resp =
    (toMock (eventAfter ev) resp) .== (eventMockResp ev)
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
        _ <- insertQuery (nodeHost $ concrete node) p
        return $ Right $ Unit
    Get node lvl -> do
        res <- selectQuery lvl $ nodeHost $ concrete node
        return $ case res of
            GetResult p -> Right $ Got p
            GetError e  -> Left $ SomeError $ show e
    Spawn _ port path join -> do
            putStrLn $ "Starting at " ++ show port ++ " joining " ++ show join
            c <- modifyMVar counter $ \n -> return (n + 1, n)
            bracketOnError (runRqlited c (testPath ++ "/" ++ path) port $ (local' <$> join))
                            stopNode
                            $ \rqNode -> do
                _ <- retryUntilAlive $ local port
                _ <- createQuery $ local port
                return $ Right $ Spawned $ reference rqNode
    ReSpawn _ _ port path join -> do
            putStrLn $ "Restarting at " ++ show port ++ " joining " ++ show join
            c <- modifyMVar counter $ \n -> return (n + 1, n)
            threadDelay 2000000
            bracketOnError (runRqlited c (testPath ++ "/" ++ path) port $ (local' <$> join))
                            stopNode
                            $ \rqNode -> do
                _ <- retryUntilAlive $ local port
                _ <- createQuery $ local port
                return $ Right $ Spawned $ reference rqNode
    Stop node -> do
        putStrLn $ "Stoppging at " ++ (show $ port $ concrete node)
        threadDelay 1000000
        stopNode $ concrete node
        return $ Right $ Unit

local :: Port -> String
local port = "localhost:" ++ show port

local' :: Int -> String
local' wh =
    "http://" ++ local (4001 + 2 * wh)

mock :: Model Symbolic -> At Cmd Symbolic -> GenSym (At Resp Symbolic)
mock (Model DBModel{..} _) (At cmd) = At <$> case cmd of
    Spawn {}   -> Resp . Right . Spawned <$> genSym
    ReSpawn {} -> Resp . Right . Spawned <$> genSym
    Stop {}    -> return $ unitResp
    Insert {}  -> return $ unitResp
    Get {}     -> return $ Resp $ Right $ Got persons

sm :: MVar Int -> Maybe Level -> StateMachine Model (At Cmd) IO (At Resp)
sm counter lvl = StateMachine initModel transition precondition postcondition
    Nothing (generatorImpl lvl) shrinker (semantics counter) mock clean

prop_sequential_rqlite :: Maybe Level -> Property
prop_sequential_rqlite lvl =
    forAllCommands (sm undefined lvl) Nothing $ \cmds -> checkCommandNames cmds $ monadicIO $ do
        liftIO $ do
            removePathForcibly testPath
            createDirectory testPath
            threadDelay 10000
        c <- liftIO $ newMVar 0
        (hist, model, res) <- runCommands (sm c lvl) cmds
        liftIO $ garbageCollect model
        prettyCommands (sm undefined lvl) hist $ res === Ok

prop_parallel_rqlite :: Maybe Level -> Property
prop_parallel_rqlite lvl =
    forAllParallelCommands (sm undefined lvl) $ \cmds -> checkCommandNamesParallel cmds $ monadicIO $ do
        liftIO $ do
            removePathForcibly testPath
            createDirectory testPath
            threadDelay 10000
        c <- liftIO $ newMVar 0
        prettyParallelCommandsWithOpts cmds (Just $ GraphOptions "rqlite.png" Png)
                =<< runParallelCommands (sm c lvl) cmds

prop_nparallel_rqlite :: Int -> Maybe Level -> Property
prop_nparallel_rqlite np lvl =
    noShrinking $ forAllNParallelCommands (sm undefined lvl) Nothing np $ \cmds ->
      monadicIO $ do
        liftIO $ do
            removePathForcibly testPath
            createDirectory testPath
            threadDelay 10000
            putStrLn "--------------"
        c <- liftIO $ newMVar 0
        prettyNParallelCommandsWithOpts cmds (Just $ GraphOptions "rqlite.png" Png)
                =<< runNParallelCommandsNTimes 3 (sm c lvl) cmds

toCommands :: forall cmd resp t. Foldable t
           => ParallelCommandsF t cmd resp -> Commands cmd resp
toCommands cmds = (prefix cmds) <> (mconcat $ concatMap toList (suffixes cmds))

length' :: Commands cmd resp -> Int
length' = length . unCommands

clean :: History (At Cmd) (At Resp) -> IO ()
clean hist = do -- mkModel
    -- forM_ (takeResponses hist) $ \case
    --     (At (Resp (Right (Spawned node)))) -> stopNode (concrete node) >> threadDelay 100000
    --     _ -> return ()
    -- print hist
    garbageCollect $ mkModel transition initModel hist
    removePathForcibly testPath
    createDirectory testPath

garbageCollect :: Model Concrete -> IO ()
garbageCollect (Model _ nodes) = do
    forM_ nodes $ \(Reference (Concrete node), p) -> do
        putStrLn $ "stoping " ++ show p
        stopNode node
        threadDelay 1000000

garbageCollectEnv :: Environment -> IO ()
garbageCollectEnv mp = do
    let ds = M.elems $ unEnvironment mp
    forM_ ds $ \ d -> case fromDynamic d of
        Just (n :: RqNode) -> stopNode n
        _                  -> return ()

generatorImpl :: Maybe Level -> Model Symbolic -> Maybe (Gen (At Cmd Symbolic))
generatorImpl _ (Model _ [])    = Just $ return $ At initCmd
generatorImpl lvl (Model DBModel{..} nodes) = Just $ At <$> do
    node <- fst <$> elements nodes
    frequency
        [ (5, Insert node <$> arbitrary)
        , (5, return $ Get node lvl)
        , (if cWhere <= 3 then 20 else 0, return $ mkSpawn Nothing cWhere $ joinNode False nodeState)
        , (if cWhere == 3 then 20 else 0, return $ Stop node)
        , respawn]
        where

        respawn :: (Int, Gen (Cmd (NodeRef Symbolic)))
        respawn = case find (isStopped . snd) (M.toList nodeState) of
            (Just (ref, Stopped n)) ->
                (20, return $ mkSpawn (Just ref) n $ joinNode True nodeState)
            _                       -> (0, undefined)

joinNode ::Bool -> Map Int NodeState -> Maybe Int
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
initCmd = Spawn 0 leaderPort "node.0" Nothing

mkSpawn :: Maybe Int -> Int -> Maybe Int -> Cmd node
mkSpawn respawm n joinmkPort =
    (case respawm of
        Nothing -> Spawn
        Just ref -> ReSpawn ref)
                  n
                  (leaderPort + 2 * n)
                  ("node." ++ show n)
                  joinmkPort

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

run :: IO ()
run = do
    print "starting"
--    (_,_,_,p) <- createProcess (proc "cat" []) -- {create_group = True}
--    terminateProcess p
    removePathForcibly "/home/kostas/node.5"
--    removePathForcibly "/home/kostas/node.6"
    p <- runRqlited 1 "/home/kostas/node.5" 4007 Nothing
    threadDelay 1000000
    _ <- createQuery $ local 4007

--    p' <- runRqlited "/home/kostas/node.6" 4009 Nothing
    -- runCommand "ping localhost"
    stopNode p
--    stopNode p'
--    stopNode p
    print "started"
    getProcessExitCode (pHandle p) >>= print
--    forever $
--        return ()
