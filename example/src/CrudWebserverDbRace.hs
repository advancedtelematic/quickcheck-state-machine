{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE QuasiQuotes                #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}

------------------------------------------------------------------------
-- |
-- Module      :  CrudWebserverDbRace
-- Copyright   :  (C) 2016, James M.C. Haver II, Sönke Hahn;
--                (C) 2017, Stevan Andjelkovic
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains the implementation and specification of a simple
-- CRUD webserver that uses a postgresql database to store data.
--
-- The implementation is based on Servant's
-- <https://github.com/haskell-servant/example-servant-persistent example-servant-persistent>
-- repository.
--
-- Readers who are not familiar with the
-- <http://haskell-servant.readthedocs.io/en/stable/ Servant> library
-- and/or the <http://www.yesodweb.com/book/persistent Persistent>
-- library might want consult the respective library's documentation in
-- case any part of the implementation of the webserver is unclear.
--
------------------------------------------------------------------------

module CrudWebserverDbRace where

import           Control.Concurrent
                   (newEmptyMVar, putMVar, takeMVar, threadDelay)
import           Control.Concurrent.Async.Lifted
                   (Async, async, cancel, waitEither)
import           Control.Exception
                   (SomeException, bracket)
import           Control.Exception
                   (catch)
import           Control.Monad.IO.Class
                   (liftIO)
import           Control.Monad.Logger
                   (NoLoggingT, runNoLoggingT)
import           Control.Monad.Reader
                   (ReaderT, ask, runReaderT)
import           Control.Monad.Trans.Control
                   (MonadBaseControl, liftBaseWith)
import           Control.Monad.Trans.Resource
                   (ResourceT)
import qualified Data.ByteString.Char8                    as BS
import           Data.Char
                   (isPrint)
import           Data.Dynamic
                   (cast)
import           Data.Functor.Classes
                   (Eq1)
import           Data.List
                   (dropWhileEnd)
import           Data.Monoid
                   ((<>))
import           Data.Proxy
                   (Proxy(Proxy))
import           Data.String.Conversions
                   (cs)
import           Data.Text
                   (Text)
import qualified Data.Text                                as T
import           Database.Persist.Postgresql
                   (ConnectionPool, ConnectionString, Key, SqlBackend,
                   createPostgresqlPool, delete, get, getJust, insert,
                   liftSqlPersistMPool, replace, runMigration,
                   runSqlPool, update, (+=.))
import           Database.Persist.TH
                   (mkMigrate, mkPersist, persistLowerCase, share,
                   sqlSettings)
import           Network
                   (PortID(PortNumber), connectTo)
import           Network.HTTP.Client
                   (Manager, defaultManagerSettings, newManager)
import qualified Network.Wai.Handler.Warp                 as Warp
import           Servant
                   ((:<|>)(..), (:>), Application, Capture, Get, JSON,
                   Post, ReqBody, Server, serve)
import           Servant.Client
                   (BaseUrl(..), ClientEnv(..), ClientM, Scheme(Http),
                   client, runClientM)
import           Servant.Server
                   (Handler)
import           System.IO
                   (Handle, hClose)
import           System.Process
                   (callProcess, readProcess)
import           Test.QuickCheck
                   (Arbitrary, Property, arbitrary, elements,
                   frequency, listOf, shrink, suchThat, (===))
import           Test.QuickCheck.Counterexamples
                   (PropertyOf)
import           Test.QuickCheck.Instances
                   ()

import           Test.StateMachine
import           Test.StateMachine.Internal.AlphaEquality
                   (alphaEqParallel)
import           Test.StateMachine.Internal.Types
                   (Internal(..), ParallelProgram'(..), Program(..))
import           Test.StateMachine.Internal.Utils
                   (shrinkPropertyHelperC)
import           Test.StateMachine.TH
                   (deriveShows, deriveTestClasses)


------------------------------------------------------------------------

-- * User datatype.

share [mkPersist sqlSettings, mkMigrate "migrateAll"] [persistLowerCase|
User json
  name Text
  age  Int
  deriving Eq Read Show
|]

------------------------------------------------------------------------

-- * The API.

type Api =
       "user" :> "add" :> ReqBody '[JSON] User     :> Post '[JSON] (Key User)
  :<|> "user" :> "get" :> Capture "key" (Key User) :> Get  '[JSON] (Maybe User)
  :<|> "user" :> "inc" :> Capture "key" (Key User) :> Get  '[JSON] ()
  :<|> "user" :> "del" :> Capture "key" (Key User) :> Get  '[JSON] ()
  :<|> "health"                                    :> Get  '[JSON] ()

api :: Proxy Api
api = Proxy

------------------------------------------------------------------------

-- * Server implementation.

data Bug = None | Logic | Race

server :: Bug -> ConnectionPool -> Server Api
server bug pool =
  userAdd :<|> userGet :<|> userBirthday :<|> userDelete :<|> health
  where
  userAdd :: User -> Handler (Key User)
  userAdd newUser = sql (insert newUser)

  userGet :: Key User -> Handler (Maybe User)
  userGet key = sql (get key)

  userBirthday :: Key User -> Handler ()
  userBirthday key = sql $ case bug of
    None  -> update key [UserAge +=. 1]
    Logic -> update key [UserAge +=. 2]
    Race  -> do
      User name age <- getJust key
      replace key (User name (age + 1))

  userDelete :: Key User -> Handler ()
  userDelete key = sql $ do
    Just _ <- get key  -- Make sure that the record exists.
    delete key

  health :: Handler ()
  health = return ()

  sql :: ReaderT SqlBackend (NoLoggingT (ResourceT IO)) a -> Handler a
  sql q = liftSqlPersistMPool q pool

------------------------------------------------------------------------

-- * How to run a server.

app :: Bug -> ConnectionPool -> Application
app bug pool = serve api (server bug pool)

mkApp :: Bug -> ConnectionString -> IO Application
mkApp bug conn = do
  pool <- runNoLoggingT (createPostgresqlPool (cs conn) 10)
  runSqlPool (runMigration migrateAll) pool
  return (app bug pool)

runServer :: Bug -> ConnectionString -> Warp.Port -> IO () -> IO ()
runServer bug conn port ready = do
  app' <- mkApp bug conn
  Warp.runSettings settings app'
  where
    settings
      = Warp.setPort port
      . Warp.setBeforeMainLoop ready
      $ Warp.defaultSettings

------------------------------------------------------------------------

-- * HTTP client for the API.

postUserC    :: User     -> ClientM (Key User)
getUserC     :: Key User -> ClientM (Maybe User)
incAgeUserC  :: Key User -> ClientM ()
deleteUserC  :: Key User -> ClientM ()
healthC      ::             ClientM ()

postUserC :<|> getUserC :<|> incAgeUserC :<|> deleteUserC :<|> healthC
  = client api

------------------------------------------------------------------------

-- * Implementation done, modelling starts.

data Action (v :: * -> *) :: * -> * where
  PostUser   :: User                   -> Action v (Key User)
  GetUser    :: Reference v (Key User) -> Action v (Maybe User)
  IncAgeUser :: Reference v (Key User) -> Action v ()
  DeleteUser :: Reference v (Key User) -> Action v ()

deriving instance Eq1 v => Eq (Action v resp)

------------------------------------------------------------------------

-- * The model.

newtype Model v = Model [(Reference v (Key User), User)]
  deriving Show

initModel :: Model v
initModel = Model []

------------------------------------------------------------------------

-- * The specification.

preconditions :: Precondition Model Action
preconditions _         (PostUser _)     = True
preconditions (Model m) (GetUser    key) = key `elem` map fst m
preconditions (Model m) (IncAgeUser key) = key `elem` map fst m
preconditions (Model m) (DeleteUser key) = key `elem` map fst m

transitions :: Transition Model Action
transitions (Model m) (PostUser   user) key = Model (m ++ [(Reference key, user)])
transitions m         (GetUser    _)    _   = m
transitions (Model m) (IncAgeUser key)  _   = case lookup key m of
  Nothing              -> Model m
  Just (User user age) -> Model (updateList key (User user (age + 1)) m)
    where
    updateList :: Eq a => a -> b -> [(a, b)] -> [(a, b)]
    updateList x y xys = (x, y) : filter ((/= x) . fst) xys
transitions (Model m) (DeleteUser key)  _   = Model (filter ((/= key) . fst) m)

postconditions :: Postcondition Model Action
postconditions _         (PostUser _)   _    = True
postconditions (Model m) (GetUser key)  resp = lookup key m == resp
postconditions _         (IncAgeUser _) _    = True
postconditions _         (DeleteUser _) _    = True

------------------------------------------------------------------------

-- * How to generate and shrink programs.

generator :: Generator Model Action
generator (Model m)
  | null m    = Untyped . PostUser <$> arbitrary
  | otherwise = frequency
      [ (1, Untyped . PostUser   <$> arbitrary)
      , (8, Untyped . GetUser    <$> elements (map fst m))
      , (8, Untyped . IncAgeUser <$> elements (map fst m))
      , (8, Untyped . DeleteUser <$> elements (map fst m))
      ]

shrinker :: Shrinker Action
shrinker (PostUser (User user age)) =
  [ PostUser (User user' age') | (user', age') <- shrink (user, age) ]
shrinker _                          = []

------------------------------------------------------------------------

-- * The semantics.

semantics :: Action Concrete resp -> ReaderT ClientEnv IO resp
semantics act = do
  env <- ask
  res <- liftIO $ flip runClientM env $ case act of
    PostUser   user -> postUserC   user
    GetUser    key  -> getUserC    (concrete key)
    IncAgeUser key  -> incAgeUserC (concrete key)
    DeleteUser key  -> deleteUserC (concrete key)
  case res of
    Left  err  -> error (show err)
    Right resp -> return resp

------------------------------------------------------------------------

sm :: Warp.Port -> StateMachine Model Action (ReaderT ClientEnv IO)
sm port = stateMachine
  generator shrinker preconditions transitions
  postconditions initModel semantics (runner port)

connectionString :: String -> ConnectionString
connectionString ip = "host=" <> BS.pack ip
  <> " dbname=postgres user=postgres password=mysecretpassword port=5432"

crudWebserverDbPort :: Int
crudWebserverDbPort = 8083

------------------------------------------------------------------------

prop_crudWebserverDbRace :: Property
prop_crudWebserverDbRace =
  monadicSequential sm' $ \prog -> do
    (hist, _, res) <- runProgram sm' prog
    prettyProgram sm' hist $
      checkActionNames prog (res === Ok)
  where
    sm' = sm crudWebserverDbPort

withCrudWebserverDbRace :: Bug -> IO () -> IO ()
withCrudWebserverDbRace bug run =
  bracket
    (setup bug connectionString crudWebserverDbPort)
    cleanup
    (const run)

------------------------------------------------------------------------

prop_crudWebserverDbRaceParallel :: PropertyOf (ParallelProgram' Action)
prop_crudWebserverDbRaceParallel =
  monadicParallelC' sm' $ \prog ->
    prettyParallelProgram' prog =<< runParallelProgram'' 30 sm' prog
  where
  sm' = sm crudWebserverDbParallelPort

prop_dbShrinkRace :: Property
prop_dbShrinkRace = shrinkPropertyHelperC prop_crudWebserverDbRaceParallel $ \pprog ->
  any (alphaEqParallel pprog)
    [ ParallelProgram' prefix
        [ Program
            [ iact (IncAgeUser (Reference sym0)) 1
            , iact (IncAgeUser (Reference sym0)) 2
            , iact (GetUser    (Reference sym0)) 3
            ]
        ]
    , ParallelProgram' prefix
        [ Program
            [ iact (IncAgeUser (Reference sym0)) 1
            , iact (IncAgeUser (Reference sym0)) 2
            ]
        , Program
            [ iact (GetUser    (Reference sym0)) 3 ]
        ]
    ]
  where
  prefix     = Program [ iact (PostUser (User "" 0)) 0 ]
  iact act n = Internal act (Symbolic (Var n))
  sym0       = Symbolic (Var 0)

instance Eq (Untyped Action) where
  Untyped act1 == Untyped act2 = cast act1 == Just act2

withCrudWebserverDbRaceParallel :: Bug -> IO () -> IO ()
withCrudWebserverDbRaceParallel bug run =
  bracket
    (setup bug connectionString crudWebserverDbParallelPort)
    cleanup
    (const run)

------------------------------------------------------------------------






crudWebserverDbParallelPort :: Int
crudWebserverDbParallelPort = 8084

instance Arbitrary User where
  arbitrary = User <$> (T.pack <$> listOf (arbitrary `suchThat` isPrint))
                   <*> arbitrary

runner :: Warp.Port -> ReaderT ClientEnv IO Property -> IO Property
runner port p = do
  mgr <- newManager defaultManagerSettings
  runReaderT p (ClientEnv mgr (burl port))

burl :: Warp.Port -> BaseUrl
burl port = BaseUrl Http "localhost" port ""

setup
  :: MonadBaseControl IO m
  => Bug -> (String -> ConnectionString) -> Warp.Port -> m (String, Async ())
setup bug conn port = liftBaseWith $ \_ -> do
  (pid, dbIp) <- setupDb
  signal   <- newEmptyMVar
  aServer  <- async (runServer bug (conn dbIp) port (putMVar signal ()))
  aConfirm <- async (takeMVar signal)
  ok <- waitEither aServer aConfirm
  case ok of
    Right () -> do
      mgr <- newManager defaultManagerSettings
      healthy mgr 10
      return (pid, aServer)
    Left () -> error "Server should not return"
  where
  healthy :: Manager -> Int -> IO ()
  healthy _   0     = error "healthy: server isn't healthy"
  healthy mgr tries = do
    res <- liftIO $ runClientM healthC (ClientEnv mgr (burl port))
    case res of
      Left  _  -> do
        threadDelay 1000000
        healthy mgr (tries - 1)
      Right () -> return ()

setupDb :: IO (String, String)
setupDb = do
  pid <- trim <$> readProcess "docker"
    [ "run"
    , "-d"
    , "-e", "POSTGRES_PASSWORD=mysecretpassword"
    , "postgres:10.1-alpine"
    ] ""
  ip <- trim <$> readProcess "docker"
    [ "inspect"
    , pid
    , "--format"
    , "'{{range .NetworkSettings.Networks}}{{.IPAddress}}{{end}}'"
    ] ""
  healthyDb ip
  return (pid, ip)
  where
  trim :: String -> String
  trim = dropWhileEnd isGarbage . dropWhile isGarbage
    where
    isGarbage = flip elem ['\'', '\n']

  healthyDb :: String -> IO ()
  healthyDb ip = do
    handle <- go 10
    hClose handle
    where
    go :: Int -> IO Handle
    go 0 = error "healtyDb: db isn't healthy"
    go n = do
      connectTo ip (PortNumber 5432)
        `catch` (\(_ :: SomeException) -> do
                    threadDelay 1000000
                    go (n - 1))


cleanup :: (String, Async ()) -> IO ()
cleanup (pid, aServer) = do
  callProcess "docker" [ "rm", "-f", pid ]
  cancel aServer

deriveShows       ''Action
deriveTestClasses ''Action
