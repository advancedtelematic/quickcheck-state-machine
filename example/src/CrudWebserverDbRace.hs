{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE QuasiQuotes                #-}
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
                   (bracket)
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
import           Data.Char
                   (isPrint)
import           Data.Functor.Classes
                   (Show1, liftShowsPrec)
import           Data.Proxy
                   (Proxy(Proxy))
import           Data.String.Conversions
                   (cs)
import           Data.Text
                   (Text)
import qualified Data.Text                       as T
import           Database.Persist.Postgresql
                   (ConnectionPool, ConnectionString, Key, SqlBackend,
                   createPostgresqlPool, delete, get, getJust, insert,
                   replace, liftSqlPersistMPool, runMigration,
                   runSqlPool, update, (+=.))
import           Database.Persist.TH
                   (mkMigrate, mkPersist, persistLowerCase, share,
                   sqlSettings)
import           Network.HTTP.Client
                   (Manager, defaultManagerSettings, newManager)
import qualified Network.Wai.Handler.Warp        as Warp
import           Servant
                   ((:<|>)(..), (:>), Application, Capture, Get, JSON,
                   Post, ReqBody, Server, serve)
import           Servant.Client
                   (BaseUrl(..), ClientEnv(..), ClientM, Scheme(Http),
                   client, runClientM)
import           Servant.Server
                   (Handler)
import           Test.QuickCheck
                   (Arbitrary, Property, arbitrary, elements,
                   frequency, listOf, shrink, suchThat, (===))
import           Test.QuickCheck.Instances
                   ()

import           Test.StateMachine
import           Test.StateMachine.TH
                   (deriveTestClasses, deriveShows)

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
  :<|> "health"                                    :> Get  '[JSON] ()

api :: Proxy Api
api = Proxy

------------------------------------------------------------------------

-- * Server implementation.

data Bug = None | Logic | Race

server :: Bug -> ConnectionPool -> Server Api
server bug pool =
  userAdd :<|> userGet :<|> userBirthday :<|> health
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
healthC      ::             ClientM ()

postUserC :<|> getUserC :<|> incAgeUserC :<|> healthC = client api

------------------------------------------------------------------------

-- * Implementation done, modelling starts.

data Action (v :: * -> *) :: * -> * where
  PostUser   :: User                   -> Action v (Key User)
  GetUser    :: Reference v (Key User) -> Action v (Maybe User)
  IncAgeUser :: Reference v (Key User) -> Action v ()

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

transitions :: Transition Model Action
transitions (Model m) (PostUser   user) key = Model (m ++ [(Reference key, user)])
transitions m         (GetUser    _)    _   = m
transitions (Model m) (IncAgeUser key)  _   = case lookup key m of
  Nothing              -> Model m
  Just (User user age) -> Model (updateList key (User user (age + 1)) m)
    where
    updateList :: Eq a => a -> b -> [(a, b)] -> [(a, b)]
    updateList x y xys = (x, y) : filter ((/= x) . fst) xys

postconditions :: Postcondition Model Action
postconditions _         (PostUser _)   _    = True
postconditions (Model m) (GetUser key)  resp = lookup key m == resp
postconditions _         (IncAgeUser _) _    = True

------------------------------------------------------------------------

-- * How to generate and shrink programs.

generator :: Generator Model Action
generator (Model m)
  | null m    = Untyped . PostUser <$> arbitrary
  | otherwise = frequency
      [ (1, Untyped . PostUser   <$> arbitrary)
      , (8, Untyped . GetUser    <$> elements (map fst m))
      , (8, Untyped . IncAgeUser <$> elements (map fst m))
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
  case res of
    Left  err  -> error (show err)
    Right resp -> return resp

------------------------------------------------------------------------

sm :: Warp.Port -> StateMachine Model Action (ReaderT ClientEnv IO)
sm port = stateMachine
  generator shrinker preconditions transitions
  postconditions initModel semantics (runner port)

connectionString :: ConnectionString
connectionString = "host=localhost dbname=postgres user=postgres password=mysecretpassword port=5432"

crudWebserverDbPort :: Int
crudWebserverDbPort = 8081

------------------------------------------------------------------------

-- docker run --net=host --name postgres -e POSTGRES_PASSWORD=mysecretpassword -d postgres

prop_crudWebserverDbRace :: Property
prop_crudWebserverDbRace =
  monadicSequential sm' $ \prog -> do
    (hist, _, res) <- runProgram sm' prog
    prettyProgram sm' hist $
      checkActionNames prog (res === Ok)
  where
    sm' = sm crudWebserverDbPort

withCrudWebserverDbRace :: Bug -> IO () -> IO ()
withCrudWebserverDbRace bug =
  bracketServer (setup bug connectionString crudWebserverDbPort)

------------------------------------------------------------------------

prop_crudWebserverDbRaceParallel :: Property
prop_crudWebserverDbRaceParallel =
  monadicParallel sm' $ \prog ->
    prettyParallelProgram prog =<< runParallelProgram sm' prog
  where
    sm' = sm crudWebserverDbParallelPort

withCrudWebserverDbRaceParallel :: Bug -> IO () -> IO ()
withCrudWebserverDbRaceParallel bug =
  bracketServer (setup bug connectionString crudWebserverDbParallelPort)

------------------------------------------------------------------------






crudWebserverDbParallelPort :: Int
crudWebserverDbParallelPort = 8082

instance Arbitrary User where
  arbitrary = User <$> (T.pack <$> listOf (arbitrary `suchThat` isPrint))
                   <*> arbitrary

runner :: Warp.Port -> ReaderT ClientEnv IO Property -> IO Property
runner port p = do
  mgr <- newManager defaultManagerSettings
  runReaderT p (ClientEnv mgr (burl port))

bracketServer :: IO (Async ()) -> IO () -> IO ()
bracketServer start run =
  bracket start cancel (const run)

burl :: Warp.Port -> BaseUrl
burl port = BaseUrl Http "localhost" port ""

setup :: MonadBaseControl IO m => Bug -> ConnectionString -> Warp.Port -> m (Async ())
setup bug conn port = liftBaseWith $ \_ -> do
  signal   <- newEmptyMVar
  aServer  <- async (runServer bug conn port (putMVar signal ()))
  aConfirm <- async (takeMVar signal)
  ok <- waitEither aServer aConfirm
  case ok of
    Right () -> do
      mgr <- newManager defaultManagerSettings
      healthy mgr 10
      return aServer
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

deriveShows       ''Action
deriveTestClasses ''Action
