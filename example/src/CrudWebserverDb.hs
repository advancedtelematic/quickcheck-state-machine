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
-- Module      :  CrudWebserverDb
-- Copyright   :  (C) 2016, James M.C. Haver II, Sönke Hahn;
--                (C) 2017, Stevan Andjelkovic
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains the implementation and specification of a simple
-- CRUD webserver that uses a sqlite database to store data.
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

module CrudWebserverDb
  ( prop_crudWebserverDb
  , prop_crudWebserverDbParallel
  , withCrudWebserverDb
  , withCrudWebserverDbParallel
  , UserId
  )
  where

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
import           Database.Persist.Sqlite
                   (ConnectionPool, Key, SqlBackend, createSqlitePool,
                   delete, get, insert, liftSqlPersistMPool,
                   runMigration, runSqlPool, update, (+=.))
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
import           System.Directory
                   (getTemporaryDirectory)
import           System.FilePath
                   ((</>))
import           Test.QuickCheck
                   (Arbitrary, Property, arbitrary, elements,
                   frequency, listOf, shrink, suchThat, (===))
import           Test.QuickCheck.Instances
                   ()

import           Test.StateMachine
import           Test.StateMachine.TH
                   (deriveTestClasses)

------------------------------------------------------------------------

-- Our webserver deals with users that have a name and an age. The
-- following is the Persistent library's way of creating the datatype
-- and corresponding database table. The "json" keyword also makes it
-- possible to (un)marshall the datatype into JSON.

share [mkPersist sqlSettings, mkMigrate "migrateAll"] [persistLowerCase|
User json
  name Text
  age  Int
  deriving Eq Read Show
|]

-- For testing we will also need to generate arbitrary users.

instance Arbitrary User where
  arbitrary = User <$> (T.pack <$> listOf (arbitrary `suchThat` isPrint))
                   <*> arbitrary

-- Note that there's a constraint on the username that only allows
-- printable characters. We'll come back to why this is later.

------------------------------------------------------------------------

-- Servant let's us describe the API of the webserver as a datatype.

-- Our webserver will have an endpoint for creating a user, which takes
-- a JSON-encoded @User@ in the body of an POST request and returns a
-- unique id. The rest of the endpoints capture said id in the URL and
-- get the user associated with it, increment the age of the user, and
-- delete the user respectively. Finally we also have a health endpoint
-- which helps us determine if the webserver is up and running.

type Api =
       "user" :> "add" :> ReqBody '[JSON] User     :> Post '[JSON] (Key User)
  :<|> "user" :> "get" :> Capture "key" (Key User) :> Get  '[JSON] (Maybe User)
  :<|> "user" :> "inc" :> Capture "key" (Key User) :> Get  '[JSON] ()
  :<|> "user" :> "del" :> Capture "key" (Key User) :> Get  '[JSON] ()
  :<|> "health"                                    :> Get  '[JSON] ()

api :: Proxy Api
api = Proxy

------------------------------------------------------------------------

-- Next we describe how the endpoints are implemented.

server :: ConnectionPool -> Server Api
server pool =
  userAdd :<|> userGet :<|> userBirthday :<|> userDelete :<|> health
  where
  userAdd :: User -> Handler (Key User)
  userAdd newUser = sql (insert newUser)

  userGet :: Key User -> Handler (Maybe User)
  userGet key = sql (get key)

  userBirthday :: Key User -> Handler ()
  userBirthday key = sql (update key [UserAge +=. 1])

  userDelete :: Key User -> Handler ()
  userDelete key = sql (delete key)

  health :: Handler ()
  health = return ()

  sql :: ReaderT SqlBackend (NoLoggingT (ResourceT IO)) a -> Handler a
  sql q = liftSqlPersistMPool q pool

app :: ConnectionPool -> Application
app pool = serve api (server pool)

mkApp :: FilePath -> IO Application
mkApp sqliteFile = do
  pool <- runNoLoggingT (createSqlitePool (cs sqliteFile) 1)
  runSqlPool (runMigration migrateAll) pool
  return (app pool)

runServer :: FilePath -> Warp.Port -> IO () -> IO ()
runServer sqliteFile port ready = do
  app' <- mkApp sqliteFile
  Warp.runSettings settings app'
  where
    settings
      = Warp.setPort port
      . Warp.setBeforeMainLoop ready
      $ Warp.defaultSettings

------------------------------------------------------------------------

-- We get the client bindings for free from the API datatype.

postUserC    :: User     -> ClientM (Key User)
getUserC     :: Key User -> ClientM (Maybe User)
incAgeUserC  :: Key User -> ClientM ()
deleteUserC  :: Key User -> ClientM ()
healthC      ::             ClientM ()

postUserC :<|> getUserC :<|> incAgeUserC :<|> deleteUserC :<|> healthC
  = client api

------------------------------------------------------------------------

-- We are now done with the implementation of the webserver, and we can
-- start with the specification and testing using the
-- <https://github.com/advancedtelematic/quickcheck-state-machine
-- quickcheck-state-machine> library.

-- We start by specifying what actions are allowed.

data Action (v :: * -> *) :: * -> * where
  PostUser   :: User                   -> Action v (Key User)
  GetUser    :: Reference v (Key User) -> Action v (Maybe User)
  IncAgeUser :: Reference v (Key User) -> Action v ()
  DeleteUser :: Reference v (Key User) -> Action v ()

-- As you can see, the actions are similar to the client bindings,
-- except for the keys being wrapped in @Reference@ at the argument
-- positions. The reason for this is that when we generate arbitrary
-- actions we will not be able to generate arbitrary ids (these are
-- unique and come from the database, they are references to previously
-- created users.

deriving instance Show1 v => Show (Action v resp)

instance Show1 (Action Symbolic) where
  liftShowsPrec _ _ _ act _ = show act

------------------------------------------------------------------------

-- Next we define the model, or reference implementation, that we want
-- to test our implementation against. It should intuitively capture the
-- requirements and be as simple as possible. We will use a map between
-- user ids and @User@s implemented using a list of pairs.

newtype Model v = Model [(Reference v (Key User), User)]
  deriving Show

-- The initial model is just an empty list.

initModel :: Model v
initModel = Model []

-- Pre-conditions are used to determine in what context an action makes
-- sense. For example, it always makes sense to create a new user, but
-- we can only retrieve a user id that has been created (and thus a key
-- in the model).

preconditions :: Precondition Model Action
preconditions _         (PostUser _)     = True
preconditions (Model m) (GetUser    key) = key `elem` map fst m
preconditions (Model m) (IncAgeUser key) = key `elem` map fst m
preconditions (Model m) (DeleteUser key) = key `elem` map fst m

-- The transition function determines how an action advances the model.
-- For example, when we create a new user we add they user id and the
-- user data to the model.

transitions :: Transition Model Action
transitions (Model m) (PostUser   user) key = Model (m ++ [(Reference key, user)])
transitions m         (GetUser    _)    _   = m
transitions (Model m) (IncAgeUser key)  _   = case lookup key m of
  Nothing              -> Model m
  Just (User user age) -> Model (updateL key (User user (age + 1)) m)
  where
  updateL :: Eq a => a -> b -> [(a, b)] -> [(a, b)]
  updateL x y xys = (x, y) : filter ((/= x) . fst) xys
transitions (Model m) (DeleteUser key)  _   = Model (filter ((/= key) . fst) m)

-- The post-condition is what is actually checked after the execution of
-- an action against the webserver. For example, when we retrieve a user
-- then the @resp@onse we get back better be the same as if we lookup
-- the key in the model.

postconditions :: Postcondition Model Action
postconditions _         (PostUser _)   _    = True
postconditions (Model m) (GetUser key)  resp = lookup key m == resp
postconditions _         (IncAgeUser _) _    = True
postconditions _         (DeleteUser _) _    = True

------------------------------------------------------------------------

-- If the model is empty, then we generate an action that creates a
-- user. If it's non-empty, we pick one of the user ids and retrieve the
-- user, increement the users age, or delete the user. We generate
-- actions that retrieve users or increment the age with higher
-- probability than creating new users or deleting them.
--
-- Note that references are picked from the model.

generator :: Generator Model Action
generator (Model m)
  | null m    = Untyped . PostUser <$> arbitrary
  | otherwise = frequency
      [ (1, Untyped . PostUser   <$> arbitrary)
      , (8, Untyped . GetUser    <$> elements (map fst m))
      , (8, Untyped . IncAgeUser <$> elements (map fst m))
      , (1, Untyped . DeleteUser <$> elements (map fst m))
      ]

-- There isn't much to shrink, only the username and age on user
-- creating actions.

shrinker :: Shrinker Action
shrinker (PostUser (User user age)) =
  [ PostUser (User user' age') | (user', age') <- shrink (user, age) ]
shrinker _                          = []

------------------------------------------------------------------------

-- The semantics of actions is given in terms of the API client
-- bindings. A @ClientEnv@ containing the URL and port to the server is
-- passed in using a reader monad.

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

-- In order for the library to deal with @Reference@s we need to explain
-- how to traverse them.

deriveTestClasses ''Action

------------------------------------------------------------------------

-- Finally we got all pieces needed to write a sequential and a parallel
-- property that asserts that the semantics respect the model in a
-- single-threaded and two-threaded context respectively.

sm :: Warp.Port -> StateMachine Model Action (ReaderT ClientEnv IO)
sm port = stateMachine
  generator shrinker preconditions transitions
  postconditions initModel semantics (runner port)


crudWebserverDbPort :: Int
crudWebserverDbPort = 8081

withCrudWebserverDb :: IO () -> IO ()
withCrudWebserverDb =
  bracketServer (setup "sqlite.db" crudWebserverDbPort)

-- Note that this property assumes that there is a server setup and
-- running. It can be checked, for example, as follows:
-- @withCrudWebserverDb (quickCheck prop_crudWebserverDb)@.
prop_crudWebserverDb :: Property
prop_crudWebserverDb =
  monadicSequential sm' $ \prog -> do
    (hist, _, res) <- runProgram sm' prog
    prettyProgram sm' hist $
      checkActionNames prog (res === Ok)
  where
    sm' = sm crudWebserverDbPort


crudWebserverDbParallelPort :: Int
crudWebserverDbParallelPort = 8082

withCrudWebserverDbParallel :: IO () -> IO ()
withCrudWebserverDbParallel =
  bracketServer (setup "sqlite-parallel.db" crudWebserverDbParallelPort)

bracketServer :: IO (Async ()) -> IO () -> IO ()
bracketServer start run =
  bracket start cancel (const run)

prop_crudWebserverDbParallel :: Property
prop_crudWebserverDbParallel =
  monadicParallel sm' $ \prog ->
    prettyParallelProgram prog =<< runParallelProgram sm' prog
  where
    sm' = sm crudWebserverDbParallelPort

-- Where the URL of the server, how to run the reader monad that the
-- semantics live in, and how to setup the webserver is defined as
-- follows.

burl :: Warp.Port -> BaseUrl
burl port = BaseUrl Http "localhost" port ""

runner :: Warp.Port -> ReaderT ClientEnv IO Property -> IO Property
runner port p = do
  mgr <- newManager defaultManagerSettings
  runReaderT p (ClientEnv mgr (burl port))

setup :: MonadBaseControl IO m => FilePath -> Warp.Port -> m (Async ())
setup sqliteFile port = liftBaseWith $ \_ -> do
  signal <- newEmptyMVar
  tmp <- getTemporaryDirectory
  aServer <- async (runServer (tmp </> sqliteFile) port (putMVar signal ()))
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

------------------------------------------------------------------------

-- Despite being a simple webserver running the two properties revealed
-- two problems.
--
-- The sequential property found that arbitrary text can't be used as
-- username, in fact not even ASCII works. For example the username
-- "\NUL" causes sqlite to drop the name, as seen in the following
-- output:
--
--     *** Failed! Falsifiable (after 14 tests and 8 shrinks):
--     [ PostUser (User {userName = "\NUL", userAge = 0}) Var 9
--     , GetUser ((Var 9)) Var 10 ]
--     Just (User {userName = "\NUL", userAge = 0}) /=
--     Just (User {userName = "",     userAge = 0})
--
-- While the parallel property found that with the connection pool size
-- set to 5, as in the original implementation, concurrent writes cause
-- "SQLite3 returned ErrorBusy while attempting to perform step..."
-- errors. After some searching I found the following
-- <http://comments.gmane.org/gmane.comp.lang.haskell.yesod/1268 thread>
-- that suggested to set the pool size to 1 instead.
