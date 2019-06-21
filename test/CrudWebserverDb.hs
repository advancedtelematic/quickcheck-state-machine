{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE QuasiQuotes                #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

-- NOTE: Make sure NOT to use DeriveAnyClass, or persistent-template
-- will do the wrong thing.

------------------------------------------------------------------------
-- |
-- Module      :  CrudWebserverDb
-- Copyright   :  (C) 2016, James M.C. Haver II, Sönke Hahn;
--                (C) 2017-2018, Stevan Andjelkovic
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan.andjelkovic@here.com>
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

module CrudWebserverDb
  ( prop_crudWebserverDb
  , prop_crudWebserverDbParallel
  , Bug(..)
  , setup
  , cleanup
  , connectionString
  , demoNoBug
  , demoLogicBug
  , demoNoRace
  , demoRace
  , UserId -- Only to silence unused warning.
  )
  where

import           Control.Concurrent
                   (newEmptyMVar, putMVar, takeMVar, threadDelay)
import           Control.Exception
                   (IOException, bracket, catch, onException)
import           Control.Monad.Logger
                   (NoLoggingT, runNoLoggingT)
import           Control.Monad.Reader
                   (ReaderT, ask, runReaderT)
import           Control.Monad.Trans.Resource
                   (ResourceT)
import qualified Data.ByteString.Char8         as BS
import           Data.Char
                   (isPrint)
import           Data.Functor.Classes
                   (Eq1)
import           Data.Kind
                   (Type)
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
import qualified Data.Text                     as T
import           Data.TreeDiff
                   (Expr(App))
import           Database.Persist.Postgresql
                   (ConnectionPool, ConnectionString, Key, SqlBackend,
                   delete, get, getJust, insert, liftSqlPersistMPool,
                   replace, runMigration, runSqlPool, update,
                   withPostgresqlPool, (+=.))
import           Database.Persist.TH
                   (mkMigrate, mkPersist, persistLowerCase, share,
                   sqlSettings)
import           GHC.Generics
                   (Generic, Generic1)
import           Network.HTTP.Client
                   (Manager, defaultManagerSettings, newManager)
import           Network.Socket
                   (AddrInfoFlag(AI_NUMERICHOST, AI_NUMERICSERV),
                   Socket, SocketType(Stream), addrAddress, addrFamily,
                   addrFlags, addrProtocol, addrSocketType, close,
                   connect, defaultHints, getAddrInfo, socket)
import qualified Network.Wai.Handler.Warp      as Warp
import           Prelude
import           Servant
                   ((:<|>)(..), (:>), Application, Capture, Delete,
                   Get, JSON, Post, Put, ReqBody, Server, serve)
import           Servant.Client
                   (BaseUrl(..), ClientEnv(..), ClientM, Scheme(Http),
                   client, mkClientEnv, runClientM)
import           Servant.Server
                   (Handler)
import           System.Process
                   (callProcess, readProcess)
import           Test.QuickCheck
                   (Arbitrary, Gen, Property, arbitrary, elements,
                   expectFailure, frequency, ioProperty, listOf,
                   quickCheck, shrink, suchThat, verboseCheck, (===))
import           Test.QuickCheck.Instances
                   ()
import           Test.QuickCheck.Monadic
                   (monadic)
import           UnliftIO
                   (Async, MonadIO, async, cancel, liftIO, waitEither)

import           Test.StateMachine
import qualified Test.StateMachine.Types.Rank2 as Rank2

------------------------------------------------------------------------
-- * User datatype




share [mkPersist sqlSettings, mkMigrate "migrateAll"] [persistLowerCase|
User json
  name Text
  age  Int
  deriving Eq Read Show Generic
|]

-- data User = User
--   { name :: Text
--   , age  :: Int
--   }

instance ToExpr User where

------------------------------------------------------------------------
-- * API




type Api =
       "user" :> "add" :> ReqBody '[JSON] User     :> Post    '[JSON] (Key User)
  :<|> "user" :> "get" :> Capture "key" (Key User) :> Get     '[JSON] (Maybe User)
  :<|> "user" :> "inc" :> Capture "key" (Key User) :> Put     '[JSON] ()
  :<|> "user" :> "del" :> Capture "key" (Key User) :> Delete  '[JSON] ()

  :<|> "health"                                    :> Get     '[JSON] ()







------------------------------------------------------------------------
-- * Server implementation

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
    muser <- get key  -- Make sure that the record exists.
    case muser of
      Just _  -> delete key
      Nothing -> error "userDelete: user doesn't exist."

  health :: Handler ()
  health = return ()

  sql :: ReaderT SqlBackend (NoLoggingT (ResourceT IO)) a -> Handler a
  sql q = liftSqlPersistMPool q pool

------------------------------------------------------------------------
-- * Client bindings


postUserC    :: User     -> ClientM (Key User)
getUserC     :: Key User -> ClientM (Maybe User)
incAgeUserC  :: Key User -> ClientM ()
deleteUserC  :: Key User -> ClientM ()
healthC      ::             ClientM ()

postUserC :<|> getUserC :<|> incAgeUserC :<|> deleteUserC :<|> healthC
  = client api







------------------------------------------------------------------------
-- * Implementation done, modelling starts



data Action (r :: Type -> Type)
  = PostUser   User
  | GetUser    (Reference (Key User) r)
  | IncAgeUser (Reference (Key User) r)
  | DeleteUser (Reference (Key User) r)
  deriving (Show, Generic1)

instance Rank2.Functor     Action where
instance Rank2.Foldable    Action where
instance Rank2.Traversable Action where
instance CommandNames      Action where

data Response (r :: Type -> Type)
  = PostedUser (Reference (Key User) r)
  | GotUser    (Maybe User)
  | IncedAgeUser
  | DeletedUser
  deriving (Show, Generic1)

instance Rank2.Foldable Response where

------------------------------------------------------------------------
-- * State machine model


newtype Model r = Model [(Reference (Key User) r, User)]
  deriving (Generic, Show)

instance ToExpr (Model Concrete) where

instance ToExpr (Key User) where
  toExpr key = App (show key) []

initModel :: Model v
initModel = Model []

transitions :: Eq1 r => Model r -> Action r -> Response r -> Model r
transitions (Model m) (PostUser   user) (PostedUser key) =
  Model (m ++ [(key, user)])
transitions m         (GetUser    _)    (GotUser _)      =
  m
transitions (Model m) (IncAgeUser key)  IncedAgeUser     =
  case lookup key m of
    Nothing              -> Model m
    Just (User user age) ->
      Model (updateModel key (User user (age + 1)) m)
transitions (Model m) (DeleteUser key)  DeletedUser      =
  Model (filter ((/= key) . fst) m)
transitions _         _                 _                =
  error "transitions"


------------------------------------------------------------------------
-- * Pre-requisites and invariants

preconditions :: Model Symbolic -> Action Symbolic -> Logic
preconditions _         (PostUser _)     = Top
preconditions (Model m) (GetUser    key) = key `member` map fst m
preconditions (Model m) (IncAgeUser key) = key `member` map fst m
preconditions (Model m) (DeleteUser key) = key `member` map fst m



postconditions :: Model Concrete -> Action Concrete -> Response Concrete -> Logic
postconditions _         (PostUser _)   _              = Top
postconditions (Model m) (GetUser key)  (GotUser musr) = lookup key m .== musr
postconditions _         (IncAgeUser _) _              = Top
postconditions _         (DeleteUser _) _              = Top
postconditions _         _              _              = error "postconditions"



------------------------------------------------------------------------
-- * How to generate and shrink programs.

generator :: Model Symbolic -> Maybe (Gen (Action Symbolic))
generator (Model m) = Just $ frequency
  [ (1, PostUser   <$> arbitrary)
  , (3, GetUser    <$> elements (map fst m))
  , (4, IncAgeUser <$> elements (map fst m))
  , (2, DeleteUser <$> elements (map fst m))
  ]

shrinker :: Model Symbolic -> Action Symbolic -> [Action Symbolic]
shrinker _ (PostUser (User user age)) =
  [ PostUser (User user' age') | (user', age') <- shrink (user, age) ]
shrinker _ _                          = []

------------------------------------------------------------------------
-- * The semantics.


semantics :: Action Concrete -> ReaderT ClientEnv IO (Response Concrete)
semantics act = do
  env <- ask
  res <- liftIO $ flip runClientM env $ case act of
    PostUser   user -> PostedUser . reference <$> postUserC   user
    GetUser    key  -> GotUser                <$> getUserC    (concrete key)
    IncAgeUser key  -> IncedAgeUser           <$  incAgeUserC (concrete key)
    DeleteUser key  -> DeletedUser            <$  deleteUserC (concrete key)
  case res of
    Left  err  -> error (show err)
    Right resp -> return resp

mock :: Model Symbolic -> Action Symbolic -> GenSym (Response Symbolic)
mock (Model m) act = case act of
  PostUser   _    -> PostedUser <$> genSym
  GetUser    key  -> GotUser <$> pure (lookup key m)
  IncAgeUser _key -> pure IncedAgeUser
  DeleteUser _key -> pure DeletedUser

------------------------------------------------------------------------

sm :: StateMachine Model Action (ReaderT ClientEnv IO) Response
sm = StateMachine initModel transitions preconditions postconditions
       Nothing generator shrinker semantics mock

------------------------------------------------------------------------
-- * Sequential property

prop_crudWebserverDb :: Int -> Property
prop_crudWebserverDb port =
  forAllCommands sm Nothing $ \cmds -> monadic (ioProperty . runner port) $ do
    (hist, _, res) <- runCommands sm cmds
    prettyCommands sm hist (res === Ok)

withCrudWebserverDb :: Bug -> Int -> IO () -> IO ()
withCrudWebserverDb bug port run =
  bracket
    (setup bug connectionString port)
    cleanup
    (const run)

demoNoBug', demoLogicBug', demoNoRace' :: Int -> IO ()
demoNoBug'    port = withCrudWebserverDb None  port
  (verboseCheck (prop_crudWebserverDb port))
demoLogicBug' port = withCrudWebserverDb Logic port
  (verboseCheck (expectFailure (prop_crudWebserverDb port)))
demoNoRace'   port = withCrudWebserverDb Race  port
  (quickCheck (prop_crudWebserverDb port))

demoNoBug, demoLogicBug, demoNoRace :: IO ()
demoNoBug    = demoNoBug'    crudWebserverDbPort
demoLogicBug = demoLogicBug' crudWebserverDbPort
demoNoRace   = demoNoRace'   crudWebserverDbPort

-----------------------------------------------------------------------
-- * Parallel property

prop_crudWebserverDbParallel :: Int -> Property
prop_crudWebserverDbParallel port =
  forAllParallelCommands sm $ \cmds -> monadic (ioProperty . runner port) $ do
    prettyParallelCommands cmds =<< runParallelCommandsNTimes 30 sm cmds

demoRace' :: Int -> IO ()
demoRace' port = withCrudWebserverDb Race port
  (quickCheck (expectFailure (prop_crudWebserverDbParallel port)))

demoRace :: IO ()
demoRace = demoRace' crudWebserverDbParallelPort

------------------------------------------------------------------------

app :: Bug -> ConnectionPool -> Application
app bug pool = serve (Proxy :: Proxy Api) (server bug pool)

mkApp :: Bug -> ConnectionString -> IO Application
mkApp bug conn = runNoLoggingT $
  withPostgresqlPool (cs conn) 10 $ \pool -> do
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

connectionString :: String -> ConnectionString
connectionString ip = "host=" <> BS.pack ip
  <> " dbname=postgres user=postgres password=mysecretpassword port=5432"

updateModel :: Eq a => a -> b -> [(a, b)] -> [(a, b)]
updateModel x y xys = (x, y) : filter ((/= x) . fst) xys

api :: Proxy Api
api = Proxy

crudWebserverDbPort :: Int
crudWebserverDbPort = 8083

crudWebserverDbParallelPort :: Int
crudWebserverDbParallelPort = 8084

instance Arbitrary User where
  arbitrary = User <$> (T.pack <$> listOf (arbitrary `suchThat` isPrint))
                   <*> arbitrary

runner :: Warp.Port -> ReaderT ClientEnv IO Property -> IO Property
runner port p = do
  mgr <- newManager defaultManagerSettings
  runReaderT p (mkClientEnv mgr (burl port))

burl :: Warp.Port -> BaseUrl
burl port = BaseUrl Http "localhost" port ""

setup
  :: MonadIO m
  => Bug -> (String -> ConnectionString) -> Warp.Port -> m (String, Async ())
setup bug conn port = liftIO $ do
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
    res <- liftIO $ runClientM healthC (mkClientEnv mgr (burl port))
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
    , "postgres:10.2"
    ] ""
  ip <- trim <$> readProcess "docker"
    [ "inspect"
    , pid
    , "--format"
    , "'{{range .NetworkSettings.Networks}}{{.IPAddress}}{{end}}'"
    ] ""
  healthyDb pid ip `onException` callProcess "docker" [ "rm", "-f", "-v", pid ]
  return (pid, ip)
  where
    trim :: String -> String
    trim = dropWhileEnd isGarbage . dropWhile isGarbage
      where
        isGarbage = flip elem ['\'', '\n']

    healthyDb :: String -> String -> IO ()
    healthyDb pid ip = do
      sock <- go 10
      close sock
      where
        go :: Int -> IO Socket
        go 0 = error "healthyDb: db isn't healthy"
        go n = do
          let hints = defaultHints
                { addrFlags      = [AI_NUMERICHOST , AI_NUMERICSERV]
                , addrSocketType = Stream
                }
          addr : _ <- getAddrInfo (Just hints) (Just ip) (Just "5432")
          sock <- socket (addrFamily addr) (addrSocketType addr) (addrProtocol addr)
          (connect sock (addrAddress addr) >>
            readProcess "docker"
              [ "exec"
              , "-u", "postgres"
              , pid
              , "psql", "-U", "postgres", "-d", "postgres", "-c", "SELECT 1 + 1"
              ] "" >> return sock)
            `catch` (\(_ :: IOException) -> do
                        threadDelay 1000000
                        go (n - 1))


cleanup :: (String, Async ()) -> IO ()
cleanup (pid, aServer) = do
  callProcess "docker" [ "rm", "-f", "-v", pid ]
  cancel aServer
