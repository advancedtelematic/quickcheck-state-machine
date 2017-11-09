{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeOperators         #-}

------------------------------------------------------------------------
-- |
-- Module      :  CrudWebserverFile
-- Copyright   :  (C) 2015, Gabriel Gonzales;
--                (C) 2017, Stevan Andjelkovic
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains the implementation and specification of a simple
-- CRUD webserver that uses files to store data.
--
-- The implementation is based on Gabriel Gonazalez's
-- <https://github.com/Gabriel439/servant-crud servant-crud> repository.
--
-- Readers unfamiliar with the Servant library might want to have a look
-- at its <http://haskell-servant.readthedocs.io/en/stable/ documentation>
-- in case some parts of the implementation of the CRUD
-- webserver are unclear.
--
------------------------------------------------------------------------

module CrudWebserverFile
 --  ( prop_crudWebserverFile
 --  , prop_crudWebserverFileParallel
 --  )
  where

import           Control.Concurrent
                   (newEmptyMVar, putMVar, takeMVar)
import           Control.Concurrent.Async
                   (Async, async, cancel, waitEither)
import           Control.Exception
                   (bracket)
import           Control.Monad.IO.Class
                   (liftIO)
import           Control.Monad.Reader
                   (ReaderT, ask, runReaderT)
import           Control.Monad.Trans.Control
                   (MonadBaseControl, liftBaseWith)
import           Data.Functor.Classes
                   (Show1, liftShowsPrec)
import           Data.Map
                   (Map)
import qualified Data.Map                    as Map
import           Data.Text
                   (Text)
import qualified Data.Text.IO                as Text
import           Network.HTTP.Client
                   (defaultManagerSettings, newManager)
import qualified Network.Wai.Handler.Warp    as Warp
import           Servant
                   ((:<|>)(..), (:>), Capture, Delete, Get, JSON,
                   Proxy(..), Put, ReqBody)
import           Servant.Client
                   (BaseUrl(..), Client, ClientEnv(..), Scheme(..),
                   client, runClientM)
import           Servant.Server
                   (Server, serve)
import qualified System.Directory            as Directory
import           System.FilePath
                   ((</>))
import           Test.QuickCheck
                   (Gen, Property, arbitrary, elements, frequency,
                   shrink, (===))
import           Test.QuickCheck.Instances
                   ()

import           Test.StateMachine
import           Test.StateMachine.TH
                   (deriveTestClasses)

-- XXX:
import           Test.QuickCheck (sample')
import           Control.Monad.State
import           Test.StateMachine.Internal.Sequential
import           Test.StateMachine.Internal.Parallel

------------------------------------------------------------------------

-- | A `PUT` request against `/:file` with a `JSON`-encoded request body
type PutFile =
    Capture "file" FilePath :> ReqBody '[JSON] Text :> Put '[JSON] ()

-- | A `GET` request against `/:file` with a `JSON`-encoded response body
type GetFile =
    Capture "file" FilePath :> Get '[JSON] Text

-- | A `DELETE` request against `/:file`
type DeleteFile =
    Capture "file" FilePath :> Delete '[JSON] ()

{-| The type of our REST API

    The server uses this to ensure that each API endpoint's handler has the
    correct type

    The client uses this to auto-generate API bindings
-}
type API =   PutFile
        :<|> GetFile
        :<|> DeleteFile

------------------------------------------------------------------------

-- | Handler for the `PutFile` endpoint
putFile :: FilePath -> Server PutFile
putFile dir file contents = liftIO (Text.writeFile (dir </> file) contents)

-- | Handler for the `GetFile` endpoint
getFile :: FilePath -> Server GetFile
getFile dir file = liftIO (Text.readFile (dir </> file))

-- | Handler for the `DeleteFile` endpoint
deleteFile :: FilePath -> Server DeleteFile
deleteFile dir file = liftIO (Directory.removeFile (dir </> file))

-- | Handler for the entire REST `API`
server :: FilePath -> Server API
server dir
  =    putFile dir
  :<|> getFile dir
  :<|> deleteFile dir

-- | Serve the `API` on port 8080
runServer :: IO () -> IO ()
runServer ready = do
  dir <- Directory.getTemporaryDirectory
  Warp.runSettings settings (serve (Proxy :: Proxy API) (server dir))
  where
    settings
      = Warp.setPort 8080
      . Warp.setBeforeMainLoop ready
      $ Warp.defaultSettings

------------------------------------------------------------------------

-- | Autogenerated API binding for the endpoints
putFileC    :: Client PutFile
getFileC    :: Client GetFile
deleteFileC :: Client DeleteFile

putFileC :<|> getFileC :<|> deleteFileC = client (Proxy :: Proxy API)

------------------------------------------------------------------------

data Action (v :: * -> *) :: * -> * where
  PutFile    :: FilePath -> Text -> Action v ()
  GetFile    :: FilePath ->         Action v Text
  DeleteFile :: FilePath ->         Action v ()

deriving instance Show1 v => Show (Action v resp)

instance Show1 (Action Symbolic) where
  liftShowsPrec _ _ _ act _ = show act

------------------------------------------------------------------------

newtype Model (v :: * -> *) = Model (Map FilePath Text)
  deriving (Eq, Show)

initModel :: Model v
initModel = Model Map.empty

preconditions :: Precondition Model Action
preconditions (Model m) act = case act of
  PutFile    _ _  -> True
  GetFile    file -> Map.member file m
  DeleteFile file -> Map.member file m

transitions :: Transition' Model Action String
transitions m         _   (Fail _)    = m
transitions (Model m) act (Success _) = Model $ case act of
  PutFile    file content -> Map.insert file content m
  GetFile    _            -> m
  DeleteFile file         -> Map.delete file m

postconditions :: Postcondition' Model Action String
postconditions _         _   (Fail _)       = False
postconditions (Model m) act (Success resp) =
  let Model m' = transitions (Model m) act (Success (Concrete resp))
  in case act of
    PutFile    file content -> Map.lookup file m' == Just content
    GetFile    file         -> Map.lookup file m  == Just resp
    DeleteFile file         -> Map.lookup file m' == Nothing

------------------------------------------------------------------------

genFilePath :: Gen FilePath
genFilePath = elements ["apa.txt", "bepa.txt"]

generator :: Generator Model Action
generator (Model m)
  | Map.null m = Untyped <$> (PutFile <$> genFilePath <*> arbitrary)
  | otherwise  = frequency
    [ (3, Untyped <$> (PutFile <$> genFilePath <*> arbitrary))
    , (5, Untyped . GetFile    <$> elements (Map.keys m))
    , (1, Untyped . DeleteFile <$> elements (Map.keys m))
    ]

shrinker :: Action v resp -> [Action v resp]
shrinker (PutFile file contents) =
  [ PutFile file contents' | contents' <- shrink contents ]
shrinker _                       = []

------------------------------------------------------------------------

semantics :: Semantics' Action (ReaderT ClientEnv IO) String
semantics act = do
  env <- ask
  res <- liftIO $ flip runClientM env $ case act of
    PutFile    file content -> putFileC    file content
    GetFile    file         -> getFileC    file
    DeleteFile file         -> deleteFileC file
  case res of
    Left  err  -> return (Fail (show err))
    Right resp -> return (Success resp)

------------------------------------------------------------------------

deriveTestClasses ''Action

instance Show (Untyped Action) where
  show (Untyped act) = show act

------------------------------------------------------------------------

burl :: BaseUrl
burl = BaseUrl Http "localhost" 8080 ""

setup :: MonadBaseControl IO m => m (Async ())
setup = liftBaseWith $ \_ -> do
  signal <- newEmptyMVar
  aServer <- async (runServer (putMVar signal ()))
  aConfirm <- async (takeMVar signal)
  ok <- waitEither aServer aConfirm
  case ok of
    Right () -> return aServer
    Left ()  -> error "Server should not return"

-- Note that this will setup and tear down a server per generated
-- program.
runner :: ReaderT ClientEnv IO Property -> IO Property
runner p =
  bracket setup cancel $ \_ -> do
    mgr <- newManager defaultManagerSettings
    runReaderT p (ClientEnv mgr burl)

------------------------------------------------------------------------

sm :: StateMachine' Model Action (ReaderT ClientEnv IO) String
sm = StateMachine
  generator shrinker preconditions transitions
  postconditions initModel semantics runner

prop_crudWebserverFile :: Property
prop_crudWebserverFile =
  monadicSequential sm $ \prog -> do
    (hist, _, res) <- runProgram sm prog
    prettyProgram sm hist $
      checkActionNames prog (res === Ok)

prop_crudWebserverFileParallel :: Property
prop_crudWebserverFileParallel =
  monadicParallel sm $ \prog ->
    prettyParallelProgram prog =<< runParallelProgram sm prog

------------------------------------------------------------------------

test :: IO ()
test = do
  progs <- sample' $ flip evalStateT initModel $ generateProgram generator preconditions transitions 0
  let prog = progs !! 10
  mapM_ print (splitProgram initModel preconditions transitions prog)
