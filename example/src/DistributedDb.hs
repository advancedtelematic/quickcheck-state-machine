{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  DistributedDb
-- Copyright   : (C) 2012, Simon Marlow;
--               (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains a distributed map. The implementation is based on Simon
-- Marlow's solution to one of the exerises in his book "Parallel and Concurrent
-- Programming in Haskell".
--
-----------------------------------------------------------------------------

module DistributedDb
  ( main )
  where

import           Control.Distributed.Process
                   (NodeId, Process, ProcessId,
                   ProcessMonitorNotification(..), SendPort, expect,
                   match, monitor, newChan, receiveChan, receiveWait,
                   say, send, sendChan, spawn, spawnLocal)
import           Control.Distributed.Process.Backend.SimpleLocalnet
                   (initializeBackend, startMaster, startSlave)
import           Control.Distributed.Process.Closure
                   (mkStaticClosure, remotable)
import           Control.Distributed.Process.Node
                   (initRemoteTable)
import           Control.Distributed.Static
                   (RemoteTable)
import           Control.Monad
                   (forM, forever, when, zipWithM_)
import           Control.Monad.IO.Class
                   (liftIO)
import           Data.Binary
                   (Binary)
import           Data.Char
                   (ord)
import qualified Data.Map                                           as Map
import           Data.Typeable
                   (Typeable)
import           GHC.Generics
                   (Generic)
import           System.Environment
                   (getArgs)
import           System.IO
                   (hFlush, stdout)
import           Text.Printf
                   (printf)

------------------------------------------------------------------------

type Key   = String -- should really use ByteString
type Value = String

data Request
  = Set Key Value
  | Get Key (SendPort (Maybe Value))
  deriving (Typeable, Generic)

instance Binary Request

worker :: Process ()
worker = go Map.empty
  where
  go store = do
    r <- expect
    case r of
      Set k v ->
        go (Map.insert k v store)
      Get k port -> do
        sendChan port (Map.lookup k store)
        go store

remotable ['worker]

------------------------------------------------------------------------

dbProc :: [NodeId] -> Process ()
dbProc peers = do

  ps <- forM peers $ \nid -> do
          say $ printf "spawning on %s" (show nid)
          spawn nid $(mkStaticClosure 'worker)

  when (null ps) $ liftIO $ ioError (userError "no workers")

  mapM_ monitor ps

  -- group the workers:
  let pairs []       = []
      pairs (a:b:xs) = [a,b] : pairs xs
      pairs [_]      = []
        -- don't use the last node if we have an odd number

      worker_pairs = pairs ps
      n_slices = length worker_pairs

  loop worker_pairs n_slices


loop :: [[ProcessId]] -> Int -> Process ()
loop worker_pairs n_slices
 = receiveWait
        [ match $ \req -> handleRequest req >> loop worker_pairs n_slices
        , match $ \(ProcessMonitorNotification _ pid reason) -> do
            say (printf "process %s died: %s" (show pid) (show reason))
            loop (map (filter (/= pid)) worker_pairs) n_slices
        ]
 where
    workersForKey :: Key -> [ProcessId]
    workersForKey k = worker_pairs !! (ord (head k) `mod` n_slices)

    handleRequest :: Request -> Process ()
    handleRequest r =
      case r of
        Set k _ -> mapM_ (flip send r) (workersForKey k)
        Get k _ -> mapM_ (flip send r) (workersForKey k)

type Database = ProcessId

createDB :: [NodeId] -> Process Database
createDB peers = spawnLocal (dbProc peers)

set :: Database -> Key -> Value -> Process ()
set db k v = send db (Set k v)

get :: Database -> Key -> Process (Maybe Value)
get db k = do
  (s, r) <- newChan
  send db (Get k s)
  receiveChan r

rcdata :: RemoteTable -> RemoteTable
rcdata = __remoteTable

------------------------------------------------------------------------

main :: IO ()
main = distribMain master rcdata

distribMain :: ([NodeId] -> Process ()) -> (RemoteTable -> RemoteTable) -> IO ()
distribMain master' frtable = do
  args <- getArgs
  let rtable = frtable initRemoteTable

  case args of
    [] -> do
      backend <- initializeBackend defaultHost defaultPort rtable
      startMaster backend master'
    [ "master" ] -> do
      backend <- initializeBackend defaultHost defaultPort rtable
      startMaster backend master'
    [ "master", port ] -> do
      backend <- initializeBackend defaultHost port rtable
      startMaster backend master'
    [ "slave" ] -> do
      backend <- initializeBackend defaultHost defaultPort rtable
      startSlave backend
    [ "slave", port ] -> do
      backend <- initializeBackend defaultHost port rtable
      startSlave backend
    [ "slave", host, port ] -> do
      backend <- initializeBackend host port rtable
      startSlave backend
    _ -> error "distribMain: bad args, mate."

defaultHost, defaultPort :: String
defaultHost = "localhost"
defaultPort = "44444"

------------------------------------------------------------------------

master :: [NodeId] -> Process ()
master peers = do

  db <- createDB peers

  let ws = words "module apa bepa cepa depa epa fepa gepa"

  zipWithM_ (set db) ws (tail ws)

  -- get db "module" >>= liftIO . print
  -- get db "xxxx"   >>= liftIO . print

  _ <- forever $ do
    l <- liftIO $ do putStr "key: "; hFlush stdout; getLine
    when (not (null l)) $ do
      r <- get db l
      liftIO $ putStrLn ("response: " ++ show r)

  return ()
