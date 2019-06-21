{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE StandaloneDeriving #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Types.History
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan.andjelkovic@here.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains the notion of a history of an execution of a
-- (parallel) program.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Types.History
  ( History(..)
  , History'
  , Pid(..)
  , HistoryEvent(..)
  , Operation(..)
  , makeOperations
  , interleavings
  , completeHistory
  )
  where

import           Data.List
                   ((\\))
import           Data.Set
                   (Set)
import           Data.Tree
                   (Forest, Tree(Node))
import           Prelude

import           Test.StateMachine.Types.References

------------------------------------------------------------------------

newtype History cmd resp = History
  { unHistory :: History' cmd resp }

deriving instance (Eq (cmd Concrete), Eq (resp Concrete)) =>
  Eq (History cmd resp)

deriving instance (Show (cmd Concrete), Show (resp Concrete)) =>
  Show (History cmd resp)

type History' cmd resp = [(Pid, HistoryEvent cmd resp)]

newtype Pid = Pid { unPid :: Int }
  deriving (Eq, Show, Ord)

data HistoryEvent cmd resp
  = Invocation !(cmd  Concrete) !(Set Var)
  | Response   !(resp Concrete)
  | Exception  !String

deriving instance (Eq (cmd Concrete), Eq (resp Concrete)) =>
  Eq (HistoryEvent cmd resp)

deriving instance (Show (cmd Concrete), Show (resp Concrete)) =>
  Show (HistoryEvent cmd resp)

------------------------------------------------------------------------

takeInvocations :: History' cmd resp -> [(Pid, cmd Concrete)]
takeInvocations []                               = []
takeInvocations ((pid, Invocation cmd _) : hist) = (pid, cmd) : takeInvocations hist
takeInvocations ((_,   Response _)       : _)    = []
takeInvocations ((_,   Exception _)      : _)    = []

findResponse :: Pid -> History' cmd resp -> [(resp Concrete, History' cmd resp)]
findResponse _   []                                         = []
findResponse pid ((pid', Response resp) : es) | pid == pid' = [(resp, es)]
findResponse pid (e                     : es)               =
  [ (resp, e : es') | (resp, es') <- findResponse pid es ]

------------------------------------------------------------------------

-- | An operation packs up an invocation event with its corresponding
--   response event.
data Operation cmd resp
  = Operation (cmd Concrete) (resp Concrete) Pid
  | Crash     (cmd Concrete) String Pid

deriving instance (Show (cmd Concrete), Show (resp Concrete)) =>
  Show (Operation cmd resp)

-- | Given a sequential history, group invocation and response events into
--   operations.
makeOperations :: History' cmd resp -> [Operation cmd resp]
makeOperations [] = []
makeOperations [(pid1, Invocation cmd _), (pid2, Exception err)]
  | pid1 == pid2 = [Crash cmd err pid1]
  | otherwise    = error "makeOperations: impossible, pid mismatch."
makeOperations ((pid1, Invocation cmd _) : (pid2, Response resp) : hist)
  | pid1 == pid2 = Operation cmd resp pid1 : makeOperations hist
  | otherwise    = error "makeOperations: impossible, pid mismatch."
makeOperations _ = error "makeOperations: impossible."

-- | Given a parallel history, return all possible interleavings of invocations
--   and corresponding response events.
interleavings :: History' cmd resp -> Forest (Operation cmd resp)
interleavings [] = []
interleavings es =
  [ Node (Operation cmd resp pid) (interleavings es')
  | (pid, cmd)  <- takeInvocations es
  , (resp, es') <- findResponse pid (filter1 (not . matchInvocation pid) es)
  ]
  where
    matchInvocation pid (pid', Invocation _ _) = pid == pid'
    matchInvocation _   _                      = False

    filter1 :: (a -> Bool) -> [a] -> [a]
    filter1 _ []                   = []
    filter1 p (x : xs) | p x       = x : filter1 p xs
                       | otherwise = xs

------------------------------------------------------------------------

crashingInvocations :: History' cmd resp -> History' cmd resp
crashingInvocations = go [] [] . reverse
  where
    go :: [Pid] -> History' cmd resp -> History' cmd resp -> History' cmd resp
    go _crashedPids crashedInvs [] = reverse crashedInvs
    go  crashedPids crashedInvs ((pid, Exception _err) : es)
      | pid `elem` crashedPids = error "impossible, a process cannot crash more than once."
      | otherwise              = go (pid : crashedPids) crashedInvs es
    go crashedPids crashedInvs (e@(pid, Invocation {}) : es)
      | pid `elem` crashedPids = go (crashedPids \\ [pid]) (e : crashedInvs) es
      | otherwise              = go crashedPids crashedInvs es
    go crashedPids crashedInvs ((_pid, Response {}) : es) =
      go crashedPids crashedInvs es

completeHistory :: (cmd Concrete -> resp Concrete) -> History cmd resp
                -> History cmd resp
completeHistory complete hist = History (hist' ++ resps)
  where
    hist' = unHistory hist
    resps = [ (pid, Response (complete cmd))
            | (pid, Invocation cmd _vars) <- crashingInvocations hist'
            ]
