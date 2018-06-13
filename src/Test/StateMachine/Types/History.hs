-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Types.History
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains the notion of a history of an execution of a
-- (parallel) program.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Types.History where

import Test.StateMachine.Types.References

------------------------------------------------------------------------

newtype History cmd resp = History
  { unHistory :: [(Pid, HistoryEvent cmd resp)] }

newtype Pid = Pid Int
  deriving Show

data HistoryEvent cmd resp
  = Invocation !(cmd  Concrete)
  | Response   !(resp Concrete)

{-
------------------------------------------------------------------------

takeInvocations :: [HistoryEvent a b] -> [HistoryEvent a b]
takeInvocations = takeWhile $ \h -> case h of
  InvocationEvent {} -> True
  _                  -> False

findCorrespondingResp :: Pid -> History' act err -> [(Result err Dynamic, History' act err)]
findCorrespondingResp _   [] = []
findCorrespondingResp pid (ResponseEvent resp _ pid' : es) | pid == pid' = [(resp, es)]
findCorrespondingResp pid (e : es) =
  [ (resp, e : es') | (resp, es') <- findCorrespondingResp pid es ]

------------------------------------------------------------------------

-- | An operation packs up an invocation event with its corresponding
--   response event.
data Operation act err = forall resp. Typeable resp =>
  Operation (act Concrete resp) String (Result err resp) String Pid

dynResp :: forall err resp. Typeable resp => Result err Dynamic -> Result err resp
dynResp (Success resp) = Success
  (either (error . show) (\(Concrete resp') -> resp') (reifyDynamic resp))
dynResp (Fail err)     = Fail err

makeOperations :: History' act err -> [Operation act err]
makeOperations [] = []
makeOperations (InvocationEvent (UntypedConcrete act) astr _ pid :
                ResponseEvent resp rstr _ : hist) =
  Operation act astr (dynResp resp) rstr pid : makeOperations hist
makeOperations _ = error "makeOperations: impossible."

-- | Given a history, return all possible interleavings of invocations
--   and corresponding response events.
linearTree :: History' act err -> [Tree (Operation act err)]
linearTree [] = []
linearTree es =
  [ Node (Operation act str (dynResp resp) "<resp>" pid) (linearTree es')
  | InvocationEvent (UntypedConcrete act) str _ pid <- takeInvocations es
  , (resp, es')  <- findCorrespondingResp pid $ filter1 (not . matchInv pid) es
  ]
  where
  filter1 :: (a -> Bool) -> [a] -> [a]
  filter1 _ []                   = []
  filter1 p (x : xs) | p x       = x : filter1 p xs
                     | otherwise = xs

  -- Hmm, is this enough?
  matchInv pid (InvocationEvent _ _ _ pid') = pid == pid'
  matchInv _   _                            = False
-}
