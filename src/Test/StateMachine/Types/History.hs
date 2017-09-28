{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}

module Test.StateMachine.Types.History where

import           Data.Dynamic
                   (Dynamic)
import           Data.Typeable
                   (Typeable)
import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Types

------------------------------------------------------------------------

-- | A history is a trace of invocations and responses from running a
--   parallel program.
newtype History act = History
  { unHistory :: History' act }
  deriving Monoid

ppHistory :: History act -> String
ppHistory = foldr go "" . unHistory
  where
  go :: HistoryEvent (UntypedConcrete act) -> String -> String
  go (InvocationEvent _ str _ _) ih = " " ++ str ++ " ==> " ++ ih
  go (ResponseEvent   _ str   _) ih =        str ++ "\n"    ++ ih

type History' act = [HistoryEvent (UntypedConcrete act)]

data UntypedConcrete (act :: (* -> *) -> * -> *) where
  UntypedConcrete :: (Show resp, Typeable resp) =>
    act Concrete resp -> UntypedConcrete act

data HistoryEvent act
  = InvocationEvent act     String Var Pid
  | ResponseEvent   Dynamic String     Pid

getProcessIdEvent :: HistoryEvent act -> Pid
getProcessIdEvent (InvocationEvent _ _ _ pid) = pid
getProcessIdEvent (ResponseEvent   _ _ pid)   = pid

data Operation act = forall resp. Typeable resp =>
  Operation (act Concrete resp) String (Concrete resp) Pid

takeInvocations :: [HistoryEvent a] -> [HistoryEvent a]
takeInvocations = takeWhile $ \h -> case h of
  InvocationEvent {} -> True
  _                  -> False

findCorrespondingResp :: Pid -> History' act -> [(Dynamic, History' act)]
findCorrespondingResp _   [] = []
findCorrespondingResp pid (ResponseEvent resp _ pid' : es) | pid == pid' = [(resp, es)]
findCorrespondingResp pid (e : es) =
  [ (resp, e : es') | (resp, es') <- findCorrespondingResp pid es ]
