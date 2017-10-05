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
newtype History act err = History
  { unHistory :: History' act err }
  deriving Monoid

ppHistory :: History act err -> String
ppHistory = foldr go "" . unHistory
  where
  go :: HistoryEvent (UntypedConcrete act) err -> String -> String
  go (InvocationEvent _ str _ _) ih = " " ++ str ++ " ==> " ++ ih
  go (ResponseEvent   _ str   _) ih =        str ++ "\n"    ++ ih

type History' act err = [HistoryEvent (UntypedConcrete act) err]

data UntypedConcrete (act :: (* -> *) -> * -> *) where
  UntypedConcrete :: (Show resp, Typeable resp) =>
    act Concrete resp -> UntypedConcrete act

data HistoryEvent act err
  = InvocationEvent act                  String Var Pid
  | ResponseEvent   (Result Dynamic err) String     Pid

getProcessIdEvent :: HistoryEvent act err -> Pid
getProcessIdEvent (InvocationEvent _ _ _ pid) = pid
getProcessIdEvent (ResponseEvent   _ _ pid)   = pid

data Operation act err = forall resp. Typeable resp =>
  Operation (act Concrete resp) String (Result (Concrete resp) err) Pid

takeInvocations :: [HistoryEvent a b] -> [HistoryEvent a b]
takeInvocations = takeWhile $ \h -> case h of
  InvocationEvent {} -> True
  _                  -> False

findCorrespondingResp :: Pid -> History' act err -> [(Result Dynamic err, History' act err)]
findCorrespondingResp _   [] = []
findCorrespondingResp pid (ResponseEvent resp _ pid' : es) | pid == pid' = [(resp, es)]
findCorrespondingResp pid (e : es) =
  [ (resp, e : es') | (resp, es') <- findCorrespondingResp pid es ]
