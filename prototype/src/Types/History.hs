module Types.History where

import Types.Reference

------------------------------------------------------------------------

newtype History cmd resp = History
  { unHistory :: [(Pid, HistoryEvent cmd resp)] }

newtype Pid = Pid Int

data HistoryEvent cmd resp
  = Invocation !(cmd  Concrete)
  | Response   !(resp Concrete)
