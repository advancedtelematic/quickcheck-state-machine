module Types.History where

import Types.Reference

------------------------------------------------------------------------

newtype History cmd resp = History [(Pid, HistoryEvent cmd resp)]

newtype Pid = Pid Int

data HistoryEvent cmd resp
  = Invocation (cmd  Symbolic)
  | Response   (resp Concrete)
