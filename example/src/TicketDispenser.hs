{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeInType                 #-}

module TicketDispenser
  ( prop_sequential
  , prop_parallel
  , prop_parallelOK
  , prop_parallelBad
  ) where

import           Control.Monad.State
                   (StateT, get, lift, modify)
import           Prelude                          hiding
                   (readFile)
import           System.Directory
                   (removePathForcibly)
import           System.FileLock
                   (SharedExclusive(..), lockFile, unlockFile)
import           System.IO.Strict
                   (readFile)
import           Test.QuickCheck
                   (Gen, frequency, ioProperty, property, (===))

import           Test.StateMachine
import           Test.StateMachine.Internal.Types

------------------------------------------------------------------------

data Action :: Signature () where
  TakeTicket :: Action refs ('Response Int)
  Reset      :: Action refs ('Response ())

------------------------------------------------------------------------

newtype Model refs = Model (Maybe Int)
  deriving (Eq, Show)

initModel :: Model refs
initModel = Model Nothing

preconditions :: Model refs -> Action refs resp -> Bool
preconditions (Model Nothing)  TakeTicket = False
preconditions (Model (Just _)) TakeTicket = True
preconditions _                Reset      = True

transitions
  :: Model refs -> Action refs resp -> Response_ refs resp -> Model refs
transitions (Model m) cmd _ = case cmd of
  TakeTicket -> Model (succ <$> m)
  Reset      -> Model (Just 0)

postconditions
  :: Model refs -> Action refs resp -> Response_ refs resp -> Property
postconditions (Model m) cmd resp = case cmd of
  TakeTicket -> Just resp === (succ <$> m)
  Reset      -> property True

smm :: StateMachineModel Model Action
smm = StateMachineModel preconditions postconditions transitions initModel

------------------------------------------------------------------------

gen :: StateT Bool Gen (Untyped Action (RefPlaceholder ()))
gen = do
  initialised <- get
  if not initialised
  then do
    modify not
    lift $ pure (Untyped Reset)
  else do
    lift $ frequency
      [ (1, pure (Untyped Reset))
      , (8, pure (Untyped TakeTicket))
      ]

shrink1 :: Action refs resp -> [Action refs resp]
shrink1 _ = []

------------------------------------------------------------------------

ticketDb, ticketLock :: FilePath
ticketDb   = "/tmp/ticket-dispenser.db"
ticketLock = "/tmp/ticket-dispenser.lock"

semantics :: SharedExclusive -> Action ConstIntRef resp -> IO (Response_ ConstIntRef resp)
semantics se cmd = case cmd of
  TakeTicket -> do
    lock <- lockFile ticketLock se
    i <- read <$> readFile ticketDb
    writeFile ticketDb (show (i + 1))
    unlockFile lock
    return (i + 1)
  Reset      -> do
    lock <- lockFile ticketLock se
    writeFile ticketDb (show (0 :: Integer))
    unlockFile lock

------------------------------------------------------------------------

instance HasResponse Action where
  response TakeTicket = SResponse
  response Reset      = SResponse

instance ShowCmd Action where
  showCmd TakeTicket = "TakeTicket"
  showCmd Reset      = "Reset"

instance IxFunctor Action where
  ifmap _ TakeTicket = TakeTicket
  ifmap _ Reset      = Reset

instance IxFoldable Action where
  ifoldMap _ TakeTicket = mempty
  ifoldMap _ Reset      = mempty

instance IxTraversable Action where
  ifor _ TakeTicket _ = pure TakeTicket
  ifor _ Reset      _ = pure Reset

------------------------------------------------------------------------

prop_sequential :: Property
prop_sequential = sequentialProperty'
  smm
  gen
  False
  shrink1
  (const (const (semantics Shared)))
  ioProperty

prop_parallel :: SharedExclusive -> Property
prop_parallel se = parallelProperty'
  smm
  gen
  False
  shrink1
  (semantics se)
  (removePathForcibly ticketDb >>
   removePathForcibly ticketLock)

prop_parallelOK :: Property
prop_parallelOK = prop_parallel Exclusive

prop_parallelBad :: Property
prop_parallelBad = prop_parallel Shared
