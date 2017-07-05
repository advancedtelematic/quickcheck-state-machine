{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE KindSignatures    #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  TicketDispenser
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains a specification of a simple ticket dispenser.
--
-----------------------------------------------------------------------------

module TicketDispenser
  ( prop_ticketDispenser
  , prop_ticketDispenserParallel
  , prop_ticketDispenserParallelOK
  , prop_ticketDispenserParallelBad
  ) where

import           Data.Char
                   (isSpace)
import           Prelude                          hiding
                   (readFile)
import           System.Directory
                   (removePathForcibly)
import           System.FileLock
                   (SharedExclusive(..), lockFile, unlockFile)
import           System.IO
                   (hClose, openTempFile)
import           System.IO.Strict
                   (readFile)
import           Test.QuickCheck
                   (Property, frequency, ioProperty, property, (===))

import           Test.StateMachine
import           Test.StateMachine.Internal.Utils
                   (shrinkPropertyHelper)

------------------------------------------------------------------------

-- The actions of the ticket dispenser are:

data Action (v :: * -> *) :: * -> * where
  TakeTicket :: Action v Int
  Reset      :: Action v ()

-- Which correspond to taking a ticket and getting the next number, and
-- resetting the number counter of the dispenser.

instance ShowAction Action where
  showAction TakeTicket = showResponse "TakeTicket"
  showAction Reset      = showResponse "Reset"

------------------------------------------------------------------------

-- The dispenser has to be reset before use, hence the maybe integer.

newtype Model (v :: * -> *) = Model (Maybe Int)
  deriving (Eq, Show)

initModel :: Model v
initModel = Model Nothing

preconditions :: Precondition Model Action
preconditions (Model Nothing)  TakeTicket = False
preconditions (Model (Just _)) TakeTicket = True
preconditions _                Reset      = True

transitions :: Transition Model Action
transitions (Model m) cmd _ = case cmd of
  TakeTicket -> Model (succ <$> m)
  Reset      -> Model (Just 0)

postconditions :: Postcondition Model Action
postconditions (Model m) cmd resp = case cmd of
  TakeTicket -> Just resp === (succ <$> m)
  Reset      -> property True

------------------------------------------------------------------------

-- With stateful generation we ensure that the dispenser is reset before
-- use.

gen :: Generator Model Action
gen (Model Nothing)  = pure (Untyped Reset)
gen (Model (Just _)) = frequency
  [ (1, pure (Untyped Reset))
  , (8, pure (Untyped TakeTicket))
  ]

shrink1 :: Action v resp -> [Action v resp]
shrink1 _ = []

------------------------------------------------------------------------

-- We will implement the dispenser using a simple database file which
-- stores the next number. A file lock is used to allow concurrent use.

semantics
  :: SharedExclusive                       -- ^ Indicates if the file
                                           -- lock should be shared
                                           -- between threads or if it
                                           -- should be exclusive.
                                           -- Sharing it could cause
                                           -- race conditions.

  -> (FilePath, FilePath)                  -- ^ File paths to the
                                           -- database storing the
                                           -- ticket counter and the
                                           -- file lock used for
                                           -- synchronisation.

  -> Action Concrete resp

  -> IO resp

semantics se (tdb, tlock) cmd = case cmd of
  TakeTicket -> do
    lock <- lockFile tlock se
    i <- read <$> readFile tdb
    writeFile tdb (show (i + 1))
    unlockFile lock
    return (i + 1)
  Reset      -> do
    lock <- lockFile tlock se
    writeFile tdb (show (0 :: Integer))
    unlockFile lock

------------------------------------------------------------------------

instance HTraversable Action where
  htraverse _ TakeTicket = pure TakeTicket
  htraverse _ Reset      = pure Reset

instance HFunctor  Action
instance HFoldable Action

------------------------------------------------------------------------

-- Sequentially the model is consistant (even though the lock is
-- shared).

prop_ticketDispenser :: Property
prop_ticketDispenser = sequentialProperty
  gen
  shrink1
  preconditions
  transitions
  postconditions
  initModel
  (semantics Shared (ticketDb, ticketLock))
  ioProperty
  where
  -- Predefined files are used for the database and the file lock.
  ticketDb, ticketLock :: FilePath
  ticketDb   = "/tmp/ticket-dispenser.db"
  ticketLock = "/tmp/ticket-dispenser.lock"

prop_ticketDispenserParallel :: SharedExclusive -> Property
prop_ticketDispenserParallel se = parallelProperty'
  gen
  shrink1
  preconditions
  transitions
  postconditions
  initModel
  setup
  (semantics se)
  cleanup
  where

  -- In the parallel case we create a temporary files for the database and
  -- the lock.
  setup = do
    (tdb,   dbh)   <- openTempFile "/tmp/" "ticket-dispenser.db"
    hClose dbh
    (tlock, lockh) <- openTempFile "/tmp/" "ticket-dispenser.lock"
    hClose lockh
    return (tdb, tlock)

  -- After the test are run we remove the temporary files.
  cleanup (tdb, tlock) = do
    removePathForcibly tdb
    removePathForcibly tlock

-- So long as the file locks are exclusive, i.e. not shared, the
-- parallel property passes.
prop_ticketDispenserParallelOK :: Property
prop_ticketDispenserParallelOK = prop_ticketDispenserParallel Exclusive

-- If we allow file locks to be shared, then we get race conditions as
-- expected. The following property asserts that one of the smallest
-- counterexamples are found.
prop_ticketDispenserParallelBad :: Property
prop_ticketDispenserParallelBad =
  shrinkPropertyHelper (prop_ticketDispenserParallel Shared) $ \output ->
    let counterExample = dropWhile isSpace (lines output !! 1) in
    counterExample `elem`
      [ "Fork [Reset] [] [Reset]"
      , "Fork [TakeTicket] [Reset] [TakeTicket]"
      , "Fork [TakeTicket] [Reset] [Reset]"
      , "Fork [Reset] [Reset] [TakeTicket]"
      ]
