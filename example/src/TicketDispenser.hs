{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeInType                 #-}

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
  ( prop_sequential
  , prop_parallel
  , prop_parallelOK
  , prop_parallelBad
  ) where

import           Control.Concurrent
                   (threadDelay)
import           Data.Char
                   (isSpace)
import           Data.Singletons.Prelude
                   (ConstSym1)
import           Data.Void
                   (Void)
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
                   (frequency, ioProperty, property, (===))

import           Test.StateMachine
import           Test.StateMachine.Internal.Utils
                   (shrinkPropertyHelper)

------------------------------------------------------------------------

-- The actions of the ticket dispenser are:

data Action :: Signature Void where
  TakeTicket :: Action refs ('Response Int)
  Reset      :: Action refs ('Response ())

-- Which correspond to taking a ticket and getting the next number, and
-- resetting the number counter of the dispenser.

------------------------------------------------------------------------

-- The dispenser has to be reset before use, hence the maybe integer.

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

-- With stateful generation we ensure that the dispenser is reset before
-- use.

gen :: Generator Void Action Bool
gen = Generator
  { generator     = const $ frequency
     [ (1, pure (Untyped Reset))
     , (8, pure (Untyped TakeTicket))
     ]
  , gprecondition = gprecondition'
  , gtransition   = gtransition'
  , initGenState  = False
  }
  where
  gprecondition' :: Bool -> Action refs resp -> Bool
  gprecondition' _ Reset      = True
  gprecondition' b TakeTicket = b

  gtransition' :: Bool -> Action refs resp -> Bool
  gtransition' _ Reset      = True
  gtransition' b TakeTicket = b

shrink1 :: Action refs resp -> [Action refs resp]
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

  -> Action (ConstSym1 Void) resp          -- ^ This example doesn't use
                                           -- any references, hence
                                           -- @ConstSym1 Void@ is used.

  -> IO (Response_ (ConstSym1 Void) resp)

semantics se (tdb, tlock) cmd = case cmd of
  TakeTicket -> do
    lock <- lockFile tlock se
    i <- read <$> readFile tdb
    threadDelay 1000
    writeFile tdb (show (i + 1))
    unlockFile lock
    return (i + 1)
  Reset      -> do
    lock <- lockFile tlock se
    writeFile tdb (show (0 :: Integer))
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

-- Sequentially the model is consistant (even though the lock is
-- shared).

prop_sequential :: Property
prop_sequential = sequentialProperty'
  smm
  gen
  shrink1
  (const (const (semantics Shared (ticketDb, ticketLock))))
  (return ())
  (const ioProperty)
  (const (return ()))
  where
  -- Predefined files are used for the database and the file lock.
  ticketDb, ticketLock :: FilePath
  ticketDb   = "/tmp/ticket-dispenser.db"
  ticketLock = "/tmp/ticket-dispenser.lock"

prop_parallel :: SharedExclusive -> Property
prop_parallel se = parallelProperty'
  smm
  gen
  shrink1
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
prop_parallelOK :: Property
prop_parallelOK = prop_parallel Exclusive

-- If we allow file locks to be shared, then we get race conditions as
-- expected. The following property asserts that one of the smallest
-- counterexamples are found.
prop_parallelBad :: Property
prop_parallelBad = shrinkPropertyHelper (prop_parallel Shared) $ \output ->
  let counterExample = dropWhile isSpace (lines output !! 1) in
  counterExample `elem`
    [ "Fork [Reset ()] [] [Reset ()]"
    , "Fork [TakeTicket ()] [Reset ()] [TakeTicket ()]"
    , "Fork [TakeTicket ()] [Reset ()] [Reset ()]"
    , "Fork [Reset ()] [Reset ()] [TakeTicket ()]"

    , "Fork [TakeTicket (),TakeTicket ()] [Reset (),TakeTicket ()] [TakeTicket (),TakeTicket ()]"
    , "Fork [TakeTicket (),TakeTicket ()] [Reset (),TakeTicket ()] [TakeTicket (),Reset ()]"
    , "Fork [TakeTicket (),TakeTicket ()] [Reset (),TakeTicket ()] [Reset (),TakeTicket ()]"
    , "Fork [TakeTicket (),TakeTicket ()] [Reset (),TakeTicket ()] [Reset (),Reset ()]"

    , "Fork [TakeTicket (),TakeTicket ()] [Reset (),TakeTicket ()] [TakeTicket (),TakeTicket ()]"
    , "Fork [TakeTicket (),Reset ()] [Reset (),TakeTicket ()] [TakeTicket (),TakeTicket ()]"
    , "Fork [Reset (),TakeTicket ()] [Reset (),TakeTicket ()] [TakeTicket (),TakeTicket ()]"
    , "Fork [Reset (),Reset ()] [Reset (),TakeTicket ()] [TakeTicket (),TakeTicket ()]"

    , "Fork [TakeTicket (),TakeTicket ()] [Reset (),Reset ()] [TakeTicket (),TakeTicket ()]"
    , "Fork [TakeTicket (),TakeTicket ()] [Reset (),Reset ()] [TakeTicket (),Reset ()]"
    , "Fork [TakeTicket (),TakeTicket ()] [Reset (),Reset ()] [Reset (),TakeTicket ()]"
    , "Fork [TakeTicket (),TakeTicket ()] [Reset (),Reset ()] [Reset (),Reset ()]"

    ]
