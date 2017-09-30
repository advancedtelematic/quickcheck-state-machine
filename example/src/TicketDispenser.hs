{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE StandaloneDeriving #-}

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
import           Data.Dynamic
                   (cast)
import           Data.Functor.Classes
                   (Eq1(..), Show1)
import           Prelude                                  hiding
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
                   (Property, frequency, property, (===))
import           Test.QuickCheck.Counterexamples
                   (PropertyOf)
import           Text.ParserCombinators.ReadP
                   (string)
import           Text.Read
                   (choice, lift, readListPrec, readListPrecDefault,
                   readPrec)

import           Test.StateMachine
import           Test.StateMachine.Internal.AlphaEquality
import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Internal.Utils
                   (shrinkPropertyHelper, shrinkPropertyHelperC)

------------------------------------------------------------------------

-- The actions of the ticket dispenser are:

data Action (v :: * -> *) :: * -> * where
  TakeTicket :: Action v Int
  Reset      :: Action v ()

deriving instance Show1 v => Show (Action v resp)

-- Which correspond to taking a ticket and getting the next number, and
-- resetting the number counter of the dispenser.

instance Show (Untyped Action) where
  show (Untyped act) = show act

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

generator :: Generator Model Action
generator (Model Nothing)  = pure (Untyped Reset)
generator (Model (Just _)) = frequency
  [ (1, pure (Untyped Reset))
  , (8, pure (Untyped TakeTicket))
  ]

shrinker :: Action v resp -> [Action v resp]
shrinker _ = []

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

instance Constructors Action where
  constructor x = Constructor $ case x of
    TakeTicket -> "TakeTicket"
    Reset      -> "Reset"
  nConstructors _ = 2

------------------------------------------------------------------------

sm :: SharedExclusive -> (FilePath, FilePath) -> StateMachine Model Action IO
sm se files = StateMachine
  generator shrinker preconditions transitions
  postconditions initModel (semantics se files) id

-- Sequentially the model is consistant (even though the lock is
-- shared).

prop_ticketDispenser :: Property
prop_ticketDispenser = monadicSequential sm' $ \prog -> do
  (hist, model, prop) <- runProgram sm' prog
  prettyProgram prog hist model $
    checkActionNames prog prop
  where
  sm' = sm Shared (ticketDb, ticketLock)
    where
    -- Predefined files are used for the database and the file lock.
    ticketDb, ticketLock :: FilePath
    ticketDb   = "/tmp/ticket-dispenser.db"
    ticketLock = "/tmp/ticket-dispenser.lock"

prop_ticketDispenserParallel :: SharedExclusive -> PropertyOf (ParallelProgram Action)
prop_ticketDispenserParallel se =
  bracketPC setup cleanup $ \files ->
    monadicParallelC (sm se files) $ \prog ->
      prettyParallelProgram prog =<< runParallelProgram' 100 (sm se files) prog
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
prop_ticketDispenserParallelOK :: PropertyOf (ParallelProgram Action)
prop_ticketDispenserParallelOK = prop_ticketDispenserParallel Exclusive

-- If we allow file locks to be shared, then we get race conditions as
-- expected. The following property asserts that one of the smallest
-- counterexamples are found.
prop_ticketDispenserParallelBad :: Property
prop_ticketDispenserParallelBad =
  shrinkPropertyHelperC (prop_ticketDispenserParallel Shared) $ \(ParallelProgram f) ->
    any (alphaEqFork f)
      [ fork [iact Reset 0]      []             [iact Reset 1]
      , fork [iact TakeTicket 0] [iact Reset 1] [iact TakeTicket 2]
      , fork [iact Reset 0]      [iact Reset 1] [iact TakeTicket 2]
      , fork [iact TakeTicket 0] [iact Reset 1] [iact Reset 2]
      ]
    where
    fork l p r = Fork (Program l) (Program p) (Program r)
    iact act n = Internal act (Symbolic (Var n))

------------------------------------------------------------------------

-- Instances needed for the last property.

deriving instance Eq1 v => Eq (Action v resp)

instance Eq (Untyped Action) where
  Untyped act1 == Untyped act2 = cast act1 == Just act2
