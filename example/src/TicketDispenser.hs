{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}

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
  , prop_ticketGenParallelValid
  , prop_ticketShrinkParallelValid
  , withDbLock
  )
  where

import           Control.Exception
                   (SomeException, catch)
import           Data.Functor.Classes
                   (Eq1(..))
import           Data.Typeable
                   (cast)
import           Prelude                             hiding
                   (readFile)
import           System.Directory
                   (createDirectoryIfMissing, getTemporaryDirectory,
                   removeFile)
import           System.FileLock
                   (SharedExclusive(..), lockFile, unlockFile)
import           System.FilePath
                   ((</>))
import           System.IO
                   (hClose, openTempFile)
import           System.IO.Strict
                   (readFile)
import           Test.QuickCheck
                   (Property, forAll, frequency, (===))
import           Test.QuickCheck.Counterexamples
                   (PropertyOf)

import           Test.StateMachine
import           Test.StateMachine.Internal.Parallel
import           Test.StateMachine.Internal.Types
import           Test.StateMachine.TH
                   (deriveShows, deriveTestClasses)
import           Utils

------------------------------------------------------------------------

-- The actions of the ticket dispenser are:

data Action (v :: * -> *) :: * -> * where
  TakeTicket :: Action v Int
  Reset      :: Action v ()

-- Which correspond to taking a ticket and getting the next number, and
-- resetting the number counter of the dispenser.

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
  TakeTicket -> Just resp == (succ <$> m)
  Reset      -> True

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
      `catch` (\(_ :: SomeException) -> return "-1")
    writeFile tdb (show (i + 1))
      `catch` (\(_ :: SomeException) -> return ())
    unlockFile lock
    return (i + 1)
  Reset      -> do
    lock <- lockFile tlock se
    writeFile tdb (show (0 :: Integer))
      `catch` (\(_ :: SomeException) -> return ())
    unlockFile lock

------------------------------------------------------------------------

deriveShows       ''Action
deriveTestClasses ''Action

------------------------------------------------------------------------

type DbLock = (FilePath, FilePath)

withDbLock :: (DbLock -> IO ()) -> IO ()
withDbLock run = do
  tmp <- getTemporaryDirectory
  let tmpTD = tmp </> "ticket-dispenser"
  createDirectoryIfMissing True tmpTD
  (tdb,   dbh)   <- openTempFile tmpTD "ticket-dispenser.db"
  hClose dbh
  (tlock, lockh) <- openTempFile tmpTD "ticket-dispenser.lock"
  hClose lockh
  run (tdb, tlock)
  removeFile tdb
  removeFile tlock

sm :: SharedExclusive -> DbLock -> StateMachine Model Action IO
sm se files = stateMachine
  generator shrinker preconditions transitions
  postconditions initModel (semantics se files) id

-- Sequentially the model is consistent (even though the lock is
-- shared).

prop_ticketDispenser :: DbLock -> Property
prop_ticketDispenser files = monadicSequential sm' $ \prog -> do
  (hist, _, res) <- runProgram sm' prog
  prettyProgram sm' hist $
    checkActionNames prog (res === Ok)
  where
  sm' = sm Shared files

prop_ticketDispenserParallel
  :: SharedExclusive -> DbLock -> PropertyOf (ParallelProgram Action)
prop_ticketDispenserParallel se files =
  monadicParallelC sm' $ \prog ->
    prettyParallelProgram prog =<< runParallelProgram' 100 sm' prog
  where
  sm' = sm se files

-- So long as the file locks are exclusive, i.e. not shared, the
-- parallel property passes.
prop_ticketDispenserParallelOK :: DbLock -> PropertyOf (ParallelProgram Action)
prop_ticketDispenserParallelOK = prop_ticketDispenserParallel Exclusive

-- If we allow file locks to be shared, then we get race conditions as
-- expected. The following property asserts that one of the smallest
-- counterexamples are found.
prop_ticketDispenserParallelBad :: DbLock -> Property
prop_ticketDispenserParallelBad files =
  minimalShrinkHelper
    shrinker preconditions (okTransition transitions) initModel
    (prop_ticketDispenserParallel Shared files)
    isMinimal
  where
  isMinimal :: ParallelProgram Action -> Bool
  isMinimal pprog
    =  parallelProgramLength pprog `elem` [2, 3]
    && (structuralSubset
          [ Untyped Reset ] [ Untyped TakeTicket, Untyped TakeTicket ] pprog ||
        structuralSubset
          [ Untyped Reset ] [ Untyped TakeTicket, Untyped Reset ] pprog ||
        structuralSubset
          [] [ Untyped Reset, Untyped Reset ] pprog)

prop_ticketGenParallelValid :: Property
prop_ticketGenParallelValid = forAll
  (generateParallelProgram generator preconditions (okTransition transitions) initModel)
  (validParallelProgram preconditions (okTransition transitions) initModel)

prop_ticketShrinkParallelValid :: Property
prop_ticketShrinkParallelValid = forAll
  (generateParallelProgram generator preconditions (okTransition transitions) initModel) $ \p ->
    all (validParallelProgram preconditions (okTransition transitions) initModel)
        (shrinkParallelProgram shrinker preconditions (okTransition transitions) initModel p)

------------------------------------------------------------------------

-- Instances needed for the last property.

deriving instance Eq1 v => Eq (Action v resp)

instance Eq (Untyped Action) where
  Untyped act1 == Untyped act2 = cast act1 == Just act2
