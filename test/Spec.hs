{-# LANGUAGE ScopedTypeVariables #-}

module Main (main) where

import           Control.Exception
                   (catch)
import           Prelude
import           System.Exit
                   (ExitCode(..))
import           System.Process
                   (StdStream(CreatePipe), proc, std_out,
                   waitForProcess, withCreateProcess)
import           Test.DocTest
                   (doctest)
import           Test.Tasty
                   (TestTree, defaultMain, testGroup, withResource)
import           Test.Tasty.HUnit
                   (testCase)
import           Test.Tasty.QuickCheck
                   (expectFailure, testProperty, withMaxSuccess)

import           Bookstore                as Store
import           CircularBuffer
import           Cleanup
import qualified CrudWebserverDb          as WS
import           DieHard
import           Echo
import           ErrorEncountered
import           Hanoi
import           IORefs
import           MemoryReference
import           Mock
import           Overflow
import           ProcessRegistry
import           RQlite
import qualified ShrinkingProps
import           SQLite
import           Test.StateMachine.Markov
                   (PropertyName, StatsDb, fileStatsDb)
import           TicketDispenser
import qualified UnionFind

------------------------------------------------------------------------

tests :: Bool -> TestTree
tests docker0 = testGroup "Tests"
  [ testCase "Doctest"
      (doctest [ "src/Test/StateMachine/Z.hs"
               , "src/Test/StateMachine/Logic.hs"
               ])
  , ShrinkingProps.tests
  , testProperty "TowersOfHanoi"
      (expectFailure (prop_hanoi 3))
  , testProperty "DieHard"
      (expectFailure (withMaxSuccess 2000 prop_dieHard))
  , testGroup "MemoryReference"
      [testProperty  "NoBugSeq"                         (prop_sequential MemoryReference.None)
      , testProperty "LogicBug"          (expectFailure (prop_sequential Logic))
      , testProperty "RaceBugSequential"                (prop_sequential Race)
      , testProperty "NoBugParallel"                    (prop_parallel MemoryReference.None)
      , testProperty "RaceBugParallel"   (expectFailure (prop_parallel   Race))
      , testProperty "CrashBugParallel"                 (prop_parallel'  Crash)
      , testProperty "CrashAndLogicBugParallel"
          (expectFailure (withMaxSuccess 10000 (prop_parallel' CrashAndLogic)))
      , testProperty "PreconditionFailed" prop_precondition
      , testProperty "ExistsCommands"     prop_existsCommands
      , testProperty "NoBug 1 thread"            (prop_nparallel MemoryReference.None 1)
      , testProperty "NoBug 2 threads"           (prop_nparallel MemoryReference.None 2)
      , testProperty "NoBug 3 threads"           (withMaxSuccess 80 $ prop_nparallel MemoryReference.None 3)
      , testProperty "NoBug 4 threads"           (withMaxSuccess 40 $ prop_nparallel MemoryReference.None 4)
      , testProperty "RaceBugParalleel 1 thread"  (prop_nparallel Race 1)
      , testProperty "RaceBugParalleel 2 threads" (expectFailure (prop_nparallel   Race 2))
      , testProperty "RaceBugParalleel 3 threads" (expectFailure (prop_nparallel   Race 3))
      , testProperty "RaceBugParalleel 4 threads" (expectFailure (prop_nparallel   Race 4))
      , testProperty "ShrinkParallelEquivalence" prop_pairs_shrink_parallel_equivalence
      , testProperty "ShrinkAndValidateParallelEquivalence" prop_pairs_shrinkAndValidate_equivalence
      , testProperty "ShrinkPairsEquialence"     prop_pairs_shrink_parallel
      ]
  , testGroup "Overflow"
      [ testProperty "2-threads" prop_parallel_overflow
      , testProperty "3-threads" $ prop_nparallel_overflow 3
      , testProperty "4-threads" $ expectFailure
                                 $ withMaxSuccess 500
                                 $ prop_nparallel_overflow 4
      ]
  , testGroup "Cleanup"
      [ testProperty "seqRegularNoOp"         $ prop_sequential_clean   Regular    Cleanup.NoBug     NoOp
      , testProperty "seqRegular"             $ prop_sequential_clean   Regular    Cleanup.NoBug     ReDo
      , testProperty "seqRegularExcNoOp"
        $ expectFailure                       $ prop_sequential_clean   Regular    Cleanup.Exception NoOp
      , testProperty "seqRegularExc"
        $ expectFailure                       $ prop_sequential_clean   Regular    Cleanup.Exception ReDo
      , testProperty "seqFilesNoOp"           $ prop_sequential_clean   Files      Cleanup.NoBug     NoOp
      , testProperty "seqFiles"               $ prop_sequential_clean   Files      Cleanup.NoBug     ReDo
      , testProperty "seqFilesExcNoOp"        $ prop_sequential_clean   Files      Cleanup.Exception NoOp
      , testProperty "seqFilesExc"            $ prop_sequential_clean   Files      Cleanup.Exception ReDo
      , testProperty "seqFilesExcAfterNoOp"   $ prop_sequential_clean   Files      Cleanup.ExcAfter  NoOp
      , testProperty "seqFilesExcAfterReDo"   $ prop_sequential_clean   Files      Cleanup.ExcAfter  ReDo
      , testProperty "seqEquivNoOp"           $ prop_sequential_clean  (Eq False)  Cleanup.NoBug     NoOp

      , testProperty "2-threadsRegularExc"
        $ expectFailure                       $ prop_parallel_clean     Regular    Cleanup.Exception NoOp
      , testProperty "2-threadsRegularExc"
        $ expectFailure                       $ prop_parallel_clean     Regular    Cleanup.Exception ReDo
      , testProperty "2-threadsFilesExc"
        $ expectFailure $ withMaxSuccess 1000 $ prop_parallel_clean     Files      Cleanup.Exception ReDo
      , testProperty "2-threadsEquivFailingNoOp"
        $ expectFailure $ withMaxSuccess 1000 $ prop_parallel_clean     (Eq True)  Cleanup.NoBug     NoOp

      , testProperty "3-threadsRegularNoOp"   $ prop_nparallel_clean  3 Regular    Cleanup.NoBug     NoOp
      , testProperty "3-threadsRegular"       $ prop_nparallel_clean  3 Regular    Cleanup.NoBug     ReDo
      , testProperty "3-threadsRegularExc"    $ expectFailure
                                              $ prop_nparallel_clean  3 Regular    Cleanup.Exception NoOp
      , testProperty "3-threadsRegularExc"
        $ expectFailure                       $ prop_nparallel_clean  3 Regular    Cleanup.Exception ReDo
      , testProperty "3-threadsFilesNoOp"     $ prop_nparallel_clean  3 Files      Cleanup.NoBug     NoOp
      , testProperty "3-threadsFiles"         $ prop_nparallel_clean  3 Files      Cleanup.NoBug     ReDo
      , testProperty "3-threadsFilesExcNoOp"  $ prop_nparallel_clean  3 Files      Cleanup.Exception NoOp
      , testProperty "3-threadsFilesExc"
        $ expectFailure $ withMaxSuccess 1000 $ prop_nparallel_clean  3 Files      Cleanup.Exception ReDo
      , testProperty "3-threadsFilesExcAfter" $ prop_nparallel_clean  3 Files      Cleanup.ExcAfter  NoOp
      , testProperty "3-threadsEquivNoOp"     $ prop_nparallel_clean  3 (Eq False) Cleanup.NoBug     NoOp
      , testProperty "3-threadsEquivFailingNoOp"
        $ expectFailure $ withMaxSuccess 1000 $ prop_nparallel_clean  3 (Eq True)  Cleanup.NoBug     NoOp
      ]
  , testGroup "SQLite"
      [ testProperty "Parallel" prop_parallel_sqlite
      ]
  , testGroup "Rqlite"
      [ whenDocker docker0 "rqlite" $ testProperty "parallel" $ withMaxSuccess 10 $ prop_parallel_rqlite (Just Weak)
      -- we currently don't add other properties, because they interfere (Tasty runs tests on parallel)
      -- , testProperty "sequential" $ withMaxSuccess 10   $ prop_sequential_rqlite (Just Weak)
      -- , testProperty "sequential-stale" $ expectFailure $ prop_sequential_rqlite (Just RQlite.None)
      ]
  , testGroup "ErrorEncountered"
      [ testProperty "Sequential" prop_error_sequential
      , testProperty "Parallel"   prop_error_parallel
      , testProperty "2-Parallel" $ prop_error_nparallel 2
      , testProperty "3-Parallel" $ prop_error_nparallel 3
      , testProperty "4-Parallel" $ prop_error_nparallel 4
      ]
  , testGroup "CrudWebserver"
      [ webServer docker0 WS.None  8800 "NoBug"                       WS.prop_crudWebserverDb
      , webServer docker0 WS.Logic 8801 "LogicBug"   (expectFailure . WS.prop_crudWebserverDb)
      , webServer docker0 WS.Race  8802 "NoRaceBug"                   WS.prop_crudWebserverDb
      , webServer docker0 WS.Race  8803 "RaceBug"    (expectFailure . WS.prop_crudWebserverDbParallel)
      ]
  , testGroup "Bookstore"
      [ dataBase docker0 "NoBug" (Store.prop_bookstore Store.NoBug)
      , dataBase docker0 "SqlStatementBug"
          $ expectFailure
          . withMaxSuccess 500
          . Store.prop_bookstore Bug
      , dataBase docker0 "InputValidationBug"
          $ expectFailure
          . withMaxSuccess 500
          . Store.prop_bookstore Injection
      ]
  , testGroup "TicketDispenser"
      [ testProperty "Sequential"                       prop_ticketDispenser
      , testProperty "ParallelWithExclusiveLock" (withMaxSuccess 30
                                                        prop_ticketDispenserParallelOK)
      , testProperty "ParallelWithSharedLock"    (expectFailure
                                                        prop_ticketDispenserParallelBad)
      , testProperty "2-ParallelWithExclusiveLock" (prop_ticketDispenserNParallelOK 2)
      , testProperty "3-ParallelWithExclusiveLock" (prop_ticketDispenserNParallelOK 3)
      , testProperty "4-ParallelWithExclusiveLock" (prop_ticketDispenserNParallelOK 4)
      , testProperty "3-ParallelWithSharedLock" (expectFailure $
                                                    prop_ticketDispenserNParallelBad 3)
      ]
  , testGroup "Mock"
      [ testProperty "sequential" prop_sequential_mock
      , testProperty "parallel"   prop_parallel_mock
      , testProperty "nparallel"  prop_nparallel_mock
      ]
  , testGroup "CircularBuffer"
      [ testProperty "unpropNoSizeCheck"
          (expectFailure (withMaxSuccess 1000 unpropNoSizeCheck))
      , testProperty "unpropFullIsEmpty"
          (expectFailure (withMaxSuccess 1000 unpropFullIsEmpty))
      , testProperty "unpropBadRem"
          (expectFailure (withMaxSuccess 1000 unpropBadRem))
      , testProperty "unpropStillBadRem"
          (expectFailure (withMaxSuccess 1000 unpropStillBadRem))
      , testProperty "prop_circularBuffer"
          prop_circularBuffer
      ]
  , testGroup "Echo"
      [ testProperty "Sequential" prop_echoOK
      , testProperty "ParallelOk" (prop_echoParallelOK False)
      , testProperty "ParallelBad" -- See issue #218.
          (expectFailure (prop_echoParallelOK True))
      , testProperty "2-Parallel" (prop_echoNParallelOK 2 False)
      , testProperty "3-Parallel" (prop_echoNParallelOK 3 False)
      , testProperty "Parallel bad, 2 threads, see issue #218"
          (expectFailure (prop_echoNParallelOK 2 True))
      , testProperty "Parallel bad, 3 threads, see issue #218"
          (expectFailure (prop_echoNParallelOK 3 True))
      ]
  , testGroup "ProcessRegistry"
      [ testProperty "Sequential" (prop_processRegistry (statsDb "processRegistry"))
      ]
  , testGroup "UnionFind"
      [ testProperty "Sequential" UnionFind.prop_unionFindSequential ]
  , testGroup "Lockstep"
      [ testProperty "IORefs_Sequential" prop_IORefs_sequential
      ]
  ]
  where
    statsDb :: PropertyName -> StatsDb IO
    statsDb = fileStatsDb "/tmp/stats-db"

    webServer docker bug port test prop
      | docker    = withResource (WS.setup bug WS.connectionString port) WS.cleanup
                     (const (testProperty test (prop port)))
      | otherwise = testCase ("No docker or running on CI, skipping: " ++ test) (return ())

    dataBase docker test prop
      | docker    = withResource Store.setup
                                 Store.cleanup
                                 (\io -> testProperty test (prop (snd <$> io)))
      | otherwise = testCase ("No docker, skipping: " ++ test) (return ())

    whenDocker docker test prop
      | docker    = prop
      | otherwise = testCase ("No docker, skipping: " ++ test) (return ())

------------------------------------------------------------------------

main :: IO ()
main = do
  -- Check if docker is avaiable.
  ec <- rawSystemNoStdout "docker" ["version"]
          `catch` (\(_ :: IOError) -> return (ExitFailure 127))
  let docker = case ec of
                 ExitSuccess   -> True
                 ExitFailure _ -> False
  defaultMain (tests docker)
    where
      rawSystemNoStdout cmd args =
        withCreateProcess
          (proc cmd args) { std_out = CreatePipe }
          (\_ _ _ -> waitForProcess)
