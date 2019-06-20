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

import           CircularBuffer
import qualified CrudWebserverDb          as WS
import           DieHard
import           Echo
import           ErrorEncountered
import           Hanoi
import           MemoryReference
import           ProcessRegistry
import qualified ShrinkingProps
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
      [testProperty  "NoBugSeq"                         (prop_sequential None)
      , testProperty "LogicBug"          (expectFailure (prop_sequential Logic))
      , testProperty "RaceBugSequential"                (prop_sequential Race)
      , testProperty "NoBugParallel"                    (prop_parallel None)
      , testProperty "RaceBugParallel"   (expectFailure (prop_parallel   Race))
      , testProperty "CrashBugParallel"                 (prop_parallel'  Crash)
      , testProperty "CrashAndLogicBugParallel"
          (expectFailure (withMaxSuccess 3000 (prop_parallel' CrashAndLogic)))
      , testProperty "PreconditionFailed" prop_precondition
      , testProperty "ExistsCommands"     prop_existsCommands
      , testProperty "NoBug 1 thread"            (prop_nparallel None 1)
      , testProperty "NoBug 2 threads"           (prop_nparallel None 2)
      , testProperty "NoBug 3 threads"           (withMaxSuccess 80 $ prop_nparallel None 3)
      , testProperty "NoBug 4 threads"           (withMaxSuccess 40 $ prop_nparallel None 4)
      , testProperty "RaceBugParalleel 1 thread"  (prop_nparallel Race 1)
      , testProperty "RaceBugParalleel 2 threads" (expectFailure (prop_nparallel   Race 2))
      , testProperty "RaceBugParalleel 3 threads" (expectFailure (prop_nparallel   Race 3))
      , testProperty "RaceBugParalleel 4 threads" (expectFailure (prop_nparallel   Race 4))
      , testProperty "ShrinkParallelEquivalence" prop_pairs_shrink_parallel_equivalence
      , testProperty "ShrinkAndValidateParallelEquivalence" prop_pairs_shrinkAndValidate_equivalence
      , testProperty "ShrinkPairsEquialence"     prop_pairs_shrink_parallel
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
  ]
  where
    statsDb :: PropertyName -> StatsDb IO
    statsDb = fileStatsDb "/tmp/stats-db"

    webServer docker bug port test prop
      | docker    = withResource (WS.setup bug WS.connectionString port) WS.cleanup
                     (const (testProperty test (prop port)))
      | otherwise = testCase ("No docker or running on CI, skipping: " ++ test) (return ())

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
