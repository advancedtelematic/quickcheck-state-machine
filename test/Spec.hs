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
  , testProperty "Towers of Hanoi"
      (expectFailure (prop_hanoi 3))
  , testProperty "Die Hard"
      (expectFailure (withMaxSuccess 2000 prop_dieHard))
  , testGroup "MemoryReference"
      [ testProperty "NoBug"                            (prop_sequential None)
      , testProperty "LogicBug"          (expectFailure (prop_sequential Logic))
      , testProperty "RaceBugSequential"                (prop_sequential Race)
      , testProperty "RaceBugParallel"   (expectFailure (prop_parallel   Race))
      , testProperty "PreconditionFailed" prop_precondition
      , testProperty "ExistsCommands"     prop_existsCommands
      ]
  , testGroup "ErrorEncountered"
      [ testProperty "sequential" prop_error_sequential
      , testProperty "parallel"   prop_error_parallel
      ]
  , testGroup "Crud webserver"
      [ webServer docker0 WS.None  8800 "No bug"                       WS.prop_crudWebserverDb
      , webServer docker0 WS.Logic 8801 "Logic bug"   (expectFailure . WS.prop_crudWebserverDb)
      , webServer docker0 WS.Race  8802 "No race bug"                  WS.prop_crudWebserverDb
      , webServer docker0 WS.Race  8803 "Race bug"    (expectFailure . WS.prop_crudWebserverDbParallel)
      ]
  , testGroup "Ticket dispenser"
      [ testProperty "sequential"                   prop_ticketDispenser
      , testProperty "parallel with exclusive lock" (withMaxSuccess 30
                                                        prop_ticketDispenserParallelOK)
      , testProperty "parallel with shared lock"    (expectFailure
                                                        prop_ticketDispenserParallelBad)
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
      [ testProperty "sequential" prop_echoOK
      , testProperty "parallel ok" (prop_echoParallelOK False)
      , testProperty "parallel bad, see issue #218"
          (expectFailure (prop_echoParallelOK True))
      ]
  , testGroup "ProcessRegistry"
      [ testProperty "sequential" prop_processRegistry
      ]
  , testGroup "UnionFind"
      [ testProperty "sequential" UnionFind.prop_unionFindSequential ]
  ]
  where
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
