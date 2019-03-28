{-# LANGUAGE ScopedTypeVariables #-}

module Main (main) where

import           Control.Exception
                   (ErrorCall(ErrorCall), Exception, catch)
import           Data.List
                   (isPrefixOf)
import           Prelude
import           System.Environment
                   (lookupEnv)
import           System.Exit
                   (ExitCode(..))
import           System.Process
                   (StdStream(CreatePipe), proc, std_out,
                   waitForProcess, withCreateProcess)
import           Test.DocTest
                   (doctest)
import           Test.QuickCheck
                   (sample)
import           Test.Tasty
                   (TestTree, defaultMain, testGroup, withResource)
import           Test.Tasty.HUnit
                   (assertFailure, testCase)
import           Test.Tasty.QuickCheck
                   (expectFailure, ioProperty, testProperty,
                   withMaxSuccess)

import           CircularBuffer
import qualified CrudWebserverDb          as WS
import           DieHard
import           Echo
import           ErrorEncountered
import           MemoryReference
import           ProcessRegistry
import qualified ShrinkingProps
import           Test.StateMachine.Markov
import           TicketDispenser
import qualified UnionFind

------------------------------------------------------------------------

tests :: Bool -> TestTree
tests docker0 = testGroup "Tests"
  [ testCase "Doctest Z module" (doctest ["src/Test/StateMachine/Z.hs"])
  , ShrinkingProps.tests
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
      [ ticketDispenser "sequential"                   prop_ticketDispenser
      , ticketDispenser "parallel with exclusive lock" (withMaxSuccess 30 .
                                                        prop_ticketDispenserParallelOK)
      , ticketDispenser "parallel with shared lock"    (expectFailure .
                                                        prop_ticketDispenserParallelBad)
      ]
  , testGroup "Circular buffer"
      [ testProperty "`unpropNoSizeCheck`: the first bug is found"
          (expectFailure unpropNoSizeCheck)
      , testProperty "`unpropFullIsEmpty`: the second bug is found"
          (expectFailure unpropFullIsEmpty)
      , testProperty "`unpropBadRem`: the third bug is found"
          (expectFailure (withMaxSuccess 1000 unpropBadRem))
      , testProperty "`unpropStillBadRem`: the fourth bug is found"
          (expectFailure unpropStillBadRem)
      , testProperty "`prop_circularBuffer`: the fixed version is correct"
          prop_circularBuffer
      ]
  , testGroup "Echo"
      [ testProperty "sequential"  (ioProperty (prop_echoOK <$> mkEnv))
      , testProperty "parallel ok" (ioProperty (prop_echoParallelOK False <$> mkEnv))
      , testProperty "parallel bad, see issue #218"
          (expectFailure (ioProperty (prop_echoParallelOK True <$> mkEnv)))
      ]
  , testGroup "ProcessRegistry"
      [ testProperty "sequential" (prop_processRegistry markovGood)
      , testCase "markovDeadlock"
          (assertException (\(ErrorCall err) -> "\nA deadlock" `isPrefixOf` err)
            (sample (generateMarkov sm markovDeadlock initState)))
      , testCase "markovNotStochastic1"
          (assertException (\(ErrorCall err) -> "The probabilities" `isPrefixOf` err)
            (sample (generateMarkov sm markovNotStochastic1 initState)))
      , testCase "markovNotStochastic2"
          (assertException (\(ErrorCall err) -> "The probabilities" `isPrefixOf` err)
            (sample (generateMarkov sm markovNotStochastic2 initState)))
      , testCase "markovNotStochastic3"
          (assertException (\(ErrorCall err) -> "The probabilities" `isPrefixOf` err)
            (sample (generateMarkov sm markovNotStochastic3 initState)))
      ]
  , testGroup "Union Find"
      [ testProperty "sequential" UnionFind.prop_unionFind_sequential
      , testProperty "parallel"   UnionFind.prop_unionFind_parallel
      ]
  ]
  where
    webServer docker bug port test prop
      | docker    = withResource (WS.setup bug WS.connectionString port) WS.cleanup
                     (const (testProperty test (prop port)))
      | otherwise = testCase ("No docker, skipping: " ++ test) (return ())

    ticketDispenser test prop =
      withResource setupLock cleanupLock
        (\ioLock -> testProperty test (ioProperty (prop <$> ioLock)))

    assertException :: Exception e => (e -> Bool) -> IO a -> IO ()
    assertException p io = do
      r <- (io >> return False) `catch` (return . p)
      if r
      then return ()
      else assertFailure "assertException: No or wrong exception thrown"

------------------------------------------------------------------------

main :: IO ()
main = do

  -- Check if docker is avaiable.
  ec <- rawSystemNoStdout "docker" ["version"]
          `catch` (\(_ :: IOError) -> return (ExitFailure 127))
  let docker = case ec of
                 ExitSuccess   -> True
                 ExitFailure _ -> False

  -- Check if we are running on CI (this environment variable is set by Travis).
  ci <- (== Just "true") <$> lookupEnv "CONTINUOUS_INTEGRATION"

  -- Only run tests involving docker when we are not on CI, as they are flaky.
  defaultMain (tests (docker && not ci))
    where
      rawSystemNoStdout cmd args =
        withCreateProcess
          (proc cmd args) { std_out = CreatePipe }
          (\_ _ _ -> waitForProcess)
