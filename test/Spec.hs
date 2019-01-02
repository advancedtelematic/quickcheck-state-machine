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
                   (expectFailure, ioProperty, testProperty,
                   withMaxSuccess)

import           CircularBuffer
import qualified CrudWebserverDb       as WS
import           DieHard
import           Echo
import           ErrorEncountered
import           MemoryReference
import           TicketDispenser

------------------------------------------------------------------------

tests :: Bool -> TestTree
tests docker0 = testGroup "Tests"
  [ testCase "Doctest Z module" (doctest ["src/Test/StateMachine/Z.hs"])
  , testProperty "Die Hard"
      (expectFailure (withMaxSuccess 2000 prop_dieHard))
  , testGroup "Memory reference"
      [ testProperty "No bug"                             (prop_sequential None)
      , testProperty "Logic bug"           (expectFailure (prop_sequential Logic))
      , testProperty "Race bug sequential"                (prop_sequential Race)
      , testProperty "Race bug parallel"   (expectFailure (prop_parallel   Race))
      , testProperty "Precondition failed" prop_precondition
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
  ]
  where
    webServer docker bug port test prop
      | docker    = withResource (WS.setup bug WS.connectionString port) WS.cleanup
                     (const (testProperty test (prop port)))
      | otherwise = testCase ("No docker, skipping: " ++ test) (return ())

    ticketDispenser test prop =
      withResource setupLock cleanupLock
        (\ioLock -> testProperty test (ioProperty (prop <$> ioLock)))

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
