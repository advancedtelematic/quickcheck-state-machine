module Main (main) where

import           Prelude
import           Test.Tasty
import           Test.Tasty.QuickCheck

import           CircularBuffer
import qualified CrudWebserverDb       as WS
import           DieHard
import           MemoryReference
import           TicketDispenser

------------------------------------------------------------------------

tests :: TestTree
tests = testGroup "Tests"
  [ testProperty "Die Hard"
      (expectFailure (withMaxSuccess 1000 prop_dieHard))
  , testGroup "Memory reference"
      [ testProperty "No bug"                             (prop_sequential None)
      , testProperty "Logic bug"           (expectFailure (prop_sequential Logic))
      , testProperty "Race bug sequential"                (prop_sequential Race)
      , testProperty "Race bug parallel"   (expectFailure (prop_parallel   Race))
      ]
  , testGroup "Crud webserver"
      [ webServer WS.None  8800 "No bug"                       WS.prop_crudWebserverDb
      , webServer WS.Logic 8801 "Logic bug"   (expectFailure . WS.prop_crudWebserverDb)
      , webServer WS.Race  8802 "No race bug"                  WS.prop_crudWebserverDb
      , webServer WS.Race  8803 "Race bug"    (expectFailure . WS.prop_crudWebserverDbParallel)
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
          (expectFailure unpropBadRem)
      , testProperty "`unpropStillBadRem`: the fourth bug is found"
          (expectFailure unpropStillBadRem)
      , testProperty "`prop_circularBuffer`: the fixed version is correct"
          prop_circularBuffer
      ]
  ]
  where
    webServer bug port test prop =
      withResource (WS.setup bug WS.connectionString port) WS.cleanup
        (const (testProperty test (prop port)))

    ticketDispenser test prop =
      withResource setupLock cleanupLock
        (\ioLock -> testProperty test (ioProperty (prop <$> ioLock)))

------------------------------------------------------------------------

main :: IO ()
main = defaultMain tests
