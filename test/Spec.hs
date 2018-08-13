module Main (main) where

import           Prelude
import           Test.Tasty
import           Test.Tasty.QuickCheck

import qualified CrudWebserverDb as WS
import           DieHard
import           MemoryReference

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
  ]
  where
    webServer bug port test prop =
      withResource (WS.setup bug WS.connectionString port) WS.cleanup
        (const (testProperty test (prop port)))

------------------------------------------------------------------------

main :: IO ()
main = defaultMain tests
