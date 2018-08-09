module Main where

import           Test.Tasty
import           Test.Tasty.QuickCheck

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
  ]

------------------------------------------------------------------------

main :: IO ()
main = defaultMain tests
