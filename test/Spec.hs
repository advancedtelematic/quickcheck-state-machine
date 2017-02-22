module Main where

import           Test.Hspec

import           Test.QuickCheck.Example

------------------------------------------------------------------------

main :: IO ()
main = hspec $ do

  describe "liftGenFork" $
    it "generates well-scoped programs"
      prop_genScope

  describe "sequentialProperty" $ do

    it "returns a property that passes when there are no bugs" $
      prop_safety None

    it "always shrinks to the minimal counterexample when there's a bug"
      prop_sequentialShrink

  describe "liftShrinkFork" $ do

    it "shrinks into subsequences"
      prop_shrinkForkSubseq

    it "shrinks into well-scoped programs"
      prop_shrinkForkScope

  describe "parallelProperty" $ do

    it "returns a property that passes when there are no race conditions" $ do
      prop_parallel None

    xit "always shrinks to one of the minimal counter examples when there's a race condition"
      prop_shrinkForkMinimal
