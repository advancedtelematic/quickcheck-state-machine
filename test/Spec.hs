module Main where

import           Test.Hspec
import           Test.Hspec.QuickCheck

import           Test.QuickCheck.StateMachineModel.Example

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

    modifyMaxSuccess (const 20) $ do

      it "shrinks into subsequences"
        prop_shrinkForkSubseq

      it "shrinks into well-scoped programs"
        prop_shrinkForkScope

  describe "parallelProperty" $ do

    modifyMaxSuccess (const 10) $ do

      it "returns a property that passes when there are no race conditions" $ do
        prop_parallel None

      it "always shrinks to one of the minimal counter examples when there's a race condition"
        prop_shrinkForkMinimal
