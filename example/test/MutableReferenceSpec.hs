module MutableReferenceSpec (spec) where

import           Test.Hspec
import           Test.Hspec.QuickCheck

import           MutableReference

------------------------------------------------------------------------

spec :: Spec
spec = do

  describe "Generation" $ do

    it "`prop_genScope`: generate well-scoped programs"
      prop_genScope

    it "`prop_genForkScope`: generate well-scoped parallel programs"
      prop_genForkScope

  describe "Sequential property" $ do

    it "`prop_safety None`: pre- and post-conditions hold when there are no bugs" $
      prop_safety None

    it "`prop_sequentialShrink`: the minimal counterexample is found when there's a bug"
      prop_sequentialShrink

  describe "Shrinking" $ do

    modifyMaxSuccess (const 20) $ do

      it "`prop_shrinkForkSubseq`: shrinking parallel programs preserves subsequences"
        prop_shrinkForkSubseq

      it "`prop_shrinkForkScope`: shrinking parallel programs preserves scope"
        prop_shrinkForkScope

  describe "Parallel property" $ do

    modifyMaxSuccess (const 10) $ do

      it "`prop_parallel None`: linearisation is possible when there are no race conditions" $ do
        prop_parallel None

      it "`prop_shrinkForkMinimal`: the minimal counterexample is found when there's a race condition"
        prop_shrinkForkMinimal
