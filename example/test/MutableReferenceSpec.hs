module MutableReferenceSpec (spec) where

import           Test.Hspec
                   (Spec, describe, it, xit)
import           Test.Hspec.QuickCheck
                   (modifyMaxSuccess)
import           Test.QuickCheck (property)

import           MutableReference
import           MutableReference.Prop

------------------------------------------------------------------------

spec :: Spec
spec = do

  describe "Generation" $ do

    it "`prop_genScope`: generate well-scoped programs"
      prop_genScope

    it "`prop_genForkScope`: generate well-scoped parallel programs"
      prop_genForkScope

  describe "Sequential property" $ do

    it "`prop_references None`: pre- and post-conditions hold when there are no bugs" $
      prop_references None

    it "`prop_sequentialShrink`: the minimal counterexample is found when there's a bug"
      prop_sequentialShrink

  describe "Shrinking" $

    modifyMaxSuccess (const 20) $ do

      it "`prop_shrinkForkSubseq`: shrinking parallel programs preserves subsequences"
        prop_shrinkForkSubseq

      it "`prop_shrinkForkScope`: shrinking parallel programs preserves scope"
        prop_shrinkForkScope

  describe "Parallel property" $

    modifyMaxSuccess (const 10) $ do

      it "`prop_referencesParallel None`: linearisation is possible when there are no race conditions" $
        prop_referencesParallel None

      it "`prop_shrinkForkMinimal`: the minimal counterexample is found when there's a race condition"
        prop_shrinkForkMinimal
