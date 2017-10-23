module MutableReferenceSpec (spec) where

import           Test.Hspec
                   (Spec, describe, it, xit)
import           Test.Hspec.QuickCheck
                   (modifyMaxSuccess)

import           HspecInstance
                   ()
import           MutableReference
import           MutableReference.Prop

------------------------------------------------------------------------

spec :: Spec
spec = do

  describe "Generation" $ do

    it "`prop_genScope`: generate well-scoped programs"
      prop_genScope

    it "`prop_genParallelScope`: generate well-scoped parallel programs"
      prop_genParallelScope

    it "`prop_genParallelSequence`: generate parallel programs where the symbolic references form a sequence"
      prop_genParallelSequence

  describe "Sequential property" $ do

    it "`prop_references None`: pre- and post-conditions hold when there are no bugs" $
      prop_references None

    it "`prop_sequentialShrink`: the minimal counterexample is found when there's a bug"
      prop_sequentialShrink

  describe "Shrinking" $

    modifyMaxSuccess (const 20) $ do

      it "`prop_shrinkParallelSubseq`: shrinking parallel programs preserves subsequences"
        prop_shrinkParallelSubseq

      it "`prop_shrinkParallelScope`: shrinking parallel programs preserves scope"
        prop_shrinkParallelScope

  describe "Parallel property" $

    modifyMaxSuccess (const 10) $ do

      it "`prop_referencesParallel None`: linearisation is possible when there are no race conditions" $
        prop_referencesParallel None

      xit "`prop_shrinkParallelMinimal`: the minimal counterexample is found when there's a race condition"
        prop_shrinkParallelMinimal
