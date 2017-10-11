module CircularBufferSpec (spec) where

import           Test.Hspec
                   (Spec, describe, it)
import           Test.Hspec.QuickCheck
import           Test.QuickCheck
                   (expectFailure)

import           CircularBuffer

spec :: Spec
spec =

  modifyMaxSuccess (const 500) $

    describe "Sequential property" $ do

      it "`unpropNoSizeCheck`: the first bug is found" $
        expectFailure unpropNoSizeCheck

      it "`unpropFullIsEmpty`: the second bug is found" $
        expectFailure unpropFullIsEmpty

      it "`unpropBadRem`: the third bug is found" $
        expectFailure unpropBadRem

      it "`unpropStillBadRem`: the fourth bug is found" $
        expectFailure unpropStillBadRem

      it "`prop_circularBuffer`: the fixed version is correct"
        prop_circularBuffer
