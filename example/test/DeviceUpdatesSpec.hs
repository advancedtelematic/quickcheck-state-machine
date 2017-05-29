module DeviceUpdatesSpec (spec) where

import           Test.Hspec
                   (Spec, describe, it)

import           DeviceUpdates

------------------------------------------------------------------------

spec :: Spec
spec =
  describe "Sequential property" $ do
    it "`prop_sequential`: the model is sound"
      prop_sequential
