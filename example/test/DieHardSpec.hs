module DieHardSpec (spec) where

import           Test.Hspec

import           DieHard

------------------------------------------------------------------------

spec :: Spec
spec = do

  describe "Sequential property" $

    it "`prop_bigJug4`: in most cases, we find the smallest solution"
      prop_bigJug4
