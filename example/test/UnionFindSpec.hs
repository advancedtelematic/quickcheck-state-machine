module UnionFindSpec (spec) where

import           Test.Hspec
                   (Spec, describe, it)

import           UnionFind

------------------------------------------------------------------------

spec :: Spec
spec =
  describe "Sequential property" $ do
    it "`prop_sequential`: invariants hold" $
      prop_sequential
