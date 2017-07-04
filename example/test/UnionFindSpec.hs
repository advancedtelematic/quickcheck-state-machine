module UnionFindSpec (spec) where

import           Test.Hspec
                   (Spec, describe, it)

import           UnionFind

------------------------------------------------------------------------

spec :: Spec
spec =
  describe "Sequential property" $
    it "`prop_unionFind`: invariants hold"
      prop_unionFind
