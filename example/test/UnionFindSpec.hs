module UnionFindSpec (spec) where

import           Test.Hspec
                   (Spec, describe, xit)

import           UnionFind

------------------------------------------------------------------------

spec :: Spec
spec =
  describe "Sequential property" $ do
    xit "`prop_unionFind`: invariants hold" $
      prop_unionFind
