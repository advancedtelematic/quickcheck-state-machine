module CrudWebserverFileSpec where

import           Test.Hspec
                   (Spec, describe, xit)

import           CrudWebserverFile

------------------------------------------------------------------------

spec :: Spec
spec = do

  describe "Sequential property" $

    xit "`prop_crudWebserverFile`: sequential property holds"
      prop_crudWebserverFile

  describe "Parallel property" $

    xit "`prop_crudWebserverFileParallel`: parallel property holds"
      prop_crudWebserverFileParallel
