module CrudWebserverFileSpec where

import           Test.Hspec
                   (Spec, describe, it, xit)

import           CrudWebserverFile

------------------------------------------------------------------------

spec :: Spec
spec = do

  describe "Sequential property" $ do

    it "`prop_crudWebserverFile`: sequential property holds" $
      prop_crudWebserverFile

  describe "Parallel property" $ do

    xit "`prop_crudWebserverFileParallel`: parallel property fails, because of file handle's busy" $
      prop_crudWebserverFileParallel
