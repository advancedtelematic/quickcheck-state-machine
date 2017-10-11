module CrudWebserverDbSpec where

import           Test.Hspec
                   (Spec, around_, describe, it)
import           Test.Hspec.QuickCheck
                   (modifyMaxSuccess)

import           CrudWebserverDb

------------------------------------------------------------------------

spec :: Spec
spec = do

  around_ withCrudWebserverDb $ modifyMaxSuccess (const 10) $

    describe "Sequential property" $

      it "`prop_crudWebserverDb`: sequential property holds"
        prop_crudWebserverDb

  around_ withCrudWebserverDbParallel $ modifyMaxSuccess (const 3) $

    describe "Parallel property" $

      it "`prop_crudWebserverDbParallel`: parallel property holds"
        prop_crudWebserverDbParallel
