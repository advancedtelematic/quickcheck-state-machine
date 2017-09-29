module CrudWebserverDbSpec where

import           Test.Hspec
                   (Spec, describe, it)
import           Test.Hspec.QuickCheck
                   (modifyMaxSuccess)

import           CrudWebserverDb

------------------------------------------------------------------------

spec :: Spec
spec = do

  modifyMaxSuccess (const 10) $

    describe "Sequential property" $

      it "`prop_crudWebserverDb`: sequential property holds" $
        prop_crudWebserverDb

  modifyMaxSuccess (const 3) $

    describe "Parallel property" $

      it "`prop_crudWebserverDbParallel`: parallel property holds"
        prop_crudWebserverDbParallel
