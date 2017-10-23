module CrudWebserverDbRaceSpec where

import           Test.Hspec
                   (Spec, around_, describe, it, xit)
import           Test.Hspec.QuickCheck
                   (modifyMaxSuccess)

import           CrudWebserverDbRace

------------------------------------------------------------------------

spec :: Spec
spec = do

  around_ (withCrudWebserverDbRace None) $ modifyMaxSuccess (const 10) $

    describe "Sequential property" $

      it "`prop_crudWebserverDbRace`: sequential property holds"
        prop_crudWebserverDbRace

  around_ (withCrudWebserverDbRaceParallel Race) $ modifyMaxSuccess (const 3) $

    describe "Parallel property" $

      xit "`prop_dbShrinkRace`: shrinking finds minimal counterexample" $
        prop_dbShrinkRace
