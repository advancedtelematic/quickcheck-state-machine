module CrudWebserverDbSpec where

import           Test.Hspec
                   (Spec, describe, it)
import           Test.Hspec.QuickCheck
                   (modifyMaxSuccess)

import           CrudWebserverDb

------------------------------------------------------------------------

spec :: Spec
spec = do

  describe "CrudWebserverDbSpec: sequential property" $

    modifyMaxSuccess (const 50) $ do

      it "`prop_crudWebserverDb`: sequential property holds if there isn't any bug" $
        demoNoBug' 48083

      it "`prop_crudWebserverDb`: sequential property fails if there is a bug" $
        demoLogicBug' 48084

      it "`prop_crudWebserverDb`: sequential property can't catch race condition" $
        demoNoRace' 48085

  describe "CrudWebserverDbSpec: parallel property" $ do

    modifyMaxSuccess (const 50) $
      it "`prop_crudWebserverDbParallel`: parallel property finds race condition" $
        demoRace' 48086

    modifyMaxSuccess (const 5) $
      it "`prop_dbShrinkRace`: shrinking finds minimal counterexample" $
        (prop_dbShrinkRace 48087)
