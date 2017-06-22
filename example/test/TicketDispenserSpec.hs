module TicketDispenserSpec (spec) where

import           Test.Hspec
                   (Spec, describe, it)
import           Test.Hspec.QuickCheck
                   (modifyMaxSuccess)

import           TicketDispenser

------------------------------------------------------------------------

spec :: Spec
spec = do

  describe "Sequential property" $
    it "`prop_sequential`: the model is sequentially sound" $
      prop_sequential

  describe "Parallel property" $ do

    modifyMaxSuccess (const 10) $ do

      it "`prop_parallelOK`: works with exclusive file locks" $
        prop_parallelOK

    it "`prop_parallelBad`: smallest counterexample is found when file locks are shared" $
      prop_parallelBad
