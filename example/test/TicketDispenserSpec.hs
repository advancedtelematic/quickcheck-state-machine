module TicketDispenserSpec (spec) where

import           Test.Hspec
                   (Spec, describe, it, xit)

import           TicketDispenser

------------------------------------------------------------------------

spec :: Spec
spec = do

  describe "Sequential property" $
    it "`prop_sequential`: the model is sequentially sound" $
      prop_sequential

  describe "Parallel property" $ do

    it "`prop_parallelOK`: works with exclusive file locks" $
      prop_parallelOK

    xit "`prop_parallelBad`: breaks with shared file locks (see #87)" $
      prop_parallelBad
