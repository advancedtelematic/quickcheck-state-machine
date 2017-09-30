{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE StandaloneDeriving #-}

module DieHardSpec (spec) where

import           Data.List
                   (find)
import           Data.Typeable
                   (cast)
import           Test.Hspec
                   (Spec, describe, it, shouldBe)
import           Test.QuickCheck
                   (Property, label, property)

import           DieHard
import           Test.StateMachine
import           Test.StateMachine.Internal.AlphaEquality
import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Internal.Utils

------------------------------------------------------------------------

validSolutions :: [[Action v ()]]
validSolutions =
  [ [ FillBig
    , BigIntoSmall
    , EmptySmall
    , BigIntoSmall
    , FillBig
    , BigIntoSmall
    ]
  , [ FillSmall
    , SmallIntoBig
    , FillSmall
    , SmallIntoBig
    , EmptyBig
    , SmallIntoBig
    , FillSmall
    , SmallIntoBig
    ]
  , [ FillSmall
    , SmallIntoBig
    , FillSmall
    , SmallIntoBig
    , EmptySmall
    , BigIntoSmall
    , EmptySmall
    , BigIntoSmall
    , FillBig
    , BigIntoSmall
    ]
  , [ FillBig
    , BigIntoSmall
    , EmptyBig
    , SmallIntoBig
    , FillSmall
    , SmallIntoBig
    , EmptyBig
    , SmallIntoBig
    , FillSmall
    , SmallIntoBig
    ]
  ]

testValidSolutions :: Bool
testValidSolutions = all ((/= 4) . bigJug . run) validSolutions
  where
  run = foldr (\c s -> transitions s c (Concrete ())) initModel

prop_bigJug4 :: Property
prop_bigJug4 = shrinkPropertyHelperC' prop_dieHard $ \prog ->
  case find (alphaEq prog)
         (map (Program . map (flip Internal (Symbolic (Var 0)))) validSolutions) of
    Nothing -> property False
    Just ex -> label (show ex) (property True)

------------------------------------------------------------------------

spec :: Spec
spec =

  describe "Sequential property" $ do

    it "`testValidSolutions`: `validSolutions` are valid solutions" $
      testValidSolutions `shouldBe` True

    it "`prop_bigJug4`: in most cases, the smallest solution is found"
      prop_bigJug4

------------------------------------------------------------------------

deriving instance Eq (Action v a)

instance Eq (Untyped Action) where
  a == b = cast a == Just b
