{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE StandaloneDeriving #-}

module DieHardSpec (spec) where

import           Data.List               (find)
import           Data.Singletons.Prelude (ConstSym1)
import           Test.Hspec
import           Test.QuickCheck         (Property, label, property)

import           DieHard
import           Test.StateMachine.Types
import           Test.StateMachine.Utils

------------------------------------------------------------------------

deriving instance Show (Step resp refs)

------------------------------------------------------------------------

validSolutions :: [[Step ('Response ()) (ConstSym1 ())]]
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
  run = foldr (\c s -> transitions s c ()) initState

prop_bigJug4 :: Property
prop_bigJug4 = shrinkPropertyHelper' prop_dieHard $ \output ->
  let counterExample = lines output !! 1 in
  case find (== counterExample) (map show validSolutions) of
    Nothing -> property False
    Just ex -> label ex (property True)

------------------------------------------------------------------------

spec :: Spec
spec = do

  describe "Sequential property" $ do

    it "`testValidSolutions`: `validSolutions` are valid solutions" $
      testValidSolutions `shouldBe` True

    it "`prop_bigJug4`: in most cases, the smallest solution is found"
      prop_bigJug4
