{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}

module DieHardSpec (spec) where

import           Data.Functor.Classes
                   (Eq1(..))
import           Data.Dynamic
                   (cast)
import           Data.List
                   (find)
import           Test.Hspec
                   (Spec, describe, it, shouldBe)
import           Test.QuickCheck
                   (Property, label, property)
import           Text.ParserCombinators.ReadP
                   (string)
import           Text.Read
                   (choice, lift, parens, readListPrec,
                   readListPrecDefault, readPrec)

import           DieHard
import           Test.StateMachine.Internal.Utils
import           Test.StateMachine

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
prop_bigJug4 = shrinkPropertyHelper' prop_dieHard $ \output ->
  let counterExample :: [Untyped Action]
      counterExample = read $ lines output !! 1
  in
  case find (== counterExample) (map (map Untyped) validSolutions) of
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

instance Show (Untyped Action) where
  show (Untyped FillBig)      = "FillBig"
  show (Untyped FillSmall)    = "FillSmall"
  show (Untyped EmptyBig)     = "EmptyBig"
  show (Untyped EmptySmall)   = "EmptySmall"
  show (Untyped SmallIntoBig) = "SmallIntoBig"
  show (Untyped BigIntoSmall) = "BigIntoSmall"

instance Read (Untyped Action) where

  readPrec = choice
    [ Untyped FillBig      <$ lift (string "FillBig")
    , Untyped FillSmall    <$ lift (string "FillSmall")
    , Untyped EmptyBig     <$ lift (string "EmptyBig")
    , Untyped EmptySmall   <$ lift (string "EmptySmall")
    , Untyped SmallIntoBig <$ lift (string "SmallIntoBig")
    , Untyped BigIntoSmall <$ lift (string "BigIntoSmall")
    ]

  readListPrec = readListPrecDefault

instance Eq (Untyped Action) where
  Untyped FillBig      == Untyped FillBig      = True
  Untyped FillSmall    == Untyped FillSmall    = True
  Untyped EmptyBig     == Untyped EmptyBig     = True
  Untyped EmptySmall   == Untyped EmptySmall   = True
  Untyped SmallIntoBig == Untyped SmallIntoBig = True
  Untyped BigIntoSmall == Untyped BigIntoSmall = True
  _                    == _                    = False
