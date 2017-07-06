{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}

module DieHardSpec (spec) where

import           Data.List
                   (find)
import           Test.Hspec
                   (Spec, describe, it, shouldBe)
import           Test.QuickCheck
                   (Property, label, property)
import           Text.ParserCombinators.ReadP
                   (string)
import           Text.Read
                   (choice, lift, readListPrec, readListPrecDefault,
                   readPrec)

import           DieHard
import           Test.StateMachine
import           Test.StateMachine.Internal.Utils
import           Test.StateMachine.Internal.AlphaEquality
import           Test.StateMachine.Internal.Types

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
  let counterExample :: Program Action
      counterExample = read $ lines output !! 1
  in
  case find (alphaEq counterExample)
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

instance Read (Internal Action) where

  readPrec = choice
    [ Internal <$> (FillBig      <$ lift (string "FillBig"))      <*> readPrec
    , Internal <$> (FillSmall    <$ lift (string "FillSmall"))    <*> readPrec
    , Internal <$> (EmptyBig     <$ lift (string "EmptyBig"))     <*> readPrec
    , Internal <$> (EmptySmall   <$ lift (string "EmptySmall"))   <*> readPrec
    , Internal <$> (SmallIntoBig <$ lift (string "SmallIntoBig")) <*> readPrec
    , Internal <$> (BigIntoSmall <$ lift (string "BigIntoSmall")) <*> readPrec
    ]

  readListPrec = readListPrecDefault

instance Eq (Internal Action) where
  Internal FillBig      _ == Internal FillBig      _ = True
  Internal FillSmall    _ == Internal FillSmall    _ = True
  Internal EmptyBig     _ == Internal EmptyBig     _ = True
  Internal EmptySmall   _ == Internal EmptySmall   _ = True
  Internal SmallIntoBig _ == Internal SmallIntoBig _ = True
  Internal BigIntoSmall _ == Internal BigIntoSmall _ = True
  _                       == _                       = False
