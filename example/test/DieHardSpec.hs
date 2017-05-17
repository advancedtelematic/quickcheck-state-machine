{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE StandaloneDeriving #-}

module DieHardSpec (spec) where

import           Data.Dynamic                 (cast)
import           Data.List                    (find)
import           Test.Hspec                   (Spec, describe, it, shouldBe)
import           Test.QuickCheck              (Property, label, property)
import           Text.ParserCombinators.ReadP (string)
import           Text.Read                    (choice, lift, parens,
                                               readListPrec,
                                               readListPrecDefault, readPrec)

import           DieHard
import           Test.StateMachine.Types
import           Test.StateMachine.Internal.Utils
import           Test.StateMachine.Internal.Types

------------------------------------------------------------------------

validSolutions :: [[Step ConstIntRef ('Response ())]]
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
  let counterExample = read $ lines output !! 1 in
  case find (== counterExample) (map (map (flip IntRefed ())) validSolutions) of
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

deriving instance Show (Step resp refs)
deriving instance Eq   (Step resp refs)

instance Show (IntRefed Step) where
  show (IntRefed cmd _) = show cmd

instance Eq (IntRefed Step) where
  IntRefed c1 _ == IntRefed c2 _ = Just c1 == cast c2

instance Read (IntRefed Step) where
  readPrec = parens $ choice
    [ IntRefed <$> parens (FillBig      <$ key "FillBig")      <*> readPrec
    , IntRefed <$> parens (FillSmall    <$ key "FillSmall")    <*> readPrec
    , IntRefed <$> parens (EmptyBig     <$ key "EmptyBig")     <*> readPrec
    , IntRefed <$> parens (EmptySmall   <$ key "EmptySmall")   <*> readPrec
    , IntRefed <$> parens (SmallIntoBig <$ key "SmallIntoBig") <*> readPrec
    , IntRefed <$> parens (BigIntoSmall <$ key "BigIntoSmall") <*> readPrec
    ]
    where
    key s = lift (string s)

  readListPrec = readListPrecDefault
