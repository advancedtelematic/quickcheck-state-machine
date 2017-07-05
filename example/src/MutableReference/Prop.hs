{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  MutableReference.Prop
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-----------------------------------------------------------------------------

module MutableReference.Prop where

import           Control.Arrow
                   ((&&&))
import           Control.Monad
                   (void)
import           Data.Char
                   (isSpace)
import           Data.Dynamic
                   (cast)
import           Data.List
                   (isSubsequenceOf)
import           Data.Tree
                   (Tree(Node), unfoldTree)
import           Test.QuickCheck
                   (Property, forAll)
import           Text.ParserCombinators.ReadP
                   (string)
import           Text.Read
                   (choice, lift, readListPrec, readListPrecDefault,
                   readPrec)

import           Test.StateMachine
import           Test.StateMachine.Internal.AlphaEquality
import           Test.StateMachine.Internal.Parallel
import           Test.StateMachine.Internal.ScopeCheck
import           Test.StateMachine.Internal.Sequential
                   (liftGen)
import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Internal.Utils

import           MutableReference

------------------------------------------------------------------------

prop_genScope :: Property
prop_genScope = forAll
  (fst <$> liftGen generator precondition transition initModel 0)
  scopeCheck

prop_genForkScope :: Property
prop_genForkScope = forAll
  (liftGenFork generator precondition transition initModel)
  scopeCheckFork

prop_sequentialShrink :: Property
prop_sequentialShrink = shrinkPropertyHelper (prop_references Bug) $ alphaEq
  (Program [ Internal New                   sym0
           , Internal (Write (Ref sym0)  5) (Symbolic (Var 1))
           , Internal (Read  (Ref sym0))    (Symbolic (Var 2))
           ])
  . read . (!! 1) . lines
  where
  sym0 = Symbolic (Var 0)

cheat :: Fork (Program Action) -> Fork (Program Action)
cheat = fmap (Program . map (\iact -> case iact of
  Internal (Write ref _) sym -> Internal (Write ref 0) sym
  _                          -> iact) . unProgram)

prop_shrinkForkSubseq :: Property
prop_shrinkForkSubseq = forAll
  (liftGenFork generator precondition transition initModel)
  $ \f@(Fork l p r) ->
    all (\(Fork l' p' r') ->
           void (unProgram l') `isSubsequenceOf` void (unProgram l) &&
           void (unProgram p') `isSubsequenceOf` void (unProgram p) &&
           void (unProgram r') `isSubsequenceOf` void (unProgram r))
        (liftShrinkFork shrink1 precondition transition initModel (cheat f))

prop_shrinkForkScope :: Property
prop_shrinkForkScope = forAll
  (liftGenFork generator precondition transition initModel) $ \f ->
    all scopeCheckFork (liftShrinkFork shrink1 precondition transition initModel f)

------------------------------------------------------------------------

prop_shrinkForkMinimal :: Property
prop_shrinkForkMinimal = shrinkPropertyHelper (prop_referencesParallel RaceCondition) $ \out ->
  let f = read $ dropWhile isSpace (lines out !! 1)
  in hasMinimalShrink f || isMinimal f
  where
  hasMinimalShrink :: Fork (Program Action) -> Bool
  hasMinimalShrink
    = anyTree isMinimal
    . unfoldTree (id &&& liftShrinkFork shrink1 precondition transition initModel)
    where
    anyTree :: (a -> Bool) -> Tree a -> Bool
    anyTree p = foldTree (\x ih -> p x || or ih)
      where
      -- `foldTree` is part of `Data.Tree` in later versions of `containers`.
      foldTree :: (a -> [b] -> b) -> Tree a -> b
      foldTree f = go where
        go (Node x ts) = f x (map go ts)

  isMinimal :: Fork (Program Action) -> Bool
  isMinimal xs = any (alphaEqFork xs) minimal

  minimal :: [Fork (Program Action)]
  minimal  = minimal' ++ map mirrored minimal'
    where
    minimal' = [ Fork (Program [w0, Internal (Read ref0) (Symbolic var1)])
                      (Program [Internal New (Symbolic var0)])
                      (Program [w1])
               | w0 <- writes
               , w1 <- writes
               ]

    mirrored :: Fork a -> Fork a
    mirrored (Fork l p r) = Fork r p l

    var0   = Var 0
    var1   = Var 1
    ref0   = Ref (Symbolic var0)

    writes =
      [ Internal (Write ref0 0) (Symbolic var1)
      , Internal (Inc   ref0)   (Symbolic var1)
      ]

instance Read (Ref Symbolic) where
  readPrec     = Ref . Symbolic <$> readPrec
  readListPrec = readListPrecDefault

instance Read (Internal Action) where

  readPrec = choice
    [ Internal <$> (New   <$ lift (string "New"))  <*> readPrec
    , Internal <$> (Read  <$ lift (string "Read")  <*> readPrec) <*> readPrec
    , Internal <$> (Write <$ lift (string "Write") <*> readPrec <*> readPrec) <*> readPrec
    , Internal <$> (Inc   <$ lift (string "Inc")   <*> readPrec) <*> readPrec
    ]

  readListPrec = readListPrecDefault

instance Eq (Internal Action) where
  Internal act1 sym1 == Internal act2 sym2 =
    cast act1 == Just act2 && cast sym1 == Just sym2
