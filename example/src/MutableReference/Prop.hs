{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE StandaloneDeriving #-}

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

import           Control.Monad
                   (void)
import           Data.List
                   (isSubsequenceOf)
  {-
import           Data.Tree
                   (Tree(Node), unfoldTree)
-}
import           Data.Dynamic
                   (cast)
import           Test.QuickCheck
                   (Property, forAll)
import           Text.ParserCombinators.ReadP
                   (string)
import           Text.Read
                   (choice, lift, parens, readListPrec,
                   readListPrecDefault, readPrec)

import           Test.StateMachine.Internal.AlphaEquality
import           Test.StateMachine.Internal.ScopeCheck
import           Test.StateMachine.Internal.Utils
import           Test.StateMachine.Prototype

import           MutableReference

------------------------------------------------------------------------

prop_genScope :: Property
prop_genScope = forAll
  (liftGen generator initModel precondition transition)
  scopeCheck

prop_genForkScope :: Property
prop_genForkScope = forAll
  (liftGenFork generator precondition transition initModel)
  scopeCheckFork

prop_sequentialShrink :: Property
prop_sequentialShrink = shrinkPropertyHelper (prop_references Bug) $ alphaEq
  [ Internal New                   var0
  , Internal (Write (Ref var0)  5) (Symbolic (Var 1))
  , Internal (Read  (Ref var0))    (Symbolic (Var 2))
  ]
  . read . (!! 1) . lines
  where
  var0 = Symbolic (Var 0)

cheat :: Fork [Internal Action] -> Fork [Internal Action]
cheat = fmap (map (\iact -> case iact of
  Internal (Write ref _) sym -> Internal (Write ref 0) sym
  _                          -> iact))

prop_shrinkForkSubseq :: Property
prop_shrinkForkSubseq = forAll
  (liftGenFork generator precondition transition initModel)
  $ \f@(Fork l p r) ->
    all (\(Fork l' p' r') -> void l' `isSubsequenceOf` void l &&
                             void p' `isSubsequenceOf` void p &&
                             void r' `isSubsequenceOf` void r)
        (liftShrinkFork shrink1 precondition transition initModel (cheat f))

prop_shrinkForkScope :: Property
prop_shrinkForkScope = forAll
  (liftGenFork generator precondition transition initModel) $ \f ->
    all scopeCheckFork (liftShrinkFork shrink1 precondition transition initModel f)

  {-
------------------------------------------------------------------------

prop_shrinkForkMinimal :: Property
prop_shrinkForkMinimal = shrinkPropertyHelper (prop_parallel RaceCondition) $ \out ->
  let f = read $ dropWhile isSpace (lines out !! 1)
  in hasMinimalShrink f || isMinimal f
  where
  hasMinimalShrink :: Fork [IntRefed Action] -> Bool
  hasMinimalShrink
    = anyTree isMinimal
    . unfoldTree (id &&& liftShrinkFork (liftGenerator gen) shrink1)
    where
    anyTree :: (a -> Bool) -> Tree a -> Bool
    anyTree p = foldTree (\x ih -> p x || or ih)
      where
      -- `foldTree` is part of `Data.Tree` in later versions of `containers`.
      foldTree :: (a -> [b] -> b) -> Tree a -> b
      foldTree f = go where
        go (Node x ts) = f x (map go ts)

  isMinimal :: Fork [IntRefed Action] -> Bool
  isMinimal xs = any (alphaEqFork xs) minimal

  minimal :: [Fork [IntRefed Action]]
  minimal  = minimal' ++ map mirrored minimal'
    where
    minimal' = [ Fork [w0, IntRefed (Read var) ()]
                      [IntRefed New var]
                      [w1]
               | w0 <- writes
               , w1 <- writes
               ]

    mirrored :: Fork a -> Fork a
    mirrored (Fork l p r) = Fork r p l

    var    = IntRef 0 0
    writes = [IntRefed (Write var 0) (), IntRefed (Inc var) ()]
-}

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
  Internal act1 sym1 == Internal act2 sym2 = cast act1 == Just act2
