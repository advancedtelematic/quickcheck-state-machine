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

{-
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
import qualified Data.Map                                 as M
import           Data.Tree
                   (Tree(Node), unfoldTree)
import           Text.ParserCombinators.ReadP
                   (string)
import           Text.Read
                   (choice, lift, parens, readListPrec,
                   readListPrecDefault, readPrec)
-}
import           Test.QuickCheck
                   (Property, forAll)

import           Test.StateMachine.Prototype
import           Test.StateMachine.Internal.ScopeCheck

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

  {-
prop_sequentialShrink :: Property
prop_sequentialShrink = shrinkPropertyHelper (prop_references Bug) $ alphaEq
  [ Internal New                                (IntRef 0 0)
  , Internal (Write (IntRef (Ref 0) (Pid 0)) 5) ()
  , Internal (Read  (IntRef (Ref 0) (Pid 0)))   ()
  ]
  . read . (!! 1) . lines

deriving instance Eq (Action ConstIntRef resp)

instance Eq (IntRefed Action) where
  IntRefed c1 _ == IntRefed c2 _ = Just c1 == cast c2

cheat :: Fork [IntRefed Action] -> Fork [IntRefed Action]
cheat = fmap (map (\ms -> case ms of
  IntRefed (Write ref _) () -> IntRefed (Write ref 0) ()
  _                         -> ms))

prop_shrinkForkSubseq :: Property
prop_shrinkForkSubseq = forAll
  (liftGenFork (liftGenerator gen))
  $ \f@(Fork l p r) ->
    all (\(Fork l' p' r') -> void l' `isSubsequenceOf` void l &&
                             void p' `isSubsequenceOf` void p &&
                             void r' `isSubsequenceOf` void r)
        (liftShrinkFork (liftGenerator gen) shrink1 (cheat f))

prop_shrinkForkScope :: Property
prop_shrinkForkScope = forAll
  (liftGenFork (liftGenerator gen))
  $ \f -> all scopeCheckFork (liftShrinkFork (liftGenerator gen) shrink1 f)

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

instance Read (IntRefed Action) where
  readPrec = parens $ choice
    [ IntRefed <$> parens (New <$ key "New") <*> readPrec
    , IntRefed <$>
        parens (Read <$ key "Read" <*> readPrec) <*> readPrec
    , IntRefed <$>
        parens (Write <$ key "Write" <*> readPrec <*> readPrec) <*> readPrec
    , IntRefed <$>
        parens (Inc <$ key "Inc" <*> readPrec) <*> readPrec
    ]
    where
    key s = lift (string s)

  readListPrec = readListPrecDefault

-}
