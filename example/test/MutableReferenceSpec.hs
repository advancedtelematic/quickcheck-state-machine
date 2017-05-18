{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE StandaloneDeriving #-}

module MutableReferenceSpec (spec) where

import           Control.Arrow                            ((&&&))
import           Control.Monad                            (void)
import           Data.Char                                (isSpace)
import           Data.Dynamic                             (cast)
import           Data.List                                (isSubsequenceOf)
import qualified Data.Map                                 as M
import           Data.Tree                                (Tree (Node),
                                                           unfoldTree)
import           Test.Hspec                               (Spec, describe, it)
import           Test.Hspec.QuickCheck                    (modifyMaxSuccess)
import           Test.QuickCheck                          (Property)
import           Text.ParserCombinators.ReadP             (string)
import           Text.Read                                (choice, lift, parens,
                                                           readListPrec,
                                                           readListPrecDefault,
                                                           readPrec)

import           MutableReference
import           Test.StateMachine.Internal.AlphaEquality
import           Test.StateMachine.Internal.Parallel
import           Test.StateMachine.Internal.ScopeCheck
import           Test.StateMachine.Internal.Sequential
import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Internal.Utils

------------------------------------------------------------------------

prop_genScope :: Property
prop_genScope = forAllShow
  (fst <$> liftGen gen (Pid 0) M.empty)
  showIntRefedList
  scopeCheck

prop_genForkScope :: Property
prop_genForkScope = forAllShow
  (liftGenFork gen)
  (showFork showIntRefedList)
  scopeCheckFork

prop_sequentialShrink :: Property
prop_sequentialShrink = shrinkPropertyHelper (prop_sequential Bug) $ alphaEq
  [ IntRefed New                                (IntRef 0 0)
  , IntRefed (Write (IntRef (Ref 0) (Pid 0)) 5) ()
  , IntRefed (Read  (IntRef (Ref 0) (Pid 0)))   ()
  ]
  . read . (!! 1) . lines

deriving instance Eq (MemStep ConstIntRef resp)

instance Eq (IntRefed MemStep) where
  IntRefed c1 _ == IntRefed c2 _ = Just c1 == cast c2

cheat :: Fork [IntRefed MemStep] -> Fork [IntRefed MemStep]
cheat = fmap (map (\ms -> case ms of
  IntRefed (Write ref _) () -> IntRefed (Write ref 0) ()
  _                         -> ms))

prop_shrinkForkSubseq :: Property
prop_shrinkForkSubseq = forAllShow
  (liftGenFork gen)
  (showFork showIntRefedList)
  $ \f@(Fork l p r) ->
    all (\(Fork l' p' r') -> void l' `isSubsequenceOf` void l &&
                             void p' `isSubsequenceOf` void p &&
                             void r' `isSubsequenceOf` void r)
        (liftShrinkFork shrink1 (cheat f))

prop_shrinkForkScope :: Property
prop_shrinkForkScope = forAllShow
  (liftGenFork gen)
  (showFork showIntRefedList)
  $ \f -> all scopeCheckFork (liftShrinkFork shrink1 f)

------------------------------------------------------------------------

prop_shrinkForkMinimal :: Property
prop_shrinkForkMinimal = shrinkPropertyHelper (prop_parallel RaceCondition) $ \out ->
  let f = read $ dropWhile isSpace (lines out !! 1)
  in hasMinimalShrink f || isMinimal f
  where
  hasMinimalShrink :: Fork [IntRefed MemStep] -> Bool
  hasMinimalShrink
    = anyTree isMinimal
    . unfoldTree (id &&& liftShrinkFork shrink1)
    where
    anyTree :: (a -> Bool) -> Tree a -> Bool
    anyTree p = foldTree (\x ih -> p x || or ih)
      where
      -- `foldTree` is part of `Data.Tree` in later versions of `containers`.
      foldTree :: (a -> [b] -> b) -> Tree a -> b
      foldTree f = go where
        go (Node x ts) = f x (map go ts)

  isMinimal :: Fork [IntRefed MemStep] -> Bool
  isMinimal xs = any (alphaEqFork xs) minimal

  minimal :: [Fork [IntRefed MemStep]]
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

instance Read (IntRefed MemStep) where
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

------------------------------------------------------------------------

spec :: Spec
spec = do

  describe "Generation" $ do

    it "`prop_genScope`: generate well-scoped programs"
      prop_genScope

    it "`prop_genForkScope`: generate well-scoped parallel programs"
      prop_genForkScope

  describe "Sequential property" $ do

    it "`prop_sequential None`: pre- and post-conditions hold when there are no bugs" $
      prop_sequential None

    it "`prop_sequentialShrink`: the minimal counterexample is found when there's a bug"
      prop_sequentialShrink

  describe "Shrinking" $

    modifyMaxSuccess (const 20) $ do

      it "`prop_shrinkForkSubseq`: shrinking parallel programs preserves subsequences"
        prop_shrinkForkSubseq

      it "`prop_shrinkForkScope`: shrinking parallel programs preserves scope"
        prop_shrinkForkScope

  describe "Parallel property" $

    modifyMaxSuccess (const 10) $ do

      it "`prop_parallel None`: linearisation is possible when there are no race conditions" $
        prop_parallel None

      it "`prop_shrinkForkMinimal`: the minimal counterexample is found when there's a race condition"
        prop_shrinkForkMinimal
