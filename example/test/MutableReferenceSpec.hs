{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ExplicitNamespaces  #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module MutableReferenceSpec (spec) where

import           Control.Arrow                         ((&&&))
import           Data.Char                             (isSpace)
import           Data.Dynamic                          (cast)
import           Data.Kind                             (type (*))
import           Data.List                             (isSubsequenceOf)
import           Data.Map                              (Map)
import qualified Data.Map                              as M
import           Data.Singletons.Prelude
import           Data.Tree                             (Tree (Node), unfoldTree)
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck
import           Text.ParserCombinators.ReadP          (string)
import           Text.Read                             (choice, lift, parens,
                                                        readListPrec,
                                                        readListPrecDefault,
                                                        readPrec)

import           MutableReference
import           Test.StateMachine.Internal.Parallel
import           Test.StateMachine.Internal.Sequential
import           Test.StateMachine.Types
import           Test.StateMachine.Types.AlphaEquality
import           Test.StateMachine.Utils

------------------------------------------------------------------------

scopeCheck
  :: forall ix cmd. (IxFoldable cmd, HasResponse cmd)
  => [(Pid, IntRefed cmd)] -> Bool
scopeCheck = go []
  where
  go :: [IntRef] -> [(Pid, IntRefed cmd)] -> Bool
  go _    []                           = True
  go refs ((_, IntRefed c miref) : cs) = case response c of
    SReference _  ->
      let refs' = miref : refs in
      all (\(Ex _ ref) -> ref `elem` refs) (itoList c) &&
      go refs' cs
    SResponse     ->
      all (\(Ex _ ref) -> ref `elem` refs) (itoList c) &&
      go refs cs

scopeCheckFork
  :: (IxFoldable cmd, HasResponse cmd)
  => Fork [IntRefed cmd] -> Bool
scopeCheckFork (Fork l p r) =
  let p' = zip (repeat 0) p in
  scopeCheck (p' ++ zip (repeat 1) l) &&
  scopeCheck (p' ++ zip (repeat 2) r)

prop_genScope :: Property
prop_genScope = forAllShow
  (fst <$> liftGen gens (Pid 0) M.empty)
  showIntRefedList
  $ \p -> let p' = zip (repeat 0) p in scopeCheck p'

prop_genForkScope :: Property
prop_genForkScope = forAllShow
  (liftGenFork gens)
  (showFork showIntRefedList)
  scopeCheckFork

prop_sequentialShrink :: Property
prop_sequentialShrink = shrinkPropertyHelper (prop_sequential Bug) $ alphaEq
  [ IntRefed New                                (IntRef 0 0)
  , IntRefed (Write (IntRef (Ref 0) (Pid 0)) 5) ()
  , IntRefed (Read  (IntRef (Ref 0) (Pid 0)))   ()
  ]
  . read . (!! 1) . lines

deriving instance Eq (MemStep resp ConstIntRef)

instance Eq (IntRefed MemStep) where
  IntRefed c1 _ == IntRefed c2 _ = Just c1 == cast c2

cheat :: Fork [IntRefed MemStep] -> Fork [IntRefed MemStep]
cheat = fmap (map (\ms -> case ms of
  IntRefed (Write ref _) () -> IntRefed (Write ref 0) ()
  _                         -> ms))

prop_shrinkForkSubseq :: Property
prop_shrinkForkSubseq = forAllShow
  (liftGenFork gens)
  (showFork showIntRefedList)
  $ \f@(Fork l p r) ->
    all (\(Fork l' p' r') -> noRefs l' `isSubsequenceOf` noRefs l &&
                             noRefs p' `isSubsequenceOf` noRefs p &&
                             noRefs r' `isSubsequenceOf` noRefs r)
        (liftShrinkFork shrink1 (cheat f))
  where
  noRefs = fmap (const ())

prop_shrinkForkScope :: Property
prop_shrinkForkScope = forAllShow
  (liftGenFork gens)
  (showFork showIntRefedList)
  $ \f -> all scopeCheckFork (liftShrinkFork shrink1 f)

debugShrinkFork :: Fork [IntRefed MemStep]
  -> [Fork [IntRefed MemStep]]
debugShrinkFork = take 1 . map snd . dropWhile fst . map (\f -> (scopeCheckFork f, f))
  . liftShrinkFork shrink1

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

  describe "Shrinking" $ do

    modifyMaxSuccess (const 20) $ do

      it "`prop_shrinkForkSubseq`: shrinking parallel programs preserves subsequences"
        prop_shrinkForkSubseq

      it "`prop_shrinkForkScope`: shrinking parallel programs preserves scope"
        prop_shrinkForkScope

  describe "Parallel property" $ do

    modifyMaxSuccess (const 10) $ do

      it "`prop_parallel None`: linearisation is possible when there are no race conditions" $ do
        prop_parallel None

      it "`prop_shrinkForkMinimal`: the minimal counterexample is found when there's a race condition"
        prop_shrinkForkMinimal
