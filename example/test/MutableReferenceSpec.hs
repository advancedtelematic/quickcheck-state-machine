{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module MutableReferenceSpec (spec) where

import           Data.Char                             (isSpace)
import           Data.Dynamic                          (cast)
import           Data.Kind
import           Data.List                             (isSubsequenceOf)
import           Data.Map                              (Map)
import qualified Data.Map                              as M
import           Data.Singletons.Prelude
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck
import           Text.ParserCombinators.ReadP          (string)
import           Text.Read

import           MutableReference
import           Test.StateMachine.Internal.Parallel
import           Test.StateMachine.Internal.Sequential
import           Test.StateMachine.Types
import           Test.StateMachine.Types.AlphaEquality
import           Test.StateMachine.Utils

------------------------------------------------------------------------

scopeCheck
  :: forall ix cmd
  .  IxFoldable cmd
  => (forall resp. cmd resp ConstIntRef -> SResponse ix resp)
  -> [(Pid, IntRefed cmd)]
  -> Bool
scopeCheck returns = go []
  where
  go :: [IntRef] -> [(Pid, IntRefed cmd)] -> Bool
  go _    []                           = True
  go refs ((_, Untyped' c miref) : cs) = case returns c of
    SReference _  ->
      let refs' = miref : refs in
      all (\(Ex _ ref) -> ref `elem` refs) (itoList c) &&
      go refs' cs
    SResponse     ->
      all (\(Ex _ ref) -> ref `elem` refs) (itoList c) &&
      go refs cs

scopeCheckFork'
  :: IxFoldable cmd
  => (forall resp. cmd resp ConstIntRef -> SResponse ix resp)
  -> Fork [IntRefed cmd] -> Bool
scopeCheckFork' returns (Fork l p r) =
  let p' = zip (repeat 0) p in
  scopeCheck returns (p' ++ zip (repeat 1) l) &&
  scopeCheck returns (p' ++ zip (repeat 2) r)

scopeCheckFork :: Fork [Untyped' MemStep ConstIntRef] -> Bool
scopeCheckFork = scopeCheckFork' returns

prop_genScope :: Property
prop_genScope = forAll (fst <$> liftGen gens (Pid 0) M.empty returns) $ \p ->
  let p' = zip (repeat 0) p in
  scopeCheck returns p'

prop_genForkScope :: Property
prop_genForkScope = forAll
  (liftGenFork gens returns)
  scopeCheckFork

prop_sequentialShrink :: Property
prop_sequentialShrink = shrinkPropertyHelper (prop_sequential Bug) $ alphaEq returns
  [ Untyped' New    (IntRef (Ref 0) (Pid 0))
  , Untyped' (Write (IntRef (Ref 0) (Pid 0)) (5)) ()
  , Untyped' (Read  (IntRef (Ref 0) (Pid 0))) ()
  ]
  . read . (!! 1) . lines

deriving instance Eq  (MemStep resp ConstIntRef)

instance Eq (Untyped' MemStep ConstIntRef) where
  Untyped' c1 _ == Untyped' c2 _ = Just c1 == cast c2

cheat :: Fork [Untyped' MemStep ConstIntRef] -> Fork [Untyped' MemStep ConstIntRef]
cheat = fmap (map (\ms -> case ms of
  Untyped' (Write ref _) () -> Untyped' (Write ref 0) ()
  _                         -> ms))

prop_shrinkForkSubseq :: Property
prop_shrinkForkSubseq = forAll (liftGenFork gens returns) $ \f@(Fork l p r) ->
  all (\(Fork l' p' r') -> noRefs l' `isSubsequenceOf` noRefs l &&
                           noRefs p' `isSubsequenceOf` noRefs p &&
                           noRefs r' `isSubsequenceOf` noRefs r)
      (liftShrinkFork returns shrink1 (cheat f))

  where
  noRefs = fmap (const ())

prop_shrinkForkScope :: Property
prop_shrinkForkScope = forAll (liftGenFork gens returns) $ \f ->
  all scopeCheckFork (liftShrinkFork returns shrink1 f)

debugShrinkFork :: Fork [Untyped' MemStep ConstIntRef]
  -> [Fork [Untyped' MemStep ConstIntRef]]
debugShrinkFork = take 1 . map snd . dropWhile fst . map (\f -> (scopeCheckFork f, f))
  . liftShrinkFork returns shrink1

------------------------------------------------------------------------

prop_shrinkForkMinimal :: Property
prop_shrinkForkMinimal = shrinkPropertyHelper (prop_parallel RaceCondition) $ \out ->
  let f = read $ dropWhile isSpace (lines out !! 1)
  in hasMinimalShrink f ||  isMinimal f
  where
  hasMinimalShrink :: Fork [Untyped' MemStep ConstIntRef] -> Bool
  hasMinimalShrink
    = anyRose isMinimal
    . rose (liftShrinkFork returns shrink1)
    where
    anyRose :: (a -> Bool) -> Rose a -> Bool
    anyRose p (Rose x xs) = p x || any (anyRose p) xs

    rose :: (a -> [a]) -> a -> Rose a
    rose more = go
      where
      go x = Rose x $ map go $ more x

  isMinimal :: Fork [Untyped' MemStep ConstIntRef] -> Bool
  isMinimal xs = any (alphaEqFork returns xs) minimal

  minimal :: [Fork [Untyped' MemStep ConstIntRef]]
  minimal  = minimal' ++ map mirrored minimal'
    where
    minimal' = [ Fork [w0, Untyped' (Read var) ()]
                      [Untyped' New var]
                      [w1]
               | w0 <- writes
               , w1 <- writes
               ]

    mirrored :: Fork a -> Fork a
    mirrored (Fork l p r) = Fork r p l

    var = IntRef 0 0
    writes = [Untyped' (Write var 0) (), Untyped' (Inc var) ()]

instance Read (Untyped' MemStep ConstIntRef) where
  readPrec = parens $ choice
    [ Untyped' <$ key "Untyped'" <*> parens (New <$ key " New") <*> readPrec
    , Untyped' <$ key "Untyped'" <*>
        parens (Read <$ key "Read" <*> readPrec) <*> readPrec
    , Untyped' <$ key "Untyped'" <*>
        parens (Write <$ key "Write" <*> readPrec <*> readPrec) <*> readPrec
    , Untyped' <$ key "Untyped'" <*>
        parens (Inc <$ key "Inc" <*> readPrec) <*> readPrec
    ]
    where
      key s = Text.Read.lift (string s)

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
