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

import           Control.Arrow
                   ((&&&))
import           Control.Monad
                   (void)
import           Control.Monad.State
                   (evalStateT)
import           Data.List
                   (isSubsequenceOf)
import           Data.Monoid
                   ((<>))
import           Data.Tree
                   (Tree(Node), unfoldTree)
import           Data.Void
                   (Void)
import           Test.QuickCheck
                   (Property, forAll, (.||.), (===))

import           Test.StateMachine
import           Test.StateMachine.Internal.AlphaEquality
import           Test.StateMachine.Internal.Parallel
import           Test.StateMachine.Internal.ScopeCheck
import           Test.StateMachine.Internal.Sequential
                   (generateProgram)
import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Internal.Utils

import           MutableReference

------------------------------------------------------------------------

oktransition :: Transition' Model Action Void
oktransition = okTransition transition

prop_genScope :: Property
prop_genScope = forAll
  (evalStateT (generateProgram generator precondition oktransition 0) initModel)
  scopeCheck

prop_genParallelScope :: Property
prop_genParallelScope = forAll
  (generateParallelProgram generator precondition oktransition initModel)
  scopeCheckParallel

prop_genParallelSequence :: Property
prop_genParallelSequence = forAll
  (generateParallelProgram generator precondition oktransition initModel)
  go
  where
  go :: ParallelProgram Action -> Property
  go (ParallelProgram (Fork l p r)) =
    vars prog === [0 .. length (unProgram prog) - 1]
    where
    prog = p <> l <> r

    vars :: Program Action -> [Int]
    vars = map (\(Internal _ (Symbolic (Var i))) -> i) . unProgram

prop_sequentialShrink :: Property
prop_sequentialShrink =
  shrinkPropertyHelperC (prop_references Bug) $ \prog ->
    alphaEq prog0 prog
  where
    sym0 = Symbolic (Var 0)
    prog0 = Program
      [ Internal New                   sym0
      , Internal (Write (Reference sym0)  5) (Symbolic (Var 1))
      , Internal (Read  (Reference sym0))    (Symbolic (Var 2))
      ]

cheat :: ParallelProgram Action -> ParallelProgram Action
cheat = ParallelProgram . fmap go . unParallelProgram
  where
  go = Program
     . map (\iact -> case iact of
               Internal (Write ref _) sym -> Internal (Write ref 0) sym
               _                          -> iact)
     . unProgram

prop_shrinkParallelSubseq :: Property
prop_shrinkParallelSubseq = forAll
  (generateParallelProgram generator precondition oktransition initModel)
  $ \prog@(ParallelProgram (Fork l p r)) ->
    all (\(ParallelProgram (Fork l' p' r')) ->
           void (unProgram l') `isSubsequenceOf` void (unProgram l) &&
           void (unProgram p') `isSubsequenceOf` void (unProgram p) &&
           void (unProgram r') `isSubsequenceOf` void (unProgram r))
        (shrinkParallelProgram shrinker precondition oktransition initModel (cheat prog))

prop_shrinkParallelScope :: Property
prop_shrinkParallelScope = forAll
  (generateParallelProgram generator precondition oktransition initModel) $ \p ->
    all scopeCheckParallel (shrinkParallelProgram shrinker precondition oktransition initModel p)

------------------------------------------------------------------------

prop_shrinkParallelMinimal :: Property
prop_shrinkParallelMinimal =
  shrinkPropertyHelperC' (prop_referencesParallel RaceCondition) checkParallelProgram'

checkParallelProgram :: ParallelProgram Action -> Bool
checkParallelProgram (ParallelProgram prog) =
  hasMinimalShrink prog || isMinimal prog
  where
  hasMinimalShrink :: Fork (Program Action) -> Bool
  hasMinimalShrink
    = anyTree isMinimal
    . unfoldTree (id &&& forkShrinker)
    where
    forkShrinker :: Fork (Program Action) -> [Fork (Program Action)]
    forkShrinker
      = map unParallelProgram
      . shrinkParallelProgram shrinker precondition oktransition initModel
      . ParallelProgram

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
    ref0   = Reference (Symbolic var0)

    writes =
      [ Internal (Write ref0 0) (Symbolic var1)
      , Internal (Inc   ref0)   (Symbolic var1)
      ]

possibleShrinks' :: (a -> [a]) -> a -> Tree a
possibleShrinks' shr = unfoldTree (id &&& shr)

possibleShrinks :: ParallelProgram' Action -> Tree (ParallelProgram' Action)
possibleShrinks = possibleShrinks'
  (shrinkParallelProgram' shrinker precondition oktransition initModel)

checkParallelProgram' :: ParallelProgram' Action -> Property
checkParallelProgram' pprog = hasMinimalShrink pprog .||. isMinimal pprog
  where
  hasMinimalShrink :: ParallelProgram' Action -> Bool
  hasMinimalShrink
    = anyTree isMinimal
    . possibleShrinks
    where
    anyTree :: (a -> Bool) -> Tree a -> Bool
    anyTree p = foldTree (\x ih -> p x || or ih)
      where
      -- `foldTree` is part of `Data.Tree` in later versions of `containers`.
      foldTree :: (a -> [b] -> b) -> Tree a -> b
      foldTree f = go where
        go (Node x ts) = f x (map go ts)

  isMinimal :: ParallelProgram' Action -> Bool
  isMinimal xs = any (alphaEqParallel xs) minimal

  minimal :: [ParallelProgram' Action]
  minimal =
    [ ParallelProgram' prefix
        [ Program
            [ iact (Write ref0 0) 1
            , iact (Inc ref0)     2
            , iact (Read ref0)    3
            ]
        ]
    , ParallelProgram' prefix
        [ Program
            [ iact (Inc ref0)     1
            , iact (Write ref0 0) 2
            , iact (Read ref0)    3
            ]
        ]
    , ParallelProgram' prefix
        [ Program
            [ iact (Inc ref0)  1
            , iact (Inc ref0)  2
            , iact (Read ref0) 3
            ]
        ]
    , ParallelProgram' prefix
        [ Program
            [ iact (Inc ref0)  1
            , iact (Inc ref0)  2
            ]
        , Program [ iact (Read ref0) 3 ]
        ]
    , ParallelProgram' prefix
        [ Program
            [ iact (Write ref0 0) 1
            , iact (Inc ref0)     2
            ]
        , Program [ iact (Read ref0) 3 ]
        ]
    , ParallelProgram' prefix
        [ Program
            [ iact (Inc ref0)     1
            , iact (Write ref0 0) 2
            ]
        , Program [ iact (Read ref0) 3 ]
        ]
    ]
    where
    iact act n = Internal act (Symbolic (Var n))

    prefix = Program [iact New 0]
    var0   = Var 0
    ref0   = Reference (Symbolic var0)
