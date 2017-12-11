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
import           Control.Monad.State
                   (evalStateT)
import           Data.List
                   (isSubsequenceOf)
import           Data.Void
                   (Void)
import           Test.QuickCheck
                   (Property, forAll, (===))

import           Test.StateMachine
import           Test.StateMachine.Internal.Parallel
import           Test.StateMachine.Internal.Sequential
                   (generateProgram)
import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Internal.Utils
                   (shrinkPropertyHelperC)

import           MutableReference
import           Utils

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
  go pprog = vars prog === [0 .. length (unProgram prog) - 1]
    where
    prog = flattenParallelProgram pprog

    vars :: Program Action -> [Int]
    vars = map (\(Internal _ (Symbolic (Var i))) -> i) . unProgram

prop_sequentialShrink :: Property
prop_sequentialShrink =
  shrinkPropertyHelperC (prop_references Bug) $ \prog ->
    alphaEq minimal prog
  where
  sym0    = Symbolic (Var 0)
  minimal = Program
    [ Internal New                         sym0
    , Internal (Write (Reference sym0)  5) (Symbolic (Var 1))
    , Internal (Read  (Reference sym0))    (Symbolic (Var 2))
    ]

cheat :: ParallelProgram Action -> ParallelProgram Action
cheat (ParallelProgram prefix suffixes)
  = ParallelProgram (go prefix) (parallelProgramAsList (map go) suffixes)
  where
  go = Program
     . map (\iact -> case iact of
               Internal (Write ref _) sym -> Internal (Write ref 0) sym
               _                          -> iact)
     . unProgram

prop_shrinkParallelSubseq :: Property
prop_shrinkParallelSubseq = forAll
  (generateParallelProgram generator precondition oktransition initModel) $ \pprog ->
    all (\pprog' -> void (unProgram (flattenParallelProgram pprog'))
                      `isSubsequenceOf`
                    void (unProgram (flattenParallelProgram pprog)))
        (shrinkParallelProgram shrinker precondition oktransition initModel (cheat pprog))

prop_shrinkParallelScope :: Property
prop_shrinkParallelScope = forAll
  (generateParallelProgram generator precondition oktransition initModel) $ \p ->
    all scopeCheckParallel (shrinkParallelProgram shrinker precondition oktransition initModel p)

------------------------------------------------------------------------

prop_shrinkParallelMinimal :: Property
prop_shrinkParallelMinimal =
  minimalShrinkHelper
    shrinker precondition (okTransition transition) initModel
    (prop_referencesParallel RaceCondition)
    isMinimal
  where
  isMinimal :: ParallelProgram Action -> Bool
  isMinimal pprog
    =  parallelProgramLength pprog == 4
    && (structuralSubset
          [Untyped New]
          [Untyped (Write ref0 0), Untyped (Inc ref0), Untyped (Read ref0)] pprog ||
        structuralSubset
          [Untyped New]
          [Untyped (Inc ref0), Untyped (Inc ref0), Untyped (Read ref0)] pprog)

    where
    ref0 = Reference (Symbolic (Var 0))
