{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Internal.Parallel
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains helpers for generating, shrinking, and checking
-- parallel programs.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Internal.Parallel
  ( generateParallelProgram
  , shrinkParallelProgram
  , validParallelProgram
  , executeParallelProgram
  , linearise
  , linearise'
  , toBoxDrawings
  ) where

import           Control.Arrow
                   ((***))
import           Control.Concurrent.Async.Lifted
                   (concurrently)
import           Control.Concurrent.STM.TChan
                   (newTChanIO)
import           Control.Monad
                   (foldM)
import           Control.Monad.State
                   (runStateT)
import           Control.Monad.Trans.Control
                   (MonadBaseControl, liftBaseWith)
import           Data.Bifunctor
                   (bimap)
import           Data.Functor.Classes
                   (Show1)
import           Data.List
                   (partition, permutations)
import           Data.Monoid
                   ((<>))
import           Data.Set
                   (Set)
import qualified Data.Set                                     as S
import           Data.Tree
                   (Tree(Node))
import           Data.Typeable
                   (Typeable)
import           Test.QuickCheck
                   (Gen, Property, choose, property, shrinkList, sized,
                   (.&&.))
import           Text.PrettyPrint.ANSI.Leijen
                   (Doc)

import           Test.StateMachine.Internal.Sequential
import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Internal.Types.Environment
import           Test.StateMachine.Internal.Utils
import           Test.StateMachine.Internal.Utils.BoxDrawer
import           Test.StateMachine.Types
import           Test.StateMachine.Types.History

------------------------------------------------------------------------

-- | Generate a parallel program whose actions all respect their
--   pre-conditions.
generateParallelProgram
  :: Generator    model act
  -> Precondition model act
  -> Transition'  model act err
  -> model Symbolic
  -> Gen (ParallelProgram act)
generateParallelProgram generator precondition transition model = do
  Program is         <- generateProgram' generator precondition transition model
  prefixLength       <- sized (\k -> choose (0, k `div` 3))
  let (prefix, rest) =  bimap Program Program (splitAt prefixLength is)
  return (ParallelProgram prefix
    (splitProgram precondition transition (advanceModel transition model prefix) rest))

-- | Shrink a parallel program in a pre-condition and scope respecting
--   way.
shrinkParallelProgram
  :: forall act model err
  .  HFoldable act
  => Eq (Untyped act)
  => Shrinker act
  -> Precondition model act
  -> Transition' model act err
  -> model Symbolic
  -> (ParallelProgram act -> [ParallelProgram act])
shrinkParallelProgram shrinker precondition transition model (ParallelProgram prefix suffixes)
  = filter (validParallelProgram precondition transition model)
      [ ParallelProgram prefix' suffixes'
      | (prefix', suffixes') <- shrinkPair' shrinkProgram' shrinkSuffixes (prefix, suffixes)
      ]
      ++
      shrinkMoveSuffixToPrefix
  where
  shrinkProgram' :: Program act -> [Program act]
  shrinkProgram'
    = map Program
    . shrinkList (liftShrinkInternal shrinker)
    . unProgram

  shrinkSuffixes :: [(Program act, Program act)] -> [[(Program act, Program act)]]
  shrinkSuffixes = shrinkList (shrinkPair shrinkProgram')

  shrinkMoveSuffixToPrefix :: [ParallelProgram act]
  shrinkMoveSuffixToPrefix = case suffixes of
    []                   -> []
    (suffix : suffixes') ->
      [ ParallelProgram (prefix <> Program [prefix'])
                        (bimap Program Program suffix' : suffixes')
      | (prefix', suffix') <- pickOneReturnRest2 (unProgram (fst suffix),
                                                  unProgram (snd suffix))
      ]

  pickOneReturnRest :: [a] -> [(a, [a])]
  pickOneReturnRest []       = []
  pickOneReturnRest (x : xs) = (x, xs) : map (id *** (x :)) (pickOneReturnRest xs)

  pickOneReturnRest2 :: ([a], [a]) -> [(a, ([a],[a]))]
  pickOneReturnRest2 (xs, ys) =
    map (id *** flip (,) ys) (pickOneReturnRest xs) ++
    map (id ***      (,) xs) (pickOneReturnRest ys)

validParallelProgram
  :: HFoldable act
  => Precondition model act
  -> Transition' model act err
  -> model Symbolic
  -> ParallelProgram act
  -> Bool
validParallelProgram precondition transition model (ParallelProgram prefix suffixes)
  =  validProgram  precondition transition model prefix
  && validSuffixes precondition transition prefixModel prefixScope (parallelProgramToList suffixes)
  where
  prefixModel = advanceModel transition model prefix
  prefixScope = boundVars prefix

boundVars :: Program act -> Set Var
boundVars
  = foldMap (\(Internal _ (Symbolic var)) -> S.singleton var)
  . unProgram

usedVars :: HFoldable act => Program act -> Set Var
usedVars
  = foldMap (\(Internal act _) -> hfoldMap (\(Symbolic var) -> S.singleton var) act)
  . unProgram

validSuffixes
  :: forall act model err
  .  HFoldable act
  => Precondition model act
  -> Transition' model act err
  -> model Symbolic
  -> Set Var
  -> [Program act]
  -> Bool
validSuffixes precondition transition model0 scope0 = go model0 scope0
  where
  go :: model Symbolic -> Set Var -> [Program act] -> Bool
  go _     _     []             = True
  go model scope (prog : progs)
    =  usedVars prog `S.isSubsetOf` scope' -- This assumes that variables
                                           -- are bound before used in a
                                           -- program.
    && parallelSafe precondition transition model prog
    && go (advanceModel transition model prog) scope' progs
    where
    scope' = boundVars prog `S.union` scope

-- | Run a parallel program, by first executing the prefix sequentially
--   and then the suffixes in parallel, and return the history (or
--   trace) of the execution.
executeParallelProgram
  :: MonadBaseControl IO m
  => HTraversable act
  => Show1 (act Symbolic)
  => Show err
  => StateMachine' model act m err
  -> ParallelProgram act
  -> m (History act err, Reason)
executeParallelProgram sm@StateMachine{..} (ParallelProgram prefix suffixes) = do

  hchan <- liftBaseWith (const newTChanIO)

  (reason0, eenv0) <- runStateT
    (executeProgram' sm hchan (Pid 0) True prefix)
    (ExecutionEnv emptyEnvironment model' model')

  if reason0 /= Ok
  then do
    hist <- liftBaseWith (const (getChanContents hchan))
    return (History hist, reason0)
  else do
    (reason, _) <- foldM (go hchan) (reason0, eenv0) suffixes
    hist <- liftBaseWith (const (getChanContents hchan))
    return (History hist, reason)
  where
  go hchan (_, eenv) (prog1, prog2) = do
    ((reason1, eenv1), (reason2, eenv2)) <- concurrently
      (runStateT (executeProgram' sm hchan (Pid 1) False prog1) eenv)
      (runStateT (executeProgram' sm hchan (Pid 2) False prog2) eenv)
    return ( reason1 `combineReason` reason2
           , combineEnv eenv1 eenv2 transition' prog2
           )
    where
    combineReason :: Reason -> Reason -> Reason
    combineReason Ok r2 = r2
    combineReason r1 _  = r1

combineEnv
  :: ExecutionEnv model
  -> ExecutionEnv model
  -> Transition' model act err
  -> Program act
  -> ExecutionEnv model
combineEnv (ExecutionEnv env1 smodel1 cmodel1) (ExecutionEnv env2 _ _) transition prog
  = ExecutionEnv (env1 <> env2) (advanceModel transition smodel1 prog) cmodel1

  -- We don't care about the concrete model when executing parallel
  -- programs, as we are not checking post-conditions.

------------------------------------------------------------------------

-- | Try to linearise a history of a parallel program execution using a
--   sequential model. See the *Linearizability: a correctness condition for
--   concurrent objects* paper linked to from the README for more info.
linearise
  :: forall model act err
  .  Transition'    model act err
  -> Postcondition' model act err
  -> InitialModel model
  -> History act err
  -> Property
linearise transition postcondition model0 = go . unHistory
  where
  go :: History' act err -> Property
  go [] = property True
  go es = anyP (step model0) (linearTree es)

  step :: model Concrete -> Tree (Operation act err) -> Property
  step model (Node (Operation act _ resp _ _) roses) =
    postcondition model act resp .&&.
    anyP' (step (transition model act (fmap Concrete resp))) roses

anyP' :: (a -> Property) -> [a] -> Property
anyP' _ [] = property True
anyP' p xs = anyP p xs

linearise'
  :: forall model act err
  .  Transition'    model act err
  -> Postcondition' model act err
  -> InitialModel model
  -> (forall resp. Typeable resp => act Concrete resp -> model Concrete -> resp)
  -> err
  -> History act err
  -> Property
linearise' transition postcondition model0 mock err = go . unHistory
  where
  go :: History' act err -> Property
  go [] = property True
  go es = anyP (step model0) (linearTree' model0 mock err es)

  step :: model Concrete -> Tree (Operation act err) -> Property
  step model (Node (Operation act _ resp _ _) roses) =
    postcondition model act resp .&&.
    anyP' (step (transition model act (fmap Concrete resp))) roses

------------------------------------------------------------------------

-- | Draw an ASCII diagram of the history of a parallel program. Useful for
--   seeing how a race condition might have occured.
toBoxDrawings :: HFoldable act => ParallelProgram act -> History act err -> Doc
toBoxDrawings (ParallelProgram prefix suffixes) = toBoxDrawings'' allVars
  where
  allVars = usedVars prefix `S.union` foldMap usedVars (parallelProgramToList suffixes)

  toBoxDrawings'' :: Set Var -> History act err -> Doc
  toBoxDrawings'' knownVars (History h) = exec evT (fmap out <$> Fork l p r)
    where
      (p, h') = partition (\e -> getProcessIdEvent e == Pid 0) h
      (l, r)  = partition (\e -> getProcessIdEvent e == Pid 1) h'

      out :: HistoryEvent act err -> String
      out (InvocationEvent _ str var _)
        | var `S.member` knownVars = show var ++ " ← " ++ str
        | otherwise = str
      out (ResponseEvent _ str _) = str

      toEventType :: [HistoryEvent act err] -> [(EventType, Pid)]
      toEventType = map go
        where
        go e = case e of
          InvocationEvent _ _ _ pid -> (Open,  pid)
          ResponseEvent   _ _   pid -> (Close, pid)

      evT :: [(EventType, Pid)]
      evT = toEventType (filter (\e -> getProcessIdEvent e `elem` map Pid [1,2]) h)

------------------------------------------------------------------------

splitProgram
  :: Precondition model act
  -> Transition'  model act err
  -> model Symbolic
  -> Program act
  -> [(Program act, Program act)]
splitProgram precondition transition model0 = go model0 [] . unProgram
  where
  go _     acc []    = reverse acc
  go model acc iacts = go (advanceModel transition model (Program safe))
                          ((Program safe1, Program safe2) : acc)
                          rest
    where
    (safe, rest)   = spanSafe model [] iacts
    (safe1, safe2) = splitAt (length safe `div` 2) safe

  spanSafe _     safe []                            = (reverse safe, [])
  spanSafe model safe (iact@(Internal _ _) : iacts)
    | length safe <= 5 && parallelSafe precondition transition model (Program (iact : safe))
        = spanSafe model (iact : safe) iacts
    | otherwise
        = (reverse safe, iact : iacts)

parallelSafe
  :: Precondition model act
  -> Transition' model act err
  -> model Symbolic
  -> Program act
  -> Bool
parallelSafe precondition transition model0
  = and
  . map (preconditionsHold model0)
  . permutations
  . unProgram
  where
  preconditionsHold _     []                         = True
  preconditionsHold model (Internal act sym : iacts)
    =  precondition model act
    && preconditionsHold (transition model act (Success sym)) iacts

advanceModel
  :: Transition' model act err
  -> model Symbolic
  -> Program act
  -> model Symbolic
advanceModel transition model0 = go model0 . unProgram
  where
  go model []                         = model
  go model (Internal act sym : iacts) =
    go (transition model act (Success sym)) iacts
