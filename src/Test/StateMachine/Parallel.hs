{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Parallel
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

module Test.StateMachine.Parallel
  ( generateParallelCommands
  -- , shrinkParallelProgram
  -- , validParallelProgram
  , runParallelCommands
  , linearise
  -- , toBoxDrawings
  ) where

import           Control.Arrow
                   ((***))
import           Control.Concurrent.Async.Lifted
                   (concurrently)
import           Control.Concurrent.STM.TChan
                   (newTChanIO)
import           Control.Monad
                   (foldM, replicateM)
import           Control.Monad.State
                   (State, runStateT)
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
import           Data.Tree
                   (Tree(Node))
import           Test.QuickCheck
                   (Gen, Property, choose, property, shrinkList, sized)
import           Test.QuickCheck.Monadic
                   (PropertyM, run)

import           Test.StateMachine.Sequential
import           Test.StateMachine.Types
import qualified Test.StateMachine.Types.Rank2   as Rank2
import           Test.StateMachine.Utils

------------------------------------------------------------------------

generateParallelCommands :: forall model cmd m resp. Rank2.Foldable resp
                         => StateMachine model cmd m resp
                         -> Gen (ParallelCommands cmd)
generateParallelCommands sm@StateMachine { initModel } = do
  Commands cmds      <- generateCommands sm
  prefixLength       <- sized (\k -> choose (0, k `div` 3))
  let (prefix, rest) =  bimap Commands Commands (splitAt prefixLength cmds)
  return (ParallelCommands prefix
            (makeSuffixes (advanceModel sm initModel newCounter prefix) rest))
  where
    makeSuffixes :: (model Symbolic, Counter) -> Commands cmd -> [Pair (Commands cmd)]
    makeSuffixes (model0, counter0) = go (model0, counter0) [] . unCommands
      where
        go _                acc []   = reverse acc
        go (model, counter) acc cmds = go (advanceModel sm model counter (Commands safe))
                                          (Pair (Commands safe1) (Commands safe2) : acc)
                                          rest
          where
            (safe, rest)   = spanSafe model counter [] cmds
            (safe1, safe2) = splitAt (length safe `div` 2) safe

        suffixLength = 5

        spanSafe :: model Symbolic -> Counter -> [Command cmd] -> [Command cmd]
                 -> ([Command cmd], [Command cmd])
        spanSafe _     _       safe []                         = (reverse safe, [])
        spanSafe model counter safe (cmd@(Command _ _) : cmds)
          | length safe <= suffixLength &&
              parallelSafe sm model counter (Commands (cmd : safe)) =
                spanSafe model counter (cmd : safe) cmds
          | otherwise = (reverse safe, cmd : cmds)

parallelSafe :: StateMachine model cmd m resp -> model Symbolic
             -> Counter -> Commands cmd -> Bool
parallelSafe StateMachine { precondition, transition, mock } model0 counter0
  = and
  . map (preconditionsHold model0 counter0)
  . permutations
  . unCommands
  where
    preconditionsHold _     _       []                         = True
    preconditionsHold model counter (Command cmd _vars : cmds) =
      let
        (resp, counter') = runGenSym (mock model cmd) counter
      in
        precondition model cmd &&
          preconditionsHold (transition model cmd resp) counter' cmds

advanceModel :: StateMachine model cmd m resp
             -> model Symbolic -> Counter -> Commands cmd
             -> (model Symbolic, Counter)
advanceModel StateMachine { transition, mock } model0 counter0 =
  go model0 counter0 . unCommands
  where
    go model counter []                         = (model, counter)
    go model counter (Command cmd _vars : cmds) =
      let
        (resp, counter') = runGenSym (mock model cmd) counter
      in
        go (transition model cmd resp) counter' cmds

------------------------------------------------------------------------

-- | Shrink a parallel program in a pre-condition and scope respecting
--   way.
shrinkParallelProgram
  :: forall cmd model m resp. (Rank2.Foldable cmd, Eq (cmd Symbolic))
  => StateMachine model cmd m resp
  -> (ParallelCommands cmd -> [ParallelCommands cmd])
shrinkParallelProgram StateMachine { shrinker, precondition, transition, initModel } (ParallelCommands prefix suffixes)
  = undefined -- XXX filter (validParallelProgram precondition transition model)
      [ ParallelCommands prefix' suffixes'
      | (prefix', suffixes') <- shrinkPair' shrinkCommands' shrinkSuffixes (prefix, map fromPair suffixes)
      ]
      ++
      shrinkMoveSuffixToPrefix
  where
  shrinkCommands' :: Commands cmd -> [Commands cmd]
  shrinkCommands'
    = map Commands
    . shrinkList (liftShrinkCommand shrinker)
    . unCommands

  shrinkSuffixes :: [(Commands cmd, Commands cmd)] -> [[(Commands cmd, Commands cmd)]]
  shrinkSuffixes = shrinkList (shrinkPair shrinkCommands')

  shrinkMoveSuffixToPrefix :: [ParallelCommands cmd]
  shrinkMoveSuffixToPrefix = case suffixes of
    []                   -> []
    (suffix : suffixes') ->
      [ ParallelCommands (prefix <> Commands [prefix'])
                         (fmap Commands (toPair suffix') : suffixes')
      | (prefix', suffix') <- pickOneReturnRest2 (unCommands (proj1 suffix),
                                                  unCommands (proj2 suffix))
      ]

  pickOneReturnRest :: [a] -> [(a, [a])]
  pickOneReturnRest []       = []
  pickOneReturnRest (x : xs) = (x, xs) : map (id *** (x :)) (pickOneReturnRest xs)

  pickOneReturnRest2 :: ([a], [a]) -> [(a, ([a],[a]))]
  pickOneReturnRest2 (xs, ys) =
    map (id *** flip (,) ys) (pickOneReturnRest xs) ++
    map (id ***      (,) xs) (pickOneReturnRest ys)

filterValidParallelCommands :: forall model cmd m resp. (Rank2.Foldable cmd, Rank2.Foldable resp)
                            => StateMachine model cmd m resp -> ParallelCommands cmd
                            -> State (model Symbolic, Set Var, Counter) (ParallelCommands cmd)
filterValidParallelCommands StateMachine { precondition, transition, mock } (ParallelCommands prefix suffixes) = undefined
{-

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
-}

------------------------------------------------------------------------

runParallelCommands :: (Rank2.Traversable cmd, Rank2.Foldable resp)
                    => MonadBaseControl IO m
                    => StateMachine model cmd m resp
                    -> ParallelCommands cmd
                    -> PropertyM m [(History cmd resp, Bool)]
runParallelCommands sm = runParallelCommandsNTimes 10 sm

runParallelCommandsNTimes :: (Rank2.Traversable cmd, Rank2.Foldable resp)
                          => MonadBaseControl IO m
                          => Int -- ^ How many times to execute the parallel program.
                          -> StateMachine model cmd m resp
                          -> ParallelCommands cmd
                          -> PropertyM m [(History cmd resp, Bool)]
runParallelCommandsNTimes n sm cmds =
  replicateM n $ do
    (hist, _reason) <- run (executeParallelCommands sm cmds)
    return (hist, linearise sm hist)

executeParallelCommands :: (Rank2.Traversable cmd, Rank2.Foldable resp)
                        => MonadBaseControl IO m
                        => StateMachine model cmd m resp
                        -> ParallelCommands cmd
                        -> m (History cmd resp, Reason)
executeParallelCommands sm@StateMachine{ initModel } (ParallelCommands prefix suffixes) = do

  hchan <- liftBaseWith (const newTChanIO)

  (reason0, (env0, _cmodel)) <- runStateT
    (executeCommands sm hchan (Pid 0) True prefix)
    (emptyEnvironment, initModel)

  if reason0 /= Ok
  then do
    hist <- liftBaseWith (const (getChanContents hchan))
    return (History hist, reason0)
  else do
    (reason, _) <- foldM (go hchan) (reason0, env0) suffixes
    hist <- liftBaseWith (const (getChanContents hchan))
    return (History hist, reason)
  where
    go hchan (_, env) (Pair cmds1 cmds2) = do
      ((reason1, (env1, _)), (reason2, (env2, _))) <- concurrently

        -- XXX: Post-conditions not checked, so we can pass in initModel here...
        -- It would be better if we made executeCommands take a Maybe model
        -- instead of the boolean...

        (runStateT (executeCommands sm hchan (Pid 1) False cmds1) (env, initModel))
        (runStateT (executeCommands sm hchan (Pid 2) False cmds2) (env, initModel))
      return ( reason1 `combineReason` reason2
             , env1 <> env2
             )
      where
        combineReason :: Reason -> Reason -> Reason
        combineReason Ok r2 = r2
        combineReason r1 _  = r1

------------------------------------------------------------------------

-- | Try to linearise a history of a parallel program execution using a
--   sequential model. See the *Linearizability: a correctness condition for
--   concurrent objects* paper linked to from the README for more info.
linearise :: forall model cmd m resp. StateMachine model cmd m resp
          -> History cmd resp -> Bool
linearise StateMachine { transition,  postcondition, initModel } = go . unHistory
  where
    go :: [(Pid, HistoryEvent cmd resp)] -> Bool
    go [] = True
    go es = any (step initModel) (interleavings es)

    step :: model Concrete -> Tree (Operation cmd resp) -> Bool
    step model (Node (Operation cmd resp _) roses) =
      postcondition model cmd resp &&
        any' (step (transition model cmd resp)) roses

any' :: (a -> Bool) -> [a] -> Bool
any' _ [] = True
any' p xs = any p xs


{-

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

-}


{-
-- | Takes the output of a parallel program runs and pretty prints a
--   counter example if any of the runs fail.
prettyParallelProgram
  :: MonadIO m
  => HFoldable act
  => Show (Untyped act)
  => ParallelProgram act
  -> [(History act err, Property)] -- ^ Output of 'runParallelProgram.
  -> PropertyM m ()
prettyParallelProgram prog
  = mapM_ (\(hist, prop) ->
              print (toBoxDrawings prog hist) `whenFailM` prop)

-}
