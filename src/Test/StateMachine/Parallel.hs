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
  -- , linearise
  -- , toBoxDrawings
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
import qualified Data.Set                        as S
import           Data.Tree
                   (Tree(Node))
import           Test.QuickCheck
                   (Gen, choose, shrinkList, sized)
import           Test.QuickCheck.Monadic
                   (PropertyM, run)

import           Test.StateMachine.Sequential
import           Test.StateMachine.Types
import qualified Test.StateMachine.Types.Rank2 as Rank2

------------------------------------------------------------------------

generateParallelCommands :: forall model cmd m resp. Rank2.Foldable resp
                         => StateMachine model cmd m resp
                         -> Gen (ParallelCommands cmd)
generateParallelCommands sm@StateMachine { initModel } = do
  Commands cmds      <- generateCommands sm
  prefixLength       <- sized (\k -> choose (0, k `div` 3))
  let (prefix, rest) =  bimap Commands Commands (splitAt prefixLength cmds)
  return (ParallelCommands prefix
            (makeSuffixes (advanceModel sm initModel prefix) rest))
  where
    makeSuffixes :: model Symbolic -> Commands cmd -> [Pair (Commands cmd)]
    makeSuffixes model0 = go model0 [] . unCommands
      where
        go _     acc []   = reverse acc
        go model acc cmds = go (advanceModel sm model (Commands safe))
                                (Pair (Commands safe1) (Commands safe2) : acc)
                                rest
          where
            (safe, rest)   = spanSafe model [] cmds
            (safe1, safe2) = splitAt (length safe `div` 2) safe

        suffixLength = 5

        spanSafe _     safe []                         = (reverse safe, [])
        spanSafe model safe (cmd@(Command _ _) : cmds)
          | length safe <= suffixLength &&
              parallelSafe sm model (Commands (cmd : safe)) =
                spanSafe model (cmd : safe) cmds
          | otherwise = (reverse safe, cmd : cmds)

parallelSafe :: StateMachine model cmd m resp -> model Symbolic -> Commands cmd
             -> Bool
parallelSafe StateMachine { precondition, transition } model0
  = and
  . map (preconditionsHold model0)
  . permutations
  . unCommands
  where
    preconditionsHold _     []                         = True
    preconditionsHold model (Command cmd _vars : cmds)
      =  precondition model cmd
      && preconditionsHold (transition model cmd undefined) cmds

-- XXX: is it good enough to start from a fresh counter every time?
advanceModel :: StateMachine model cmd m resp
             -> model Symbolic -> Commands cmd -> model Symbolic
advanceModel StateMachine { transition, mock } model0 =
  go model0 newCounter . unCommands
  where
    go model _       []                         = model
    go model counter (Command cmd _vars : cmds) =
      let
        (resp, counter') = runGenSym (mock model cmd) counter
      in
        go (transition model cmd resp) counter' cmds

------------------------------------------------------------------------

{-

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
-}

runParallelCommands :: (Rank2.Traversable cmd, Rank2.Foldable resp)
                    => MonadBaseControl IO m
                    => StateMachine model cmd m resp
                    -> ParallelCommands cmd
                    -> PropertyM m (History cmd resp, Reason)
runParallelCommands sm = run . executeParallelCommands sm

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

{-

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
runParallelProgram
  :: MonadBaseControl IO m
  => Show1 (act Symbolic)
  => Show err
  => HTraversable act
  => StateMachine' model act m err
     -- ^
  -> ParallelProgram act
  -> PropertyM m [(History act err, Property)]
runParallelProgram = runParallelProgram' 10

runParallelProgram'
  :: MonadBaseControl IO m
  => Show1 (act Symbolic)
  => Show err
  => HTraversable act
  => Int -- ^ How many times to execute the parallel program.
  -> StateMachine' model act m err
     -- ^
  -> ParallelProgram act
  -> PropertyM m [(History act err, Property)]
runParallelProgram' n sm@StateMachine{..} prog =
  replicateM n $ do
    (hist, _reason) <- run (executeParallelProgram sm prog)
    return (hist, linearise transition' postcondition' model' hist)

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
