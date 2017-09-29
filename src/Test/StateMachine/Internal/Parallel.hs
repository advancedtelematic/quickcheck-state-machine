{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}

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
  , executeParallelProgram
  , linearise
  , toBoxDrawings
  , toBoxDrawings'
  ) where

import           Control.Concurrent.Async.Lifted
                   (concurrently)
import           Control.Concurrent.Lifted
                   (threadDelay)
import           Control.Concurrent.STM
                   (STM, atomically)
import           Control.Concurrent.STM.TChan
                   (TChan, newTChanIO, tryReadTChan, writeTChan)
import           Control.Monad
                   (foldM)
import           Control.Monad.State
                   (StateT, evalState, evalStateT, execStateT, get,
                   lift, modify, runState, runStateT)
import           Control.Monad.Trans.Control
                   (MonadBaseControl, liftBaseWith)
import           Data.Dynamic
                   (toDyn)
import           Data.List
                   (partition)
import           Data.Set
                   (Set)
import qualified Data.Set                                     as S
import           Data.Tree
                   (Tree(Node))
import           Test.QuickCheck
                   (Gen, Property, property, shrinkList, (.&&.))
import           Text.PrettyPrint.ANSI.Leijen
                   (Doc)

import           Test.StateMachine.Internal.Sequential
import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Internal.Types.Environment
import           Test.StateMachine.Internal.Utils
import           Test.StateMachine.Internal.Utils.BoxDrawer
import           Test.StateMachine.Types                      hiding
                   (StateMachine(..))
import           Test.StateMachine.Types.History

------------------------------------------------------------------------

-- | Generate a parallel program whose actions all respect their
--   pre-conditions.
generateParallelProgram
  :: Generator    model act
  -> Precondition model act
  -> Transition   model act
  -> model Symbolic
  -> Gen (ParallelProgram act)
generateParallelProgram generator precondition transition model = do
  let generate     =  generateProgram generator precondition transition
  (prefix, model') <- runStateT  (generate 0) model
  let offset       =  length (unProgram prefix)
  left             <- evalStateT (generate offset) model'
  let offset'      =  offset + length (unProgram left)
  right            <- evalStateT (generate offset') model'
  return (ParallelProgram (Fork left prefix right))

-- | Shrink a parallel program in a pre-condition and scope respecting
--   way.
shrinkParallelProgram
  :: HFoldable act
  => Shrinker act
  -> Precondition model act
  -> Transition model act
  -> model Symbolic
  -> (ParallelProgram act -> [ParallelProgram act])
shrinkParallelProgram shrinker precondition transition model
  = fmap ParallelProgram
  . go
  . unParallelProgram
  where
  go (Fork l p r) = map forkFilterInvalid
    [ Fork l' p' r'
    | (p', (l', r')) <- shrinkPair' shrinker' (shrinkPair shrinker') (p, (l, r))
    ]
    where
    shrinker'
      = map Program
      . shrinkList (liftShrinkInternal shrinker)
      . unProgram

  forkFilterInvalid (Fork l p r) =
    let
      filterProgram         = filterInvalid precondition transition
      (p', (model', scope)) = runState  (filterProgram p) (model, S.empty)
      l'                    = evalState (filterProgram l) (model', scope)
      r'                    = evalState (filterProgram r) (model', scope)
    in Fork l' p' r'

-- | Run a parallel program, by first executing the prefix sequentially
--   and then the suffixes in parallel, and return the history (or
--   trace) of the execution.
executeParallelProgram
  :: forall m act
  .  MonadBaseControl IO m
  => HTraversable act
  => Show (Untyped act)
  => Semantics act m
  -> ParallelProgram act
  -> m (History act)
executeParallelProgram semantics = liftSemFork . unParallelProgram
  where
  liftSemFork
    :: HTraversable act
    => Show (Untyped act)
    => Fork (Program act)
    -> m (History act)
  liftSemFork (Fork left prefix right) = do
    hchan <- liftBaseWith (const newTChanIO)
    env   <- execStateT (runMany hchan (Pid 0) (unProgram prefix)) emptyEnvironment
    _     <- concurrently
      (evalStateT (runMany hchan (Pid 1) (unProgram left))  env)
      (evalStateT (runMany hchan (Pid 2) (unProgram right)) env)
    History <$> liftBaseWith (const (getChanContents hchan))
    where
    getChanContents :: forall a. TChan a -> IO [a]
    getChanContents chan = reverse <$> atomically (go [])
      where
      go :: [a] -> STM [a]
      go acc = do
        mx <- tryReadTChan chan
        case mx of
          Just x  -> go $ x : acc
          Nothing -> return acc

  runMany
    :: HTraversable act
    => Show (Untyped act)
    => TChan (HistoryEvent (UntypedConcrete act))
    -> Pid
    -> [Internal act]
    -> StateT Environment m ()
  runMany hchan pid = flip foldM () $ \_ (Internal act sym@(Symbolic var)) -> do
    env <- get
    let cact = either (error . show) id (reify env act)
    liftBaseWith $ const $ atomically $ writeTChan hchan $
      InvocationEvent (UntypedConcrete cact) (show (Untyped act)) var pid
    resp <- lift (semantics cact)
    modify (insertConcrete sym (Concrete resp))
    threadDelay 10
    liftBaseWith $ const $ atomically $ writeTChan hchan $ ResponseEvent (toDyn resp) (show resp) pid

------------------------------------------------------------------------

linearTree :: History' act -> [Tree (Operation act)]
linearTree [] = []
linearTree es =
  [ Node (Operation act str (dynResp resp) pid) (linearTree es')
  | InvocationEvent (UntypedConcrete act) str _ pid <- takeInvocations es
  , (resp, es')  <- findCorrespondingResp pid $ filter1 (not . matchInv pid) es
  ]
  where
  dynResp resp = either (error . show) id (reifyDynamic resp)

  filter1 :: (a -> Bool) -> [a] -> [a]
  filter1 _ []                   = []
  filter1 p (x : xs) | p x       = x : filter1 p xs
                     | otherwise = xs

  -- Hmm, is this enough?
  matchInv pid (InvocationEvent _ _ _ pid') = pid == pid'
  matchInv _   _                            = False

linearise
  :: forall model act
  .  Transition    model act
  -> Postcondition model act
  -> InitialModel model
  -> History act
  -> Property
linearise transition postcondition model0 = go . unHistory
  where
  go :: History' act -> Property
  go [] = property True
  go es = anyP (step model0) (linearTree es)

  step :: model Concrete -> Tree (Operation act) -> Property
  step model (Node (Operation act _ resp@(Concrete resp') _) roses) =
    postcondition model act resp' .&&.
    anyP' (step (transition model act resp)) roses
    where
    anyP' :: (a -> Property) -> [a] -> Property
    anyP' _ [] = property True
    anyP' p xs = anyP p xs

------------------------------------------------------------------------

toBoxDrawings :: HFoldable act => ParallelProgram act -> History act -> Doc
toBoxDrawings prog = toBoxDrawings' allVars
  where
  allVars    = S.unions [l, p, r]
  Fork l p r = fmap (S.unions . vars . unProgram) (unParallelProgram prog)
  vars xs    = [ getUsedVars x | Internal x _ <- xs]

toBoxDrawings' :: Set Var -> History act -> Doc
toBoxDrawings' knownVars (History h) = exec evT (fmap out <$> Fork l p r)
  where
    (p, h') = partition (\e -> getProcessIdEvent e == Pid 0) h
    (l, r)  = partition (\e -> getProcessIdEvent e == Pid 1) h'

    out :: HistoryEvent act -> String
    out (InvocationEvent _ str var _)
      | var `S.member` knownVars = show var ++ " ← " ++ str
      | otherwise = str
    out (ResponseEvent _ str _) = str

    toEventType :: [HistoryEvent act] -> [(EventType, Pid)]
    toEventType = map go
      where
      go e = case e of
        InvocationEvent _ _ _ pid -> (Open,  pid)
        ResponseEvent   _ _   pid -> (Close, pid)

    evT :: [(EventType, Pid)]
    evT = toEventType (filter (\e -> getProcessIdEvent e `elem` map Pid [1,2]) h)
