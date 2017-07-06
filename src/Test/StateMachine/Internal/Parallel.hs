{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE ScopedTypeVariables       #-}

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
-- This module contains the building blocks needed to implement the
-- 'Test.StateMachine.parallelProperty' helper.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Internal.Parallel
  ( liftGenParallelProgram
  , liftShrinkParallelProgram
  , liftSemParallelProgram
  , liftGenFork
  , liftShrinkFork
  , liftSemFork
  , checkParallelInvariant
  , History
  ) where

import           Control.Concurrent
                   (threadDelay)
import           Control.Concurrent.ParallelIO.Local
                   (parallel_, withPool)
import           Control.Concurrent.STM
                   (STM, atomically)
import           Control.Concurrent.STM.TChan
                   (TChan, newTChanIO, tryReadTChan, writeTChan)
import           Control.Monad
                   (foldM)
import           Control.Monad.State
                   (StateT, evalStateT, execStateT, get, lift, modify)
import           Data.Dynamic
                   (Dynamic, toDyn)
import           Data.List
                   (partition)
import           Data.Set
                   (Set)
import qualified Data.Set                                     as S
import           Data.Tree
                   (Tree(Node))
import           Data.Typeable
                   (Typeable)
import           System.Random
                   (randomRIO)
import           Test.QuickCheck
                   (Gen, Property, counterexample, property,
                   shrinkList, (.&&.))
import           Test.QuickCheck.Monadic
                   (PropertyM)
import           Text.PrettyPrint.ANSI.Leijen
                   (Doc)

import           Test.StateMachine.Internal.Sequential
import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Internal.Types.Environment
import           Test.StateMachine.Internal.Utils
import           Test.StateMachine.Internal.Utils.BoxDrawer
import           Test.StateMachine.Types

------------------------------------------------------------------------

data UntypedConcrete (act :: (* -> *) -> * -> *) where
  UntypedConcrete :: (Show resp, Typeable resp) =>
    act Concrete resp -> UntypedConcrete act

type History act = [HistoryEvent (UntypedConcrete act)]

data HistoryEvent act
  = InvocationEvent act     String Var Pid
  | ResponseEvent   Dynamic String     Pid

getProcessIdEvent :: HistoryEvent act -> Pid
getProcessIdEvent (InvocationEvent _ _ _ pid) = pid
getProcessIdEvent (ResponseEvent   _ _ pid)   = pid

data Operation act = forall resp. Typeable resp =>
  Operation (act Concrete resp) String (Concrete resp) Pid

takeInvocations :: [HistoryEvent a] -> [HistoryEvent a]
takeInvocations = takeWhile $ \h -> case h of
  InvocationEvent {} -> True
  _                  -> False

findCorrespondingResp :: Pid -> History act -> [(Dynamic, History act)]
findCorrespondingResp _   [] = []
findCorrespondingResp pid (ResponseEvent resp _ pid' : es) | pid == pid' = [(resp, es)]
findCorrespondingResp pid (e : es) =
  [ (resp, e : es') | (resp, es') <- findCorrespondingResp pid es ]

linearTree :: History act -> [Tree (Operation act)]
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
  -> (forall v. model v)
  -> History act
  -> Property
linearise _    _    _       [] = property True
linearise next post initial es = anyP (step initial) . linearTree $ es
  where
  step :: model Concrete -> Tree (Operation act) -> Property
  step m (Node (Operation act _ resp@(Concrete resp') _) roses) =
    post m act resp' .&&.
    anyP' (step (next m act resp)) roses
    where
    anyP' :: (a -> Property) -> [a] -> Property
    anyP' _ [] = property True
    anyP' p xs = anyP p xs

toBoxDrawings :: Set Var -> History act -> Doc
toBoxDrawings knownVars h = exec evT (fmap out <$> Fork l p r)
  where
    (p, h') = partition (\e -> getProcessIdEvent e == Pid 0) h
    (l, r)  = partition (\e -> getProcessIdEvent e == Pid 1) h'

    out :: HistoryEvent act -> String
    out (InvocationEvent _ str var _) | var `S.member` knownVars = show var ++ " ← " ++ str
                                      | otherwise = str
    out (ResponseEvent _ str _) = str

    toEventType :: History cmd -> [(EventType, Pid)]
    toEventType = map $ \e -> case e of
      InvocationEvent _ _ _ (Pid pid) -> (Open, Pid pid)
      ResponseEvent _ _ (Pid pid)     -> (Close, Pid pid)
    evT :: [(EventType, Pid)]
    evT = toEventType (filter (\e -> getProcessIdEvent e `elem` map Pid [1,2]) h)

------------------------------------------------------------------------

liftGenFork
  :: Generator    model act
  -> Precondition model act
  -> Transition   model act
  -> model Symbolic
  -> Gen (Fork (Program act))
liftGenFork gen pre next model = do
  (prefix, model') <- liftGen gen pre next model  0
  (left,   _)      <- liftGen gen pre next model' (length (unProgram prefix) + 1)
  (right,  _)      <- liftGen gen pre next model' (length (unProgram left)   + 1)
  return (Fork left prefix right)

liftGenParallelProgram
  :: Generator    model act
  -> Precondition model act
  -> Transition   model act
  -> model Symbolic
  -> Gen (ParallelProgram act)
liftGenParallelProgram gen pre next model =
  fmap ParallelProgram (liftGenFork gen pre next model)

forkFilterInvalid
  :: HFoldable act
  => Precondition model act
  -> Transition model act
  -> model Symbolic
  -> Fork (Program act)
  -> Fork (Program act)
forkFilterInvalid pre trans m (Fork l p r) =
  Fork (Program $ snd $ filterInvalid pre trans m' vars (unProgram l))
       (Program p')
       (Program $ snd $ filterInvalid pre trans m' vars (unProgram r))
  where
    ((m', vars), p') = filterInvalid pre trans m S.empty (unProgram p)

liftShrinkFork
  :: HFoldable act
  => Shrinker act
  -> Precondition model act
  -> Transition model act
  -> model Symbolic
  -> (Fork (Program act) -> [Fork (Program act)])
liftShrinkFork shrinker pre trans model (Fork (Program l) (Program p) (Program r)) =
  map (forkFilterInvalid pre trans model)
  [ Fork (Program l') (Program p') (Program r')
  | (p', (l', r')) <- shrinkPair shrinkSub (shrinkPair shrinkSub shrinkSub) (p, (l, r))
  ]
  where
  shrinkSub = shrinkList (liftShrinkInternal shrinker)

liftShrinkParallelProgram
  :: HFoldable act
  => Shrinker act
  -> Precondition model act
  -> Transition model act
  -> model Symbolic
  -> (ParallelProgram act -> [ParallelProgram act])
liftShrinkParallelProgram shrinker pre trans model =
  fmap ParallelProgram . liftShrinkFork shrinker pre trans model . unParallelProgram


-- | Lift the semantics of a single action into a semantics for forks of
--   internal actions. The prefix of the fork is executed sequentially,
--   while the two suffixes are executed in parallel, and the result (or
--   trace) is collected in a so called history.
liftSemFork
  :: HTraversable act
  => Show (Untyped act)
  => Semantics act IO
  -> Fork (Program act)
  -> IO (History act)
liftSemFork sem (Fork left prefix right) = do
  hchan <- newTChanIO
  env   <- execStateT (runMany sem hchan (Pid 0) (unProgram prefix)) emptyEnvironment
  withPool 2 $ \pool ->
    parallel_ pool
      [ evalStateT (runMany sem hchan (Pid 1) (unProgram left))  env
      , evalStateT (runMany sem hchan (Pid 2) (unProgram right)) env
      ]
  getChanContents hchan
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

-- | Lift the semantics of a single action into a semantics for parallel
--   programs. The prefix of the fork is executed sequentially,
--   while the two suffixes are executed in parallel, and the result (or
--   trace) is collected in a so called history.
liftSemParallelProgram
  :: HTraversable act
  => Show (Untyped act)
  => Semantics act IO
  -> ParallelProgram act
  -> IO (History act)
liftSemParallelProgram sem = liftSemFork sem . unParallelProgram


runMany
  :: HTraversable act
  => Show (Untyped act)
  => (forall resp. act Concrete resp -> IO resp)
  -> TChan (HistoryEvent (UntypedConcrete act))
  -> Pid
  -> [Internal act]
  -> StateT Environment IO ()
runMany sem hchan pid = flip foldM () $ \_ (Internal act sym@(Symbolic var)) -> do
  env <- get
  let cact = either (error . show) id (reify env act)
  lift $ atomically $ writeTChan hchan $
    InvocationEvent (UntypedConcrete cact) (show (Untyped act)) var pid
  resp <- lift (sem cact)
  modify (insertConcrete sym (Concrete resp))
  lift $ do
    threadDelay =<< randomRIO (0, 20)
    atomically $ writeTChan hchan $ ResponseEvent (toDyn resp) (show resp) pid

-- | Check if a history can be linearised.
checkParallelInvariant
  :: HFoldable act
  => Transition    model act
  -> Postcondition model act
  -> InitialModel model
  -> ParallelProgram act
  -> History act
  -> Property
checkParallelInvariant next post initial prog hist
  = counterexample ("Couldn't linearise:\n\n" ++ show (toBoxDrawings allVars hist))
  $ linearise next post initial hist
  where
  vars xs    = [ getUsedVars x | Internal x _ <- xs]
  Fork l p r = fmap (S.unions . vars . unProgram) $ unParallelProgram prog
  allVars    = S.unions [l, p, r]
