{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Markov
-- Copyright   :  (C) 2019, Stevan Andjelkovic
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan.andjelkovic@here.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains helper functions for testing using Markov chains.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Markov
  ( Markov
  , makeMarkov
  , toAdjacencyMap
  , (-<)
  , (>-)
  , (/-)
  , markovGenerator
  , coverMarkov
  , tabulateMarkov
  , transitionMatrix
  , stimulusMatrix
  , historyObservations
  , markovToDot
  , markovToPs
  , StatsDb(..)
  , PropertyName
  , nullStatsDb
  , fileStatsDb
  , persistStats
  , computeReliability
  , printReliability
  , quickCheckReliability
  )
  where

import           Control.Arrow
                   ((&&&))
import           Data.Bifunctor
                   (bimap)
import           Data.Either
                   (partitionEithers)
import           Data.List
                   (genericLength)
import           Data.Map
                   (Map)
import qualified Data.Map                           as Map
import           Data.Matrix
                   (Matrix, elementwise, fromLists, matrix, ncols,
                   nrows, submatrix, toLists, zero)
import           Data.Maybe
                   (fromMaybe)
import           Generic.Data
                   (FiniteEnum, GBounded, GEnum, gfiniteEnumFromTo,
                   gmaxBound, gminBound, gtoFiniteEnum)
import           GHC.Generics
                   (Generic, Rep)
import           Prelude                            hiding
                   (readFile)
import           System.Directory
                   (removeFile)
import           System.FilePath.Posix
                   (replaceExtension)
import           System.IO
                   (IOMode(ReadWriteMode), hGetContents, openFile)
import           System.Process
                   (callProcess)
import           Test.QuickCheck
                   (Gen, Property, Testable, coverTable, frequency,
                   property, quickCheck, tabulate)
import           Test.QuickCheck.Monadic
                   (PropertyM, run)
import           Test.QuickCheck.Property
                   (Callback(PostTest),
                   CallbackKind(NotCounterexample), callback)
import           Text.Read
                   (readMaybe)

import           MarkovChain

import           Test.StateMachine.Logic
                   (boolean)
import           Test.StateMachine.Types
                   (Command, Commands, Counter, History, Operation(..),
                   StateMachine(..), getCommand, makeOperations,
                   newCounter, unCommands, unHistory)
import           Test.StateMachine.Types.GenSym
                   (runGenSym)
import           Test.StateMachine.Types.References
                   (Concrete, Symbolic)

------------------------------------------------------------------------

-- | Markov chain.
newtype Markov state cmd_ prob = Markov
  { unMarkov :: Map state [Transition state cmd_ prob] }

data Transition state cmd_ prob = Transition
  { command     :: cmd_
  , probability :: prob
  , to          :: state
  }

-- | Constructor for 'Markov' chains.
makeMarkov :: Ord state
           => [Map state [Transition state cmd_ prob]] -> Markov state cmd_ prob
makeMarkov = Markov . Map.unions

-- | Expose inner graph structure of markov chain
toAdjacencyMap
  :: Ord state
  => Markov state cmd_ prob
  -> Map state (Map state (cmd_, prob))
toAdjacencyMap (Markov m) =
  fmap (foldr f mempty) m
  where
    f Transition{..} = Map.insert to (command, probability)

infixl 5 -<

-- | Infix operator for starting to creating a transition in the 'Markov' chain,
--   finish the transition with one of '(>-)' or '(/-)' depending on whether the
--   transition has a specific or a uniform probability.
(-<) :: Fractional prob
     => state -> [Either (cmd_, state) ((cmd_, prob), state)]
     -> Map state [Transition state cmd_ prob]
from -< es = Map.singleton from (map go es)
  where
    go (Left   (command,               to)) = Transition command uniform to
    go (Right ((command, probability), to)) = Transition {..}

    (ls, rs) = partitionEithers es
    uniform  = (100 - sum (map snd (map fst rs))) / genericLength ls
    -- ^ Note: If `length ls == 0` then `uniform` is not used, so division by
    -- zero doesn't happen.

infixl 5 >-

-- | Finish making a transition with a specified probability distribution.
(>-) :: (cmd_, prob) -> state -> Either (cmd_, state) ((cmd_, prob), state)
(cmd, prob) >- state = Right ((cmd, prob), state)

infixl 5 /-

-- | Finish making a transition with an uniform probability distribution.
(/-) :: cmd_ -> state -> Either (cmd_, state) ((cmd_, prob), state)
cmd /- state = Left (cmd, state)

------------------------------------------------------------------------

-- | Create a generator from a 'Markov' chain.
markovGenerator :: forall state cmd_ cmd model. (Show state, Show cmd_)
                => (Ord state, Ord cmd_)
                => Markov state cmd_ Double
                -> Map cmd_ (model Symbolic -> Gen (cmd Symbolic))
                -> (model Symbolic -> state)
                -> (state -> Bool)
                -> (model Symbolic -> Maybe (Gen (cmd Symbolic)))
markovGenerator markov gens partition isSink model
  | isSink (partition model) = Nothing
  | otherwise                = Just (frequency (go (partition model)))
  where
    go :: state -> [(Int, Gen (cmd Symbolic))]
    go state
      = map (round . probability
             &&& (\cmd_ -> fromMaybe (errMissing cmd_) (Map.lookup cmd_ gens) model) . command)
      . fromMaybe errDeadlock
      . Map.lookup state
      . unMarkov
      $ markov
      where
        errDeadlock = error
          ("markovGenerator: deadlock, no commands can be generated in given state: "
          ++ show state)

        errMissing cmd_ = error
          ("markovGenerator: don't know how to generate the command: "
          ++ show cmd_)

-- | Variant of QuickCheck's 'coverTable' which works on 'Markov' chains.
coverMarkov :: (Show state, Show cmd_, Testable prop)
            => Markov state cmd_ Double -> prop -> Property
coverMarkov markov prop = foldr go (property prop) (Map.toList (unMarkov markov))
  where
    go (from, ts) ih =
      coverTable (show from)
        (map (\Transition{..} -> (toTransitionString command to, probability)) ts) ih

toTransitionString :: (Show state, Show cmd_) => cmd_ -> state -> String
toTransitionString cmd to = "-< " ++ show cmd ++ " >- " ++ show to

-- | Variant of QuickCheck's 'tabulate' which works for 'Markov' chains.
tabulateMarkov :: forall model state cmd cmd_ m resp prop. Testable prop
               => (Show state, Show cmd_)
               => StateMachine model cmd m resp
               -> (model Symbolic -> state)
               -> (cmd Symbolic -> cmd_)
               -> Commands cmd resp
               -> prop
               -> Property
tabulateMarkov sm partition constructor cmds0 =
  tabulateTransitions (commandsToTransitions sm cmds0)
  where
    tabulateTransitions :: [(state, Transition state cmd_ prob)]
                        -> prop
                        -> Property
    tabulateTransitions ts prop = foldr go (property prop) ts
      where
        go (from, Transition {..}) ih =
          tabulate (show from) [ toTransitionString command to ] ih

    commandsToTransitions :: StateMachine model cmd m resp
                          -> Commands cmd resp
                          -> [(state, Transition state cmd_ ())]
    commandsToTransitions StateMachine { initModel, transition, mock } =
      go initModel newCounter [] . unCommands
      where
        go :: model Symbolic -> Counter -> [(state, Transition state cmd_ ())]
           -> [Command cmd resp] -> [(state, Transition state cmd_ ())]
        go _model _counter acc []           = acc
        go  model  counter acc (cmd : cmds) = go model' counter' ((from, t) : acc) cmds
          where
            from   = partition model
            cmd'   = getCommand cmd
            model' = transition model cmd' resp

            (resp, counter') = runGenSym (mock model cmd') counter

            t = Transition
                  { command     = constructor cmd'
                  , probability = ()
                  , to          = partition model'
                  }

------------------------------------------------------------------------

enumMatrix :: forall e a. (Generic e, GEnum FiniteEnum (Rep e), GBounded (Rep e))
           => ((e, e) -> a)
           -> Matrix a
enumMatrix f = matrix dimension dimension (f . bimap g g)
  where
    g :: Int -> e
    g = gtoFiniteEnum . pred -- We need the predecessor because 'matrix' starts
                             -- indexing from 1.

    dimension :: Int
    dimension = length es

    es :: [e]
    es = gfiniteEnumFromTo gminBound gmaxBound

transitionMatrix :: forall state cmd_. Ord state
                 => (Generic state, GEnum FiniteEnum (Rep state), GBounded (Rep state))
                 => Markov state cmd_ Double
                 -> Matrix Double
transitionMatrix markov = enumMatrix go
  where
    go :: (state, state) -> Double
    go (state, state') = fromMaybe 0
      (Map.lookup state' =<< Map.lookup state availableStates)

    availableStates :: Map state (Map state Double)
    availableStates
      = fmap (Map.fromList . map (to &&& (/ 100) . probability))
      . unMarkov
      $ markov

enumMatrix'
  :: forall state cmd a
   . (Generic state, GEnum FiniteEnum (Rep state), GBounded (Rep state))
  => (Generic cmd,   GEnum FiniteEnum (Rep cmd),   GBounded (Rep cmd))
  => ((state, cmd) -> a)
  -> Matrix a
enumMatrix' f = matrix m n (f . bimap g h)
  where
    g :: Int -> state
    g = gtoFiniteEnum . pred -- We need the predecessor because 'matrix' starts
                             -- indexing from 1.

    h :: Int -> cmd
    h = gtoFiniteEnum . pred

    m :: Int
    m = length states

    n :: Int
    n = length cmds

    states :: [state]
    states = gfiniteEnumFromTo gminBound gmaxBound

    cmds :: [cmd]
    cmds = gfiniteEnumFromTo gminBound gmaxBound

stimulusMatrix
  :: forall state cmd. (Ord state, Ord cmd)
  => (Generic state, GEnum FiniteEnum (Rep state), GBounded (Rep state))
  => (Generic cmd,   GEnum FiniteEnum (Rep cmd),   GBounded (Rep cmd))
  => Markov state cmd Double
  -> Matrix Double
stimulusMatrix markov = enumMatrix' go
  where
    go :: (state, cmd) -> Double
    go (state, cmd) = fromMaybe 0
      (Map.lookup cmd =<< Map.lookup state availableCmds)

    availableCmds :: Map state (Map cmd Double)
    availableCmds
      = fmap (Map.fromList . map (command &&& (/ 100) . probability))
      . unMarkov
      $ markov

------------------------------------------------------------------------

historyObservations :: forall model cmd m resp state cmd_ prob. Ord state
                    => Ord cmd_
                    => (Generic state, GEnum FiniteEnum (Rep state), GBounded (Rep state))
                    => StateMachine model cmd m resp
                    -> Markov state cmd_ prob
                    -> (model Concrete -> state)
                    -> (cmd Concrete -> cmd_)
                    -> History cmd resp
                    -> ( Matrix Double
                       , Matrix Double
                       )
historyObservations StateMachine { initModel, transition, postcondition } markov partition constructor
  = go initModel Map.empty Map.empty . makeOperations . unHistory
  where
    go _model ss fs [] =
      ( enumMatrix @state (fromMaybe 0 . flip Map.lookup ss)
      , enumMatrix @state (fromMaybe 0 . flip Map.lookup fs)
      )
    go  model ss fs (op : ops) = case op of
      Operation cmd resp _pid ->
        let
          state  = partition model
          model' = transition model cmd resp
          state' = partition model'
          incr   = Map.insertWith (\_new old -> old + 1) (state, state') 1
        in
          if boolean (postcondition model cmd resp)
          then go model' (incr ss) fs        ops
          else go model' ss        (incr fs) ops

      Crash cmd _err _pid ->
        let
          state  = partition model
          state' = fromMaybe err
                     (Map.lookup (constructor cmd) =<< Map.lookup state nextState)
          incr   = Map.insertWith (\_new old -> old + 1) (state, state') 1
        in
          go model ss (incr fs) ops
        where
          err = error "historyObservations: impossible."

    nextState :: Map state (Map cmd_ state)
    nextState
      = fmap (Map.fromList . map (command &&& to))
      . unMarkov
      $ markov

------------------------------------------------------------------------

markovToDot :: (Show state, Show cmd_, Show prob)
            => Markov state cmd_ prob -> String
markovToDot = go "digraph g {\n" . Map.toList . unMarkov
  where
    go acc []                   = acc ++ "}"
    go acc ((from, via) : more) = go acc' more
      where
        acc' :: String
        acc' = acc ++
          unlines [ string (show from) ++
                    " -> " ++
                    string (show to) ++
                    " [label=" ++ string (show cmd ++ "\\n(" ++ show prob ++ "%)") ++ "]"
                  | Transition cmd prob to <- via
                  ]

        string :: String -> String
        string s = "\"" ++ s ++ "\""

markovToPs :: (Show state, Show cmd_, Show prob)
           => Markov state cmd_ prob -> FilePath -> IO ()
markovToPs markov out = do
  let dotFile = replaceExtension out "dot"
  writeFile dotFile (markovToDot markov)
  callProcess "dot" ["-Tps", dotFile, "-o", out]

------------------------------------------------------------------------

data StatsDb m = StatsDb
  { store :: (Matrix Double, Matrix Double) -> m ()
  , load  :: m (Maybe (Matrix Double, Matrix Double))
  }

type PropertyName = String

nullStatsDb :: Monad m => StatsDb m
nullStatsDb = StatsDb
  { store = const (return ())
  , load  = return Nothing
  }

fileStatsDb :: FilePath -> PropertyName -> StatsDb IO
fileStatsDb fp name = StatsDb
  { store = store
  , load  = load
  }
  where
    store :: (Matrix Double, Matrix Double) -> IO ()
    store observed = do
      appendFile (fp ++ "-" ++ name) (show (bimap toLists toLists observed) ++ "\n")

    load :: IO (Maybe (Matrix Double, Matrix Double))
    load = do
      mprior <- parse     <$> readFile' (fp ++ "-" ++ name ++ "-cache")
      mnew   <- parseMany <$> readFile' (fp ++ "-" ++ name)

      let sumElem :: [Matrix Double] -> Matrix Double
          sumElem = foldl1 (elementwise (+))

      let mprior' = case (mprior, mnew) of
            (Just (sprior, fprior), Just new) ->
              Just (bimap sumElem sumElem (bimap (sprior :) (fprior :) (unzip new)))
            (Nothing, Just new)   -> Just (bimap sumElem sumElem (unzip new))
            (Just prior, Nothing) -> Just prior
            (Nothing, Nothing)    -> Nothing

      case mprior' of
        Just prior' -> writeFile  (fp ++ "-" ++ name ++ "-cache") (show (bimap toLists toLists prior'))
        Nothing     -> return ()

      removeFile (fp ++ "-" ++ name)

      return mprior'

      where
        parseMany :: String -> Maybe ([(Matrix Double, Matrix Double)])
        parseMany = sequence
                  . map parse
                  . lines

        parse :: String -> Maybe (Matrix Double, Matrix Double)
        parse = fmap (bimap fromLists fromLists) . readMaybe

    readFile' :: FilePath -> IO String
    readFile' file = hGetContents =<< openFile file ReadWriteMode

persistStats :: Monad m
             => StatsDb m -> (Matrix Double, Matrix Double) -> PropertyM m ()
persistStats StatsDb { store } = run . store

computeReliability :: Monad m
                   => StatsDb m -> Matrix Double -> (Matrix Double, Matrix Double)
                   -> m (Double, Double)
computeReliability StatsDb { load } usage observed = do
  mpriors <- load

  return (singleUseReliability (reduce usage) mpriors (bimap reduce reduce observed))
    where
      n      = ncols usage
      m      = pred n
      reduce = submatrix 1 m 1 n

printReliability :: Testable prop
                 => StatsDb IO -> Matrix Double -> (Matrix Double, Matrix Double)
                 -> prop -> Property
printReliability sdb usage observed = callback $ PostTest NotCounterexample $ \_state _result ->
  print =<< computeReliability sdb usage observed

quickCheckReliability :: Testable prop
                      => StatsDb IO -> Matrix Double -> prop -> IO ()
quickCheckReliability sdb usage prop = do
  quickCheck prop
  print =<< computeReliability sdb usage observed
    where
      observed = ( zero (nrows usage) (ncols usage)
                 , zero (nrows usage) (ncols usage)
                 )
