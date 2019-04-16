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
  , (-<)
  , (>-)
  , (/-)
  , markovGenerator
  , coverMarkov
  , tabulateMarkov
  , transitionMatrix
  , historyObservations
  )
  where

import           Control.Arrow
                   ((&&&))
import           Data.Bifunctor
                   (bimap)
import           Data.Either
                   (partitionEithers)
import           Data.Function
                   (on)
import           Data.List
                   (genericLength, groupBy, sortBy)
import           Data.Map
                   (Map)
import qualified Data.Map                           as Map
import           Data.Matrix
                   (Matrix, matrix)
import           Data.Maybe
                   (fromMaybe)
import           Data.Ord
                   (comparing)
import           Generic.Data
                   (FiniteEnum, GBounded, GEnum, gfiniteEnumFromTo,
                   gmaxBound, gminBound, gtoFiniteEnum)
import           GHC.Generics
                   (Generic, Rep)
import           Prelude
import           Test.QuickCheck
                   (Gen, Property, Testable, frequency,
                   property)

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
import           Test.StateMachine.Utils
                   (newCoverTable, newTabulate)

------------------------------------------------------------------------

-- | Markov chain.
newtype Markov state cmd_ prob = Markov
  { unMarkov :: [[Transition state cmd_ prob]] }

data Transition state cmd_ prob = Transition
  { from        :: state
  , command     :: cmd_
  , probability :: prob
  , to          :: state
  }

-- | Constructor for 'Markov' chains.
makeMarkov :: [[Transition state cmd_ prob]] -> Markov state cmd_ prob
makeMarkov = Markov

infixl 5 -<

-- | Infix operator for starting to creating a transition in the 'Markov' chain,
--   finish the transition with one of '(>-)' or '(/-)' depending on whether the
--   transition has a specific or a uniform probability.
(-<) :: Fractional prob
     => state -> [Either (cmd_, state) ((cmd_, prob), state)]
     -> [Transition state cmd_ prob]
from -< es = map go es
  where
    go (Left   (command,               to)) = Transition from command uniform to
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
markovGenerator :: forall state cmd_ cmd model. (Show state, Ord state, Ord cmd_)
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
    go s = case availableCommands s markov of
      Nothing  -> error ("markovGenerator: deadlock, no commands can be generated in given state:\n"
                         ++ show s)
      Just dcs -> map (bimap round (\cmd_ -> (gens Map.! cmd_) model)) dcs

    availableCommands :: state -> Markov state cmd_ Double -> Maybe [(Double, cmd_)]
    availableCommands state
      = lookup state
      . go'
      . groupBy ((==) `on` from) -- XXX: Perhaps we can enforce the sorted and
                                 -- grouped structure by construction instead?
      . sortBy (comparing from)
      . concat
      . unMarkov
      where
        go' :: [[Transition state cmd_ Double]] -> [(state, [(Double, cmd_)])]
        go' []                  = []
        go' ([]         : _xss) = error "Use NonEmpty?"
        go' (xs@(x : _) : xss)  = (from x, map (probability &&& command) xs) : go' xss

-- | Variant of QuickCheck's 'coverTable' which works on 'Markov' chains.
coverMarkov :: (Show state, Show cmd_, Testable prop)
            => Markov state cmd_ Double -> prop -> Property
coverMarkov markov prop = foldr go (property prop) (concat (unMarkov markov))
  where
    go Transition {..} ih =
      newCoverTable (show from)
        [(toTransitionString command to, probability)] ih

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
    tabulateTransitions :: [Transition state cmd_ prob]
                        -> prop
                        -> Property
    tabulateTransitions ts prop = foldr go (property prop) ts
      where
        go Transition {..} ih =
          newTabulate (show from) [ toTransitionString command to ] ih

    commandsToTransitions :: StateMachine model cmd m resp
                          -> Commands cmd resp
                          -> [Transition state cmd_ ()]
    commandsToTransitions StateMachine { initModel, transition, mock } =
      go initModel newCounter [] . unCommands
      where
        go :: model Symbolic -> Counter -> [Transition state cmd_ ()]
           -> [Command cmd resp] -> [Transition state cmd_ ()]
        go _model _counter acc []           = acc
        go  model  counter acc (cmd : cmds) = go model' counter' (t : acc) cmds
          where
            cmd'   = getCommand cmd
            model' = transition model cmd' resp

            (resp, counter') = runGenSym (mock model cmd') counter

            t = Transition
                  { from        = partition model
                  , command     = constructor cmd'
                  , probability = ()
                  , to          = partition model'
                  }

------------------------------------------------------------------------

enumMatrix :: forall e a. (Generic e, GEnum FiniteEnum (Rep e), GBounded (Rep e))
           => ((e, e) -> a)
           -> Matrix a -- |e| x |e|
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
                 -> Matrix Double -- |state| x |state|
transitionMatrix markov = enumMatrix go
  where
    go :: (state, state) -> Double
    go (state, state') = fromMaybe 0
      (Map.lookup state' (availableStates state markov))

    availableStates :: state -> Markov state cmd_ Double -> Map state Double
    availableStates state
      = maybe Map.empty Map.fromList
      . lookup state
      . go'
      . groupBy ((==) `on` from) -- XXX: Perhaps we can enforce the sorted and
                                 -- grouped structure by construction instead?
      . sortBy (comparing from)
      . concat
      . unMarkov
      where
        go' :: [[Transition state cmd_ Double]] -> [(state, [(state, Double)])]
        go' []                  = []
        go' ([]         : _xss) = error "Use NonEmpty?"
        go' (xs@(x : _) : xss)  = (from x, map (to &&& probability) xs) : go' xss

------------------------------------------------------------------------

historyObservations :: forall model cmd m resp state cmd_ prob. Eq cmd_
                    => (Show cmd_, Show state, Ord state)
                    => (Generic state, GEnum FiniteEnum (Rep state), GBounded (Rep state))
                    => StateMachine model cmd m resp
                    -> Markov state cmd_ prob
                    -> (model Concrete -> state)
                    -> (cmd Concrete -> cmd_)
                    -> History cmd resp
                    -> ( Matrix Double -- |state| x |state|
                       , Matrix Double -- |state| x |state|
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
          state' = nextState state (constructor cmd) markov
          incr   = Map.insertWith (\_new old -> old + 1) (state, state') 1
        in
          go model ss (incr fs) ops

    nextState :: state -> cmd_ -> Markov state cmd_ prob -> state
    nextState state cmd
      = fromMaybe (error ("historyObservations: impossible, command doesn't exist: " ++ show cmd))
      . lookup cmd
      . fromMaybe (error ("historyObservations: impossible, state doesn't exist: " ++ show state))
      . lookup state
      . go'
      . groupBy ((==) `on` from) -- XXX: Perhaps we can enforce the sorted and
                                 -- grouped structure by construction instead?
      . sortBy (comparing from)
      . concat
      . unMarkov
      where
        go' :: [[Transition state cmd_ prob]] -> [(state, [(cmd_, state)])]
        go' []                  = []
        go' ([]         : _xss) = error "Use NonEmpty?"
        go' (xs@(x : _) : xss)  = (from x, map (command &&& to) xs) : go' xss
