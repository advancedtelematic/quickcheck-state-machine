{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.StateMachine.Markov
  ( Markov(..)
  , Transition(..)
  , tabulateMarkov
  , coverMarkov
  , (-<)
  , (>-)
  , markovGenerator
  )
  where

import           Control.Arrow
                   ((&&&))
import           Data.Bifunctor
                   (bimap)
import           Data.Function
                   (on)
import           Data.List
                   (groupBy, sortBy)
import           Data.Map
                   (Map)
import qualified Data.Map                           as Map
import           Data.Ord
                   (comparing)
import           Prelude
import           Test.QuickCheck
                   (Gen, Property, Testable, frequency, property)

import           Test.StateMachine.Types
                   (Command, Commands, Counter, StateMachine(..),
                   getCommand, newCounter, unCommands)
import           Test.StateMachine.Types.GenSym
                   (runGenSym)
import           Test.StateMachine.Types.References
                   (Symbolic)
import           Test.StateMachine.Utils
                   (newCoverTable, newTabulate)

------------------------------------------------------------------------

newtype Markov state cmd_ prob = Markov
  { unMarkov :: [[Transition state cmd_ prob]] }

data Transition state cmd_ prob = Transition
  { from        :: state
  , command     :: cmd_
  , probability :: prob
  , to          :: state
  }

infixl 5 -<
infixl 5 >-

(-<) :: state -> [((cmd_, prob), state)] -> [Transition state cmd_ prob]
from -< xs = [ Transition {..} | ((command, probability), to) <- xs ]

(>-) :: (cmd_, prob) -> state -> ((cmd_, prob), state)
(>-) = (,)

coverMarkov :: (Show state, Show cmd_, Testable prop)
            => Markov state cmd_ Double -> prop -> Property
coverMarkov markov prop = foldr go (property prop) (concat (unMarkov markov))
  where
    go Transition {..} ih = newCoverTable (show from)
                              [(toTransitionString command to, probability)] ih

commandsToTransitions :: forall model state cmd cmd_ m resp.
                         StateMachine model cmd m resp
                      -> (model Symbolic -> state)
                      -> (cmd Symbolic -> cmd_)
                      -> Commands cmd resp
                      -> [Transition state cmd_ ()]
commandsToTransitions StateMachine { initModel, transition, mock } partition constructor =
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

tabulateTransitions :: (Show cmd_, Show state, Testable prop)
                    => [Transition state cmd_ prob]
                    -> prop
                    -> Property
tabulateTransitions ts prop = foldr go (property prop) ts
  where
    go Transition {..} ih = newTabulate (show from) [ toTransitionString command to ] ih

toTransitionString :: (Show state, Show cmd_) => cmd_ -> state -> String
toTransitionString cmd to = "-< " ++ show cmd ++ " >- " ++ show to

tabulateMarkov :: (Show cmd_, Show state, Testable prop)
               => StateMachine model cmd m resp
               -> (model Symbolic -> state)
               -> (cmd Symbolic -> cmd_)
               -> Commands cmd resp
               -> prop
               -> Property
tabulateMarkov sm partition constructor cmds =
  tabulateTransitions (commandsToTransitions sm partition constructor cmds)

------------------------------------------------------------------------

availableCommands :: Ord state
                  => state -> Markov state cmd_ Double -> Maybe [(Double, cmd_)]
availableCommands state
  = lookup state
  . go
  . groupBy ((==) `on` from)
  . sortBy (comparing from)
  . concat
  . unMarkov
  where
    go :: [[Transition state cmd_ Double]] -> [(state, [(Double, cmd_)])]
    go []                  = []
    go ([]         : _xss) = error "Use NonEmpty?"
    go (xs@(x : _) : xss)  = (from x, map (probability &&& command) xs) : go xss

markovGenerator :: forall state cmd_ cmd model. (Show state, Ord state, Ord cmd_)
                => Markov state cmd_ Double
                -> Map cmd_ (model Symbolic -> Gen (cmd Symbolic))
                -> (model Symbolic -> Maybe state)
                -> (model Symbolic -> Maybe (Gen (cmd Symbolic)))
markovGenerator markov gens partition model = fmap (frequency . go) (partition model)
  where
    go :: state -> [(Int, Gen (cmd Symbolic))]
    go s = case availableCommands s markov of
      Nothing  -> error ("markovGenerator: deadlock, no commands can be generated in given state:\n"
                         ++ show s)
      Just dcs -> map (bimap round (\cmd_ -> (gens Map.! cmd_) model)) dcs
