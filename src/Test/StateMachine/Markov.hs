{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.StateMachine.Markov
  ( tabulateMarkov
  , coverTransitions
  , (-<)
  , (>-)
  )
  where

import           Prelude
import           Test.QuickCheck
                   (Property, Testable, property)

import           Test.StateMachine.Types
                   (Command, Commands, Counter, StateMachine(..),
                   getCommand, newCounter, unCommands)
import           Test.StateMachine.Types.GenSym
                   (runGenSym)
import           Test.StateMachine.Types.References
                   (Symbolic)
import           Test.StateMachine.Utils
                   (newTabulate, newCoverTable)

------------------------------------------------------------------------

data Transition state cmd_ prob = Transition
  { from        :: state
  , command     :: cmd_
  , probability :: prob
  , to          :: state
  }

infixl 5 -<
infixl 5 >-

(-<) :: state -> (cmd_, prob) -> (state, (cmd_, prob))
(-<) = (,)

(>-) :: (state, (cmd_, prob)) -> state -> Transition state cmd_ prob
(from, (command, probability)) >- to = Transition {..}

coverTransitions :: (Show state, Show cmd_, Testable prop)
                 => [Transition state cmd_ Double] -> prop -> Property
coverTransitions ts prop = foldr go (property prop) ts
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
