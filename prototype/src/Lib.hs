{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lib where

import           Control.Monad.IO.Class  (liftIO)
import           Control.Monad.State     (StateT, evalStateT, get, lift, put)
import           Data.Maybe              (fromMaybe)
import           Test.QuickCheck         (Gen, Property, Testable, choose,
                                          forAllShrink, frequency, shrinkList,
                                          sized, suchThat)
import           Test.QuickCheck.Monadic (PropertyM)

import           Types

------------------------------------------------------------------------

forAllShrinkCommands :: Testable prop
                     => Show (cmd Symbolic)
                     => StateMachine model cmd resp
                     -> ([cmd Symbolic] -> prop)     -- ^ Predicate.
                     -> Property
forAllShrinkCommands sm =
  -- forAllShrinkShow (generateCommands sm) (shrinkCommands sm) (const "")
  forAllShrink (generateCommands sm) (shrinkCommands sm)

generateCommands :: StateMachine model cmd resp -> Gen [cmd Symbolic]
generateCommands sm@StateMachine { initModel } =
  evalStateT (generateCommandsState sm 0) initModel

generateCommandsState :: forall model cmd resp. StateMachine model cmd resp
                      -> Counter
                      -> StateT (model Symbolic) Gen [cmd Symbolic]
generateCommandsState sm@StateMachine { precondition, transition, mock } counter0 = do
  size0 <- lift (sized (\k -> choose (0, k)))
  go size0 counter0 (generatorFrequency sm)
  where
    go :: Int -> Counter -> (model Symbolic -> Gen (cmd Symbolic))
       -> StateT (model Symbolic) Gen [cmd Symbolic]
    go 0    _     _   = return []
    go size counter gen = do
      model <- get
      cmd   <- lift (gen model `suchThat` precondition model)
      let resp = runGenSym (mock model cmd) counter
      put (transition model cmd resp)
      cmds  <- go (size - 1) (counter + 1) gen
      return (cmd : cmds)

generatorFrequency :: forall model cmd resp. StateMachine model cmd resp
                   -> model Symbolic
                   -> Gen (cmd Symbolic)
generatorFrequency StateMachine { generator, weight } model =
  frequency =<< sequence (map go (generator model))
  where
    go :: Gen (cmd Symbolic) -> Gen (Int, Gen (cmd Symbolic))
    go gen = do
      cmd <- gen
      return (fromMaybe (\_ _ -> 1) weight model cmd, gen)

shrinkCommands :: StateMachine model cmd resp -> [cmd Symbolic] -> [[cmd Symbolic]]
shrinkCommands sm@StateMachine { shrinker, precondition }
  = filter (validCommands sm)
  . shrinkList shrinker

validCommands :: StateMachine model cmd resp -> [cmd Symbolic] -> Bool
validCommands StateMachine { precondition } = undefined

modelCheck :: StateMachine model cmd resp -> [cmd Symbolic]
           -> PropertyM IO Result -- XXX: (History cmd, model Symbolic, Result)
modelCheck sm cmds = do
  liftIO (modelCheckIO sm 1000 cmds)

-- XXX: IO not needed...
modelCheckIO :: StateMachine model cmd resp -> Counter -> [cmd Symbolic]
             -> IO Result -- XXX: (History cmd, model Symbolic, Result)
modelCheckIO StateMachine { initModel, transition, postcondition, mock } counter =
  go initModel
  where
    go _ []           = return Ok
    go m (cmd : cmds) = do
      let resp = runGenSym (mock m cmd) counter
      if postcondition m cmd resp
      then go (transition m cmd resp) cmds
      else return PostconditionFailed

runCommands
  :: StateMachine model cmd resp
  -> [cmd Symbolic]
  -> PropertyM IO (History cmd, model Concrete, Result)
runCommands sm = liftIO . runCommandsIO sm

runCommandsIO
  :: StateMachine model cmd resp
  -> [cmd Symbolic]
  -> IO (History cmd, model Concrete, Result)
runCommandsIO = undefined

prettyPrintHistory :: StateMachine model cmd resp -> History cmd -> IO ()
prettyPrintHistory = undefined
