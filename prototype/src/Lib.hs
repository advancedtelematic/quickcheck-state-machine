{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lib where

import           Control.Concurrent.STM
                   (atomically)
import           Control.Concurrent.STM.TChan
                   (TChan, writeTChan)
import           Control.Monad.State
                   (StateT, evalStateT, get, lift, put)
import           Data.Dynamic
                   (Dynamic, toDyn)
import           Data.Either
                   (fromRight)
import           Data.Maybe
                   (fromMaybe)
import           Data.Set
                   (Set)
import qualified Data.Set                     as S
import qualified Rank2
import           Test.QuickCheck
                   (Gen, Property, Testable, choose, frequency,
                   shrinkList, sized, suchThat)
import           Test.QuickCheck.Monadic
                   (PropertyM, run)
import           Text.Show.Pretty
                   (ppShow)

import           QuickCheckUtils
import           Types

------------------------------------------------------------------------

forAllShrinkCommands :: Testable prop
                     => (Show (cmd Symbolic), Show (resp Symbolic))
                     => (Rank2.Foldable cmd, Rank2.Foldable resp)
                     => StateMachine model cmd resp
                     -> (Commands cmd resp -> prop)     -- ^ Predicate.
                     -> Property
forAllShrinkCommands sm =
  forAllShrinkShow (generateCommands sm) (shrinkCommands sm) ppShow

generateCommands :: StateMachine model cmd resp -> Gen (Commands cmd resp)
generateCommands sm@StateMachine { initModel } =
  evalStateT (generateCommandsState sm newCounter) initModel

generateCommandsState :: forall model cmd resp. StateMachine model cmd resp
                      -> Counter
                      -> StateT (model Symbolic) Gen (Commands cmd resp)
generateCommandsState sm@StateMachine { precondition, transition, mock } counter0 = do
  size0 <- lift (sized (\k -> choose (0, k)))
  Commands <$> go size0 counter0 (generatorFrequency sm)
  where
    go :: Int -> Counter -> (model Symbolic -> Gen (cmd Symbolic))
       -> StateT (model Symbolic) Gen [Command cmd resp]
    go 0    _       _   = return []
    go size counter gen = do
      model <- get
      cmd   <- lift (gen model `suchThat` precondition model)
      let (resp, counter') = runGenSym (mock model cmd) counter
      put (transition model cmd resp)
      cmds  <- go (size - 1) counter' gen
      return (Command cmd resp : cmds)

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

getUsedVars :: Rank2.Foldable f => f Symbolic -> Set Var
getUsedVars = Rank2.foldMap (\(Symbolic v) -> S.singleton v)

-- | Shrink commands in a pre-condition and scope respecting way.
shrinkCommands :: (Rank2.Foldable cmd, Rank2.Foldable resp)
               => StateMachine model cmd resp -> Commands cmd resp
               -> [Commands cmd resp]
shrinkCommands sm@StateMachine { shrinker }
  = filter (validCommands sm)
  . map Commands
  . shrinkList (liftShrinkCommand shrinker)
  . unCommands

liftShrinkCommand :: (cmd Symbolic -> [cmd Symbolic])
                  -> (Command cmd resp -> [Command cmd resp])
liftShrinkCommand shrinker (Command cmd resp) =
  [ Command cmd' resp | cmd' <- shrinker cmd ]

validCommands :: forall model cmd resp. (Rank2.Foldable cmd, Rank2.Foldable resp)
              => StateMachine model cmd resp -> Commands cmd resp -> Bool
validCommands StateMachine { precondition, transition, initModel } =
  go initModel S.empty . unCommands
  where
    go :: model Symbolic -> Set Var -> [Command cmd resp] -> Bool
    go _     _     []                        = True
    go model scope (Command cmd resp : cmds) =
      valid && go (transition model cmd resp) (getUsedVars resp `S.union` scope) cmds
      where
        valid = precondition model cmd && getUsedVars cmd `S.isSubsetOf` scope

modelCheck :: forall model cmd resp m. Monad m => StateMachine model cmd resp
           -> Commands cmd resp
           -> PropertyM m Reason -- XXX: (History cmd, model Symbolic, Reason)
modelCheck StateMachine { initModel, transition, precondition, postcondition }
  = run . return . go initModel . unCommands
  where
    go :: model Symbolic -> [Command cmd resp] -> Reason
    go _ []                        = Ok
    go m (Command cmd resp : cmds)
      | not (precondition m cmd) = PreconditionFailed
      | otherwise                =
          if postcondition m cmd resp
          then go (transition m cmd resp) cmds
          else PostconditionFailed

runCommands :: StateMachine model cmd resp
            -> Commands cmd resp
            -> PropertyM IO (History cmd resp, model Concrete, Reason)
runCommands sm = run . runCommandsIO sm

runCommandsIO :: StateMachine model cmd resp
              -> Commands cmd resp
              -> IO (History cmd resp, model Concrete, Reason)
runCommandsIO = undefined

prettyPrintHistory :: StateMachine model cmd resp -> History cmd resp -> IO ()
prettyPrintHistory = undefined

{-
-- | Execute a program and return a history, the final model and a result which
--   contains the information of whether the execution respects the state
--   machine model or not.
executeProgram
  :: MonadBaseControl IO m
  => Show1 (act Symbolic)
  => HTraversable act
  => Show err
  => StateMachine' model act m err
  -> Program act
  -> m (History act err, model Concrete, Reason)
executeProgram sm@StateMachine{..} prog = do
  hchan <- liftBaseWith (const newTChanIO)
  let eenv = ExecutionEnv emptyEnvironment model' model'
  (reason, eenv') <- runStateT (executeProgram' sm hchan (Pid 0) True prog) eenv
  hist <- liftBaseWith (const (getChanContents hchan))
  return (History hist, cmodel eenv', reason)
-}

data ExecutionEnv model = ExecutionEnv
  { env    :: Environment
  , smodel :: model Symbolic
  , cmodel :: model Concrete
  }

executeCommands
  :: (Rank2.Traversable cmd, Rank2.Foldable resp)
  => StateMachine model cmd resp
  -> TChan (Pid, HistoryEvent cmd resp)
  -> Pid
  -> Bool -- ^ Check post-condition?
  -> Commands cmd resp
  -> StateT (ExecutionEnv model) IO Reason
executeCommands StateMachine { transition, precondition,
                               postcondition, semantics } hchan pid check =
  go . unCommands
  where
    go []                        = return Ok
    go (Command cmd resp : cmds) = do
      ExecutionEnv { env, smodel, cmodel } <- get
      if not (precondition smodel cmd)
      then
        return PreconditionFailed
      else do
        let ccmd = fromRight (error "executeCommands: impossible") (reify env cmd)
        lift (atomically (writeTChan hchan (pid, Invocation cmd)))
        cresp <- lift (semantics ccmd)
        lift (atomically (writeTChan hchan (pid, Response cresp)))
        if check && not (postcondition cmodel ccmd cresp)
        then
          return PostconditionFailed
        else do
          put ExecutionEnv
                { smodel = transition smodel  cmd  resp
                , cmodel = transition cmodel ccmd cresp
                , env    = insertConcretes (S.toList (getUsedVars resp))
                                           (getUsedConcrete cresp) env
                }
          go cmds

getUsedConcrete :: Rank2.Foldable f => f Concrete -> [Dynamic]
getUsedConcrete = Rank2.foldMap (\(Concrete x u) -> [toDyn (x, u)])
