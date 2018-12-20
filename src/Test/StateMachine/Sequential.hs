{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Sequential
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan.andjelkovic@here.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains helpers for generating, shrinking, and checking
-- sequential programs.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Sequential
  ( forAllCommands
  , generateCommands
  , generateCommandsState
  , getUsedVars
  , shrinkCommands
  , liftShrinkCommand
  , validCommands
  , filterMaybe
  , runCommands
  , getChanContents
  , executeCommands
  , prettyPrintHistory
  , prettyCommands
  , commandNames
  , commandNamesInOrder
  , checkCommandNames
  , tabulateState
  )
  where

import           Control.Exception
                   (ErrorCall, IOException, displayException)
import           Control.Monad.Catch
                   (MonadCatch, catch)
import           Control.Monad.State.Strict
                   (MonadIO, State, StateT, evalState, evalStateT, get,
                   lift, put, runStateT)
import           Data.Dynamic
                   (Dynamic, toDyn)
import           Data.Either
                   (fromRight)
import           Data.List
                   (groupBy, sortBy)
import qualified Data.Map                          as M
import           Data.Map.Strict
                   (Map)
import           Data.Maybe
                   (fromMaybe)
import           Data.Monoid
                   ((<>))
import           Data.Proxy
                   (Proxy(..))
import           Data.Set
                   (Set)
import qualified Data.Set                          as S
import           Data.TreeDiff
                   (ToExpr, ansiWlBgEditExprCompact, ediff)
import           Generic.Data
                   (FiniteEnum, GBounded, GEnum)
import           GHC.Generics
                   (Generic, Generic1, Rep, Rep1, from1)
import           Prelude
import           Test.QuickCheck
                   (Gen, Property, Testable, choose, collect,
                   shrinkList, sized, tabulate)
import           Test.QuickCheck.Monadic
                   (PropertyM, monitor, run)
import           Text.PrettyPrint.ANSI.Leijen
                   (Doc)
import qualified Text.PrettyPrint.ANSI.Leijen      as PP
import           Text.Show.Pretty
                   (ppShow)
import           UnliftIO
                   (TChan, atomically, newTChanIO, tryReadTChan,
                   writeTChan)

import           Test.StateMachine.ConstructorName
import           Test.StateMachine.Logic
import           Test.StateMachine.Markov
import           Test.StateMachine.Types
import qualified Test.StateMachine.Types.Rank2     as Rank2
import           Test.StateMachine.Utils

------------------------------------------------------------------------

forAllCommands :: Testable prop
               => (Show (cmd Symbolic), Show (model Symbolic), Show state)
               => (Generic state, GEnum FiniteEnum (Rep state), GBounded (Rep state))
               => (Rank2.Foldable cmd, Rank2.Foldable resp)
               => AdvancedStateMachine model state cmd m resp
               -> Maybe Int -- ^ Minimum number of commands.
               -> (Commands cmd -> prop)     -- ^ Predicate.
               -> Property
forAllCommands sm mnum =
  forAllShrinkShow (generateCommands sm mnum) (shrinkCommands sm) ppShow

generateCommands :: (Rank2.Foldable resp, Show (model Symbolic))
                 => (Generic state, GEnum FiniteEnum (Rep state), GBounded (Rep state))
                 => (Show state, Show (cmd Symbolic))
                 => AdvancedStateMachine model state cmd m resp
                 -> Maybe Int -- ^ Minimum number of commands.
                 -> Gen (Commands cmd)
generateCommands sm@StateMachine { initModel } mnum =
  evalStateT (generateCommandsState sm newCounter mnum) initModel

generateCommandsState :: forall model state cmd m resp. Rank2.Foldable resp
                      => (Generic state, GEnum FiniteEnum (Rep state), GBounded (Rep state))
                      => (Show (model Symbolic), Show state, Show (cmd Symbolic))
                      => AdvancedStateMachine model state cmd m resp
                      -> Counter
                      -> Maybe Int -- ^ Minimum number of commands.
                      -> StateT (model Symbolic) Gen (Commands cmd)
generateCommandsState StateMachine { precondition, generator, transition, distribution, mock } counter0 mnum
  = case distribution of
      Nothing              -> sizeBased
      Just (markov, start) -> chainBased markov start
  where
    sizeBased :: StateT (model Symbolic) Gen (Commands cmd)
    sizeBased = do
      size0 <- lift (sized (\k -> choose (fromMaybe 0 mnum, k)))
      Commands <$> go size0 counter0 []
      where
        go :: Int -> Counter -> [Command cmd]
           -> StateT (model Symbolic) Gen [Command cmd]
        go 0    _       cmds = return (reverse cmds)
        go size counter cmds = do
          model <- get
          mnext <- lift $ [(1, generator model)] `suchThatOneOf` (boolean . precondition model)
          case mnext of
            Nothing   -> error $ concat
                           [ "A deadlock occured while generating commands.\n"
                           , "No pre-condition holds in the following model:\n"
                           , ppShow model
                           -- XXX: show trace of commands generated so far?
                           ]
            Just next -> do
              let (resp, counter') = runGenSym (mock model next) counter
              put (transition model next resp)
              go (size - 1) counter' (Command next (getUsedVars resp) : cmds)

    chainBased :: Markov model state cmd
               -> state
               -> StateT (model Symbolic) Gen (Commands cmd)
    chainBased markov start = Commands <$> go counter0 [] start
      where
        go :: Counter -> [Command cmd] -> state -> StateT (model Symbolic) Gen [Command cmd]
        go counter cmds state = do
          model <- get
          let gen = runMarkov markov model state
          ecmd  <- lift (gen `suchThatEither` \case
                           Nothing       -> True
                           Just (cmd, _) -> boolean (precondition model cmd))
          case ecmd of
            Left ces -> error $ concat
                          [ "\n"
                          , "A deadlock occured while generating commands.\n"
                          , "No pre-condition holds in the following model:\n\n"
                          , "    " ++ ppShow model
                          , "\n\nThe following commands have been generated so far:\n\n"
                          , "    " ++ ppShow (reverse cmds)
                          , "\n\n"
                          , "Example commands generated whose pre-condition doesn't hold:\n\n"
                          , "    " ++ ppShow ces
                          , "\n"
                          ]
            Right Nothing                 -> return (reverse cmds)
            Right (Just (cmd, state')) -> do
              let (resp, counter') = runGenSym (mock model cmd) counter
              put (transition model cmd resp)
              go counter' (Command cmd (getUsedVars resp) : cmds) state'

getUsedVars :: Rank2.Foldable f => f Symbolic -> Set Var
getUsedVars = Rank2.foldMap (\(Symbolic v) -> S.singleton v)

-- | Shrink commands in a pre-condition and scope respecting way.
shrinkCommands :: (Rank2.Foldable cmd, Rank2.Foldable resp)
               => AdvancedStateMachine model state cmd m resp -> Commands cmd
               -> [Commands cmd]
shrinkCommands sm@StateMachine { initModel, shrinker }
  = filterMaybe ( flip evalState (initModel, S.empty, newCounter)
                . validCommands sm
                . Commands)
  . shrinkList (liftShrinkCommand shrinker)
  . unCommands

liftShrinkCommand :: (cmd Symbolic -> [cmd Symbolic])
                  -> (Command cmd -> [Command cmd])
liftShrinkCommand shrinker (Command cmd resp) =
  [ Command cmd' resp | cmd' <- shrinker cmd ]

filterMaybe :: (a -> Maybe b) -> [a] -> [b]
filterMaybe _ []       = []
filterMaybe f (x : xs) = case f x of
  Nothing ->     filterMaybe f xs
  Just y  -> y : filterMaybe f xs

validCommands :: forall model state cmd m resp. (Rank2.Foldable cmd, Rank2.Foldable resp)
              => AdvancedStateMachine model state cmd m resp -> Commands cmd
              -> State (model Symbolic, Set Var, Counter) (Maybe (Commands cmd))
validCommands StateMachine { precondition, transition, mock } =
  fmap (fmap Commands) . go . unCommands
  where
    go :: [Command cmd] -> State (model Symbolic, Set Var, Counter) (Maybe [Command cmd])
    go []                         = return (Just [])
    go (Command cmd _vars : cmds) = do
      (model, scope, counter) <- get
      if boolean (precondition model cmd) && getUsedVars cmd `S.isSubsetOf` scope
      then do
        let (resp, counter') = runGenSym (mock model cmd) counter
            vars             = getUsedVars resp
        put ( transition model cmd resp
            , vars `S.union` scope
            , counter')
        mih <- go cmds
        case mih of
          Nothing -> return Nothing
          Just ih -> return (Just (Command cmd vars : ih))
      else
        return Nothing

runCommands :: (Rank2.Traversable cmd, Rank2.Foldable resp)
            => (MonadCatch m, MonadIO m)
            => AdvancedStateMachine model submodel cmd m resp
            -> Commands cmd
            -> PropertyM m (History cmd resp, model Concrete, Reason)
runCommands sm@StateMachine { initModel } = run . go
  where
    go cmds = do
      hchan <- newTChanIO
      (reason, (_, _, _, model)) <- runStateT
        (executeCommands sm hchan (Pid 0) True cmds)
        (emptyEnvironment, initModel, newCounter, initModel)
      hist <- getChanContents hchan
      return (History hist, model, reason)

getChanContents :: MonadIO m => TChan a -> m [a]
getChanContents chan = reverse <$> atomically (go' [])
  where
    go' acc = do
      mx <- tryReadTChan chan
      case mx of
        Just x  -> go' (x : acc)
        Nothing -> return acc

executeCommands :: (Rank2.Traversable cmd, Rank2.Foldable resp)
                => (MonadCatch m, MonadIO m)
                => AdvancedStateMachine model submodel cmd m resp
                -> TChan (Pid, HistoryEvent cmd resp)
                -> Pid
                -> Bool -- ^ Check invariant and post-condition?
                -> Commands cmd
                -> StateT (Environment, model Symbolic, Counter, model Concrete) m Reason
executeCommands StateMachine {..} hchan pid check =
  go . unCommands
  where
    go []                         = return Ok
    go (Command scmd vars : cmds) = do
      (env, smodel, counter, cmodel) <- get
      case (check, logic (precondition smodel scmd)) of
        (True, VFalse ce) -> return (PreconditionFailed (show ce))
        _                 -> do
          let ccmd = fromRight (error "executeCommands: impossible") (reify env scmd)
          atomically (writeTChan hchan (pid, Invocation ccmd vars))
          !ecresp <- lift (fmap Right (semantics ccmd))
                       `catch` (\(err :: IOException) ->
                                   return (Left (displayException err)))
                       `catch` (\(err :: ErrorCall) ->
                                   return (Left (displayException err)))
          case ecresp of
            Left err    -> do
              atomically (writeTChan hchan (pid, Exception err))
              return ExceptionThrown
            Right cresp -> do
              atomically (writeTChan hchan (pid, Response cresp))
              let (sresp, counter') = runGenSym (mock smodel scmd) counter
              case (check, logic (postcondition cmodel ccmd cresp)) of
                (True, VFalse ce) -> return (PostconditionFailed (show ce))
                _                 -> case (check, logic (fromMaybe (const Top) invariant cmodel)) of
                                       (True, VFalse ce') -> return (InvariantBroken (show ce'))
                                       _                  -> do
                                         put ( insertConcretes (S.toList vars) (getUsedConcrete cresp) env
                                             , transition smodel scmd sresp
                                             , counter'
                                             , transition cmodel ccmd cresp
                                             )
                                         go cmds

getUsedConcrete :: Rank2.Foldable f => f Concrete -> [Dynamic]
getUsedConcrete = Rank2.foldMap (\(Concrete x) -> [toDyn x])

modelDiff :: ToExpr (model r) => model r -> Maybe (model r) -> Doc
modelDiff model = ansiWlBgEditExprCompact . flip ediff model . fromMaybe model

prettyPrintHistory :: forall model state cmd m resp. ToExpr (model Concrete)
                   => (Show (cmd Concrete), Show (resp Concrete))
                   => AdvancedStateMachine model state cmd m resp
                   -> History cmd resp
                   -> IO ()
prettyPrintHistory StateMachine { initModel, transition }
  = PP.putDoc
  . go initModel Nothing
  . makeOperations
  . unHistory
  where
    go :: model Concrete -> Maybe (model Concrete) -> [Operation cmd resp] -> Doc
    go current previous []                             =
      PP.line <> modelDiff current previous <> PP.line <> PP.line
    go current previous [Crash cmd err pid] =
      mconcat
        [ PP.line
        , modelDiff current previous
        , PP.line, PP.line
        , PP.string "   == "
        , PP.string (show cmd)
        , PP.string " ==> "
        , PP.string err
        , PP.string " [ "
        , PP.int (unPid pid)
        , PP.string " ]"
        , PP.line
        ]
    go current previous (Operation cmd resp pid : ops) =
      mconcat
        [ PP.line
        , modelDiff current previous
        , PP.line, PP.line
        , PP.string "   == "
        , PP.string (show cmd)
        , PP.string " ==> "
        , PP.string (show resp)
        , PP.string " [ "
        , PP.int (unPid pid)
        , PP.string " ]"
        , PP.line
        , go (transition current cmd resp) (Just current) ops
        ]
    go _ _ _ = error "prettyPrintHistory: impossible."

prettyCommands :: (MonadIO m, ToExpr (model Concrete))
               => (Show (cmd Concrete), Show (resp Concrete))
               => AdvancedStateMachine model state cmd m resp
               -> History cmd resp
               -> Property
               -> PropertyM m ()
prettyCommands sm hist prop = prettyPrintHistory sm hist `whenFailM` prop

------------------------------------------------------------------------


-- | Print distribution of commands and fail if some commands have not
--   been executed.
checkCommandNames :: forall cmd. (Generic1 cmd, GConName1 (Rep1 cmd))
                  => Commands cmd -> Property -> Property
checkCommandNames cmds
  = collect names
  . oldCover (length names == numOfConstructors) 1 "coverage"
  where
    names             = commandNames cmds
    numOfConstructors = length (gconNames1 (Proxy :: Proxy (Rep1 cmd Symbolic)))

commandNames :: forall cmd. (Generic1 cmd, GConName1 (Rep1 cmd))
             => Commands cmd -> [(String, Int)]
commandNames = M.toList . foldl go M.empty . unCommands
  where
    go :: Map String Int -> Command cmd -> Map String Int
    go ih cmd = M.insertWith (+) (gconName cmd) 1 ih

commandNamesInOrder :: forall cmd. (Generic1 cmd, GConName1 (Rep1 cmd))
                    => Commands cmd -> [String]
commandNamesInOrder = reverse . foldl go [] . unCommands
  where
    go :: [String] -> Command cmd -> [String]
    go ih cmd = gconName cmd : ih

------------------------------------------------------------------------

tabulateState :: (Generic1 cmd, GConName1 (Rep1 cmd))
              => (MonadIO m, Show state)
              => AdvancedStateMachine model state cmd m resp
              -> History cmd resp
              -> PropertyM m ()
tabulateState StateMachine {..} hist = case distribution of
  Nothing              -> error "tabulateState: A Markov chain must be specified."
  Just (markov, start) -> do
    let stateTransitions = go markov start initModel [] (makeOperations (unHistory hist))
    mapM_ (monitor . uncurry tabulate) (groupByState stateTransitions)
  where
    go _markov _state _model acc []         = reverse acc
    go markov  state  model  acc (op : ops) =
      let
        cmd     = operationCommand op
        conName = gconName1 (from1 cmd)
        state'  = fromMaybe (error ("gatherTransition: " ++ conName ++
                                    " not found in Markov chain."))
                            (lookupMarkov markov state conName)
      in
        case op of
          Operation _cmd resp _pid
            | boolean (postcondition model cmd resp) ->
                go markov state' (transition model cmd resp)
                   ((state, conName, Right state') : acc) ops
            | otherwise -> reverse ((state, conName, Left state') : acc)
          Crash _cmd _err _pid -> reverse ((state, conName, Left state') : acc)

    groupByState
      = map (\xs -> case xs of
                []         -> error "groupByState: impossible."
                (s, _) : _ -> (s, map snd xs))
      . groupBy (\x y -> fst x == fst y)
      . sortBy (\x y -> fst x `compare` fst y)
      . map (\(state, _conName, state') -> (show state, show state'))
