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
  )
  where

import           Control.Exception
                   (ErrorCall, IOException, displayException)
import           Control.Monad
                   (unless)
import           Control.Monad.Catch
                   (MonadCatch, catch)
import           Control.Monad.State.Strict
                   (MonadIO, State, StateT, evalState, evalStateT, get,
                   lift, put, runStateT)
import           Data.Dynamic
                   (Dynamic, toDyn)
import           Data.Either
                   (fromRight)
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
import qualified Data.Vector                       as V
import           GHC.Generics
                   (Generic1, Rep1)
import           Prelude
import           Test.QuickCheck
                   (Gen, Property, Testable, choose, collect, cover,
                   shrinkList, sized)
import           Test.QuickCheck.Monadic
                   (PropertyM, run)
import           Text.PrettyPrint.ANSI.Leijen
                   (Doc)
import qualified Text.PrettyPrint.ANSI.Leijen      as PP
import           Text.Show.Pretty
                   (ppShow)
import           UnliftIO
                   (MonadIO, TChan, newTChanIO, tryReadTChan, writeTChan,
                   atomically)

import           Test.StateMachine.ConstructorName
import           Test.StateMachine.Logic
import           Test.StateMachine.Markov
import           Test.StateMachine.Types
import qualified Test.StateMachine.Types.Rank2     as Rank2
import           Test.StateMachine.Utils

------------------------------------------------------------------------

forAllCommands :: Testable prop
               => (Show (cmd Symbolic), Show (model Symbolic))
               => (Show submodel, Eq submodel)
               => (Rank2.Foldable cmd, Rank2.Foldable resp)
               => AdvancedStateMachine model submodel cmd m resp
               -> Maybe Int -- ^ Minimum number of commands.
               -> (Commands cmd -> prop)     -- ^ Predicate.
               -> Property
forAllCommands sm mnum =
  forAllShrinkShow (generateCommands sm mnum) (shrinkCommands sm) ppShow

generateCommands :: (Rank2.Foldable resp, Show (model Symbolic))
                 => (Show submodel, Eq submodel)
                 => Show (cmd Symbolic)
                 => AdvancedStateMachine model submodel cmd m resp
                 -> Maybe Int -- ^ Minimum number of commands.
                 -> Gen (Commands cmd)
generateCommands sm@StateMachine { initModel } mnum =
  evalStateT (generateCommandsState sm newCounter mnum) initModel

generateCommandsState :: forall model submodel cmd m resp. Rank2.Foldable resp
                      => (Show submodel, Eq submodel)
                      => (Show (model Symbolic), Show (cmd Symbolic))
                      => AdvancedStateMachine model submodel cmd m resp
                      -> Counter
                      -> Maybe Int -- ^ Minimum number of commands.
                      -> StateT (model Symbolic) Gen (Commands cmd)
generateCommandsState StateMachine { precondition, generator, transition, distribution, mock } counter0 mnum
  = case distribution of
      Nothing     -> sizeBased
      Just markov -> chainBased markov
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

    chainBased :: Markov (model Symbolic) submodel (cmd Symbolic)
               -> StateT (model Symbolic) Gen (Commands cmd)
    chainBased markov@(Markov classify _) = Commands <$> go counter0 []
      where
        go :: Counter -> [Command cmd] -> StateT (model Symbolic) Gen [Command cmd]
        go counter cmds = do
          model <- get
          let gen = runMarkov markov model
          ecmd  <- lift (gen `suchThatEither` \case
                           Stop              -> True
                           Continue (cmd, _) -> boolean (precondition model cmd))
          case ecmd of
            Left ces -> error $ concat
                          [ "\n"
                          , "A deadlock occured while generating commands.\n"
                          , "No pre-condition holds in the following model:\n\n"
                          , "    " ++ ppShow model
                          , "\n\n"
                          , "    " ++ ppShow (classify model)
                          , "\n\nThe following commands have been generated so far:\n\n"
                          , "    " ++ ppShow (reverse cmds)
                          , "\n\n"
                          , "Example commands generated whose pre-condition doesn't hold:\n\n"
                          , "    " ++ ppShow ces
                          , "\n"
                          ]
            Right Stop                        -> return (reverse cmds)
            Right (Continue (cmd, submodel')) -> do
              let (resp, counter') = runGenSym (mock model cmd) counter
                  model'           = transition model cmd resp

              unless (classify model' == submodel') $
                error $ concat
                  [ "\n"
                  , "The transition function and the Markov chain do not agree on what the\n"
                  , "next model is. After the command:\n\n"
                  , "    " ++ ppShow cmd
                  , "\n\n"
                  , "transition function says the next model is:\n\n"
                  , "    " ++ ppShow (classify model')
                  , "\n\n"
                  , "while the Markov chain says it is:\n\n"
                  , "    " ++ ppShow submodel'
                  , "\n"
                  ]

              put model'
              go counter' (Command cmd (getUsedVars resp) : cmds)

getUsedVars :: Rank2.Foldable f => f Symbolic -> Set Var
getUsedVars = Rank2.foldMap (\(Symbolic v) -> S.singleton v)

-- | Shrink commands in a pre-condition and scope respecting way.
shrinkCommands :: (Rank2.Foldable cmd, Rank2.Foldable resp)
               => AdvancedStateMachine model submodel cmd m resp -> Commands cmd
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

validCommands :: forall model submodel cmd m resp. (Rank2.Foldable cmd, Rank2.Foldable resp)
              => AdvancedStateMachine model submodel cmd m resp -> Commands cmd
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
            => StateMachine model cmd m resp
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

prettyPrintHistory :: forall model submodel cmd m resp. ToExpr (model Concrete)
                   => (Show (cmd Concrete), Show (resp Concrete))
                   => AdvancedStateMachine model submodel cmd m resp
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
               => AdvancedStateMachine model submodel cmd m resp
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
