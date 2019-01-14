{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}

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
  , measureFrequency
  , calculateFrequency
  , getUsedVars
  , shrinkCommands
  , shrinkAndValidate
  , ValidateEnv(..)
  , ShouldShrink(..)
  , initValidateEnv
  , runCommands
  , getChanContents
  , executeCommands
  , prettyPrintHistory
  , prettyCommands
  , commandNames
  , commandNamesInOrder
  , checkCommandNames
  , transitionMatrix
  )
  where

import           Control.Exception
                   (ErrorCall, IOException, displayException)
import           Control.Monad.Catch
                   (MonadCatch, catch)
import           Control.Monad.State
                   (StateT, evalStateT, get, lift, put, runStateT)
import           Data.Bifunctor
                   (second)
import           Data.Dynamic
                   (Dynamic, toDyn)
import           Data.Either
                   (fromRight)
import           Data.List
                   (elemIndex)
import qualified Data.Map                          as M
import           Data.Map.Strict
                   (Map)
import           Data.Matrix
                   (Matrix, getRow, matrix)
import           Data.Maybe
                   (fromMaybe)
import           Data.Monoid
                   ((<>))
import           Data.Proxy
                   (Proxy(..))
import qualified Data.Set                          as S
import           Data.TreeDiff
                   (ToExpr, ansiWlBgEditExprCompact, ediff)
import qualified Data.Vector                       as V
import           Prelude
import           Test.QuickCheck
                   (Gen, Property, Testable, choose, collect, generate,
                   resize, sized, suchThat)
import           Test.QuickCheck.Monadic
                   (PropertyM, run)
import           Text.PrettyPrint.ANSI.Leijen
                   (Doc)
import qualified Text.PrettyPrint.ANSI.Leijen      as PP
import           Text.Show.Pretty
                   (ppShow)
import           UnliftIO
                   (MonadIO, TChan, atomically, newTChanIO,
                   tryReadTChan, writeTChan)

import           Test.StateMachine.ConstructorName
import           Test.StateMachine.Logic
import           Test.StateMachine.Types
import qualified Test.StateMachine.Types.Rank2     as Rank2
import           Test.StateMachine.Utils

------------------------------------------------------------------------

forAllCommands :: Testable prop
               => (Show (cmd Symbolic), Show (resp Symbolic), Show (model Symbolic))
               => CommandNames cmd
               => (Rank2.Traversable cmd, Rank2.Foldable resp)
               => StateMachine model cmd m resp
               -> Maybe Int -- ^ Minimum number of commands.
               -> (Commands cmd resp -> prop)     -- ^ Predicate.
               -> Property
forAllCommands sm mnum =
  forAllShrinkShow (generateCommands sm mnum) (shrinkCommands sm) ppShow

generateCommands :: (Rank2.Foldable resp, Show (model Symbolic))
                 => CommandNames cmd
                 => StateMachine model cmd m resp
                 -> Maybe Int -- ^ Minimum number of commands.
                 -> Gen (Commands cmd resp)
generateCommands sm@StateMachine { initModel } mnum =
  evalStateT (generateCommandsState sm newCounter mnum) (initModel, Nothing)

generateCommandsState :: forall model cmd m resp. Rank2.Foldable resp
                      => Show (model Symbolic)
                      => CommandNames cmd
                      => StateMachine model cmd m resp
                      -> Counter
                      -> Maybe Int -- ^ Minimum number of commands.
                      -> StateT (model Symbolic, Maybe (cmd Symbolic)) Gen (Commands cmd resp)
generateCommandsState StateMachine { precondition, generator, transition
                                   , mock, distribution } counter0 mnum = do
  size0 <- lift (sized (\k -> choose (fromMaybe 0 mnum, k)))
  Commands <$> go size0 counter0 []
  where
    go :: Int -> Counter -> [Command cmd resp]
       -> StateT (model Symbolic, Maybe (cmd Symbolic)) Gen [Command cmd resp]
    go 0    _       cmds = return (reverse cmds)
    go size counter cmds = do
      (model, mprevious) <- get
      case generator model of
          Nothing -> return (reverse cmds)
          Just cmd -> do
            mnext <- lift $ commandFrequency cmd distribution mprevious
                        `suchThatOneOf` (boolean . precondition model)
            case mnext of
              Nothing   -> error $ concat
                             [ "A deadlock occured while generating commands.\n"
                             , "No pre-condition holds in the following model:\n"
                             , ppShow model
                             -- XXX: show trace of commands generated so far?
                             ]
              Just next -> do
                let (resp, counter') = runGenSym (mock model next) counter
                put (transition model next resp, Just next)
                go (size - 1) counter' (Command next resp (getUsedVars resp) : cmds)

commandFrequency :: forall cmd. CommandNames cmd
                 => Gen (cmd Symbolic) -> Maybe (Matrix Int) -> Maybe (cmd Symbolic)
                 -> [(Int, Gen (cmd Symbolic))]
commandFrequency gen Nothing             _          = [ (1, gen) ]
commandFrequency gen (Just distribution) mprevious  =
  [ (freq, gen `suchThat` ((== con) . cmdName)) | (freq, con) <- weights ]
    where
      idx = case mprevious of
              Nothing       -> 1
              Just previous ->
                let
                  con = cmdName previous
                  err = "genetateCommandState: no command: " <> con
                in
                  fromMaybe (error err) ((+ 2) <$>
                    elemIndex con (cmdNames (Proxy :: Proxy (cmd Symbolic))))
      row     = V.toList (getRow idx distribution)
      weights = zip row (cmdNames (Proxy :: Proxy (cmd Symbolic)))

measureFrequency :: (Rank2.Foldable resp, Show (model Symbolic))
                 => CommandNames cmd
                 => StateMachine model cmd m resp
                 -> Maybe Int -- ^ Minimum number of commands.
                 -> Int       -- ^ Maximum number of commands.
                 -> IO (Map (String, Maybe String) Int)
measureFrequency sm min0 size = do
  cmds <- generate (sequence [ resize n (generateCommands sm min0) | n <- [0, 2..size] ])
  return (M.unions (map calculateFrequency cmds))

calculateFrequency :: CommandNames cmd
                   => Commands cmd resp -> Map (String, Maybe String) Int
calculateFrequency = go M.empty . unCommands
  where
    go m [] = m
    go m [cmd]
      = M.insertWith (\_ old -> old + 1) (commandName cmd, Nothing) 1 m
    go m (cmd1 : cmd2 : cmds)
      = go (M.insertWith (\_ old -> old + 1) (commandName cmd1,
                                              Just (commandName cmd2)) 1 m) cmds

getUsedVars :: Rank2.Foldable f => f Symbolic -> [Var]
getUsedVars = Rank2.foldMap (\(Symbolic v) -> [v])

-- | Shrink commands in a pre-condition and scope respecting way.
shrinkCommands ::  forall model cmd m resp. (Rank2.Traversable cmd, Rank2.Foldable resp)
               => StateMachine model cmd m resp -> Commands cmd resp
               -> [Commands cmd resp]
shrinkCommands sm@StateMachine { initModel } =
    concatMap go . shrinkListS' . unCommands
  where
    go :: Shrunk [Command cmd resp] -> [Commands cmd resp]
    go (Shrunk shrunk cmds) = map snd $
        shrinkAndValidate sm
                          (if shrunk then DontShrink else MustShrink)
                          (initValidateEnv initModel)
                          (Commands cmds)

-- | Environment required during 'shrinkAndValidate'
data ValidateEnv model = ValidateEnv {
      -- | The model we're starting validation from
      veModel   :: model Symbolic

      -- | Reference renumbering
      --
      -- When a command
      --
      -- > Command .. [Var i, ..]
      --
      -- is changed during validation to
      --
      -- > Command .. [Var j, ..]
      --
      -- then any subsequent uses of @Var i@ should be replaced by @Var j@. This
      -- is recorded in 'veScope'. When we /remove/ the first command
      -- altogether (during shrinking), then @Var i@ won't appear in the
      -- 'veScope' and shrank candidates that contain commands referring to @Var
      -- i@ should be considered as invalid.
    , veScope   :: Map Var Var

      -- | Counter (for generating new references)
    , veCounter :: Counter
    }

initValidateEnv :: model Symbolic -> ValidateEnv model
initValidateEnv initModel = ValidateEnv {
      veModel   = initModel
    , veScope   = M.empty
    , veCounter = newCounter
    }

data ShouldShrink = MustShrink | DontShrink

-- | Validate list of commands, optionally shrinking one of the commands
--
-- The input to this function is a list of commands ('Commands'), for example
--
-- > [A, B, C, D, E, F, G, H]
--
-- The /result/ is a /list/ of 'Commands', i.e. a list of lists. The
-- outermost list is used for all the shrinking possibilities. For example,
-- let's assume we haven't shrunk something yet, and therefore need to shrink
-- one of the commands. Let's further assume that only commands B and E can be
-- shrunk, to B1, B2 and E1, E2, E3 respectively. Then the result will look
-- something like
--
-- > [    -- outermost list recording all the shrink possibilities
-- >     [A', B1', C', D', E' , F', G', H']   -- B shrunk to B1
-- >   , [A', B1', C', D', E' , F', G', H']   -- B shrunk to B2
-- >   , [A', B' , C', D', E1', F', G', H']   -- E shrunk to E1
-- >   , [A', B' , C', D', E2', F', G', H']   -- E shrunk to E2
-- >   , [A', B' , C', D', E3', F', G', H']   -- E shrunk to E3
-- > ]
--
-- where one of the commands has been shrunk and all commands have been
-- validated and renumbered (references updated). So, in this example, the
-- result will contain at most 5 lists; it may contain fewer, since some of
-- these lists may not be valid.
--
-- If we _did_ already shrink something, then no commands will be shrunk, and
-- the resulting list will either be empty (if the list of commands was invalid)
-- or contain a /single/ element with the validated and renumbered commands.
shrinkAndValidate :: forall model cmd m resp. (Rank2.Traversable cmd, Rank2.Foldable resp)
                  => StateMachine model cmd m resp
                  -> ShouldShrink
                  -> ValidateEnv model
                  -> Commands cmd resp
                  -> [(ValidateEnv model, Commands cmd resp)]
shrinkAndValidate StateMachine { precondition, transition, mock, shrinker } =
    \env shouldShrink cmds -> map (second Commands) $ go env shouldShrink (unCommands cmds)
  where
    go :: ShouldShrink -> ValidateEnv model -> [Command cmd resp] -> [(ValidateEnv model, [Command cmd resp])]
    go MustShrink   _   [] = []          -- we failed to shrink anything
    go DontShrink   env [] = [(env, [])] -- successful termination
    go shouldShrink (ValidateEnv model scope counter) (Command cmd' _resp vars' : cmds) =
      case Rank2.traverse (remapVars scope) cmd' of
        Just remapped ->
          -- shrink at most one command
          let candidates :: [(ShouldShrink, cmd Symbolic)]
              candidates =
                case shouldShrink of
                  DontShrink -> [(DontShrink, remapped)]
                  MustShrink -> map (DontShrink,) (shrinker model remapped)
                             ++ [(MustShrink, remapped)]
          in flip concatMap candidates $ \(shouldShrink', cmd) ->
               if boolean (precondition model cmd)
                 then let (resp, counter') = runGenSym (mock model cmd) counter
                          vars = getUsedVars resp
                          env' = ValidateEnv {
                                     veModel   = transition model cmd resp
                                   , veScope   = M.fromList (zip vars' vars) `M.union` scope
                                   , veCounter = counter'
                                   }
                      in map (second (Command cmd resp vars:)) $ go shouldShrink' env' cmds
                 else []
        Nothing ->
          []

    remapVars :: Map Var Var -> Symbolic a -> Maybe (Symbolic a)
    remapVars scope (Symbolic v) = Symbolic <$> M.lookup v scope

runCommands :: (Rank2.Traversable cmd, Rank2.Foldable resp)
            => (MonadCatch m, MonadIO m)
            => StateMachine model cmd m resp
            -> Commands cmd resp
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
                => StateMachine model cmd m resp
                -> TChan (Pid, HistoryEvent cmd resp)
                -> Pid
                -> Bool -- ^ Check invariant and post-condition?
                -> Commands cmd resp
                -> StateT (Environment, model Symbolic, Counter, model Concrete) m Reason
executeCommands StateMachine {..} hchan pid check =
  go . unCommands
  where
    go []                           = return Ok
    go (Command scmd _ vars : cmds) = do
      (env, smodel, counter, cmodel) <- get
      case (check, logic (precondition smodel scmd)) of
        (True, VFalse ce) -> return (PreconditionFailed (show ce))
        _                 -> do
          let ccmd = fromRight (error "executeCommands: impossible") (reify env scmd)
          atomically (writeTChan hchan (pid, Invocation ccmd (S.fromList vars)))
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
                                         put ( insertConcretes vars (getUsedConcrete cresp) env
                                             , transition smodel scmd sresp
                                             , counter'
                                             , transition cmodel ccmd cresp
                                             )
                                         go cmds

getUsedConcrete :: Rank2.Foldable f => f Concrete -> [Dynamic]
getUsedConcrete = Rank2.foldMap (\(Concrete x) -> [toDyn x])

modelDiff :: ToExpr (model r) => model r -> Maybe (model r) -> Doc
modelDiff model = ansiWlBgEditExprCompact . flip ediff model . fromMaybe model

prettyPrintHistory :: forall model cmd m resp. ToExpr (model Concrete)
                   => (Show (cmd Concrete), Show (resp Concrete))
                   => StateMachine model cmd m resp
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
               => StateMachine model cmd m resp
               -> History cmd resp
               -> Property
               -> PropertyM m ()
prettyCommands sm hist prop = prettyPrintHistory sm hist `whenFailM` prop

------------------------------------------------------------------------


-- | Print distribution of commands and fail if some commands have not
--   been executed.
checkCommandNames :: forall cmd resp. CommandNames cmd
                  => Commands cmd resp -> Property -> Property
checkCommandNames cmds
  = collect names
  . oldCover (length names == numOfConstructors) 1 "coverage"
  where
    names             = commandNames cmds
    numOfConstructors = length (cmdNames (Proxy :: Proxy (cmd Symbolic)))

commandNames :: forall cmd resp. CommandNames cmd
             => Commands cmd resp -> [(String, Int)]
commandNames = M.toList . foldl go M.empty . unCommands
  where
    go :: Map String Int -> Command cmd resp -> Map String Int
    go ih cmd = M.insertWith (+) (commandName cmd) 1 ih

commandNamesInOrder :: forall cmd resp. CommandNames cmd
                    => Commands cmd resp -> [String]
commandNamesInOrder = reverse . foldl go [] . unCommands
  where
    go :: [String] -> Command cmd resp -> [String]
    go ih cmd = commandName cmd : ih


transitionMatrix :: forall cmd. CommandNames cmd
                 => Proxy (cmd Symbolic)
                 -> (String -> String -> Int) -> Matrix Int
transitionMatrix _ f =
  let cons = cmdNames (Proxy :: Proxy (cmd Symbolic))
      n    = length cons
      m    = succ n
  in matrix m n $ \case
                    (1, j) -> f "<START>"               (cons !! pred j)
                    (i, j) -> f (cons !! pred (pred i)) (cons !! pred j)
