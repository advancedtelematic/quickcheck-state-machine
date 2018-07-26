{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Sequential
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
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
  , debugGenerateCommands
  , debugGenerateCommandsState
  , measureFrequency
  , calculateFrequency
  , getUsedVars
  , shrinkCommands
  , liftShrinkCommand
  , validCommands
  , filterMaybe
  , modelCheck
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

import           Control.Concurrent.STM
                   (atomically)
import           Control.Concurrent.STM.TChan
                   (TChan, newTChanIO, tryReadTChan, writeTChan)
import           Control.Exception
                   (ErrorCall, IOException, displayException)
import           Control.Monad.Catch
                   (MonadCatch, catch)
import           Control.Monad.State
                   (MonadIO, State, StateT, evalState, evalStateT, get,
                   lift, liftIO, put, runStateT)
import           Control.Monad.Trans.Control
                   (MonadBaseControl, liftBaseWith)
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
import           Data.Set
                   (Set)
import qualified Data.Set                          as S
import           Data.TreeDiff
                   (ToExpr, ansiWlBgEditExpr, ediff)
import qualified Data.Vector                       as V
import           GHC.Generics
                   (Generic1, Rep1, from1)
import           Test.QuickCheck
                   (Gen, Property, Testable, choose, collect, cover,
                   frequency, generate, oneof, resize, shrinkList,
                   sized, suchThat)
import           Test.QuickCheck.Monadic
                   (PropertyM, run)
import           Text.PrettyPrint.ANSI.Leijen
                   (Doc)
import qualified Text.PrettyPrint.ANSI.Leijen      as PP
import           Text.Show.Pretty
                   (ppShow)

import           Test.StateMachine.ConstructorName
import           Test.StateMachine.Logic
import           Test.StateMachine.Types
import qualified Test.StateMachine.Types.Rank2     as Rank2
import           Test.StateMachine.Utils

------------------------------------------------------------------------

forAllCommands :: Testable prop
               => Show (cmd Symbolic)
               => (Generic1 cmd, GConName (Rep1 cmd))
               => (Rank2.Foldable cmd, Rank2.Foldable resp)
               => StateMachine model cmd m resp
               -> Maybe Int -- ^ Minimum number of commands.
               -> (Commands cmd -> prop)     -- ^ Predicate.
               -> Property
forAllCommands sm mnum =
  forAllShrinkShow (generateCommands sm mnum) (shrinkCommands sm) ppShow

generateCommands :: Rank2.Foldable resp
                 => (Generic1 cmd, GConName (Rep1 cmd))
                 => StateMachine model cmd m resp
                 -> Maybe Int -- ^ Minimum number of commands.
                 -> Gen (Commands cmd)
generateCommands sm@StateMachine { initModel } mnum =
  evalStateT (generateCommandsState sm newCounter mnum) (initModel, Nothing)

generateCommandsState :: forall model cmd m resp
                       . Rank2.Foldable resp
                      => (Generic1 cmd, GConName (Rep1 cmd))
                      => StateMachine model cmd m resp
                      -> Counter
                      -> Maybe Int -- ^ Minimum number of commands.
                      -> StateT (model Symbolic, Maybe (cmd Symbolic)) Gen (Commands cmd)
generateCommandsState StateMachine { precondition, generator, transition
                                   , mock, transMat } counter0 mnum = do
  size0 <- lift (sized (\k -> choose (fromMaybe 0 mnum, k)))
  Commands <$> go size0 counter0
  where
    go :: Int -> Counter -> StateT (model Symbolic, Maybe (cmd Symbolic)) Gen [Command cmd]
    go 0    _       = return []
    go size counter = do
      (model, mfrom) <- get
      let genCmd  = oneof (generator model)
          idx     = case mfrom of
                      Nothing   -> 1
                      Just from -> let from' = from1 from
                                   in  fromMaybe (error $ "no command: " <> gconName from') $
                                         succ . succ <$> elemIndex (gconName from') (gconNames from')
          row     = V.toList $ getRow idx transMat
          weights = zip row (gconNames (undefined :: Rep1 cmd Symbolic))
      to <- lift $ commandFrequency genCmd weights
                     `suchThat` (boolean . precondition model) -- XXX suchThat
      let (resp, counter') = runGenSym (mock model to) counter
      put (transition model to resp, Just to)
      cmds  <- go (size - 1) counter'
      return (Command to (getUsedVars resp) : cmds)

commandFrequency :: (Generic1 cmd, GConName (Rep1 cmd))
                 => Gen (cmd Symbolic) -> [(Int, String)] -> Gen (cmd Symbolic)
commandFrequency g p =
  frequency [(i, g `suchThat` ((== s) . gconName . from1)) | (i, s) <- p]

debugGenerateCommands :: (Show (cmd Symbolic), ToExpr (model Symbolic))
                      => (Generic1 cmd, GConName (Rep1 cmd))
                      => StateMachine model cmd m resp
                      -> Int -- ^ Minimum number of commands.
                      -> Int -- ^ Maximum number of commands.
                      -> IO ()
debugGenerateCommands sm@StateMachine { initModel } min0 max0 =
  evalStateT (debugGenerateCommandsState sm newCounter min0 max0) (initModel, Nothing)

debugGenerateCommandsState :: forall model cmd m resp. Show (cmd Symbolic)
                           => (Generic1 cmd, GConName (Rep1 cmd))
                           => ToExpr (model Symbolic)
                           => StateMachine model cmd m resp
                           -> Counter
                           -> Int -- ^ Minimum number of commands.
                           -> Int -- ^ Maximum number of commands.
                           -> StateT (model Symbolic, Maybe (cmd Symbolic)) IO ()
debugGenerateCommandsState StateMachine { precondition, transition, mock, transMat, generator }
                           counter0 min0 max0 = do
  size0 <- liftIO (generate (choose (min0, max0)))
  go size0 counter0 Nothing
  where
    go :: Int -> Counter -> Maybe (model Symbolic) -> StateT (model Symbolic, Maybe (cmd Symbolic)) IO ()
    go 0    _       previous = do
      (current, _) <- get
      liftIO (print (modelDiff current previous))
      liftIO (putStrLn "")
    go size counter previous = do
      (current, mfrom) <- get
      liftIO (print (modelDiff current previous))
      liftIO (putStrLn "")
      let genCmd  = oneof (generator current)
          idx     = case mfrom of
                      Nothing   -> 1
                      Just from -> fromMaybe (error $ "no command: " <> gconName (from1 from)) $
                                     succ <$> elemIndex (gconName (from1 from)) (gconNames (from1 from))
          row     = V.toList $ getRow idx transMat
          weights = zip row (gconNames (undefined :: Rep1 cmd Symbolic))
      to <- lift $ generate $ commandFrequency genCmd weights
                                `suchThat` (boolean . precondition current) -- XXX suchThat
      liftIO (putStrLn ("  == " ++ show to ++ " ==>\n"))
      let (resp, counter') = runGenSym (mock current to) counter
      put ((transition current to resp), Just to)
      go (size - 1) counter' (Just current)

measureFrequency :: (Rank2.Foldable resp, Generic1 cmd, GConName (Rep1 cmd))
                 => StateMachine model cmd m resp
                 -> Maybe Int -- ^ Minimum number of commands.
                 -> Int       -- ^ Maximum number of commands.
                 -> IO (Map (String, Maybe String) Int)
measureFrequency sm min0 size = do
  cmds <- generate (sequence [ resize n (generateCommands sm min0) | n <- [0, 2..size] ])
  return (M.unions (map calculateFrequency cmds))

calculateFrequency :: (Generic1 cmd, GConName (Rep1 cmd))
                   => Commands cmd -> Map (String, Maybe String) Int
calculateFrequency = go M.empty . unCommands
  where
    go m [] = m
    go m [Command cmd _]
      = M.insertWith (\_ old -> old + 1) (gconName (from1 cmd), Nothing) 1 m
    go m (Command cmd1 _ : Command cmd2 _ : cmds)
      = go (M.insertWith (\_ old -> old + 1) (gconName (from1 cmd1),
                                              Just (gconName (from1 cmd2))) 1 m) cmds

getUsedVars :: Rank2.Foldable f => f Symbolic -> Set Var
getUsedVars = Rank2.foldMap (\(Symbolic v) -> S.singleton v)

-- | Shrink commands in a pre-condition and scope respecting way.
shrinkCommands :: (Rank2.Foldable cmd, Rank2.Foldable resp)
               => StateMachine model cmd m resp -> Commands cmd
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

validCommands :: forall model cmd m resp. (Rank2.Foldable cmd, Rank2.Foldable resp)
              => StateMachine model cmd m resp -> Commands cmd
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

modelCheck :: forall model cmd resp m. Monad m => StateMachine model cmd m resp
           -> Commands cmd
           -> PropertyM m Reason -- XXX: (History cmd, model Symbolic, Reason)
modelCheck StateMachine { initModel, transition, precondition, spostcondition, mock }
  = run . return . go initModel newCounter . unCommands
  where
    go :: model Symbolic -> Counter -> [Command cmd] -> Reason
    go _ _       []                        = Ok
    go m counter (Command cmd _vars : cmds)
      | not (boolean (precondition m cmd)) = PreconditionFailed
      | otherwise                          =
          let (resp, counter') = runGenSym (mock m cmd) counter in
          case logic (fromMaybe err spostcondition m cmd resp) of
            VTrue     -> go (transition m cmd resp) counter' cmds
            VFalse ce -> PostconditionFailed (show ce)
            where
              err = error "modelCheck: Symbolic post-condition must be \
                          \ specificed in state machine in order to do model checking."

runCommands :: (Rank2.Traversable cmd, Rank2.Foldable resp)
            => (MonadCatch m, MonadBaseControl IO m)
            => StateMachine model cmd m resp
            -> Commands cmd
            -> PropertyM m (History cmd resp, model Concrete, Reason)
runCommands sm@StateMachine { initModel } = run . go
  where
    go cmds = do
      hchan                <- liftBaseWith (const newTChanIO)
      (reason, (_, model)) <- runStateT (executeCommands sm hchan (Pid 0) True cmds)
                                          (emptyEnvironment, initModel)
      hist                 <- liftBaseWith (const (getChanContents hchan))
      return (History hist, model, reason)

getChanContents :: TChan a -> IO [a]
getChanContents chan = reverse <$> atomically (go' [])
  where
    go' acc = do
      mx <- tryReadTChan chan
      case mx of
        Just x  -> go' (x : acc)
        Nothing -> return acc

executeCommands :: (Rank2.Traversable cmd, Rank2.Foldable resp)
                => (MonadCatch m, MonadBaseControl IO m)
                => StateMachine model cmd m resp
                -> TChan (Pid, HistoryEvent cmd resp)
                -> Pid
                -> Bool -- ^ Check invariant and post-condition?
                -> Commands cmd
                -> StateT (Environment, model Concrete) m Reason
executeCommands StateMachine { transition, postcondition, invariant, semantics } hchan pid check =
  go . unCommands
  where
    go []                         = return Ok
    go (Command scmd vars : cmds) = do
      (env, model) <- get
      let ccmd = fromRight (error "executeCommands: impossible") (reify env scmd)
      liftBaseWith (const (atomically (writeTChan hchan (pid, Invocation ccmd vars))))
      !ecresp <- lift (fmap Right (semantics ccmd))
                   `catch` (\(err :: IOException) ->
                               return (Left (ExceptionThrown (displayException err))))
                   `catch` (\(err :: ErrorCall) ->
                               return (Left (ExceptionThrown (displayException err))))
      case ecresp of
        Left err    -> return err
        Right cresp -> do
          liftBaseWith (const (atomically (writeTChan hchan (pid, Response cresp))))
          if check
          then case logic (postcondition model ccmd cresp) of
            VFalse ce -> return (PostconditionFailed (show ce))
            VTrue     -> case logic (fromMaybe (const Top) invariant model) of
                           VFalse ce' -> return (InvariantBroken (show ce'))
                           VTrue      -> do
                             put ( insertConcretes (S.toList vars) (getUsedConcrete cresp) env
                                 , transition model ccmd cresp
                                 )
                             go cmds
          else do
            put ( insertConcretes (S.toList vars) (getUsedConcrete cresp) env
                , transition model ccmd cresp
                )
            go cmds

getUsedConcrete :: Rank2.Foldable f => f Concrete -> [Dynamic]
getUsedConcrete = Rank2.foldMap (\(Concrete x) -> [toDyn x])

modelDiff :: ToExpr (model r) => model r -> Maybe (model r) -> Doc
modelDiff model = ansiWlBgEditExpr . flip ediff model . fromMaybe model

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
checkCommandNames :: forall cmd. (Generic1 cmd, GConName (Rep1 cmd))
                  => Commands cmd -> Property -> Property
checkCommandNames cmds
  = collect names
  . cover (length names == numOfConstructors) 1 "coverage"
  where
    names             = commandNames cmds
    numOfConstructors = length (gconNames (undefined :: Rep1 cmd Symbolic))

commandNames :: forall cmd. (Generic1 cmd, GConName (Rep1 cmd))
             => Commands cmd -> [(String, Int)]
commandNames = M.toList . foldl go M.empty . unCommands
  where
    go :: Map String Int -> Command cmd -> Map String Int
    go ih (Command cmd _) = M.insertWith (+) (gconName (from1 cmd)) 1 ih

commandNamesInOrder :: forall cmd. (Generic1 cmd, GConName (Rep1 cmd))
                    => Commands cmd -> [String]
commandNamesInOrder = reverse . foldl go [] . unCommands
  where
    go :: [String] -> Command cmd -> [String]
    go ih (Command cmd _) = gconName (from1 cmd) : ih


transitionMatrix :: forall cmd
                  . GConName (Rep1 cmd)
                 => Proxy (cmd Symbolic)
                 -> (String -> String -> Int) -> Matrix Int
transitionMatrix _ f =
  let cons = gconNames (undefined :: Rep1 cmd Symbolic)
      n    = length cons
      m    = succ n
  in matrix m n $ \case
                    (1, j) -> f "<START>"               (cons !! pred j)
                    (i, j) -> f (cons !! pred (pred i)) (cons !! pred j)
