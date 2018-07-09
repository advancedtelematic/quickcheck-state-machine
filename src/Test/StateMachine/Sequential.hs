{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

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
  ( forAllShrinkCommands
  , generateCommands
  , generateCommandsState
  , getUsedVars
  , shrinkCommands
  , liftShrinkCommand
  , validCommands
  -- , modelCheck
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

import           Control.Concurrent.STM
                   (atomically)
import           Control.Concurrent.STM.TChan
                   (TChan, newTChanIO, tryReadTChan, writeTChan)
import           Control.Monad.State
                   (MonadIO, State, StateT, evalState, evalStateT, get,
                   lift, put, runStateT)
import           Control.Monad.Trans.Control
                   (MonadBaseControl, liftBaseWith)
import           Data.Dynamic
                   (Dynamic, toDyn)
import           Data.Either
                   (fromRight)
import           Data.Map
                   (Map)
import qualified Data.Map                      as M
import           Data.Maybe
                   (fromMaybe)
import           Data.Monoid
                   ((<>))
import           Data.Set
                   (Set)
import qualified Data.Set                      as S
import           Data.TreeDiff
                   (ToExpr, ansiWlBgEditExpr, ediff, prettyExpr,
                   toExpr)
import           Debug.Trace
                   (trace, traceShow)
import           GHC.Generics
                   ((:*:)((:*:)), (:+:)(L1, R1), C, Constructor, D,
                   Generic1, K1, M1, Rec1, Rep1, S, U1, conName, from1,
                   unM1, unRec1)
import           Test.QuickCheck
                   (Gen, Property, Testable, choose, collect, cover,
                   frequency, shrinkList, sized, suchThat)
import           Test.QuickCheck.Monadic
                   (PropertyM, run)
import           Text.PrettyPrint.ANSI.Leijen
                   (Doc)
import qualified Text.PrettyPrint.ANSI.Leijen  as PP
import           Text.Show.Pretty
                   (ppShow)

import           Test.StateMachine.Types
import qualified Test.StateMachine.Types.Rank2 as Rank2
import           Test.StateMachine.Utils

------------------------------------------------------------------------

forAllShrinkCommands :: Testable prop
                     => (Show (cmd Symbolic), ToExpr (model Symbolic))
                     => (Rank2.Foldable cmd, Rank2.Foldable resp)
                     => StateMachine model cmd m resp
                     -> Maybe Int -- ^ Minimum number of commands.
                     -> (Commands cmd -> prop)     -- ^ Predicate.
                     -> Property
forAllShrinkCommands sm mnum =
  forAllShrinkShow (generateCommands sm mnum) (shrinkCommands sm) ppShow

generateCommands :: (Show (cmd Symbolic), ToExpr (model Symbolic))
                 => Rank2.Foldable resp
                 => StateMachine model cmd m resp
                 -> Maybe Int -- ^ Minimum number of commands.
                 -> Gen (Commands cmd)
generateCommands sm@StateMachine { initModel } mnum =
  evalStateT (generateCommandsState sm newCounter mnum) initModel

generateCommandsState :: forall model cmd m resp. Rank2.Foldable resp
                      => (Show (cmd Symbolic), ToExpr (model Symbolic))
                      => StateMachine model cmd m resp
                      -> Counter
                      -> Maybe Int -- ^ Minimum number of commands.
                      -> StateT (model Symbolic) Gen (Commands cmd)
generateCommandsState StateMachine { generator, weight, precondition,
                                     transition, mock } counter0 mnum = do
  size0 <- lift (sized (\k -> choose (fromMaybe 0 mnum, k)))
  Commands <$> go size0 counter0
  where
    go :: Int -> Counter -> StateT (model Symbolic) Gen [Command cmd]
    go 0    _       = return []
    go size counter = do
      model <- get
      cmd   <- lift (generatorFrequency model `suchThat` precondition model)
      let (resp, counter') = runGenSym (mock model cmd) counter
      put (transition model cmd resp)
      cmds  <- go (size - 1) counter'
      return (Command cmd (getUsedVars resp) : cmds)

    generatorFrequency :: model Symbolic -> Gen (cmd Symbolic)
    generatorFrequency model = frequency =<< sequence (map g (generator model))
      where
        g :: Gen (cmd Symbolic) -> Gen (Int, Gen (cmd Symbolic))
        g gen = do
          cmd <- gen
          return (fromMaybe (\_ _ -> 1) weight model cmd, return cmd)

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
      if precondition model cmd && getUsedVars cmd `S.isSubsetOf` scope
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

{-
modelCheck :: forall model cmd resp m. Monad m => StateMachine model cmd m resp
           -> Commands cmd
           -> PropertyM m Reason -- XXX: (History cmd, model Symbolic, Reason)
modelCheck StateMachine { initModel, transition, precondition, postcondition, mock }
  = run . return . go initModel newCounter . unCommands
  where
    go :: model Symbolic -> Counter -> [Command cmd] -> Reason
    go _ _       []                         = Ok
    go m counter (Command cmd _vars : cmds)
      | not (precondition m cmd) = PreconditionFailed
      | otherwise                =
          let (resp, counter') = runGenSym (mock m cmd) counter in
          if postcondition m cmd resp
          then go (transition m cmd resp) counter' cmds
          else PostconditionFailed
-}

runCommands :: (Rank2.Traversable cmd, Rank2.Foldable resp)
            => MonadBaseControl IO m
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
                => MonadBaseControl IO m
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
      cresp <- lift (semantics ccmd)
      liftBaseWith (const (atomically (writeTChan hchan (pid, Response cresp))))
      if check && not (postcondition model ccmd cresp)
      then
        return PostconditionFailed
      else if check && not (fromMaybe (const True) invariant model)
           then return InvariantBroken
           else do
             put ( insertConcretes (S.toList vars) (getUsedConcrete cresp) env
                 , transition model ccmd cresp
                 )
             go cmds
        where
          getUsedConcrete :: Rank2.Foldable f => f Concrete -> [Dynamic]
          getUsedConcrete = Rank2.foldMap (\(Concrete x) -> [toDyn x])

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
    modelDiff :: model Concrete -> Maybe (model Concrete) -> Doc
    modelDiff model = ansiWlBgEditExpr . flip ediff model . fromMaybe model

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
checkCommandNames :: (Generic1 cmd, GConName (Rep1 cmd))
                  => Commands cmd -> Property -> Property
checkCommandNames cmds
  = collect names
  . cover (length names == numOfConstructors) 1 "coverage"
  where
    names = commandNames cmds
    numOfConstructors = 3 -- XXX

commandNames :: forall cmd. (Generic1 cmd, GConName (Rep1 cmd))
             => Commands cmd -> [(String, Int)]
commandNames = M.toList . foldl go M.empty . unCommands
  where
    go :: Map String Int -> Command cmd -> Map String Int
    go ih (Command cmd _) = M.insertWith (+) (gconName (from1 cmd)) 1 ih

class GConName f where
  gconName   :: f a -> String
  -- gconNumber :: f a -> Int

instance GConName U1 where
  gconName _ = ""

instance GConName (K1 i c) where
  gconName _ = ""

instance Constructor c => GConName (M1 C c f) where
  gconName = conName

instance GConName f => GConName (M1 D d f) where
  gconName = gconName . unM1

instance GConName f => GConName (M1 S d f) where
  gconName = gconName . unM1


instance (GConName f, GConName g) => GConName (f :+: g) where
  gconName (L1 x) = gconName x
  gconName (R1 y) = gconName y

instance (GConName f, GConName g) => GConName (f :*: g) where
  gconName (x :*: y) = gconName x ++ gconName y

instance GConName f => GConName (Rec1 f) where
  gconName = gconName . unRec1

commandNamesInOrder :: forall cmd. (Generic1 cmd, GConName (Rep1 cmd))
                    => Commands cmd -> [String]
commandNamesInOrder = reverse . foldl go [] . unCommands
  where
    go :: [String] -> Command cmd -> [String]
    go ih (Command cmd _) = gconName (from1 cmd) : ih

------------------------------------------------------------------------

instance GConName (Reference a) where
  gconName _ = ""