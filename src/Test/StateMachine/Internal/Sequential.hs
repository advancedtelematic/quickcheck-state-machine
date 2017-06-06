{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ExplicitNamespaces  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Internal.Sequential
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains the building blocks needed to implement the
-- 'Test.StateMachine.sequentialProperty' helper.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Internal.Sequential
  ( liftGen
  , liftGen'
  , liftShrinker
  , liftShrink
  , liftSem
  , removeCommands
  , collectStats
  , checkSequentialInvariant
  ) where

import           Control.Monad.State
                   (StateT, get, lift, mapStateT, modify, runStateT)
import           Data.Functor.Compose
                   (Compose(..), getCompose)
import           Data.Map
                   (Map)
import qualified Data.Map                                as M
import           Data.Set
                   (Set)
import qualified Data.Set                                as S
import           Data.Singletons.Decide
                   (SDecide)
import           Data.Singletons.Prelude
                   (type (@@), DemoteRep, Proxy(Proxy), Sing, SingKind,
                   fromSing)
import           Test.QuickCheck
                   (Gen, choose, classify, counterexample, label,
                   sized)
import           Test.QuickCheck.Monadic
                   (PropertyM, monitor, pre, run)
import           Test.QuickCheck.Property
                   (Property)

import           Test.StateMachine.Internal.IxMap
                   (IxMap)
import qualified Test.StateMachine.Internal.IxMap        as IxM
import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Internal.Types.IntRef
                   (showRef)
import           Test.StateMachine.Internal.Utils
import           Test.StateMachine.Types

------------------------------------------------------------------------

-- | Lift a generator of untyped commands with reference placeholders
--   into a generator of lists of untyped internal commands.
liftGen
  :: forall ix cmd
  .  Ord       ix
  => SingKind  ix
  => DemoteRep ix ~ ix
  => IxTraversable cmd
  => HasResponse cmd
  => Gen (Untyped cmd (RefPlaceholder ix))  -- ^ Generator to be lifted.
  -> Pid                                    -- ^ Process id.
  -> Map ix Int                             -- ^ Keeps track of how many
                                            --   refereces of sort 'ix' are in
                                            --   scope.
  -> Gen ([IntRefed cmd], Map ix Int)
liftGen gen pid
  = fmap (\((rs, _), ns) -> (rs, ns))
  . liftGen' (lift gen) () pid

-- | Same as the above, but for stateful generators.
liftGen'
  :: forall ix cmd genState
  .  Ord       ix
  => SingKind  ix
  => DemoteRep ix ~ ix
  => IxTraversable cmd
  => HasResponse cmd
  => StateT genState Gen (Untyped cmd (RefPlaceholder ix)) -- ^ Stateful
                                                           -- generator to be
                                                           -- lifted.

  -> genState                                              -- ^ Initial
                                                           -- generator state.
  -> Pid
  -> Map ix Int
  -> Gen (([IntRefed cmd], genState), Map ix Int)
liftGen' gen gs pid ns = sized $ \sz -> runStateT (runStateT (go sz) gs) ns
  where

  go :: Int -> StateT genState (StateT (Map ix Int) Gen) [IntRefed cmd]
  go 0  = return []
  go sz = do

    scopes <- lift get

    Untyped cmd <- genFromMaybe $ do
      Untyped cmd <- mapStateT lift gen
      cmd' <- lift $ lift $ getCompose $ ifor
        (Proxy :: Proxy ConstIntRef) cmd (translate scopes)
      return $ Untyped <$> cmd'

    ixref <- case response cmd of
      SResponse    -> return ()
      SReference i -> do
        lift $ modify (M.insertWith (\_ old -> old + 1) (fromSing i) 0)
        m <- lift get
        return $ IntRef (Ref (m M.! fromSing i)) pid

    (IntRefed cmd ixref :) <$> go (sz - 1)

  translate
    :: forall (i :: ix)
    .  Map ix Int
    -> Sing i
    -> RefPlaceholder ix @@ i
    -> Compose Gen Maybe IntRef
  translate scopes i _ = Compose $ case M.lookup (fromSing i) scopes of
    Nothing -> return Nothing
    Just u  -> do
      v <- choose (0, max 0 (u - 1))
      return . Just $ IntRef (Ref v) pid

------------------------------------------------------------------------

-- | A shrinker of typed commands can be lifted to a shrinker of untyped
--   commands.
liftShrinker :: (forall resp. Shrinker (cmd ConstIntRef resp)) -> Shrinker (IntRefed cmd)
liftShrinker shrinker (IntRefed cmd miref) =
  [ IntRefed cmd' miref
  | cmd' <- shrinker cmd
  ]

-- | Lift a shrinker of internal commands into a shrinker of lists of
--   untyped internal commands.
liftShrink
  :: IxFoldable  cmd
  => HasResponse cmd
  => (forall resp. Shrinker (cmd ConstIntRef resp)) -- ^ Shrinker to be lifted.
  -> Shrinker [IntRefed cmd]
liftShrink shrinker = go
  where
  go []       = []
  go (c : cs) =
    [ [] ] ++
    [ removeCommands c cs ] ++
    [ c' : cs' | (c', cs') <- shrinkPair (liftShrinker shrinker) go (c, cs) ]

-- | Remove commands that uses a reference.
removeCommands
  :: forall cmd
  .  IxFoldable cmd
  => HasResponse cmd
  => IntRefed cmd    -- ^ If this command returns a reference, then
  -> [IntRefed cmd]  -- ^ remove all commands that use that reference in
                     --   this list. If a command we remove uses another
                     --   reference, then we proceed recursively.
  -> [IntRefed cmd]
removeCommands (IntRefed cmd0 miref0) cmds0 =
  case response cmd0 of
    SResponse    -> cmds0
    SReference _ -> go cmds0 (S.singleton miref0)
  where
  go :: [IntRefed cmd] -> Set IntRef -> [IntRefed cmd]
  go []                                 _       = []
  go (cmd@(IntRefed cmd' miref) : cmds) removed =
    case response cmd' of
      SReference _ | cmd' `uses` removed ->       go cmds (S.insert miref removed)
                   | otherwise           -> cmd : go cmds removed
      SResponse    | cmd' `uses` removed ->       go cmds removed
                   | otherwise           -> cmd : go cmds removed

uses :: IxFoldable cmd => cmd ConstIntRef resp -> Set IntRef -> Bool
uses cmd xs = iany (\_ iref -> iref `S.member` xs) cmd

------------------------------------------------------------------------

-- | Lift semantics of typed commands with external references, into
--   semantics for typed commands with internal references.
liftSem
  :: forall ix cmd refs resp m
  .  SDecide ix
  => Monad m
  => IxFunctor cmd
  => HasResponse cmd
  => (cmd refs resp -> m (Response_ refs resp)) -- ^ Semantics to be lifted.
  -> cmd ConstIntRef resp
  -> MayResponse_ ConstIntRef resp
  -> StateT (IxMap ix IntRef refs) m (Response_ ConstIntRef resp)
liftSem sem cmd iref = do

  env <- get
  let cmd' = ifmap @_ @_ @_ @_ @refs (\s i -> env IxM.! (s, i)) cmd

  case response cmd' of
    SResponse    -> lift $ sem cmd'
    SReference i -> do
      ref <- lift $ sem cmd'
      modify $ IxM.insert i iref ref
      return iref

------------------------------------------------------------------------

-- | Collects length statistics about the input list.
collectStats :: [a] -> Property -> Property
collectStats cmds
  = classify (len == 0)              "0     commands"
  . classify (len >= 1  && len < 15) "1-15  commands"
  . classify (len >= 15 && len < 30) "15-30 commands"
  . classify (len >= 30)             "30+   commands"
  where
  len = length cmds

------------------------------------------------------------------------

-- | Check that the pre- and post-conditions hold in a sequential way.
checkSequentialInvariant
  :: ShowCmd cmd
  => Monad m
  => SDecide   ix
  => IxFunctor cmd
  => Show (model ConstIntRef)
  => HasResponse cmd
  => StateMachineModel model cmd
  -> model ConstIntRef
  -> (forall resp. model ConstIntRef -> MayResponse_ ConstIntRef resp -> cmd refs resp ->
        m (Response_ refs resp))
  -> [IntRefed cmd]                 -- ^ List of commands to check.
  -> PropertyM (StateT (IxMap ix IntRef refs) m) ()
checkSequentialInvariant _ _ _ []                              = return ()
checkSequentialInvariant
  smm@StateMachineModel {..} m sem (IntRefed cmd miref : cmds) = do
    let s = takeWhile (/= ' ') $ showCmd $ ifmap (const showRef) cmd
    monitor $ label s
    pre $ precondition m cmd
    resp <- run $ liftSem (sem m miref) cmd miref
    let m' = transition m cmd resp
    liftProperty $
      counterexample ("\nThe post-condition for `" ++ s ++ "' failed!\n\n" ++ show m') $
        postcondition m cmd resp
    checkSequentialInvariant smm m' sem cmds
