{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ExplicitNamespaces  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module Test.StateMachine.Internal.Sequential
  ( liftGen
  , liftShrink
  , liftSem
  , removeCommands
  ) where

import           Control.Monad.State              (StateT, get, lift, modify,
                                                   runStateT)
import           Data.Functor.Compose             (Compose (..), getCompose)
import           Data.Map                         (Map)
import qualified Data.Map                         as M
import           Data.Set                         (Set)
import qualified Data.Set                         as S
import           Data.Singletons.Decide           (SDecide)
import           Data.Singletons.Prelude          (type (@@), DemoteRep,
                                                   Proxy (Proxy), Sing,
                                                   SingKind, fromSing)
import           Test.QuickCheck                  (Gen, choose, frequency,
                                                   sized)

import           Test.StateMachine.Internal.IxMap (IxMap)
import qualified Test.StateMachine.Internal.IxMap as IxM
import           Test.StateMachine.Types
import           Test.StateMachine.Utils

------------------------------------------------------------------------

liftGen
  :: forall ix cmd
  .  Ord       ix
  => SingKind  ix
  => DemoteRep ix ~ ix
  => IxTraversable cmd
  => HasResponse cmd
  => [(Int, Gen (Untyped cmd (IxRefs ix)))]
  -> Pid
  -> Map ix Int
  -> Gen ([IntRefed cmd], Map ix Int)
liftGen gens pid ns = sized $ \sz -> runStateT (go sz) ns
  where

  translate
    :: forall (i :: ix)
    .  Map ix Int
    -> Sing i
    -> IxRefs ix @@ i
    -> Compose Gen Maybe IntRef
  translate scopes i _ = Compose $ case M.lookup (fromSing i) scopes of
    Nothing -> return Nothing
    Just u  -> do
      v <- choose (0, max 0 (u - 1))
      return . Just $ IntRef (Ref v) pid

  go :: Int -> StateT (Map ix Int) Gen [IntRefed cmd]
  go 0  = return []
  go sz = do

    scopes       <- get

    Untyped cmd <- lift . genFromMaybe $ do
      Untyped cmd <- frequency gens
      cmd' <- getCompose $ ifor (Proxy :: Proxy ConstIntRef) cmd (translate scopes)
      return $ Untyped <$> cmd'

    ixref <- case response cmd of
      SResponse    -> return ()
      SReference i -> do
        modify (M.insertWith (\_ old -> old + 1) (fromSing i) 0)
        m <- get
        return $ IntRef (Ref (m M.! fromSing i)) pid

    (Untyped' cmd ixref :) <$> go (pred sz)

------------------------------------------------------------------------

liftShrink
  :: IxFoldable  cmd
  => HasResponse cmd
  => Shrinker (IntRefed cmd)
  -> Shrinker [IntRefed cmd]
liftShrink shrinker = go
  where
  go []       = []
  go (c : cs) =
    [ [] ] ++
    [ removeCommands c cs ] ++
    [ c' : cs' | (c', cs') <- shrinkPair' shrinker go (c, cs) ]

removeCommands
  :: forall cmd
  .  IxFoldable cmd
  => HasResponse cmd
  => IntRefed cmd
  -> [IntRefed cmd]
  -> [IntRefed cmd]
removeCommands (Untyped' cmd0 miref0) cmds0 =
  case response cmd0 of
    SResponse    -> cmds0
    SReference _ -> go cmds0 (S.singleton miref0)
  where
  go :: [IntRefed cmd] -> Set IntRef -> [IntRefed cmd]
  go []                                 _       = []
  go (cmd@(Untyped' cmd' miref) : cmds) removed =
    case response cmd' of
      SReference _ | cmd' `uses` removed ->       go cmds (S.insert miref removed)
                   | otherwise           -> cmd : go cmds removed
      SResponse    | cmd' `uses` removed ->       go cmds removed
                   | otherwise           -> cmd : go cmds removed

uses :: IxFoldable cmd => cmd resp ConstIntRef -> Set IntRef -> Bool
uses cmd xs = iany (\_ iref -> iref `S.member` xs) cmd

------------------------------------------------------------------------

liftSem
  :: forall ix cmd refs resp m
  .  SDecide ix
  => Monad m
  => IxFunctor cmd
  => HasResponse cmd
  => (cmd resp refs -> m (Response_ refs resp))
  -> cmd resp ConstIntRef
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
