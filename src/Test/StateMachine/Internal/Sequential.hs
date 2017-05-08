{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ExplicitNamespaces  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
import           Data.Kind                        (type (*))
import           Data.Map                         (Map)
import qualified Data.Map                         as M
import           Data.Set                         (Set)
import qualified Data.Set                         as S
import           Data.Singletons.Decide           (SDecide)
import           Data.Singletons.Prelude          (type (@@), ConstSym1,
                                                   DemoteRep, Proxy (Proxy),
                                                   Sing, SingKind, TyFun,
                                                   fromSing)
import           Test.QuickCheck                  (Gen, choose, frequency,
                                                   sized)

import           Test.StateMachine.Internal.IxMap (IxMap)
import qualified Test.StateMachine.Internal.IxMap as IxM
import           Test.StateMachine.Types
import           Test.StateMachine.Utils

------------------------------------------------------------------------

liftGen
  :: forall
     (ix   :: *)
     (refs :: TyFun ix * -> *)
     (cmd  :: Response ix -> (TyFun ix * -> *) -> *)
  .  Ord       ix
  => SingKind  ix
  => DemoteRep ix ~ ix
  => [(Int, Gen (Untyped cmd refs))]
  -> Pid
  -> Map ix Int
  -> (forall resp refs'. cmd resp refs' -> SResponse ix resp)
  -> (forall f p q resp. Applicative f
        => Proxy q
        -> cmd resp p
        -> (forall (x :: ix). Sing x -> p @@ x -> f (q @@ x))
        -> f (cmd resp q))
  -> Gen ([Untyped' cmd ConstIntRef], Map ix Int)
liftGen gens pid ns returns ixfor = sized $ \sz -> runStateT (go sz) ns
  where

  translate
    :: Map ix Int
    -> forall (x :: ix). Sing x
    -> refs @@ x
    -> Compose Gen Maybe (ConstIntRef @@ x)
  translate scopes i _ = Compose $ case M.lookup (fromSing i) scopes of
    Nothing -> return Nothing
    Just u  -> do
      v <- choose (0, max 0 (u - 1))
      return . Just $ IntRef (Ref v) pid

  go :: Int -> StateT (Map ix Int) Gen [Untyped' cmd ConstIntRef]
  go 0  = return []
  go sz = do

    scopes       <- get

    Untyped cmd <- lift . genFromMaybe $ do
      Untyped cmd <- frequency gens
      cmd' <- getCompose $ ixfor (Proxy :: Proxy ConstIntRef) cmd (translate scopes)
      return $ Untyped <$> cmd'

    ixref <- case returns cmd of
      SResponse    -> return ()
      SReference i -> do
        modify (M.insertWith (\_ old -> old + 1) (fromSing i) 0)
        m <- get
        return $ IntRef (Ref (m M.! fromSing i)) pid

    (Untyped' cmd ixref :) <$> go (pred sz)

------------------------------------------------------------------------

liftShrink
  :: forall
     (ix   :: *)
     (cmd  :: Response ix -> (TyFun ix * -> *) -> *)
  .  IxFoldable (Untyped' cmd)
  => (forall resp refs. cmd resp refs -> SResponse ix resp)
  -> Shrinker (Untyped' cmd ConstIntRef)
  -> Shrinker [Untyped' cmd ConstIntRef]
liftShrink returns shrinker = go
  where
  go []       = []
  go (c : cs) =
    [ [] ] ++
    [ removeCommands c cs returns ] ++
    [ c' : cs' | (c', cs') <- shrinkPair' shrinker go (c, cs) ]

removeCommands
  :: forall
     (ix :: *)
     (cmd  :: Response ix -> (TyFun ix * -> *) -> *)
  .  IxFoldable (Untyped' cmd)
  => Untyped' cmd ConstIntRef
  -> [Untyped' cmd ConstIntRef]
  -> (forall resp refs. cmd resp refs -> SResponse ix resp)
  -> [Untyped' cmd ConstIntRef]
removeCommands (Untyped' cmd0 miref0) cmds0 returns =
  case returns cmd0 of
    SResponse    -> cmds0
    SReference _ -> go cmds0 (S.singleton miref0)
  where
  go :: [Untyped' cmd ConstIntRef] -> Set IntRef -> [Untyped' cmd ConstIntRef]
  go []                                  _       = []
  go (cmd@(Untyped' cmd' miref) : cmds) removed =
    case returns cmd' of
      SReference _ | cmd `uses` removed ->       go cmds (S.insert miref removed)
                   | otherwise          -> cmd : go cmds removed
      SResponse    | cmd `uses` removed ->       go cmds removed
                   | otherwise          -> cmd : go cmds removed

uses :: IxFoldable (cmd resp) => cmd resp ConstIntRef -> Set IntRef -> Bool
uses cmd xs = iany (\_ iref -> iref `S.member` xs) cmd

------------------------------------------------------------------------

liftSem
  :: forall
     (ix   :: *)
     (resp :: Response ix)
     (refs :: TyFun ix * -> *)
     (cmd  :: Response ix -> (TyFun ix * -> *) -> *)
     (m    :: * -> *)
  .  SDecide ix
  => Monad m
  => IxFunctor1 cmd
  => (forall resp'. cmd resp' refs -> m (Response_ refs resp'))
  -> (forall resp' refs'. cmd resp' refs' -> SResponse ix resp')
  -> cmd resp ConstIntRef
  -> MayResponse_ ConstIntRef resp
  -> StateT (IxMap ix IntRef refs) m (Response_ ConstIntRef resp)
liftSem sem returns cmd iref = do

  env <- get

  let cmd' :: cmd resp refs
      cmd' = ifmap1 (\s i -> env IxM.! (s, i)) cmd

  case returns cmd' of

    SResponse    -> lift $ sem cmd'

    SReference i -> do
      ref <- lift $ sem cmd'
      modify $ IxM.insert i iref ref
      return iref
