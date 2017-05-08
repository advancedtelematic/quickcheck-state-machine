{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ExplicitNamespaces        #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeInType                #-}
{-# LANGUAGE TypeOperators             #-}

module Test.StateMachine.Internal.Parallel
  ( liftGenFork
  , liftShrinkFork
  , runMany
  , linearise
  , toForkOfOps
  , mkHistoryKit
  , fromRose
  , response
  , invocation
  , getProcessIdHistory
  , getHistoryChannel
  ) where

import           Control.Concurrent                    (threadDelay)
import           Control.Concurrent.STM                (atomically)
import           Control.Concurrent.STM.TChan          (TChan, newTChanIO,
                                                        writeTChan)
import           Control.Monad                         (foldM)
import           Control.Monad.State                   (StateT, lift)
import           Data.Dynamic                          (Dynamic, fromDynamic,
                                                        toDyn)
import           Data.Kind                             (type (*))
import           Data.List                             (partition)
import           Data.Map                              (Map)
import qualified Data.Map                              as M
import qualified Data.Set                              as S
import           Data.Singletons.Decide                (SDecide)
import           Data.Singletons.Prelude               (type (@@), ConstSym1,
                                                        DemoteRep, Proxy, Sing,
                                                        SingKind, TyFun,
                                                        fromSing)
import           Data.Typeable                         (Typeable)
import           System.Random                         (randomRIO)
import           Test.QuickCheck                       (Gen, Property, property,
                                                        (.&&.))
import           Text.PrettyPrint.ANSI.Leijen          (Pretty, pretty,
                                                        prettyList, text, vsep,
                                                        (<+>))

import           Test.StateMachine.Internal.IxMap      (IxMap)
import           Test.StateMachine.Internal.Sequential
import           Test.StateMachine.Types
import           Test.StateMachine.Utils

------------------------------------------------------------------------

liftGenFork
  :: forall
     (ix   :: *)
     (refs :: TyFun ix * -> *)
     (cmd  :: Response ix -> (TyFun ix * -> *) -> *)
  .  Ord       ix
  => SingKind  ix
  => DemoteRep ix ~ ix
  => IxFunctor1 cmd
  => [(Int, Gen (Untyped cmd refs))]
  -> (forall resp refs'. cmd resp refs' -> SResponse ix resp)
  -> (forall f p q resp. Applicative f
        => Proxy q
        -> cmd resp p
        -> (forall (x :: ix). Sing x -> p @@ x -> f (q @@ x))
        -> f (cmd resp q))
  -> Gen (Fork [Untyped' cmd (ConstSym1 IntRef)])
liftGenFork gens returns ixFor = do
  (prefix, ns) <- liftGen gens 0 M.empty returns ixFor
  left         <- fst <$> liftGen gens 1 ns returns ixFor
  right        <- fst <$> liftGen gens 2 ns returns ixFor
  return $ Fork
    (map (\(Untyped' cmd miref) ->
            Untyped' (ifmap1 (fixPid ns) cmd) miref) left)
    prefix
    (map (\(Untyped' cmd miref) ->
            Untyped' (ifmap1 (fixPid ns) cmd) miref) right)
  where
  fixPid :: Map ix Int -> Sing (i :: ix) -> IntRef -> IntRef
  fixPid ns i iref@(IntRef (Ref ref) _)
    | ref <= ns M.! fromSing i = IntRef (Ref ref) 0
    | otherwise                = iref

------------------------------------------------------------------------

liftShrinkFork
  :: forall
     (ix   :: *)
     (cmd  :: Response ix -> (TyFun ix * -> *) -> *)
  .  IxFoldable (Untyped' cmd)
  => Ord (Untyped' cmd (ConstSym1 IntRef))
  => (forall resp refs. cmd resp refs -> SResponse ix resp)
  -> Shrinker (Untyped' cmd (ConstSym1 IntRef))
  -> Shrinker (Fork [Untyped' cmd (ConstSym1 IntRef)])
liftShrinkFork returns shrinker f@(Fork l0 p0 r0) = S.toList $ S.fromList $

  -- Only shrink the branches:
  [ Fork l' p0 r'
  | (l', r') <- shrinkPair' (liftShrink returns shrinker)
                            (liftShrink returns shrinker)
                            (l0, r0)
  ] ++

  -- Only shrink the prefix:
  shrinkPrefix f

  where
  shrinkPrefix
    :: Fork [Untyped' cmd (ConstSym1 IntRef)] -> [Fork [Untyped' cmd (ConstSym1 IntRef)]]
  shrinkPrefix (Fork _ []       _) = []
  shrinkPrefix (Fork l (p : ps) r) =
      [ Fork l'   []                      r'   ] ++
      [ Fork l''  (removeCommands p ps returns) r''  ] ++
      [ Fork l''' (p' : ps')              r'''
      | (p', Fork l''' ps' r''') <- shrinkPair' shrinker shrinkPrefix (p, Fork l ps r)
      ]
      where
      l'  = removeManyCommands (p : ps) l
      r'  = removeManyCommands (p : ps) r

      l'' = removeCommands p l returns
      r'' = removeCommands p r returns

      removeManyCommands
        :: [Untyped' cmd (ConstSym1 IntRef)] -> [Untyped' cmd (ConstSym1 IntRef)]
        -> [Untyped' cmd (ConstSym1 IntRef)]
      removeManyCommands []       ds = ds
      removeManyCommands (c : cs) ds = removeManyCommands cs (removeCommands c ds returns)

------------------------------------------------------------------------

type History cmd refs = [HistoryEvent (Untyped' cmd refs)]

data HistoryEvent cmd
  = InvocationEvent
      { invocation        :: cmd
      , getProcessIdEvent :: Pid
      }
  | ResponseEvent
      { response          :: Dynamic
      , getProcessIdEvent :: Pid
      }

data Operation cmd refs = forall resp.
  (Show (Response_ refs resp),
   Typeable resp,
   Typeable (Response_ refs resp)) =>
  Operation (cmd resp refs) (Response_ refs resp) Pid

instance ShowCmd cmd refs => Pretty (Operation cmd refs) where
  pretty (Operation cmd resp _) =
    text (showCmd cmd) <+> text "-->" <+> text (show resp)
  prettyList                     = vsep . map pretty

takeInvocations :: History cmd refs -> [HistoryEvent (Untyped' cmd refs)]
takeInvocations = takeWhile $ \h -> case h of
  InvocationEvent _ _ -> True
  _                   -> False

findCorrespondingResp :: Pid -> History cmd refs -> [(Dynamic, History cmd refs)]
findCorrespondingResp _   [] = []
findCorrespondingResp pid (ResponseEvent resp pid' : es) | pid == pid' = [(resp, es)]
findCorrespondingResp pid (e : es) =
  [ (resp, e : es') | (resp, es') <- findCorrespondingResp pid es ]

linearTree :: History cmd refs -> [Rose (Operation cmd refs)]
linearTree [] = []
linearTree es =
  [ Rose (Operation cmd (dynResp resp) pid) (linearTree es')
  | InvocationEvent (Untyped' cmd _) pid <- takeInvocations es
  , (resp, es')  <- findCorrespondingResp pid $ filter1 (not . matchInv pid) es
  ]
  where
  dynResp resp = maybe (error "linearTree: impossible.") id $ fromDynamic resp

  filter1 :: (a -> Bool) -> [a] -> [a]
  filter1 _ []                   = []
  filter1 p (x : xs) | p x       = x : filter1 p xs
                     | otherwise = xs

  -- Hmm, is this enough?
  matchInv pid (InvocationEvent _ pid') = pid == pid'
  matchInv _   _                        = False

linearise
  :: forall cmd model
  .  StateMachineModel model cmd
  -> History cmd (ConstSym1 IntRef)
  -> Property
linearise _                        [] = property True
linearise StateMachineModel {..} xs0 = anyP (step initialModel) . linearTree $ xs0
  where
  step :: model (ConstSym1 IntRef) -> Rose (Operation cmd (ConstSym1 IntRef)) -> Property
  step m (Rose (Operation cmd resp _) roses) =
    postcondition m cmd resp .&&.
    anyP' (step (transition m cmd resp)) roses
    where
    anyP' :: (a -> Property) -> [a] -> Property
    anyP' _ [] = property True
    anyP' p xs = anyP p xs

------------------------------------------------------------------------

toForkOfOps :: forall cmd refs. History cmd refs -> Fork [Operation cmd refs]
toForkOfOps h = Fork (mkOps l) p' (mkOps r)
  where
  (p, h') = partition (\e -> getProcessIdEvent e == 0) h
  (l, r)  = partition (\e -> getProcessIdEvent e == 1) h'

  p'      = mkOps p

  mkOps :: [HistoryEvent (Untyped' cmd refs)] -> [Operation cmd refs]
  mkOps [] = []
  mkOps (InvocationEvent (Untyped' cmd _) _ : ResponseEvent resp pid : es)
    = Operation cmd (dynResp resp) pid : mkOps es
    where
    dynResp = maybe (error "toForkOfOps: impossible.") id . fromDynamic
  mkOps _  = error "mkOps: Impossible."

------------------------------------------------------------------------

data HistoryKit cmd refs = HistoryKit
  { getHistoryChannel   :: TChan (HistoryEvent (Untyped' cmd refs))
  , getProcessIdHistory :: Pid
  }

mkHistoryKit :: Pid -> IO (HistoryKit cmd refs)
mkHistoryKit pid = do
  chan <- newTChanIO
  return $ HistoryKit chan pid

runMany
  :: SDecide ix
  => IxFunctor1 cmd
  => HistoryKit cmd (ConstSym1 IntRef)
  -> (forall resp. cmd resp refs -> IO (Response_ refs resp))
  -> (forall resp refs'. cmd resp refs' -> SResponse ix resp)
  -> [Untyped' cmd (ConstSym1 IntRef)]
  -> StateT (IxMap ix IntRef refs) IO ()
runMany kit step returns = flip foldM () $ \_ cmd'@(Untyped' cmd iref) -> do
  lift $ atomically $ writeTChan (getHistoryChannel kit) $
    InvocationEvent cmd' (getProcessIdHistory kit)
  resp <- liftSem step returns cmd iref

  lift $ do
    threadDelay =<< randomRIO (0, 20)
    atomically $ writeTChan (getHistoryChannel kit) $
      ResponseEvent (toDyn resp) (getProcessIdHistory kit)
