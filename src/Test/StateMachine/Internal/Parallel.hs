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
  , liftSemFork
  , checkParallelInvariant
  ) where

import           Control.Concurrent                    (threadDelay)
import           Control.Concurrent.ParallelIO.Local   (parallel_, withPool)
import           Control.Concurrent.STM                (STM, atomically)
import           Control.Concurrent.STM.TChan          (TChan, newTChanIO,
                                                        tryReadTChan,
                                                        writeTChan)
import           Control.Monad                         (foldM)
import           Control.Monad.State                   (StateT, evalStateT,
                                                        execStateT, lift)
import           Data.Dynamic                          (Dynamic, fromDynamic,
                                                        toDyn)
import           Data.Kind                             (type (*))
import           Data.List                             (partition)
import           Data.Map                              (Map)
import qualified Data.Map                              as M
import qualified Data.Set                              as S
import           Data.Singletons.Decide                (SDecide)
import           Data.Singletons.Prelude               (DemoteRep, Sing,
                                                        SingKind, TyFun,
                                                        fromSing)
import           Data.Typeable                         (Typeable)
import           System.Random                         (randomRIO)
import           Test.QuickCheck                       (Gen, Property,
                                                        counterexample,
                                                        property, (.&&.))
import           Test.QuickCheck.Monadic               (PropertyM)
import           Text.PrettyPrint.ANSI.Leijen          (Pretty, pretty,
                                                        prettyList, text, vsep,
                                                        (<+>))

import           Test.StateMachine.Internal.IxMap      (IxMap)
import qualified Test.StateMachine.Internal.IxMap      as IxM
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
  => IxTraversable cmd
  => [(Int, Gen (Untyped cmd refs))]
  -> (forall resp refs'. cmd resp refs' -> SResponse ix resp)
  -> Gen (Fork [Untyped' cmd ConstIntRef])
liftGenFork gens returns = do
  (prefix, ns) <- liftGen gens 0 M.empty returns
  left         <- fst <$> liftGen gens 1 ns returns
  right        <- fst <$> liftGen gens 2 ns returns
  return $ Fork
    (map (\(Untyped' cmd miref) ->
            Untyped' (ifmap (fixPid ns) cmd) miref) left)
    prefix
    (map (\(Untyped' cmd miref) ->
            Untyped' (ifmap (fixPid ns) cmd) miref) right)
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
  .  IxFoldable cmd
  => Ord (Untyped' cmd ConstIntRef)
  => (forall resp refs. cmd resp refs -> SResponse ix resp)
  -> Shrinker (Untyped' cmd ConstIntRef)
  -> Shrinker (Fork [Untyped' cmd ConstIntRef])
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
    :: Fork [Untyped' cmd ConstIntRef] -> [Fork [Untyped' cmd ConstIntRef]]
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
        :: [Untyped' cmd ConstIntRef] -> [Untyped' cmd ConstIntRef]
        -> [Untyped' cmd ConstIntRef]
      removeManyCommands []       ds = ds
      removeManyCommands (c : cs) ds = removeManyCommands cs (removeCommands c ds returns)

------------------------------------------------------------------------

type History cmd = [HistoryEvent (Untyped' cmd ConstIntRef)]

data HistoryEvent cmd
  = InvocationEvent cmd     Pid
  | ResponseEvent   Dynamic Pid

getProcessIdEvent :: HistoryEvent cmd -> Pid
getProcessIdEvent (InvocationEvent _ pid) = pid
getProcessIdEvent (ResponseEvent   _ pid) = pid

data Operation cmd = forall resp.
  (Show (Response_ ConstIntRef resp),
   Typeable resp,
   Typeable (Response_ ConstIntRef resp)) =>
  Operation (cmd resp ConstIntRef) (Response_ ConstIntRef resp) Pid

instance ShowCmd cmd => Pretty (Operation cmd) where
  pretty (Operation cmd resp _) =
    text (showCmd cmd) <+> text "-->" <+> text (show resp)
  prettyList                     = vsep . map pretty

takeInvocations :: History cmd -> [HistoryEvent (Untyped' cmd ConstIntRef)]
takeInvocations = takeWhile $ \h -> case h of
  InvocationEvent _ _ -> True
  _                   -> False

findCorrespondingResp :: Pid -> History cmd -> [(Dynamic, History cmd)]
findCorrespondingResp _   [] = []
findCorrespondingResp pid (ResponseEvent resp pid' : es) | pid == pid' = [(resp, es)]
findCorrespondingResp pid (e : es) =
  [ (resp, e : es') | (resp, es') <- findCorrespondingResp pid es ]

linearTree :: History cmd -> [Rose (Operation cmd)]
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
  -> History cmd
  -> Property
linearise _                        [] = property True
linearise StateMachineModel {..} xs0 = anyP (step initialModel) . linearTree $ xs0
  where
  step :: model ConstIntRef -> Rose (Operation cmd) -> Property
  step m (Rose (Operation cmd resp _) roses) =
    postcondition m cmd resp .&&.
    anyP' (step (transition m cmd resp)) roses
    where
    anyP' :: (a -> Property) -> [a] -> Property
    anyP' _ [] = property True
    anyP' p xs = anyP p xs

------------------------------------------------------------------------

toForkOfOps :: forall cmd. History cmd -> Fork [Operation cmd]
toForkOfOps h = Fork (mkOps l) p' (mkOps r)
  where
  (p, h') = partition (\e -> getProcessIdEvent e == 0) h
  (l, r)  = partition (\e -> getProcessIdEvent e == 1) h'

  p'      = mkOps p

  mkOps :: [HistoryEvent (Untyped' cmd ConstIntRef)] -> [Operation cmd]
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
  => IxFunctor cmd
  => HistoryKit cmd ConstIntRef
  -> (forall resp. cmd resp refs -> IO (Response_ refs resp))
  -> (forall resp refs'. cmd resp refs' -> SResponse ix resp)
  -> [Untyped' cmd ConstIntRef]
  -> StateT (IxMap ix IntRef refs) IO ()
runMany kit sem returns = flip foldM () $ \_ cmd'@(Untyped' cmd iref) -> do
  lift $ atomically $ writeTChan (getHistoryChannel kit) $
    InvocationEvent cmd' (getProcessIdHistory kit)
  resp <- liftSem sem returns cmd iref

  lift $ do
    threadDelay =<< randomRIO (0, 20)
    atomically $ writeTChan (getHistoryChannel kit) $
      ResponseEvent (toDyn resp) (getProcessIdHistory kit)

liftSemFork
  :: SDecide ix
  => IxFunctor cmd
  => (forall resp. cmd resp refs -> IO (Response_ refs resp))
  -> (forall resp refs'. cmd resp refs' -> SResponse ix resp)
  -> Fork [Untyped' cmd ConstIntRef]
  -> IO (History cmd)
liftSemFork sem returns (Fork left prefix right) = do
  kit <- mkHistoryKit 0
  env <- execStateT (runMany kit sem returns prefix) IxM.empty
  withPool 2 $ \pool -> do
    parallel_ pool
      [ evalStateT (runMany (kit { getProcessIdHistory = 1}) sem returns left)  env
      , evalStateT (runMany (kit { getProcessIdHistory = 2}) sem returns right) env
      ]
  hist <- getChanContents $ getHistoryChannel kit
  return hist
  where
  getChanContents :: forall a. TChan a -> IO [a]
  getChanContents chan = reverse <$> atomically (go [])
    where
    go :: [a] -> STM [a]
    go acc = do
      mx <- tryReadTChan chan
      case mx of
        Just x  -> go $ x : acc
        Nothing -> return acc

checkParallelInvariant
  :: ShowCmd cmd
  => StateMachineModel model cmd -> History cmd -> PropertyM IO ()
checkParallelInvariant smm hist
  = liftProperty
  . counterexample (("Couldn't linearise:\n\n" ++) $ show $ pretty $ toForkOfOps hist)
  $ linearise smm hist
