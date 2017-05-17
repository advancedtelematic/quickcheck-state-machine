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
import qualified Data.Map                              as M
import           Data.Maybe                            (fromMaybe)
import           Data.Singletons.Decide                (SDecide)
import           Data.Singletons.Prelude               (DemoteRep, SingKind,
                                                        TyFun, fromSing)
import           Data.Tree                             (Tree (Node))
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
import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Types
import           Test.StateMachine.Internal.Utils

------------------------------------------------------------------------

liftGenFork
  :: Ord       ix
  => SingKind  ix
  => DemoteRep ix ~ ix
  => IxTraversable cmd
  => HasResponse   cmd
  => [(Int, Gen (Untyped cmd (RefPlaceholder ix)))]
  -> Gen (Fork [IntRefed cmd])
liftGenFork gens = do
  (prefix, ns) <- liftGen gens 0 M.empty
  left         <- fst <$> liftGen gens 1 ns
  right        <- fst <$> liftGen gens 2 ns
  return $ Fork
    (map (\(IntRefed cmd miref) ->
            IntRefed (ifmap (fixPid ns) cmd) miref) left)
    prefix
    (map (\(IntRefed cmd miref) ->
            IntRefed (ifmap (fixPid ns) cmd) miref) right)
  where
  fixPid ns i iref@(IntRef (Ref ref) _)
    | ref <= ns M.! fromSing i = IntRef (Ref ref) 0
    | otherwise                = iref

------------------------------------------------------------------------

liftShrinkFork
  :: forall cmd
  .  IxFoldable  cmd
  => HasResponse cmd
  => (forall resp. Shrinker (cmd ConstIntRef resp))
  -> Shrinker (Fork [IntRefed cmd])
liftShrinkFork shrinker f@(Fork l0 p0 r0) =

  -- Only shrink the branches:
  [ Fork l' p0 r'
  | (l', r') <- shrinkPair (liftShrink shrinker)
                           (liftShrink shrinker)
                           (l0, r0)
  ] ++

  -- Only shrink the prefix:
  shrinkPrefix f

  where
  shrinkPrefix :: Fork [IntRefed cmd] -> [Fork [IntRefed cmd]]
  shrinkPrefix (Fork _ []       _) = []
  shrinkPrefix (Fork l (p : ps) r) =
      [ Fork l'   []                      r'   ] ++
      [ Fork l''  (removeCommands p ps) r''  ] ++
      [ Fork l''' (p' : ps')              r'''
      | (p', Fork l''' ps' r''') <- shrinkPair (liftShrinker shrinker)
                                               shrinkPrefix
                                               (p, Fork l ps r)
      ]
      where
      l'  = removeManyCommands (p : ps) l
      r'  = removeManyCommands (p : ps) r

      l'' = removeCommands p l
      r'' = removeCommands p r

      removeManyCommands :: [IntRefed cmd] -> [IntRefed cmd] -> [IntRefed cmd]
      removeManyCommands []       ds = ds
      removeManyCommands (c : cs) ds = removeManyCommands cs (removeCommands c ds)

------------------------------------------------------------------------

type History cmd = [HistoryEvent (IntRefed cmd)]

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
  Operation (cmd ConstIntRef resp) (Response_ ConstIntRef resp) Pid

instance ShowCmd cmd => Pretty (Operation cmd) where
  pretty (Operation cmd resp _) =
    text (showCmd cmd) <+> text "-->" <+> text (show resp)
  prettyList                     = vsep . map pretty

takeInvocations :: History cmd -> [HistoryEvent (IntRefed cmd)]
takeInvocations = takeWhile $ \h -> case h of
  InvocationEvent _ _ -> True
  _                   -> False

findCorrespondingResp :: Pid -> History cmd -> [(Dynamic, History cmd)]
findCorrespondingResp _   [] = []
findCorrespondingResp pid (ResponseEvent resp pid' : es) | pid == pid' = [(resp, es)]
findCorrespondingResp pid (e : es) =
  [ (resp, e : es') | (resp, es') <- findCorrespondingResp pid es ]

linearTree :: History cmd -> [Tree (Operation cmd)]
linearTree [] = []
linearTree es =
  [ Node (Operation cmd (dynResp resp) pid) (linearTree es')
  | InvocationEvent (IntRefed cmd _) pid <- takeInvocations es
  , (resp, es')  <- findCorrespondingResp pid $ filter1 (not . matchInv pid) es
  ]
  where
  dynResp resp = fromMaybe (error "linearTree: impossible.") (fromDynamic resp)

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
  step :: model ConstIntRef -> Tree (Operation cmd) -> Property
  step m (Node (Operation cmd resp _) roses) =
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

  mkOps :: [HistoryEvent (IntRefed cmd)] -> [Operation cmd]
  mkOps [] = []
  mkOps (InvocationEvent (IntRefed cmd _) _ : ResponseEvent resp pid : es)
    = Operation cmd (dynResp resp) pid : mkOps es
    where
    dynResp = fromMaybe (error "toForkOfOps: impossible.") . fromDynamic
  mkOps _  = error "mkOps: Impossible."

------------------------------------------------------------------------

data HistoryKit cmd refs = HistoryKit
  { getHistoryChannel   :: TChan (HistoryEvent (IntRefed cmd))
  , getProcessIdHistory :: Pid
  }

mkHistoryKit :: Pid -> IO (HistoryKit cmd refs)
mkHistoryKit pid = do
  chan <- newTChanIO
  return $ HistoryKit chan pid

runMany
  :: SDecide ix
  => IxFunctor   cmd
  => HasResponse cmd
  => HistoryKit cmd ConstIntRef
  -> (forall resp. cmd refs resp -> IO (Response_ refs resp))
  -> [IntRefed cmd]
  -> StateT (IxMap ix IntRef refs) IO ()
runMany kit sem = flip foldM () $ \_ cmd'@(IntRefed cmd iref) -> do
  lift $ atomically $ writeTChan (getHistoryChannel kit) $
    InvocationEvent cmd' (getProcessIdHistory kit)
  resp <- liftSem sem cmd iref

  lift $ do
    threadDelay =<< randomRIO (0, 20)
    atomically $ writeTChan (getHistoryChannel kit) $
      ResponseEvent (toDyn resp) (getProcessIdHistory kit)

liftSemFork
  :: forall
     (ix    :: *)
     (cmd   :: Signature ix)
     (refs  :: TyFun ix * -> *)
  .  SDecide ix
  => IxFunctor   cmd
  => HasResponse cmd
  => (forall resp. cmd refs resp -> IO (Response_ refs resp))
  -> Fork [IntRefed cmd]
  -> IO (History cmd)
liftSemFork sem (Fork left prefix right) = do
  kit <- mkHistoryKit 0
  env <- execStateT (runMany kit sem prefix) IxM.empty
  withPool 2 $ \pool ->
    parallel_ pool
      [ evalStateT (runMany (kit { getProcessIdHistory = 1}) sem left)  env
      , evalStateT (runMany (kit { getProcessIdHistory = 2}) sem right) env
      ]
  getChanContents $ getHistoryChannel kit
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
