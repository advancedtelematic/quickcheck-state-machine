{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module Test.QuickCheck.StateMachineModel where

import           Control.Concurrent                      (threadDelay)
import           Control.Concurrent.ParallelIO.Local     (parallel_, withPool)
import           Control.Concurrent.STM.TChan            (TChan, newTChanIO,
                                                          writeTChan)
import           Control.Monad.State
import           Control.Monad.STM                       (atomically)
import           Data.Dynamic
import           Data.Functor.Compose                    (Compose (..),
                                                          getCompose)
import           Data.Kind
import           Data.List                               (partition)
import           Data.Map                                (Map)
import qualified Data.Map                                as M
import           Data.Maybe                              (fromJust)
import           Data.Monoid                             ((<>))
import           Data.Set                                (Set)
import qualified Data.Set                                as S
import           Data.Singletons.Prelude                 hiding ((:-), Map)
import           Data.Singletons.TH
import           System.Random                           (randomRIO)
import           Test.QuickCheck
import           Test.QuickCheck.Monadic
import           Test.QuickCheck.Property                (Property (..))
import           Text.PrettyPrint.ANSI.Leijen            (Pretty, align, dot,
                                                          indent, int, pretty,
                                                          prettyList, text,
                                                          underline, vsep,
                                                          (<+>))

import           Test.QuickCheck.StateMachineModel.IxMap (IxMap)
import qualified Test.QuickCheck.StateMachineModel.IxMap as IxM
import           Test.QuickCheck.StateMachineModel.Utils

------------------------------------------------------------------------

data Response ix = Response Type | Reference ix

data SResponse ix :: Response ix -> * where
  SResponse  ::                     SResponse ix ('Response  t)
  SReference :: Sing (i :: ix)   -> SResponse ix ('Reference i)

type family Response_ (refs :: TyFun ix k -> *) (resp :: Response ix) :: k where
  Response_ refs ('Response  t) = t
  Response_ refs ('Reference i) = refs @@ i

type family MayResponse_ (refs :: TyFun ix k -> *) (resp :: Response ix) :: k where
  MayResponse_ refs ('Response  t) = ()
  MayResponse_ refs ('Reference i) = refs @@ i

newtype Pid = Pid Int
  deriving (Eq, Ord, Show, Read, Num)

newtype Ref = Ref Int
  deriving (Eq, Ord, Show, Read, Enum, Num)

data IntRef = IntRef Ref Pid
  deriving (Eq, Ord, Show, Read)

data Untyped (f :: Response resp -> (TyFun i * -> *) -> *) refs where
  Untyped :: (Show (Response_ (ConstSym1 IntRef) resp),
               Typeable (Response_ (ConstSym1 IntRef) resp),
               Typeable resp) => f resp refs -> Untyped f refs

data Untyped' (f :: Response resp -> (TyFun i * -> *) -> *) refs where
  Untyped' :: (Show     (Response_ refs resp),
                Typeable (Response_ refs resp),
                Typeable resp
               ) =>
    f resp refs -> MayResponse_ (ConstSym1 IntRef) resp -> Untyped' f refs

data Operation cmd refs = forall resp.
  (Show (Response_ refs resp),
   Typeable resp,
   Typeable (Response_ refs resp)) =>
  Operation (cmd resp refs) (Response_ refs resp) Pid

data IxRefs ix :: (TyFun ix *) -> *

type instance Apply (IxRefs _) i = Sing i

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
  -> cmd resp (ConstSym1 IntRef)
  -> MayResponse_ (ConstSym1 IntRef) resp
  -> StateT (IxMap ix IntRef refs) m (Response_ (ConstSym1 IntRef) resp)
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
  -> Gen ([Untyped' cmd (ConstSym1 IntRef)], Map ix Int)
liftGen gens pid ns returns ixfor = sized $ \sz -> runStateT (go sz) ns
  where

  translate
    :: Map ix Int
    -> forall (x :: ix). Sing x
    -> refs @@ x
    -> Compose Gen Maybe (ConstSym1 IntRef @@ x)
  translate scopes i _ = Compose $ case M.lookup (fromSing i) scopes of
    Nothing -> return Nothing
    Just u  -> do
      v <- choose (0, max 0 (u - 1))
      return . Just $ IntRef (Ref v) pid

  go :: Int -> StateT (Map ix Int) Gen [Untyped' cmd (ConstSym1 IntRef)]
  go 0  = return []
  go sz = do

    scopes       <- get

    Untyped cmd <- lift . genFromMaybe $ do
      Untyped cmd <- frequency gens
      cmd' <- getCompose $ ixfor (Proxy :: Proxy (ConstSym1 IntRef)) cmd (translate scopes)
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
  -> Shrinker (Untyped' cmd (ConstSym1 IntRef))
  -> Shrinker [Untyped' cmd (ConstSym1 IntRef)]
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
  => Untyped' cmd (ConstSym1 IntRef)
  -> [Untyped' cmd (ConstSym1 IntRef)]
  -> (forall resp refs. cmd resp refs -> SResponse ix resp)
  -> [Untyped' cmd (ConstSym1 IntRef)]
removeCommands (Untyped' cmd0 miref0) cmds0 returns =
  case returns cmd0 of
    SResponse    -> cmds0
    SReference _ -> go cmds0 (S.singleton miref0)
  where
  go :: [Untyped' cmd (ConstSym1 IntRef)] -> Set IntRef -> [Untyped' cmd (ConstSym1 IntRef)]
  go []                                  _       = []
  go (cmd@(Untyped' cmd' miref) : cmds) removed =
    case returns cmd' of
      SReference _ | cmd `uses` removed ->       go cmds (S.insert miref removed)
                   | otherwise          -> cmd : go cmds removed
      SResponse    | cmd `uses` removed ->       go cmds removed
                   | otherwise          -> cmd : go cmds removed

uses :: IxFoldable (cmd resp) => cmd resp (ConstSym1 IntRef) -> Set IntRef -> Bool
uses cmd xs = iany (\_ iref -> iref `S.member` xs) cmd

------------------------------------------------------------------------

data StateMachineModel model cmd = StateMachineModel
  { precondition  :: forall refs resp. IxForallF Ord refs =>
      model refs -> cmd resp refs -> Bool
  , postcondition :: forall refs resp. IxForallF Ord refs =>
      model refs -> cmd resp refs -> Response_ refs resp -> Property
  , transition    :: forall refs resp. IxForallF Ord refs =>
      model refs -> cmd resp refs -> Response_ refs resp -> model refs
  , initialModel  :: forall refs.      model refs
  }

sequentialProperty
  :: forall
     (ix    :: *)
     (cmd   :: Response ix -> (TyFun ix * -> *) -> *)
     (refs  :: TyFun ix * -> *)
     (model :: (TyFun ix * -> *) -> *)
     (m     :: * -> *)
  .  Monad m
  => IxFunctor1 cmd
  => Show (Untyped' cmd (ConstSym1 IntRef))
  => IxFoldable (Untyped' cmd)
  => Ord       ix
  => SDecide   ix
  => SingKind  ix
  => DemoteRep ix ~ ix
  => StateMachineModel model cmd
  -> [(Int, Gen (Untyped cmd (IxRefs ix)))]
  -> (forall refs'. Shrinker (Untyped' cmd refs'))
  -> (forall resp refs'. cmd resp refs' -> SResponse ix resp)
  -> (forall resp. cmd resp refs -> m (Response_ refs resp))
  -> (forall f p q resp. Applicative f
        => Proxy q
        -> cmd resp p
        -> (forall (x :: ix). Sing x -> p @@ x -> f (q @@ x))
        -> f (cmd resp q))
  -> (m Property -> Property)
  -> Property
sequentialProperty StateMachineModel {..} gens shrinker returns runCmd ixFor runM =
  forAllShrink
    (fst <$> liftGen gens 0 M.empty returns ixFor)
    (liftShrink returns shrinker)
    $ \cmds ->
      let len = length cmds in
      classify (len == 0)              "0     commands" $
      classify (len >= 1  && len < 15) "1-15  commands" $
      classify (len >= 15 && len < 30) "15-30 commands" $
      classify (len >= 30)             "30+   commands" $
        monadic (runM . flip evalStateT IxM.empty) $ go initialModel cmds
  where
  go :: model (ConstSym1 IntRef) -> [Untyped' cmd (ConstSym1 IntRef)]
     -> PropertyM (StateT (IxMap ix IntRef refs) m) ()
  go _ []                                  = return ()
  go m (cmd@(Untyped' cmd' miref) : cmds) = do
    let s = takeWhile (/= ' ') $ show cmd
    monitor $ label s
    -- traceShowM m
    pre $ precondition m cmd'
    resp <- run $ liftSem runCmd returns cmd' miref
    liftProperty $
      counterexample ("The post-condition for `" ++ s ++ "' failed!") $
        postcondition m cmd' resp
    go (transition m cmd' resp) cmds

------------------------------------------------------------------------

data Fork a = Fork a a a
  deriving (Eq, Functor, Show, Ord, Read)

instance Pretty a => Pretty (Fork a) where
  pretty (Fork l p r) = vsep
    [ underline $ text "Prefix:"
    , indent 5 $ pretty p
    , underline $ text "Parallel:"
    , indent 2 $ int 1 <> dot <+> align (pretty l)
    , indent 2 $ int 2 <> dot <+> align (pretty r)
    ]

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

data Rose a = Rose a [Rose a]
  deriving Show

fromRose :: Rose a -> [a]
fromRose (Rose x xs) = x : concatMap fromRose xs

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
  [ Rose (Operation cmd (fromJust $ fromDynamic resp) pid) (linearTree es')
  | InvocationEvent (Untyped' cmd _) pid <- takeInvocations es
  , (resp, es')  <- findCorrespondingResp pid $ filter1 (not . matchInv pid) es
  ]
  where
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

class ShowCmd (cmd :: Response ix -> (TyFun ix * -> *) -> *) (refs :: TyFun ix * -> *) where
  showCmd :: forall resp. cmd resp refs -> String

instance ShowCmd cmd refs => Pretty (Operation cmd refs) where
  pretty (Operation cmd resp _) =
    text (showCmd cmd) <+> text "-->" <+> text (show resp)
  prettyList                     = vsep . map pretty

toForkOfOps :: forall cmd refs. History cmd refs -> Fork [Operation cmd refs]
toForkOfOps h = Fork (mkOps l) p' (mkOps r)
  where
  (p, h') = partition (\e -> getProcessIdEvent e == 0) h
  (l, r)  = partition (\e -> getProcessIdEvent e == 1) h'

  p'      = mkOps p

  mkOps :: [HistoryEvent (Untyped' cmd refs)] -> [Operation cmd refs]
  mkOps [] = []
  mkOps (InvocationEvent (Untyped' cmd _) _ : ResponseEvent resp pid : es)
    = Operation cmd (fromJust $ fromDynamic resp) pid : mkOps es
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

parallelProperty
  :: forall
     (ix    :: *)
     (cmd   :: Response ix -> (TyFun ix * -> *) -> *)
     (refs  :: TyFun ix * -> *)
     (model :: (TyFun ix * -> *) -> *)
  .  IxFunctor1 cmd
  => IxFoldable (Untyped' cmd)
  => Show (Untyped' cmd (ConstSym1 IntRef))
  => ShowCmd cmd (ConstSym1 IntRef)
  => Ord (Untyped' cmd (ConstSym1 IntRef))
  => Ord       ix
  => SDecide   ix
  => SingKind  ix
  => DemoteRep ix ~ ix
  => StateMachineModel model cmd
  -> [(Int, Gen (Untyped cmd (IxRefs ix)))]
  -> (forall refs'. Shrinker (Untyped' cmd refs'))
  -> (forall resp refs'. cmd resp refs' -> SResponse ix resp)
  -> (forall resp. cmd resp refs -> IO (Response_ refs resp))
  -> (forall f p q resp. Applicative f
        => Proxy q
        -> cmd resp p
        -> (forall (x :: ix). Sing x -> p @@ x -> f (q @@ x))
        -> f (cmd resp q))
  -> Property
parallelProperty smm gen shrinker returns runStep ifor
  = forAllShrinkShow
      (liftGenFork gen returns ifor)
      (liftShrinkFork returns shrinker)
      show $ monadicIO . \(Fork left prefix right) -> do
        replicateM_ 10 $ do
          kit <- run $ mkHistoryKit 0
          env <- run $ execStateT (runMany kit runStep returns prefix) IxM.empty
          run $ withPool 2 $ \pool -> do
            parallel_ pool
              [ evalStateT (runMany (kit { getProcessIdHistory = 1}) runStep returns left)  env
              , evalStateT (runMany (kit { getProcessIdHistory = 2}) runStep returns right) env
              ]
          hist <- run $ getChanContents $ getHistoryChannel kit
          liftProperty $ counterexample
            (("Couldn't linearise:\n\n" ++) $ show $ pretty $ toForkOfOps hist) $
              linearise smm hist

------------------------------------------------------------------------

canonical'
  :: forall
     (ix   :: *)
     (cmd  :: Response ix -> (TyFun ix * -> *) -> *)
  .  SDecide ix
  => (forall resp refs. cmd resp refs -> SResponse ix resp)
  -> (forall f p q resp. Applicative f
        => Proxy q
        -> cmd resp p
        -> (forall (x :: ix). Sing x -> p @@ x -> f (q @@ x))
        -> f (cmd resp q))
  -> IxMap ix IntRef (ConstSym1 IntRef)
  -> [Untyped' cmd (ConstSym1 IntRef)]
  -> ([Untyped' cmd (ConstSym1 IntRef)], IxMap ix IntRef (ConstSym1 IntRef))
canonical' returns ixfor im = flip runState im . go
  where
  go :: [Untyped' cmd (ConstSym1 IntRef)]
     -> State (IxMap ix IntRef (ConstSym1 IntRef)) [Untyped' cmd (ConstSym1 IntRef)]
  go xs = forM xs $ \(Untyped' cmd ref) -> do
    cmd' <- ixfor (Proxy :: Proxy (ConstSym1 IntRef)) cmd $ \ ix iref -> do
      (IxM.! (ix, iref)) <$> Control.Monad.State.get
    ref' <- case returns cmd of
      SResponse -> return ()
      SReference i -> do
        m <- Control.Monad.State.get
        let ref' = IntRef (Ref $ IxM.size i m) (Pid 0)
        put $ IxM.insert i ref ref' m
        return $ ref'
    return $ Untyped' cmd' ref'

canonical
  :: forall
     (ix   :: *)
     (cmd  :: Response ix -> (TyFun ix * -> *) -> *)
  .  SDecide ix
  => (forall resp refs. cmd resp refs -> SResponse ix resp)
  -> (forall f p q resp. Applicative f
        => Proxy q
        -> cmd resp p
        -> (forall (x :: ix). Sing x -> p @@ x -> f (q @@ x))
        -> f (cmd resp q))
  -> [Untyped' cmd (ConstSym1 IntRef)]
  -> [Untyped' cmd (ConstSym1 IntRef)]
canonical returns ixfor = fst . canonical' returns ixfor IxM.empty

canonicalFork
  :: forall
     (ix   :: *)
     (cmd  :: Response ix -> (TyFun ix * -> *) -> *)
  .  SDecide ix
  => (forall resp refs. cmd resp refs -> SResponse ix resp)
  -> (forall f p q resp. Applicative f
        => Proxy q
        -> cmd resp p
        -> (forall (x :: ix). Sing x -> p @@ x -> f (q @@ x))
        -> f (cmd resp q))
  -> Fork [Untyped' cmd (ConstSym1 IntRef)]
  -> Fork [Untyped' cmd (ConstSym1 IntRef)]
canonicalFork returns ixfor (Fork l p r) = Fork l' p' r'
  where
  (p', im') = canonical' returns ixfor IxM.empty p
  l'        = fst $ canonical' returns ixfor im' l
  r'        = fst $ canonical' returns ixfor im' r

alphaEq
  :: forall
     (ix   :: *)
     (cmd  :: Response ix -> (TyFun ix * -> *) -> *)
  .  SDecide ix
  => Eq (Untyped' cmd (ConstSym1 IntRef))
  => (forall resp refs. cmd resp refs -> SResponse ix resp)
  -> (forall f p q resp. Applicative f
        => Proxy q
        -> cmd resp p
        -> (forall (x :: ix). Sing x -> p @@ x -> f (q @@ x))
        -> f (cmd resp q))
  -> [Untyped' cmd (ConstSym1 IntRef)]
  -> [Untyped' cmd (ConstSym1 IntRef)]
  -> Bool
alphaEq returns ixfor c0 c1
  = canonical returns ixfor c0 == canonical returns ixfor c1

alphaEqFork
  :: forall
     (ix   :: *)
     (cmd  :: Response ix -> (TyFun ix * -> *) -> *)
  .  SDecide ix
  => Eq (Untyped' cmd (ConstSym1 IntRef))
  => (forall resp refs. cmd resp refs -> SResponse ix resp)
  -> (forall f p q resp. Applicative f
        => Proxy q
        -> cmd resp p
        -> (forall (x :: ix). Sing x -> p @@ x -> f (q @@ x))
        -> f (cmd resp q))
  -> Fork [Untyped' cmd (ConstSym1 IntRef)]
  -> Fork [Untyped' cmd (ConstSym1 IntRef)]
  -> Bool
alphaEqFork returns ixfor f1 f2
  = canonicalFork returns ixfor f1 == canonicalFork returns ixfor f2

------------------------------------------------------------------------

ppFork :: Show (cmd ref) => Fork [cmd ref] -> IO ()
ppFork = putStrLn . ppFork'

ppFork' :: Show (cmd ref) => Fork [cmd ref] -> String
ppFork' = show . pretty . fmap (prettyList . map show)

ppForks :: Show (cmd ref) => [Fork [cmd ref]] -> IO ()
ppForks = mapM_ putStrLn . lines . ppForks'

ppForks' :: Show (cmd ref) => [Fork [cmd ref]] -> String
ppForks' = unlines . map (show . pretty . fmap (prettyList . map show))
