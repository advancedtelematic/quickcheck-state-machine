{-# OPTIONS_GHC -fno-warn-orphans      #-}

{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

module Test.QuickCheck.StateMachineModel where

import           Control.Concurrent                      (threadDelay)
import           Control.Concurrent.ParallelIO.Local     (parallel_, withPool)
import           Control.Concurrent.STM.TChan            (TChan, newTChanIO,
                                                          tryReadTChan,
                                                          writeTChan)
import           Control.Monad.State
import           Control.Monad.STM                       (STM, atomically)
import           Data.Dynamic
import           Data.Foldable                           (toList)
import           Data.List                               (partition)
import           Data.Map                                (Map)
import qualified Data.Map                                as M
import           Data.Maybe                              (fromJust, isJust)
import           Data.Monoid                             ((<>))
import qualified Data.Set                                as Set
import           System.Random                           (randomRIO)
import           Test.QuickCheck
import           Test.QuickCheck.Monadic
import           Test.QuickCheck.Property                (Property (..))
import           Text.PrettyPrint.ANSI.Leijen            (Pretty, align, dot,
                                                          empty, indent, int,
                                                          pretty, prettyList,
                                                          text, underline, vsep,
                                                          (<+>))

import           Test.QuickCheck.StateMachineModel.Utils

import           Unsafe.Coerce

------------------------------------------------------------------------

liftSemSeq
  :: forall cmd resp ix ref m
  .  (Monad m, Enum ix, Typeable ref, RefKit cmd)
  => Typeable resp
  => Ord ix
  => Show resp
  => (cmd resp ref -> m resp)
  -> cmd resp ix -> StateT (Map ix ref) m resp
liftSemSeq sem cmd = do

  env <- get
  Untyped cmd' <- return $ fmap (\ix -> env M.! ix) $ Untyped cmd
  let Just (cmd'' :: cmd resp ref) = ccast cmd'

  case returnsRef' cmd'' of
    Just Refl -> do
      ref <- lift $ sem cmd''
      let ix :: ix
          ix = toEnum . length . M.keys $ env
      modify $ M.insert ix ref
      return $ unsafeCoerce ix
    Nothing -> do
      resp <- lift $ sem cmd''
      return resp

liftSem
  :: forall cmd resp ix ref m
  .  (Monad m, Enum ix, Typeable ref, RefKit cmd)
  => Typeable resp
  => Ord (ix, Int)
  => Show resp
  => (cmd resp ref -> m resp)
  -> Int
  -> cmd resp (ix, Int) -> StateT (Map (ix, Int) ref) m resp
liftSem sem pid cmd = do

  env <- get
  Untyped cmd' <- return $ fmap (\ix -> env M.! ix) $ Untyped cmd
  let Just (cmd'' :: cmd resp ref) = ccast cmd'

  case returnsRef' cmd'' of
    Just Refl -> do
      ref <- lift $ sem cmd''
      let ix :: ix
          ix = toEnum . length . filter ((== pid) . snd) . M.keys $ env
      modify $ M.insert (ix, pid) ref
      return $ unsafeCoerce (ix, pid)

    Nothing -> do
      resp <- lift $ sem cmd''
      return resp

ccast
  :: forall a resp cmd ref. (Typeable a, Typeable resp)
  => cmd a ref -> Maybe (cmd resp ref)
ccast x = fmap (\Refl -> x) (eqT :: Maybe (a :~: resp))

------------------------------------------------------------------------

data Untyped f b where
  Untyped :: (Typeable a, Show a) => f a b -> Untyped f b

typed :: Typeable a => Show a => Untyped f b -> f a b
typed (Untyped f) = fromJust $ ccast f

liftGen
  :: forall cmd ref
  .  RefKit cmd
  => Enum ref
  => [(Int, Gen (Untyped cmd ()))]
  -> Int
  -> Gen ([Untyped cmd ref], Int)
liftGen gens n = sized $ \sz -> runStateT (go sz) n
  where
  go :: Int -> StateT Int Gen [Untyped cmd ref]
  go 0  = return []
  go sz = do
    scope <- get
    cmd   <- lift $ frequency gens
    if scope == 0
    then do
      if returnsRef cmd && null (usesRefs cmd)
      then do
        put 1
        ih <- go (sz - 1)
        return $ fmap (error "impossible: no refs used") cmd : ih
      else go sz
    else do
      when (returnsRef cmd) $
        modify succ
      ih <- go (sz - 1)
      if null $ usesRefs cmd
      then
        return $ fmap (error "impossible: no refs used") cmd : ih
      else do
        ref <- toEnum <$> lift (choose (0, scope - 1))
        return $ fmap (const ref) cmd : ih

------------------------------------------------------------------------

liftShrink
  :: RefKit cmd
  => (Enum ref, Ord ref)
  => (Untyped cmd ref -> [Untyped cmd ref])
  -> ([Untyped cmd ref] -> [[Untyped cmd ref]])
liftShrink shrinker = liftShrink' 0 shrinker

liftShrink'
  :: RefKit cmd
  => (Enum ref, Ord ref)
  => Int
  -> (Untyped cmd ref -> [Untyped cmd ref])
  -> ([Untyped cmd ref] -> [[Untyped cmd ref]])
liftShrink' n0 shrinker = go n0
  where
  go _ []       = []
  go n (c : cs) =
    [ [] ] ++
    [ fixRefs n c cs ] ++
    [ c' : cs' | (c', cs') <- shrinkPair' shrinker (go n') (c, cs) ]
    where
    n' = if returnsRef c then n + 1 else n

liftShrinkPid
  :: RefKit cmd
  => (Enum ix, Ord ix)
  => Int
  -> (Untyped cmd (ix, Int) -> [Untyped cmd (ix, Int)])
  -> ([Untyped cmd (ix, Int)] -> [[Untyped cmd (ix, Int)]])
liftShrinkPid pid shrinker = go 0
  where
  go _ []       = []
  go n (c : cs) =
    [ [] ] ++
    [ fixRefsPid n pid c cs ] ++
    [ c' : cs' | (c', cs') <- shrinkPair' shrinker (go n') (c, cs) ]
    where
    n' = if returnsRef c then n + 1 else n

------------------------------------------------------------------------

data StateMachineModel model cmd = StateMachineModel
  { precondition  :: forall ix resp. Ord ix => model ix -> cmd resp ix -> Bool
  , postcondition :: forall ix resp. (Enum ix, Ord ix) => model ix -> cmd resp ix -> resp -> Property
  , transition    :: forall ix resp. (Enum ix, Ord ix) => model ix -> cmd resp ix -> resp -> model ix
  , initialModel  :: forall ix.      model ix
  }

sequentialProperty
  :: forall m cmd ix ref model
  .  Show (Untyped cmd ix)
  => Monad m
  => (Enum ix, Ord ix)
  => RefKit cmd
  => Typeable ref
  => StateMachineModel model cmd
  -> [(Int, Gen (Untyped cmd ()))]
  -> (Untyped cmd ix -> [Untyped cmd ix])
  -> (forall resp. cmd resp ref -> m resp)
  -> (m Property -> Property)
  -> Property
sequentialProperty StateMachineModel {..} gens shrinker runCmd runM =
  forAllShrink
    (fst <$> liftGen gens 0)
    (liftShrink shrinker)
    $ \cmds ->
      let len = length cmds in
      classify (len == 0)              "0     commands" $
      classify (len >= 1  && len < 15) "1-15  commands" $
      classify (len >= 15 && len < 30) "15-30 commands" $
      classify (len >= 30)             "30+   commands" $
        monadic (runM . flip evalStateT M.empty) $ go initialModel cmds
  where
  go :: model ix -> [Untyped cmd ix] -> PropertyM (StateT (Map ix ref) m) ()
  go _ []           = return ()
  go m (cmd@(Untyped cmd') : cmds) = do
    let s = takeWhile (/= ' ') $ show cmd
    monitor $ label s
    pre $ precondition m cmd'
    resp <- run $ liftSemSeq runCmd cmd'
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
  :: forall cmd ix
  .  RefKit cmd
  => Enum ix
  => Functor (Untyped cmd)
  => Ord ix
  => [(Int, Gen (Untyped cmd ()))]
  -> Gen (Fork [Untyped cmd (ix, Int)])
liftGenFork gens = do
  (prefix, n) <- liftGen gens 0
  left        <- fst <$> liftGen gens n
  right       <- fst <$> liftGen gens n
  return $ Fork
    (map (fmap (fixPid n 1)) left)
    (map (fmap (\ix -> (ix, 0))) prefix)
    (map (fmap (fixPid n 2)) right)
  where
  fixPid :: Int -> Int -> ix -> (ix, Int)
  fixPid n pid ix | fromEnum ix < n = (ix, 0)
                | otherwise       = (toEnum (fromEnum ix - n), pid)

------------------------------------------------------------------------

liftShrinkFork
  :: forall cmd ix
  .  RefKit cmd
  => (Enum ix, Ord ix)
  => Ord (Untyped cmd (ix, Int))
  => (Untyped cmd (ix, Int) -> [Untyped cmd (ix, Int)])
  -> (Fork [Untyped cmd (ix, Int)] -> [Fork [Untyped cmd (ix, Int)]])
liftShrinkFork shrinker f@(Fork l0 p0 r0) = Set.toList $ Set.fromList $

  -- Only shrink the branches:
  [ Fork l' p0 r'
  | (l', r') <- shrinkPair' (liftShrinkPid 1 shrinker)
                            (liftShrinkPid 2 shrinker)
                            (l0, r0)
  ] ++

  -- Only shrink the prefix:
  shrinkPrefix f

  where
  shrinkPrefix
    :: RefKit cmd
    => (Enum ix, Ord ix)
    => Fork [Untyped cmd (ix, Int)] -> [Fork [Untyped cmd (ix, Int)]]
  shrinkPrefix = go 0
    where
    go _ (Fork _ []       _) = []
    go n (Fork l (p : ps) r) =
      [ Fork l'   []               r'   ] ++
      [ Fork l''  (fixRefsPid n 0 p ps) r''  ] ++
      [ Fork l''' (p' : ps')       r'''
      | (p', Fork l''' ps' r''') <- shrinkPair' shrinker (go n') (p, Fork l ps r)
      ]
      where
      l'  = fixManyRefsPid n 0 (p : ps) l
      r'  = fixManyRefsPid n 0 (p : ps) r

      l'' = fixRefsPid n 0 p l
      r'' = fixRefsPid n 0 p r

      n'  | returnsRef p = n + 1
          | otherwise    = n

------------------------------------------------------------------------

type History cmd ref = [HistoryEvent (Untyped cmd ref)]

data HistoryEvent cmd
  = InvocationEvent
      { invocation        :: cmd
      , getProcessIdEvent :: Int
      }
  | ResponseEvent
      { response          :: Dynamic
      , getProcessIdEvent :: Int
      }

data Rose a = Rose a [Rose a]
  deriving Show

fromRose :: Rose a -> [a]
fromRose (Rose x xs) = x : concatMap fromRose xs

takeInvocations :: History cmd ref -> [HistoryEvent (Untyped cmd ref)]
takeInvocations = takeWhile $ \h -> case h of
  InvocationEvent _ _ -> True
  _                   -> False

findCorrespondingResp :: Int -> History cmd ref -> [(Dynamic, History cmd ref)]
findCorrespondingResp _   [] = []
findCorrespondingResp pid (ResponseEvent resp pid' : es) | pid == pid' = [(resp, es)]
findCorrespondingResp pid (e : es) =
  [ (resp, e : es') | (resp, es') <- findCorrespondingResp pid es ]

data Operation cmd ref = forall resp. (Typeable resp, Show resp) =>
  Operation (cmd resp ref) resp Int (Maybe Int)

linearTree :: History cmd ix -> [Rose (Operation cmd ix)]
linearTree [] = []
linearTree es =
  [ Rose (Operation cmd (fromJust $ fromDynamic resp) pid Nothing) (linearTree es')
  | InvocationEvent (Untyped cmd) pid <- takeInvocations es
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

instance (Enum a, Enum b) => Enum (a, b) where

  toEnum   i      = let (x, y) = cantorsPairingInv i
                    in (toEnum x, toEnum y)
    where
    cantorsPairingInv :: Int -> (Int, Int)
    cantorsPairingInv z = (x, y)
      where
      w :: Int
      w = floor ((sqrt ((8 :: Double) * fromInteger (toInteger z) + 1) - 1) / 2)
      t :: Int
      t = (w * w + w) `div` 2
      y = z - t
      x = w - y

  fromEnum (a, b) = cantorsPairing (fromEnum a) (fromEnum b)
    where
    cantorsPairing :: Int -> Int -> Int
    cantorsPairing m n = (m + n) * (m + n + 1) `div` 2 + n

linearise
  :: forall cmd ix model
  .  (Enum ix, Ord (ix, Int))
  => Show (model (ix, Int))
  => Functor (Untyped cmd)
  => StateMachineModel model cmd
  -> History cmd (ix, Int)
  -> Property
linearise _                       [] = property True
linearise StateMachineModel {..} xs0 = anyP (step initialModel) . linearTree $ xs0
  where
  step :: model (ix, Int) -> Rose (Operation cmd (ix, Int)) -> Property
  step m (Rose (Operation cmd resp _ _) roses) =
    postcondition m cmd resp .&&.
    anyP' (step (transition m cmd resp)) roses
    where
    anyP' :: (a -> Property) -> [a] -> Property
    anyP' _ [] = property True
    anyP' p xs = anyP p xs

------------------------------------------------------------------------

instance (Show (Untyped cmd ref)) => Pretty (Operation cmd ref) where
  pretty (Operation cmd resp _ mix) =
    text (show (Untyped cmd)) <+> text "-->" <+> text (show resp) <> maybe empty int mix
  prettyList                        = vsep . map pretty

toForkOfOps
  :: forall cmd ref
  .  (RefKit cmd)
  => History cmd ref -> Fork [Operation cmd ref]
toForkOfOps h = Fork (fst $ mkOps n0 l) p' (fst $ mkOps n0 r)
  where
  (p, h') = partition (\e -> getProcessIdEvent e == 0) h
  (l, r)  = partition (\e -> getProcessIdEvent e == 1) h'

  (p', n0) = mkOps 0 p

  mkOps :: Int -> [HistoryEvent (Untyped cmd ref)] -> ([Operation cmd ref], Int)
  mkOps n [] = ([], n)
  mkOps n (InvocationEvent (Untyped cmd) _ : ResponseEvent resp pid : es)
    | returnsRef (Untyped cmd) = let (ih, n') = mkOps (n + 1) es
                       in  (Operation cmd (fromJust $ fromDynamic resp) pid (Just n) : ih, n')
    | otherwise      = let (ih, n') = mkOps n es
                       in  (Operation cmd (fromJust $ fromDynamic resp) pid Nothing  : ih, n')
  mkOps _ _ = error "mkOps: Impossible."

------------------------------------------------------------------------

data HistoryKit cmd ref = HistoryKit
  { getHistoryChannel   :: TChan (HistoryEvent (Untyped cmd ref))
  , getProcessIdHistory :: Int
  }

mkHistoryKit :: Int -> IO (HistoryKit cmd ref)
mkHistoryKit pid = do
  chan <- newTChanIO
  return $ HistoryKit chan pid

runMany
  :: RefKit cmd
  => Typeable ref
  => (Enum ix, Ord ix)
  => HistoryKit cmd (ix, Int)
  -> (forall resp. cmd resp ref -> IO resp)
  -> [Untyped cmd (ix, Int)] -> StateT (Map (ix, Int) ref) IO ()
runMany kit step = flip foldM () $ \_ cmd'@(Untyped cmd) -> do
  lift $ atomically $ writeTChan (getHistoryChannel kit) $
    InvocationEvent cmd' (getProcessIdHistory kit)
  resp <- liftSem step (getProcessIdHistory kit) cmd
  lift $ do
    threadDelay =<< randomRIO (0, 20)
    atomically $ writeTChan (getHistoryChannel kit) $
      ResponseEvent (toDyn resp) (getProcessIdHistory kit)

parallelProperty
  :: forall cmd ix ref model
  .  (Ord (Untyped cmd (ix, Int)), Show (Untyped cmd (ix, Int)))
  => (Enum ix, Ord ix, Show ix)
  => Typeable ref
  => Show (model (ix, Int))
  => RefKit cmd
  => StateMachineModel model cmd
  -> [(Int, Gen (Untyped cmd ()))]
  -> (Untyped cmd (ix, Int) -> [Untyped cmd (ix, Int)])
  -> (forall resp. cmd resp ref -> IO resp)
  -> Property
parallelProperty smm gen shrinker runStep
  = forAllShrinkShow (liftGenFork gen) (liftShrinkFork shrinker) show
  $ monadicIO
  . \(Fork left prefix right) -> do
      replicateM_ 10 $ do
        kit <- run $ mkHistoryKit 0
        env <- run $ execStateT (runMany kit runStep prefix) M.empty
        run $ withPool 2 $ \pool -> do
          parallel_ pool
            [ evalStateT (runMany (kit { getProcessIdHistory = 1}) runStep left)  env
            , evalStateT (runMany (kit { getProcessIdHistory = 2}) runStep right) env
            ]

        hist <- run $ getChanContents $ getHistoryChannel kit
        liftProperty $ counterexample
          (("Couldn't linearise:\n\n" ++) $ show $ pretty $ toForkOfOps hist) $
            linearise smm hist
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

------------------------------------------------------------------------

class (Functor (Untyped cmd), Foldable (Untyped cmd)) => RefKit cmd where

  returnsRef :: Untyped cmd ref -> Bool
  returnsRef (Untyped c) = isJust $ returnsRef' c

  returnsRef' :: cmd resp ref -> Maybe (resp :~: ref)

  usesRefs :: Untyped cmd ref -> [ref]
  usesRefs = toList

  countRefReturns :: [Untyped cmd ref] -> Int
  countRefReturns = length . filter returnsRef

  fixRefs
    :: (Enum ref, Ord ref)
    => Int -> Untyped cmd ref -> [Untyped cmd ref] -> [Untyped cmd ref]
  fixRefs n c cs
    | returnsRef c
        = map (fmap (\ref -> if r < ref then toEnum (fromEnum ref - 1) else ref))
        . filter (\ms -> [r] /= usesRefs ms)
        $ cs
    | otherwise = cs
    where
    r = toEnum n

  fixRefsPid
    :: forall ix
    .  (Enum ix, Ord ix)
    => Int -> Int -> Untyped cmd (ix, Int) -> [Untyped cmd (ix, Int)] -> [Untyped cmd (ix, Int)]
  fixRefsPid n pid c cs
    | returnsRef c
        = map (fmap (\(ix, pid') -> if pid == pid' && toEnum n < ix
                                    then (toEnum (fromEnum ix - 1), pid')
                                    else (ix, pid')))
        . filter (\ms -> [r] /= usesRefs ms)
        $ cs
    | otherwise = cs
    where
    r :: (ix, Int)
    r = (toEnum n, pid)

  fixManyRefs
    :: (Enum ref, Ord ref)
    => Int -> [Untyped cmd ref] -> [Untyped cmd ref] -> [Untyped cmd ref]
  fixManyRefs _ []       ds = ds
  fixManyRefs n (c : cs) ds = fixManyRefs n cs (fixRefs n c ds)

  fixManyRefsPid
    :: (Enum ix, Ord ix)
    => Int -> Int -> [Untyped cmd (ix, Int)] -> [Untyped cmd (ix, Int)] -> [Untyped cmd (ix, Int)]
  fixManyRefsPid _ _   []       ds = ds
  fixManyRefsPid n pid (c : cs) ds = fixManyRefsPid n pid cs (fixRefsPid n pid c ds)

------------------------------------------------------------------------

ppFork :: Show (cmd ref) => Fork [cmd ref] -> IO ()
ppFork = putStrLn . ppFork'

ppFork' :: Show (cmd ref) => Fork [cmd ref] -> String
ppFork' = show . pretty . fmap (prettyList . map show)

ppForks :: Show (cmd ref) => [Fork [cmd ref]] -> IO ()
ppForks = mapM_ putStrLn . lines . ppForks'

ppForks' :: Show (cmd ref) => [Fork [cmd ref]] -> String
ppForks' = unlines . map (show . pretty . fmap (prettyList . map show))

debugShrink
  :: (Show (Untyped cmd (ix, Int)), RefKit cmd, Ord (Untyped cmd (ix, Int)), Enum ix, Ord ix)
  => (Untyped cmd (ix, Int) -> [Untyped cmd (ix, Int)]) -> Fork [Untyped cmd (ix, Int)] -> IO ()
debugShrink shrinker = mapM_ ppFork . liftShrinkFork shrinker
