{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ScopedTypeVariables       #-}
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
import           Data.Maybe                              (fromJust)
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
import           Unsafe.Coerce

import           Test.QuickCheck.StateMachineModel.Utils

------------------------------------------------------------------------

liftSem
  :: (Monad m, Enum ix, Typeable ref, RefKit (Untyped cmd) ix)
  => (forall resp. cmd resp ref -> m resp)
  -> (forall resp. (Typeable resp, Show resp) => cmd resp ix -> StateT [ref] m resp)
liftSem sem cmd = do

  env <- get
  Untyped cmd' <- return $ fmap (\ix -> env !! fromEnum ix) $ Untyped cmd
  resp <- lift $ sem cmd'

  when (returnsRef (Untyped cmd)) $
    modify (++ [ unsafeCoerce resp ])

  return $ unsafeCoerce resp

------------------------------------------------------------------------

data Untyped f b where
  Untyped :: (Typeable a, Show a) => f a b -> Untyped f b

liftGen
  :: forall cmd ref
  .  RefKit (Untyped cmd) ()
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
  :: RefKit (Untyped cmd) ref
  => (Untyped cmd ref -> [Untyped cmd ref])
  -> ([Untyped cmd ref] -> [[Untyped cmd ref]])
liftShrink shrinker = liftShrink' 0 shrinker

liftShrink'
  :: RefKit (Untyped cmd) ref
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

------------------------------------------------------------------------

data StateMachineModel model cmd ix = StateMachineModel
  { precondition  :: forall resp. model -> cmd resp ix -> Bool
  , postcondition :: forall resp. model -> cmd resp ix -> resp -> Property
  , transition    :: forall resp. model -> cmd resp ix -> resp -> model
  , initialModel  :: model
  }

sequentialProperty
  :: forall m cmd ix ref model
  .  Show (Untyped cmd ix)
  => Monad m
  => RefKit (Untyped cmd) ix
  => RefKit (Untyped cmd) ()
  => Typeable ref
  => StateMachineModel model cmd ix
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
        monadic (runM . flip evalStateT []) $ go initialModel cmds
  where
  go :: model -> [Untyped cmd ix] -> PropertyM (StateT [ref] m) ()
  go _ []           = return ()
  go m (cmd@(Untyped cmd') : cmds) = do
    let s = takeWhile (/= ' ') $ show cmd
    monitor $ label s
    pre $ precondition m cmd'
    resp <- run $ liftSem runCmd cmd'
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
  :: RefKit (Untyped cmd) ()
  => Enum ix
  => [(Int, Gen (Untyped cmd ()))]
  -> Gen (Fork [Untyped cmd ix])
liftGenFork gens = do
  (prefix, n) <- liftGen gens 0
  left        <- fst <$> liftGen gens n
  right       <- fst <$> liftGen gens n
  return $ Fork left prefix right

------------------------------------------------------------------------

liftShrinkFork
  :: forall cmd ix
  .  RefKit (Untyped cmd) ix
  => Ord (Untyped cmd ix)
  => (Untyped cmd ix -> [Untyped cmd ix])
  -> (Fork [Untyped cmd ix] -> [Fork [Untyped cmd ix]])
liftShrinkFork shrinker f@(Fork l0 p0 r0) = Set.toList $ Set.fromList $

  -- Only shrink the branches:
  [ Fork l' p0 r'
  | (l', r') <- shrinkPair (liftShrink' (countRefReturns p0) shrinker) (l0, r0)
  ] ++

  -- Only shrink the prefix:
  shrinkPrefix f

  where
  shrinkPrefix
    :: RefKit (Untyped cmd) ix
    => Fork [Untyped cmd ix] -> [Fork [Untyped cmd ix]]
  shrinkPrefix = go 0
    where
    go _ (Fork _ []       _) = []
    go n (Fork l (p : ps) r) =
      [ Fork l'   []               r'   ] ++
      [ Fork l''  (fixRefs n p ps) r''  ] ++
      [ Fork l''' (p' : ps')       r'''
      | (p', Fork l''' ps' r''') <- shrinkPair' shrinker (go n') (p, Fork l ps r)
      ]
      where
      l'  = fixManyRefs n (p : ps) l
      r'  = fixManyRefs n (p : ps) r

      l'' = fixRefs n p l
      r'' = fixRefs n p r

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

linearise
  :: forall cmd ix model
  .  StateMachineModel model cmd ix
  -> History cmd ix
  -> Property
linearise _                       [] = property True
linearise StateMachineModel {..} xs0 = anyP (step initialModel) . linearTree $ xs0
  where
  step :: model -> Rose (Operation cmd ix) -> Property
  step m (Rose (Operation cmd resp _ _) roses) = postcondition m cmd resp .&&.
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
  .  (RefKit (Untyped cmd) ref)
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
  :: RefKit (Untyped cmd) ix
  => Typeable ref
  => HistoryKit cmd ix
  -> (forall resp. cmd resp ref -> IO resp)
  -> [Untyped cmd ix] -> StateT [ref] IO ()
runMany kit step = flip foldM () $ \_ cmd'@(Untyped cmd) -> do
  lift $ atomically $ writeTChan (getHistoryChannel kit) $
    InvocationEvent cmd' (getProcessIdHistory kit)
  resp <- liftSem step cmd
  lift $ do
    threadDelay =<< randomRIO (0, 20)
    atomically $ writeTChan (getHistoryChannel kit) $
      ResponseEvent (toDyn resp) (getProcessIdHistory kit)

parallelProperty
  :: forall cmd ix ref model
  .  (Ord (Untyped cmd ix), Show (Untyped cmd ix))
  => Show ix
  => Typeable ref
  => RefKit (Untyped cmd) ix
  => RefKit (Untyped cmd) ()
  => StateMachineModel model cmd ix
  -> [(Int, Gen (Untyped cmd ()))]
  -> (Untyped cmd ix -> [Untyped cmd ix])
  -> (forall resp. cmd resp ref -> IO resp)
  -> Property
parallelProperty smm gen shrinker runStep
  = forAllShrinkShow (liftGenFork gen) (liftShrinkFork shrinker) show
  $ monadicIO
  . \(Fork left prefix right) -> do
      replicateM_ 10 $ do
        kit <- run $ mkHistoryKit 0
        env <- run $ execStateT (runMany kit runStep prefix) []
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

class (Functor cmd, Foldable cmd, Enum ref, Ord ref) => RefKit cmd ref where

  returnsRef :: cmd ref -> Bool

  usesRefs :: cmd ref -> [ref]
  usesRefs = toList

  countRefReturns :: [cmd ref] -> Int
  countRefReturns = length . filter returnsRef

  fixRefs :: Int -> cmd ref -> [cmd ref] -> [cmd ref]
  fixRefs n c cs
    | returnsRef c
        = map (fmap (\ref -> if r < ref then toEnum (fromEnum ref - 1) else ref))
        . filter (\ms -> [r] /= usesRefs ms)
        $ cs
    | otherwise = cs
    where
    r = toEnum n

  fixManyRefs :: Int -> [cmd ref] -> [cmd ref] -> [cmd ref]
  fixManyRefs _ []       ds = ds
  fixManyRefs n (c : cs) ds = fixManyRefs n cs (fixRefs n c ds)

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
  :: (Show (Untyped cmd ref), RefKit (Untyped cmd) ref, Ord (Untyped cmd ref))
  => (Untyped cmd ref -> [Untyped cmd ref]) -> Fork [Untyped cmd ref] -> IO ()
debugShrink shrinker = mapM_ ppFork . liftShrinkFork shrinker
