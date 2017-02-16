{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RecordWildCards        #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module Test.QuickCheck.StateMachineModel where

import           Control.Concurrent                  (threadDelay)
import           Control.Concurrent.ParallelIO.Local (parallel_, withPool)
import           Control.Concurrent.STM.TChan        (TChan, newTChanIO,
                                                      tryReadTChan, writeTChan)
import           Control.Monad.State
import           Control.Monad.STM                   (STM, atomically)
import           Data.Char                           (toLower)
import           Data.Foldable                       (toList)
import           Data.List                           (partition)
import           Data.Monoid                         ((<>))
import qualified Data.Set                            as Set
import           System.Random                       (randomRIO)
import           Test.QuickCheck
import           Test.QuickCheck.Monadic
import           Test.QuickCheck.Property            (Property (..))
import           Text.PrettyPrint.ANSI.Leijen        (Pretty, align, dot,
                                                      indent, int, pretty,
                                                      prettyList, text,
                                                      underline, vsep, (<+>))

------------------------------------------------------------------------

forAllShrinkShow
  :: Testable prop
  => Gen a -> (a -> [a]) -> (a -> String) -> (a -> prop) -> Property
forAllShrinkShow gen shrinker shower pf =
  again $
  MkProperty $
  gen >>= \x ->
    unProperty $
    shrinking shrinker x $ \x' ->
      counterexample (shower x') (pf x')

assert' :: Monad m => String -> Bool -> PropertyM m ()
assert' _   True  = return ()
assert' msg False = fail msg

------------------------------------------------------------------------

liftSem
  :: (MonadState [ref] m, RefKit cmd ref')
  => (cmd ref -> m resp)
  -> (resp -> Maybe ref)
  -> (cmd ref' -> m resp)
liftSem sem isRef cmd
  | returnsRef cmd = do
      env <- get
      resp <- sem (fmap (\ref -> env !! fromEnum ref) cmd)
      case isRef resp of
        Nothing  -> error "liftSem: response wasn't a ref."
        Just ref -> do
          modify (++ [ref])
          return resp
  | otherwise      = do
      env <- get
      sem (fmap (\ref -> env !! fromEnum ref) cmd)

------------------------------------------------------------------------

liftGen
  :: forall cmd ref
  .  RefKit cmd ()
  => Enum ref
  => [(Int, Gen (cmd ()))] -> Int -> Gen ([cmd ref], Int)
liftGen gens n = sized $ \sz -> runStateT (go sz) n
  where
  go :: Int -> StateT Int Gen [cmd ref]
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
        return $ fmap undefined cmd : ih
      else go sz
    else do
      when (returnsRef cmd) $
        modify succ
      ih <- go (sz - 1)
      if null $ usesRefs cmd
      then
        return $ fmap undefined cmd : ih
      else do
        ref <- toEnum <$> lift (choose (0, scope - 1))
        return $ fmap (const ref) cmd : ih

------------------------------------------------------------------------

liftShrink
  :: RefKit cmd ref
  => (cmd ref -> [cmd ref]) -> [cmd ref] -> [[cmd ref]]
liftShrink shrinker = liftShrink' 0 shrinker

liftShrink'
  :: RefKit cmd ref
  => Int -> (cmd ref -> [cmd ref]) -> [cmd ref] -> [[cmd ref]]
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

monadicOur :: env -> PropertyM (StateT env IO) () -> Property
monadicOur env0 = monadic $ ioProperty . flip evalStateT env0

data StateMachineModel model cmd resp = StateMachineModel
  { precondition  :: model -> cmd -> Bool
  , postcondition :: model -> cmd -> resp -> Bool
  , transition    :: model -> cmd -> resp -> model
  , initialModel  :: model
  }

sequentialProperty
  :: forall cmd ref ref' model resp
  .  Show (cmd ref)
  => RefKit cmd ref
  => RefKit cmd ()
  => StateMachineModel model (cmd ref) resp
  -> [(Int, Gen (cmd ()))]
  -> (cmd ref -> [cmd ref])
  -> ([cmd ref] -> String)
  -> (cmd ref' -> StateT [ref'] IO resp)
  -> (resp -> Maybe ref')
  -> Property
sequentialProperty StateMachineModel {..} gens shrinker shower runCmd isRef =
  forAllShrinkShow
    (fst <$> liftGen gens 0)
    (liftShrink shrinker)
    shower $
    monadicOur [] . go initialModel
  where
  go :: model -> [cmd ref] -> PropertyM (StateT [ref'] IO) ()
  go _ []           = return ()
  go m (cmd : cmds) = do
    let s = map toLower $ takeWhile (/= ' ') $ show cmd
    monitor $ collect s
    pre $ precondition m cmd
    resp <- run $ runCmd' cmd
    assert' ("`" ++ s ++ "_post'") (postcondition m cmd resp)
    go (transition m cmd resp) cmds
    where
    runCmd' = liftSem runCmd isRef

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
  :: RefKit cmd ()
  => Enum ref
  => [(Int, Gen (cmd ()))] -> Gen (Fork [cmd ref])
liftGenFork gens = do
  (prefix, n) <- liftGen gens 0
  left        <- fst <$> liftGen gens n
  right       <- fst <$> liftGen gens n
  return $ Fork left prefix right

------------------------------------------------------------------------

liftShrinkFork
  :: forall cmd ref
  .  (RefKit cmd ref, Ord (cmd ref))
  => (cmd ref -> [cmd ref]) -> Fork [cmd ref] -> [Fork [cmd ref]]
liftShrinkFork shrinker f@(Fork l0 p0 r0) = Set.toList $ Set.fromList $

  -- Only shrink the branches:
  [ Fork l' p0 r'
  | (l', r') <- shrinkPair (liftShrink' (countRefReturns p0) shrinker) (l0, r0)
  ] ++

  -- Only shrink the prefix:
  shrinkPrefix f

  where
  shrinkPrefix
    :: RefKit cmd ref
    => Fork [cmd ref] -> [Fork [cmd ref]]
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

shrinkPair :: (a -> [a]) -> (a, a) -> [(a, a)]
shrinkPair shrinker = shrinkPair' shrinker shrinker

shrinkPair' :: (a -> [a]) -> (b -> [b]) -> (a, b) -> [(a, b)]
shrinkPair' shrinkerA shrinkerB (x, y) =
  [ (x', y) | x' <- shrinkerA x ] ++
  [ (x, y') | y' <- shrinkerB y ]

------------------------------------------------------------------------

type History cmd resp = [HistoryEvent cmd resp]

data HistoryEvent cmd resp
  = InvocationEvent { invocation   :: cmd
                    , getProcessId :: Int
                    }
  | ResponseEvent   { response     :: resp
                    , getProcessId :: Int
                    }
  deriving (Eq, Show, Read)

data Rose a = Rose a [Rose a]
  deriving Show

fromRose :: Rose a -> [a]
fromRose (Rose x xs) = x : concatMap fromRose xs

takeInvocations :: History cmd resp -> [HistoryEvent cmd resp]
takeInvocations = takeWhile $ \h -> case h of
  InvocationEvent _ _ -> True
  _                   -> False

findCorrespondingResp :: Int -> History cmd resp -> [(resp, History cmd resp)]
findCorrespondingResp _   [] = []
findCorrespondingResp pid (ResponseEvent r pid' : es) | pid == pid' = [(r, es)]
findCorrespondingResp pid (e : es) =
  [ (res, e : es') | (res, es') <- findCorrespondingResp pid es ]

data Operation cmd resp = Operation cmd resp Int
  deriving Show

linearTree :: (Eq cmd, Eq resp) => History cmd resp -> [Rose (Operation cmd resp)]
linearTree [] = []
linearTree es =
  [ Rose (Operation cmd resp pid) (linearTree es')
  | e@(InvocationEvent cmd pid) <- takeInvocations es
  , (resp, es')  <- findCorrespondingResp pid $ filter1 (/= e) es
  ]
  where
  filter1 :: (a -> Bool) -> [a] -> [a]
  filter1 _ []                   = []
  filter1 p (x : xs) | p x       = x : filter1 p xs
                     | otherwise = xs

linearise
  :: forall cmd resp model
  .  Eq cmd
  => Eq resp
  => model
  -> (model -> cmd -> resp -> Maybe model)
  -> History cmd resp
  -> [[Operation cmd resp]]
linearise m0 postNext = map fromRose . filter (postConditionsHold m0) . linearTree
  where
  postConditionsHold :: model -> Rose (Operation cmd resp) -> Bool
  postConditionsHold m (Rose (Operation cmd resp _) roses) = case postNext m cmd resp of
    Nothing -> False
    Just m' -> any' (postConditionsHold m') roses
    where
    any' :: (a -> Bool) -> [a] -> Bool
    any' _ [] = True
    any' p xs = any p xs

------------------------------------------------------------------------

instance (Show cmd, Show resp) => Pretty (Operation cmd resp) where
  pretty (Operation cmd resp _) = text (show cmd) <+> text "-->" <+> text (show resp)
  prettyList                    = vsep . map pretty

toForkOfOps :: (Eq cmd, Eq resp) => History cmd resp -> Fork [Operation cmd resp]
toForkOfOps h = Fork (mkOps l) (mkOps p) (mkOps r)
  where
  (p, h') = partition (\e -> getProcessId e == 0) h
  (l, r)  = partition (\e -> getProcessId e == 1) h'

  mkOps :: [HistoryEvent cmd resp] -> [Operation cmd resp]
  mkOps [] = []
  mkOps (InvocationEvent cmd _ : ResponseEvent resp pid : es)
    = Operation cmd resp pid : mkOps es
  mkOps _ = error "mkOps: Impossible."

------------------------------------------------------------------------

data HistoryKit cmd resp = HistoryKit
  { getHistoryChannel :: TChan (HistoryEvent cmd resp)
  , getProcessId'     :: Int
  }

mkHistoryKit :: Int -> IO (HistoryKit cmd resp)
mkHistoryKit pid = do
  chan <- newTChanIO
  return $ HistoryKit chan pid

runMany
  :: HistoryKit cmd resp
  -> env
  -> (cmd -> StateT env IO resp)
  -> [cmd]
  -> IO env
runMany _   env _    []           = return env
runMany kit env step (cmd : cmds) = do
  atomically $ writeTChan (getHistoryChannel kit) $
    InvocationEvent cmd (getProcessId' kit)
  (resp, env') <- runStateT (step cmd) env
  threadDelay =<< randomRIO (0, 20)
  atomically $ writeTChan (getHistoryChannel kit) $
    ResponseEvent  resp (getProcessId' kit)
  runMany kit env' step cmds

parallelProperty
  :: forall cmd ref ref' resp model
  .  (Ord (cmd ref), Show (cmd ref))
  => (Eq resp, Show resp)
  => RefKit cmd ref
  => RefKit cmd ()
  => (model -> cmd ref -> resp -> Maybe model)
  -> model
  -> [(Int, Gen (cmd ()))]
  -> (cmd ref -> [cmd ref])
  -> (cmd ref' -> StateT [ref'] IO resp)
  -> (resp -> Maybe ref')
  -> Property
parallelProperty postNext m0 gen shrinker runStep isRef
  = forAllShrinkShow (liftGenFork gen) (liftShrinkFork shrinker) show
  $ monadicIO
  . \(Fork left prefix right) -> do
      pre $ scopeCheck $ prefix <> left
      pre $ scopeCheck $ prefix <> right
      replicateM_ 10 $ do
        kit <- run $ mkHistoryKit 0
        e <- run $ runMany kit [] runStep' prefix
        run $ withPool 2 $ \pool -> do
          parallel_ pool [ runMany (kit { getProcessId' = 1}) e runStep' left
                         , runMany (kit { getProcessId' = 2}) e runStep' right
                         ]

        hist <- run $ getChanContents $ getHistoryChannel kit

        if null hist
        then return ()
        else do
          let lin = linearise m0 postNext hist
          when (null lin) $ do
            monitor $ counterexample $ show $ pretty $ toForkOfOps hist
          assert' "Couldn't linearise" $ not $ null lin
  where
  runStep' :: cmd ref -> StateT [ref'] IO resp
  runStep' = liftSem runStep isRef

  getChanContents :: forall a. TChan a -> IO [a]
  getChanContents chan = do
    xs <- atomically $ go []
    return $ reverse xs
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

  scopeCheck :: [cmd ref] -> Bool
  scopeCheck = go 0
    where
    go _ []       = True
    go s (c : cs) = all (\r -> r < toEnum s) (usesRefs c) &&
      go (if returnsRef c then s + 1 else s) cs

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
  :: (Show (cmd ref), RefKit cmd ref, Ord (cmd ref))
  => (cmd ref -> [cmd ref]) -> Fork [cmd ref] -> IO ()
debugShrink shrinker = mapM_ ppFork . liftShrinkFork shrinker
