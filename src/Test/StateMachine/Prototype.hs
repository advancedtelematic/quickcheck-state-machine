{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}

module Test.StateMachine.Prototype where

import           Control.Concurrent
                   (threadDelay)
import           Control.Concurrent.ParallelIO.Local
                   (parallel_, withPool)
import           Control.Concurrent.STM
import           Control.Monad.Identity
import           Control.Monad.State
                   (StateT, evalStateT, execStateT, get, lift, modify)
import           Data.Dynamic
import           Data.Functor.Classes
                   (Eq1(..), Ord1(..), Show1(..), showsPrec1)
import           Data.Functor.Const (Const(..))
import           Data.IORef
import           Data.List
                   (partition)
import           Data.Map
                   (Map)
import qualified Data.Map                            as M
import           Data.Set
                   (Set)
import qualified Data.Set                            as Set
import           Data.Tree
import           System.Random
                   (randomRIO)
import           Text.PrettyPrint.ANSI.Leijen
                   (Doc)
import           Test.QuickCheck
import           Test.QuickCheck.Monadic

import           Test.StateMachine.Internal.Utils.BoxDrawer
import qualified Test.StateMachine.Internal.Types as INTERNAL

------------------------------------------------------------------------

-- Stuff taken from Hedgehog.

newtype Opaque a = Opaque
  { unOpaque :: a
  } deriving (Eq, Ord)

instance Show (Opaque a) where
  showsPrec _ (Opaque _) = showString "Opaque"

newtype Var =
  Var Int
  deriving (Eq, Ord, Show, Num)

data Symbolic a where
  Symbolic :: Typeable a => Var -> Symbolic a

deriving instance Eq  (Symbolic a)
deriving instance Ord (Symbolic a)

instance Show (Symbolic a) where
  showsPrec p (Symbolic x) = showsPrec p x

instance Show1 Symbolic where
  liftShowsPrec _ _ p (Symbolic x) = showsPrec p x

instance Eq1 Symbolic where
  liftEq _ (Symbolic x) (Symbolic y) = x == y

instance Ord1 Symbolic where
  liftCompare _ (Symbolic x) (Symbolic y) = compare x y

newtype ShowSymbolic a = ShowSymbolic Var

instance Show1 ShowSymbolic where
  liftShowsPrec _ _ p (ShowSymbolic (Var i)) _ = "$" ++ show i

newtype Concrete a where
  Concrete :: a -> Concrete a
  deriving (Eq, Ord, Functor, Foldable, Traversable)

instance Show a => Show (Concrete a) where
  showsPrec = showsPrec1

instance Show1 Concrete where
  liftShowsPrec sp _ p (Concrete x) = sp p x

instance Eq1 Concrete where
  liftEq eq (Concrete x) (Concrete y) = eq x y

instance Ord1 Concrete where
  liftCompare comp (Concrete x) (Concrete y) = comp x y

class HFunctor t => HFoldable (t :: (* -> *) -> * -> *) where
  hfoldMap :: Monoid m => (forall a. v a -> m) -> t v b -> m

  default hfoldMap :: (HTraversable t, Monoid m) => (forall a. v a -> m) -> t v b -> m
  hfoldMap f = getConst . htraverse (Const . f)

class (HFunctor t, HFoldable t) => HTraversable (t :: (* -> *) -> * -> *) where
  htraverse :: Applicative f => (forall a. g a -> f (h a)) -> t g b -> f (t h b)

data ShowResponse resp = ShowResponse
  { theAction :: String
  , showVar   :: Bool
  , showResp  :: resp -> String
  }

class ShowAction (act :: (* -> *) -> * -> *) where
  showAction :: Show1 v => act v resp -> ShowResponse resp

newtype Environment =
  Environment {
      unEnvironment :: Map Var Dynamic
    } deriving (Show)

-- | Environment errors.
--
data EnvironmentError =
    EnvironmentValueNotFound !Var
  | EnvironmentTypeError !TypeRep !TypeRep
    deriving (Eq, Ord, Show)

-- | Create an empty environment.
--
emptyEnvironment :: Environment
emptyEnvironment =
  Environment M.empty

-- | Insert a symbolic / concrete pairing in to the environment.
--
insertConcrete :: Symbolic a -> Concrete a -> Environment -> Environment
insertConcrete (Symbolic k) (Concrete v) =
  Environment . M.insert k (toDyn v) . unEnvironment

-- | Cast a 'Dynamic' in to a concrete value.
--
reifyDynamic :: forall a. Typeable a => Dynamic -> Either EnvironmentError (Concrete a)
reifyDynamic dyn =
  case fromDynamic dyn of
    Nothing ->
      Left $ EnvironmentTypeError (typeRep (Proxy :: Proxy a)) (dynTypeRep dyn)
    Just x ->
      Right $ Concrete x

-- | Turns an environment in to a function for looking up a concrete value from
--   a symbolic one.
--
reifyEnvironment :: Environment -> (forall a. Symbolic a -> Either EnvironmentError (Concrete a))
reifyEnvironment (Environment vars) (Symbolic n) =
  case M.lookup n vars of
    Nothing ->
      Left $ EnvironmentValueNotFound n
    Just dyn ->
      reifyDynamic dyn

reify :: HTraversable t => Environment -> t Symbolic b -> Either EnvironmentError (t Concrete b)
reify vars =
  htraverse (reifyEnvironment vars)

------------------------------------------------------------------------

type Untyped act = Untyped' act Symbolic

data Untyped' (act :: (* -> *) -> * -> *) (v :: * -> *) where
  Untyped :: (Typeable resp, Show resp) => act v resp -> Untyped' act v

data Internal (act :: (* -> *) -> * -> *) where
  Internal :: (Typeable resp, Show resp) => act Symbolic resp -> Symbolic resp -> Internal act

liftProperty :: Monad m => Property -> PropertyM m ()
liftProperty prop = MkPropertyM (\k -> fmap (prop .&&.) <$> k ())

class HFunctor (f :: (* -> *) -> * -> *) where
  hfmap :: (forall a. g a -> h a) -> f g b -> f h b

  default hfmap :: HTraversable f => (forall a. g a -> h a) -> f g b -> f h b
  hfmap f = runIdentity . htraverse (Identity . f)

------------------------------------------------------------------------

type Generator model act = model Symbolic -> Gen (Untyped act)

type Precondition model act = forall resp.
  model Symbolic -> act Symbolic resp -> Bool

type Transition model act = forall resp v. Ord1 v =>
  model v -> act v resp -> v resp -> model v

type Postcondition model act = forall resp.
  model Concrete -> act Concrete resp -> resp -> Property

------------------------------------------------------------------------

data Ref v = Ref (v (Opaque (IORef Int)))

unRef :: Ref Concrete -> IORef Int
unRef (Ref (Concrete (Opaque ref))) = ref

instance Eq1 v => Eq (Ref v) where
  Ref v1 == Ref v2 = liftEq (==) v1 v2

instance Show1 v => Show (Ref v) where
  show (Ref v) = showsPrec1 10 v ""

data Action (v :: * -> *) :: * -> * where
  New   ::          Action v (Opaque (IORef Int))
  Read  :: Ref v -> Action v Int
  Write :: Ref v -> Int -> Action v ()
  Inc   :: Ref v -> Action v ()

instance Show (Internal Action) where
  show (Internal New           r) = show r ++ " <- New"
  show (Internal (Read  ref)   _) = "Read ("  ++ show ref ++ ")"
  show (Internal (Write ref i) _) = "Write (" ++ show ref ++ ") " ++ show i
  show (Internal (Inc   ref)   _) = "Inc ("   ++ show ref ++ ")"

instance ShowAction Action where
  showAction New           = ShowResponse "New"                                   True  show
  showAction (Read ref)    = ShowResponse ("Read " ++ show ref)                   False show
  showAction (Write ref i) = ShowResponse ("Write " ++ show ref ++ " " ++ show i) False show
  showAction (Inc ref)     = ShowResponse ("Inc " ++ show ref)                    False show

instance HFunctor Action
instance HFoldable Action

instance HTraversable Action where
  htraverse _ New                 = pure New
  htraverse f (Read  (Ref ref))   = Read  . Ref <$> f ref
  htraverse f (Write (Ref ref) i) = Write . Ref <$> f ref <*> pure i
  htraverse f (Inc   (Ref ref))   = Inc   . Ref <$> f ref

newtype Model v = Model [(Ref v, Int)]

initModel :: Model v
initModel = Model []

generator :: Generator Model Action
generator (Model m)
  | null m    = pure (Untyped New)
  | otherwise = frequency
      [ (1, pure (Untyped New))
      , (8, Untyped .    Read  <$> elements (map fst m))
      , (8, Untyped <$> (Write <$> elements (map fst m) <*> arbitrary))
      , (8, Untyped .    Inc   <$> elements (map fst m))
      ]

shrink1 :: Action v resp -> [Action v resp]
shrink1 _ = []

semantics :: Action Concrete resp -> IO resp
semantics New           = Opaque <$> newIORef 0
semantics (Read  ref)   = readIORef  (unRef ref)
semantics (Write ref i) = writeIORef (unRef ref) i
semantics (Inc   ref)   = do
  v <- readIORef (unRef ref)
  threadDelay 100
  writeIORef (unRef ref) (v + 1)

precondition :: Precondition Model Action
precondition _         New           = True
precondition (Model m) (Read  ref)   = ref `elem` map fst m
precondition (Model m) (Write ref _) = ref `elem` map fst m
precondition (Model m) (Inc   ref)   = ref `elem` map fst m

transition :: Transition Model Action
transition (Model m) New           ref = Model (m ++ [(Ref ref, 0)])
transition m         (Read  _)     _   = m
transition (Model m) (Write ref i) _   = Model ((ref, i) : filter ((/= ref) . fst) m)
transition (Model m) (Inc   ref)   _   = Model ((ref, old + 1) : filter ((/= ref) . fst) m)
  where
  Just old = lookup ref m

postcondition :: Postcondition Model Action
postcondition _         New         _    = property True
postcondition (Model m) (Read ref)  resp = lookup ref m === Just resp
postcondition _         (Write _ _) _    = property True
postcondition _         (Inc _)     _    = property True

------------------------------------------------------------------------

liftGen
  :: forall model act
  .  Generator model act
  -> model Symbolic
  -> Precondition model act
  -> Transition model act
  -> Gen [Internal act]
liftGen gen model pre next
   =  (\(acts, _, _) -> acts)
  <$> liftGen' gen pre next model 0

liftGen'
  :: forall model act
  .  Generator model act
  -> Precondition model act
  -> Transition model act
  -> model Symbolic
  -> Int
  -> Gen ([Internal act], model Symbolic, Int)
liftGen' gen pre next model0 n = sized $ \size -> go size n model0
  where
  go :: Int -> Int -> model Symbolic -> Gen ([Internal act], model Symbolic, Int)
  go 0  i model = return ([], model, i)
  go sz i model = do
    Untyped act <- gen model `suchThat` \(Untyped act) -> pre model act
    let sym = Symbolic (Var i)
    (acts, model', j) <- go (sz - 1) (i + 1) (next model act sym)
    return (Internal act sym : acts, model', j + 1)

liftShrinkInternal
  :: (forall v resp. act v resp -> [act v resp])
  -> Internal act -> [Internal act]
liftShrinkInternal shrinker (Internal act sym) =
  [ Internal act' sym | act' <- shrinker act ]

liftShrink
  :: HFoldable act
  => (forall v resp. act v resp -> [act v resp])
  -> Precondition model act
  -> Transition model act
  -> model Symbolic
  -> [Internal act]
  -> [[Internal act]]
liftShrink oldShrink pre trans model = map (snd . filterInvalid pre trans model Set.empty) . shrinkList (liftShrinkInternal oldShrink)

getUsedVars
  :: HFoldable act
  => act Symbolic a -> Set Var
getUsedVars = hfoldMap (\(Symbolic v) -> Set.singleton v)

filterInvalid
  :: HFoldable act
  => Precondition model act
  -> Transition model act
  -> model Symbolic
  -> Set Var
  -> [Internal act] -> ((model Symbolic, Set Var), [Internal act])
filterInvalid pre trans = go
 where
   go m known [] = ((m, known), [])
   go m known (x@(Internal act sym@(Symbolic var)) : xs)
     | getUsedVars act `Set.isSubsetOf` known && pre m act =
         fmap (x :) $ go (trans m act sym) (Set.insert var known) xs
     | otherwise = go m known xs

liftModel
  :: Monad m
  => HFunctor act
  => model Symbolic
  -> model Concrete
  -> [Internal act]
  -> Precondition model act
  -> (forall resp. act Concrete resp -> m resp) -- ^ Semantics
  -> Transition model act
  -> Postcondition model act
  -> PropertyM (StateT Environment m) ()
liftModel _ _  []                        _       _   _     _        = return ()
liftModel m m' (Internal act sym : acts) precond sem trans postcond = do
  pre (precond m act)
  env <- run get
  let act' = hfmap (fromSymbolic env) act
  resp <- run (lift (sem act'))
  liftProperty (postcond m' act' resp)
  run (modify (insertConcrete sym (Concrete resp)))
  liftModel
    (trans m  act sym)
    (trans m' act' (Concrete resp))
    acts precond sem trans postcond

fromSymbolic :: Environment -> Symbolic v ->  Concrete v
fromSymbolic env sym = case reifyEnvironment env sym of
  Left  err -> error (show err)
  Right con -> con

------------------------------------------------------------------------

sequentialProperty
  :: Monad m
  => Show (Internal act)
  => HFunctor act
  => HFoldable act
  => Generator model act
  -> (forall resp v. act v resp -> [act v resp])   -- ^ Shrinker
  -> Precondition model act
  -> Transition    model act
  -> Postcondition model act
  -> (forall v. model v)                           -- ^ Initial model
  -> (forall resp. act Concrete resp -> m resp)    -- ^ Semantics
  -> (m Property -> Property)                      -- ^ Runner
  -> Property
sequentialProperty gen shrinker precond trans postcond m sem runner =
  forAllShrink
  (liftGen gen m precond trans)
  (liftShrink shrinker precond trans m)
  $ \acts -> do
    monadic (runner . flip evalStateT emptyEnvironment)
      (liftModel m m acts precond sem trans postcond)

prop_references :: Property
prop_references = sequentialProperty generator shrink1 precondition
  transition postcondition initModel semantics ioProperty

------------------------------------------------------------------------

parallelProperty
  :: ShowAction act
  => Show (Internal act) -- used by the forAllShrink
  => HTraversable act
  => Generator model act
  -> (forall resp v. act v resp -> [act v resp])          -- ^ Shrinker
  -> Precondition  model act
  -> Transition    model act
  -> Postcondition model act
  -> (forall v. model v)                                  -- ^ Initial model
  -> (forall resp. act Concrete resp -> IO resp)          -- ^ Semantics
  -> Property
parallelProperty gen shrinker precond trans postcond initial sem =
  forAllShrink
    (liftGenFork gen precond trans initial)
    (liftShrinkFork shrinker precond trans initial) $ \fork -> monadicIO $ do
      replicateM_ 10 $ do
        hist <- run $ liftSemFork sem fork
        checkParallelInvariant precond trans postcond initial hist

prop_parallelReferences :: Property
prop_parallelReferences = parallelProperty generator shrink1 precondition
  transition postcondition initModel semantics

------------------------------------------------------------------------

data Fork a = Fork a a a
  deriving Show

type History act = [HistoryEvent (Untyped' act Concrete)]

newtype Pid = Pid Int
  deriving Eq

data HistoryEvent act
  = InvocationEvent act     String Pid
  | ResponseEvent   Dynamic String Pid

getProcessIdEvent :: HistoryEvent act -> Pid
getProcessIdEvent (InvocationEvent _ _ pid) = pid
getProcessIdEvent (ResponseEvent   _ _ pid) = pid

data Operation act = forall resp. Typeable resp =>
  Operation (act Concrete resp) String (Concrete resp) Pid

takeInvocations :: [HistoryEvent a] -> [HistoryEvent a]
takeInvocations = takeWhile $ \h -> case h of
  InvocationEvent _ _ _ -> True
  _                     -> False

findCorrespondingResp :: Pid -> History act -> [(Dynamic, History act)]
findCorrespondingResp _   [] = []
findCorrespondingResp pid (ResponseEvent resp _ pid' : es) | pid == pid' = [(resp, es)]
findCorrespondingResp pid (e : es) =
  [ (resp, e : es') | (resp, es') <- findCorrespondingResp pid es ]

linearTree :: History act -> [Tree (Operation act)]
linearTree [] = []
linearTree es =
  [ Node (Operation act str (dynResp resp) pid) (linearTree es')
  | InvocationEvent (Untyped act) str pid <- takeInvocations es
  , (resp, es')  <- findCorrespondingResp pid $ filter1 (not . matchInv pid) es
  ]
  where
  dynResp resp = either (error . show) id (reifyDynamic resp)

  filter1 :: (a -> Bool) -> [a] -> [a]
  filter1 _ []                   = []
  filter1 p (x : xs) | p x       = x : filter1 p xs
                     | otherwise = xs

  -- Hmm, is this enough?
  matchInv pid (InvocationEvent _ _ pid') = pid == pid'
  matchInv _   _                          = False

linearise
  :: forall model act
  .  Transition    model act
  -> Postcondition model act
  -> (forall v. model v)
  -> History act
  -> Property
linearise _    _    _    [] = property True
linearise next post init es = anyP (step init) . linearTree $ es
  where
  step :: model Concrete -> Tree (Operation act) -> Property
  step m (Node (Operation act _ resp@(Concrete resp') _) roses) =
    post m act resp' .&&.
    anyP' (step (next m act resp)) roses
    where
    anyP' :: (a -> Property) -> [a] -> Property
    anyP' _ [] = property True
    anyP' p xs = anyP p xs

anyP :: (a -> Property) -> [a] -> Property
anyP p = foldr (\x ih -> p x .||. ih) (property False)

toBoxDrawings :: History act -> Doc
toBoxDrawings h = exec evT (fmap (fmap out) $ INTERNAL.Fork l p r)
  where
    (p, h') = partition (\e -> getProcessIdEvent e == Pid 0) h
    (l, r)  = partition (\e -> getProcessIdEvent e == Pid 1) h'

    out :: HistoryEvent act -> String
    out (InvocationEvent _ str pid) = str
    out (ResponseEvent _ str pid)   = str

    toEventType :: History cmd -> [(EventType, INTERNAL.Pid)]
    toEventType = map $ \e -> case e of
      InvocationEvent _ _ (Pid pid) -> (Open, INTERNAL.Pid pid)
      ResponseEvent _ _ (Pid pid)   -> (Close, INTERNAL.Pid pid)
    evT :: [(EventType, INTERNAL.Pid)]
    evT = toEventType (filter (\e -> getProcessIdEvent e `elem` map Pid [1,2]) h)

------------------------------------------------------------------------

liftGenFork
  :: Generator    model act
  -> Precondition model act
  -> Transition   model act
  -> model Symbolic
  -> Gen (Fork [Internal act])
liftGenFork gen pre next model = do
  (prefix, model', m) <- liftGen' gen pre next model  0
  (left,   _,      n) <- liftGen' gen pre next model' m
  (right,  _,      _) <- liftGen' gen pre next model' n
  return (Fork left prefix right)

forkFilterInvalid
  :: HFoldable act
  => Precondition model act
  -> Transition model act
  -> model Symbolic
  -> Fork [Internal act]
  -> Fork [Internal act]
forkFilterInvalid pre trans m (Fork l p r) =
  Fork (snd $ filterInvalid pre trans m' vars l)
       p'
       (snd $ filterInvalid pre trans m' vars r)
  where
    ((m', vars), p') = filterInvalid pre trans m Set.empty p

shrinkPair
  :: (a -> [a])
  -> (b -> [b])
  -> ((a, b) -> [(a, b)])
shrinkPair shrinkA shrinkB (a, b) =
     [ (a', b) | a' <- shrinkA a ]
  ++ [ (a, b') | b' <- shrinkB b ]

liftShrinkFork
  :: HFoldable act
  => (forall v resp. act v resp -> [act v resp])
  -> Precondition model act
  -> Transition model act
  -> model Symbolic
  -> (Fork [Internal act] -> [Fork [Internal act]])
liftShrinkFork oldShrink pre trans model (Fork l p r) =
  map (forkFilterInvalid pre trans model)
  [ Fork l' p' r' | (p', (l', r')) <- shrinkPair shrinkSub (shrinkPair shrinkSub shrinkSub) (p, (l, r))]
  where
    shrinkSub = shrinkList (liftShrinkInternal oldShrink)

liftSemFork
  :: HTraversable act
  => ShowAction act
  => (forall resp. act Concrete resp -> IO resp)
  -> Fork [Internal act]
  -> IO (History act)
liftSemFork sem (Fork left prefix right) = do
  hchan <- newTChanIO
  env   <- execStateT (runMany sem hchan (Pid 0) prefix) emptyEnvironment
  withPool 2 $ \pool ->
    parallel_ pool
      [ evalStateT (runMany sem hchan (Pid 1) left)  env
      , evalStateT (runMany sem hchan (Pid 2) right) env
      ]
  getChanContents hchan
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

runMany
  :: HTraversable act
  => ShowAction act
  => (forall resp. act Concrete resp -> IO resp)
  -> TChan (HistoryEvent (Untyped' act Concrete))
  -> Pid
  -> [Internal act]
  -> StateT Environment IO ()
runMany sem hchan pid = flip foldM () $ \_ (Internal act sym@(Symbolic (Var var))) -> do
  env <- get
  let showAct = showAction $ hfmap (\(Symbolic v) -> ShowSymbolic v) act
  let invStr | showVar showAct = "$" ++ show var ++ " ← " ++ theAction showAct
             | otherwise       = theAction showAct
  let cact = case reify env act of
        Left  err  -> error (show err)
        Right cact -> cact
  lift $ atomically $ writeTChan hchan $ InvocationEvent (Untyped cact) invStr pid
  resp <- lift (sem cact)
  modify (insertConcrete sym (Concrete resp))
  lift $ do
    threadDelay =<< randomRIO (0, 20)
    atomically $ writeTChan hchan $ ResponseEvent (toDyn resp) (showResp showAct resp) pid

checkParallelInvariant
  :: Precondition  model act
  -> Transition    model act
  -> Postcondition model act
  -> (forall v. model v)
  -> History act
  -> PropertyM IO ()
checkParallelInvariant pre next post initial hist
  = liftProperty
  . counterexample ("Couldn't linearise:\n\n" ++ show (toBoxDrawings hist))
  $ linearise next post initial hist

instance Show (HistoryEvent (Untyped' act Concrete)) where
  show (InvocationEvent _ str _) = str
  show (ResponseEvent   _ str _) = str
