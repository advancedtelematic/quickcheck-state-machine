{-# OPTIONS_GHC -fno-warn-orphans  #-}

{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ProcessRegistry
-- Copyright   :  (C) 2017, Jacob Stanley; 2018, Stevan Andjelkovic
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan.andjelkovic@here.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains the process registry example that is commonly
-- used in the papers on Erlang QuickCheck, e.g. "Finding Race
-- Conditions in Erlang with QuickCheck and PULSE". Parts of the code
-- are stolen from an example in Hedgehog.
--
-----------------------------------------------------------------------------

module ProcessRegistry
  ( prop_processRegistry
  , markovGood
  , markovDeadlock
  , markovNotStochastic1
  , markovNotStochastic2
  , markovNotStochastic3
  , sm
  , initFiniteModel
  , printStaticStats
  , printStats
  )
  where

import           Control.Exception
                   (Exception(..), catch, throwIO)
import           Control.Monad
                   (when)
import           Control.Monad.IO.Class
                   (MonadIO(..))
import           Data.Bifunctor
                   (first)
import           Data.Foldable
                   (toList)
import           Data.Foldable
                   (traverse_)
import           Data.Functor.Classes
                   (Eq1, Show1)
import           Data.Hashable
                   (Hashable(..))
import qualified Data.HashTable.IO             as HashTable
import qualified Data.List                     as List
import           Data.Map
                   (Map)
import qualified Data.Map                      as Map
import           Data.Maybe
                   (fromJust, isJust, isNothing)
import           Data.Proxy
                   (Proxy(Proxy))
import           Data.TreeDiff
                   (ToExpr(..), defaultExprViaShow)
import           Generic.Data
                   (gfiniteEnumFromTo, gmaxBound, gminBound)
import           GHC.Generics
                   (Generic)
import qualified Numeric.LinearAlgebra         as LinAlg
import           Numeric.LinearAlgebra.Static
                   (L, Sq, matrix, unwrap)
import           Prelude                       hiding
                   (elem, notElem)
import qualified Prelude                       as P
import           System.FilePath
                   ((<.>), (</>))
import           System.IO.Unsafe
                   (unsafePerformIO)
import           System.Posix.Types
                   (CPid(..))
import qualified System.Process                as Proc
import           System.Random
                   (randomRIO)
import           Test.QuickCheck
                   (Gen, Property, elements, maxFailPercent,
                   maxSuccess, noShrinking, oneof,
                   quickCheckWithResult, stdArgs, tables, (===))
import           Test.QuickCheck.Monadic
                   (monadicIO)
import           Text.Printf
                   (printf)

import           MarkovChain
import           Test.StateMachine
import           Test.StateMachine.Types
                   (Reference(..))
import qualified Test.StateMachine.Types.Rank2 as Rank2

------------------------------------------------------------------------
-- Domain

data Mock = Mock
  { registry :: Map Pname Pid
  , pids     :: [Pid]
  , next     :: Pid
  } deriving (Show, Generic)

newtype Pname = Pname String
  deriving stock (Eq, Ord, Show, Generic)

newtype Pid = Pid Int
  deriving newtype (Num, Enum)
  deriving stock (Eq, Generic, Show)

emptyMock :: Mock
emptyMock = Mock mempty mempty 0

data Err = PidNotFound | AlreadyRegistered | NotRegistered | UnknownError
  deriving (Eq, Show)

instance Exception Err

data Success r = Unit () | Got r
  deriving (Eq, Show, Functor, Foldable, Traversable)

newtype Resp r = Resp (Either Err (Success r))
  deriving (Eq, Show, Functor, Foldable, Traversable)

type MockOp a = Mock -> (Either Err a, Mock)

mSpawn :: MockOp Pid
mSpawn Mock{..} =
  let pid = next
  in (Right pid, Mock{ pids = pid:pids, next = succ next, .. })

mKill :: Pid -> MockOp ()
mKill pid Mock{..}
  | pid `P.notElem` pids = (Left PidNotFound, Mock{..})
  | otherwise = (Right (), Mock{ pids = List.delete pid pids, ..})

mRegister :: Pname -> Pid -> MockOp ()
mRegister pname pid Mock{..}
  | pid `P.notElem` pids = (Left PidNotFound, Mock{..})
  | Just _ <- Map.lookup pname registry = (Left AlreadyRegistered, Mock{..})
  | otherwise = (Right (), Mock{ registry = Map.insert pname pid registry, .. })

mUnregister :: Pname -> MockOp ()
mUnregister pname Mock{..}
  | Nothing <- Map.lookup pname registry = (Left NotRegistered, Mock{..})
  | otherwise = (Right (), Mock{ registry = Map.delete pname registry, ..})

mWhereIs :: Pname -> MockOp Pid
mWhereIs pname Mock{..}
  | Just pid <- Map.lookup pname registry = (Right pid, Mock{..})
  | otherwise = (Left NotRegistered, Mock{..})

data Cmd r
  = Spawn
  | Kill r
  | Register Pname r
  | Unregister Pname
  | WhereIs Pname
  deriving (Show, Functor, Foldable, Traversable)

runMock :: Cmd Pid -> Mock -> (Resp Pid, Mock)
runMock Spawn = first (Resp . fmap Got) . mSpawn
runMock (Register pname pid) = first (Resp . fmap Unit) . mRegister pname pid
runMock (Unregister pname) = first (Resp . fmap Unit) . mUnregister pname
runMock (Kill pid) = first (Resp . fmap Unit) . mKill pid
runMock (WhereIs pname) = first (Resp . fmap Got) . mWhereIs pname

------------------------------------------------------------------------
-- Implementation
--
-- The following code is stolen from an Hedgehog example:
--
-- Fake Process Registry
--
-- /These are global to simulate some kind of external system we're
-- testing./
--

instance Hashable Pname

instance Hashable Proc.Pid where
  hashWithSalt salt (CPid pid) = hashWithSalt salt pid

type PidTable = HashTable.CuckooHashTable Proc.Pid Proc.ProcessHandle

pidTable :: PidTable
pidTable =
  unsafePerformIO $ HashTable.new
{-# NOINLINE pidTable #-}

type ProcessTable = HashTable.CuckooHashTable Pname Proc.Pid

procTable :: ProcessTable
procTable =
  unsafePerformIO $ HashTable.new
{-# NOINLINE procTable #-}

ioReset :: IO ()
ioReset = do
  ks <- fmap fst <$> HashTable.toList procTable
  traverse_ (HashTable.delete procTable) ks

ioSpawn :: IO Proc.Pid
ioSpawn = do
  die <- randomRIO (1, 6) :: IO Int
  when (die == -1) $
    throwIO UnknownError
  ph <- Proc.spawnCommand "true"
  mpid <- Proc.getPid ph
  case mpid of
    Nothing  -> throwIO PidNotFound
    Just pid -> do
      HashTable.insert pidTable pid ph
      return pid

ioRegister :: Pname -> Proc.Pid -> IO ()
ioRegister name pid = do
  mpid <- HashTable.lookup pidTable pid
  when (isNothing mpid) $
    throwIO PidNotFound
  mp <- HashTable.lookup procTable name
  when (isJust mp) $
    throwIO AlreadyRegistered
  HashTable.insert procTable name pid

ioUnregister :: Pname -> IO ()
ioUnregister pname = do
  mp <- HashTable.lookup procTable pname
  when (isNothing mp) $
    throwIO NotRegistered
  HashTable.delete procTable pname

ioKill :: Proc.Pid -> IO ()
ioKill pid = do
  m <- HashTable.lookup pidTable pid
  when (isNothing m) $
    throwIO PidNotFound
  HashTable.delete pidTable pid

ioWhereIs :: Pname -> IO Proc.Pid
ioWhereIs name = do
  mpid <- HashTable.lookup procTable name
  case mpid of
    Nothing  -> throwIO NotRegistered
    Just pid -> pure pid

catchErr :: IO (Success h) -> IO (Resp h)
catchErr act = catch (Resp . Right <$> act) handler
  where
    handler :: Err -> IO (Resp h)
    handler e = pure $ Resp (Left e)

runIO :: Cmd Proc.Pid -> IO (Resp Proc.Pid)
runIO = catchErr . go
  where
    go :: Cmd Proc.Pid -> IO (Success Proc.Pid)
    go Spawn                = Got  <$> ioSpawn
    go (Register pname pid) = Unit <$> ioRegister pname pid
    go (Unregister pname)   = Unit <$> ioUnregister pname
    go (Kill pid)           = Unit <$> ioKill pid
    go (WhereIs pname)      = Got  <$> ioWhereIs pname

------------------------------------------------------------------------
-- Model

newtype At f r = At (f (Reference Proc.Pid r))
type    f :@ r = At f r

deriving stock instance Show (f (Reference Proc.Pid r)) => Show (At f r)

semantics :: Cmd :@ Concrete -> IO (Resp :@ Concrete)
semantics (At c) = (At . fmap reference) <$> runIO (concrete <$> c)

type PidRefs r = [(Reference Proc.Pid r, Pid)]

(!) :: Eq k => [(k, a)] -> k -> a
env ! r = fromJust (lookup r env)

data Model r = Model Mock (PidRefs r)
  deriving Generic

deriving instance Show1 r => Show (Model r)

initModel :: Model r
initModel = Model emptyMock []

toMock :: (Functor f, Eq1 r) => Model r -> f :@ r -> f Pid
toMock (Model _ pids) (At fr) = (pids !) <$> fr

step :: Eq1 r => Model r -> Cmd :@ r -> (Resp Pid, Mock)
step m@(Model mock _) c = runMock (toMock m c) mock

data Event r = Event
  { before   :: Model  r
  , cmd      :: Cmd :@ r
  , after    :: Model  r
  , mockResp :: Resp Pid
  }

lockstep :: Eq1 r
         => Model   r
         -> Cmd  :@ r
         -> Resp :@ r
         -> Event   r
lockstep m@(Model _ hs) c (At resp) = Event
  { before   = m
  , cmd      = c
  , after    = Model mock' (hs <> hs')
  , mockResp = resp'
  }
  where
    (resp', mock') = step m c
    hs' = zip (toList resp) (toList resp')

transition :: Eq1 r => Model r -> Cmd :@ r -> Resp :@ r -> Model r
transition m c = after . lockstep m c

precondition :: Model Symbolic -> Cmd :@ Symbolic -> Logic
precondition (Model _ refs) (At c) =
  forall (toList c) (`elem` map fst refs)

postcondition
  :: Model   Concrete
  -> Cmd  :@ Concrete
  -> Resp :@ Concrete
  -> Logic
postcondition m c r = toMock (after e) r .== mockResp e
  where
    e = lockstep m c r

symbolicResp
  :: Model Symbolic
  -> Cmd :@ Symbolic
  -> GenSym (Resp :@ Symbolic)
symbolicResp m c = At <$> traverse (const genSym) resp
  where
    (resp, _mock') = step m c

generator :: Model Symbolic -> Gen (Cmd :@ Symbolic)
generator m@(Model _ refs) = oneof $ concat
    [ withoutPids
    , if null refs then [] else withPids
    ]
  where
    withoutPids :: [Gen (Cmd :@ Symbolic)]
    withoutPids =
      [ genSpawn m ]

    withPids :: [Gen (Cmd :@ Symbolic)]
    withPids =
      [ genRegister m
      , genUnregister m
      , genKill m
      , genWhereIs m
      ]

genName :: Gen Pname
genName = elements (map Pname ["A", "B", "C"])

genSpawn, genRegister, genUnregister, genKill, genWhereIs ::
  Model Symbolic -> Gen (Cmd :@ Symbolic)
genSpawn _      = At <$> pure Spawn
genRegister m   = At <$> (Register <$> genName <*> genRef m)
genUnregister _ = At . Unregister <$> genName
genKill m       = At . Kill <$> genRef m
genWhereIs _    = At . WhereIs <$> genName

genRef :: Model Symbolic -> Gen (Reference Proc.Pid Symbolic)
genRef (Model _ refs) = elements (map fst refs)

shrinker :: Model Symbolic -> Cmd :@ Symbolic -> [Cmd :@ Symbolic]
shrinker _ _ = []

sm :: Markov Model FiniteModel (At Cmd)
   -> AdvancedStateMachine Model FiniteModel (At Cmd) IO (At Resp)
sm chain =
  StateMachine
    initModel
    transition
    precondition
    postcondition
    Nothing
    (Just . generator)
    (Just (chain, (Zero, Zero)))
    shrinker
    semantics
    symbolicResp

------------------------------------------------------------------------
-- additional class instances

instance CommandNames (At Cmd) where
  cmdName (At Spawn{})      = "Spawn"
  cmdName (At Register{})   = "Register"
  cmdName (At Unregister{}) = "Unregister"
  cmdName (At Kill{})       = "Kill"
  cmdName (At WhereIs{})    = "WhereIs"
  cmdNames _ = ["Spawn", "Register", "Unregister", "Kill", "WhereIs"]

instance Functor f => Rank2.Functor (At f) where
  fmap = \f (At x) -> At $ fmap (lift f) x
    where
      lift :: (r x -> r' x) -> Reference x r -> Reference x r'
      lift f (Reference x) = Reference (f x)

instance Foldable f => Rank2.Foldable (At f) where
  foldMap = \f (At x) -> foldMap (lift f) x
    where
      lift :: (r x -> m) -> Reference x r -> m
      lift f (Reference x) = f x

instance Traversable t => Rank2.Traversable (At t) where
  traverse = \f (At x) -> At <$> traverse (lift f) x
    where
      lift :: Functor f
           => (r x -> f (r' x)) -> Reference x r -> f (Reference x r')
      lift f (Reference x) = Reference <$> f x

deriving instance ToExpr (Model Concrete)
deriving instance ToExpr Mock
deriving newtype instance ToExpr Pid
deriving newtype instance ToExpr Pname

instance ToExpr Proc.Pid where
  toExpr = defaultExprViaShow

------------------------------------------------------------------------

prop_processRegistry :: Markov Model FiniteModel (At Cmd) -> Property
prop_processRegistry chain = noShrinking $
  forAllCommands sm' Nothing $ \cmds ->
    monadicIO $ do
      liftIO ioReset
      (hist, _model, res) <- runCommands sm' cmds
      tabulateState sm' hist
      prettyCommands sm' hist
        $ checkCommandNames cmds
        $ res === Ok
 where
   sm' = sm chain

------------------------------------------------------------------------
-- Usage specification

data Fin2
  = Zero
  | One
  | Two
  deriving (Enum, Bounded, Show, Eq, Read, Ord)

type FiniteModel = (Fin2, Fin2)

initFiniteModel :: FiniteModel
initFiniteModel = (Zero, Zero)

markovGood :: Markov Model FiniteModel (At Cmd)
markovGood = Markov f
  where
    f :: FiniteModel -> [(Int, Continue Model FiniteModel (At Cmd))]
    f (Zero, Zero) = [ (100, Continue "Spawn" genSpawn (One, Zero)) ]

    f (One,  Zero) = [ (40,  Continue "Spawn" genSpawn (Two, Zero))
                     , (40,  Continue "Register" genRegister (One, One))
                     , (20,  Continue "Kill" genKill (Zero, Zero))
                     ]
    f (One,  One)  = [ (50,  Continue "Spawn" genSpawn (Two, One))
                     , (20,  Continue "Unregister" genUnregister (One, Zero))
                     , (30,  Continue "WhereIs" genWhereIs (One, One))
                     ]
    f (Two, Zero)  = [ (80, Continue "Register" genRegister (Two, One))
                     , (20, Continue "Kill" genKill (One, Zero))
                     ]

    f (Two, One)   = [ (40, Continue "Register" genRegister (Two, Two))
                     , (10, Continue "Kill" genKill (One, One))
                     , (20, Continue "Unregister" genUnregister (Two, Zero))
                     , (20, Continue "WhereIs" genWhereIs (Two, One))
                     , (10, Stop)
                     ]
    f (Two, Two)   = [ (30, Stop)
                     , (20, Continue "Unregister" genUnregister (Two, One))
                     , (50, Continue "WhereIs" genWhereIs (Two, Two))
                     ]
    f _            = []

markovDeadlock :: Markov Model FiniteModel (At Cmd)
markovDeadlock = Markov f
  where
    genName' :: Gen Pname
    genName' = return (Pname "A")

    genRegister' :: Model Symbolic -> Gen (Cmd :@ Symbolic)
    genRegister' m   = At <$> (Register <$> genName' <*> genRef m)

    f :: FiniteModel -> [(Int, Continue Model FiniteModel (At Cmd))]
    f (Zero, Zero) = [ (100, Continue "Spawn"    genSpawn (One, Zero)) ]
    f (One,  Zero) = [ (100, Continue "Spawn"    genSpawn (Two, Zero)) ]
    f (Two, Zero)  = [ (100, Continue "Register" genRegister' (Two, One)) ]
    f (Two, One)   = [ (100, Continue "Register" genRegister' (Two, Two)) ]
    f (Two, Two)   = [ (100, Stop) ]
    f _            = []

markovNotStochastic1 :: Markov Model FiniteModel (At Cmd)
markovNotStochastic1 = Markov f
  where
    f (Zero, Zero) = [ ( 90, Continue "Spawn" genSpawn (One, Zero)) ]
    f (One, Zero)  = [ (100, Stop) ]
    f _            = []

markovNotStochastic2 :: Markov Model FiniteModel (At Cmd)
markovNotStochastic2 = Markov f
  where
    f (Zero, Zero) = [ (110, Continue "Spawn" genSpawn (One, Zero))
                     , (-10, Stop)
                     ]
    f (One, Zero)  = [ (100, Stop) ]
    f _            = []

markovNotStochastic3 :: Markov Model FiniteModel (At Cmd)
markovNotStochastic3 = Markov f
  where
    f (Zero, Zero) = [ (90, Continue "Spawn" genSpawn (One, Zero))
                     , (10, Stop)
                     ]
    f (One, Zero)  = [ (100, Stop) ]
    f (Two, Two)   = [ (90, Stop) ]
    f _            = []

printStaticStats :: IO ()
printStaticStats = do
  case transitionMatrix markovGood of
    SomeMatrix _ _ mat -> do
      let mat' :: Sq 10
          mat' = matrix (concat (LinAlg.toLists (unwrap mat)))
      putStrLn ""
      putStrLn "Transition matrix:"
      print mat'
      putStrLn ""
      putStrLn "Long-run state occupancy:"
      let states :: [FiniteModel]
          states = gfiniteEnumFromTo gminBound gmaxBound
      mapM_ (\(s, p) -> printf "%-15s %-15.2f\n" (show s) p)
        (zip states (LinAlg.toList (unwrap (MarkovChain.pi mat'))))
      putStrLn ""
      putStrLn "Expected test case length:"
      print (expectedLength (fundamental (reduceCol (reduceRow mat'))))

printStats :: Int -> Maybe FilePath -> IO ()
printStats runs mdir = do
  let args = stdArgs { maxFailPercent = 10, maxSuccess = runs }
  res <- quickCheckWithResult args (prop_processRegistry markovGood)
  case compatibleMatrices (Proxy @10) (transitionMatrix markovGood)
                          (results (Proxy @FiniteModel) (tables res)) of
    Left err -> error err
    Right (CompatibleMatrices pn p s f) -> do
      putStrLn ""
      putStrLn "Succcessful transitions from state i to state j:"
      print s
      putStrLn ""
      putStrLn "Failed transitions from state i to state j:"
      print f
      putStrLn ""
      putStrLn "Single use reliability:"
      case mdir of
        Nothing  -> print (singleUseReliability pn (reduceRow p) Nothing (s, f))
        Just dir -> do
          -- Load and print priors?
          r <- singleUseReliabilityIO pn (reduceRow p :: L 9 10)
                                      (dir </> "successes" <.> "hmatrix")
                                      (dir </> "failures" <.> "hmatrix")
                                      (s, f)
          print r
