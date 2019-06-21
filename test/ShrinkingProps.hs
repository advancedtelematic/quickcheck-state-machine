{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveFoldable      #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ImplicitParams      #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module ShrinkingProps (
    tests
    -- Just to avoid compiler warnings
  , ShrinkSeqFailure(..)
  , ShrinkParFailure(..)
  ) where

import           Prelude

import           Control.Monad
                   (forM_, replicateM)
import           Control.Monad.Except
                   (Except, runExcept, throwError)
import           Control.Monad.State
                   (State, gets, modify, runState, state)
import           Data.Bifunctor
                   (first)
import           Data.Foldable
                   (toList)
import           Data.Functor.Classes
                   (Eq1, Show1)
import           Data.List.Split (chunksOf)
import           Data.Map.Strict
                   (Map)
import qualified Data.Map.Strict               as Map
import           Data.Monoid
                   ((<>))
import           Data.Proxy
import           Data.Set
                   (Set)
import qualified Data.Set                      as Set
import           Data.TreeDiff
                   (defaultExprViaShow)
import           Data.Typeable
                   (Typeable)
import           GHC.Generics
                   (Generic, Generic1)
import           GHC.Stack
import           Text.Show.Pretty
                   (ppShow)
import           UnliftIO.STM

import           Test.QuickCheck.Monadic
                   (monadicIO)
import           Test.Tasty
import           Test.Tasty.QuickCheck
                   (Arbitrary(..), Gen, Property, conjoin,
                   counterexample, elements, forAllShrinkShow,
                   getNonNegative, getSmall, oneof, property,
                   testProperty, (===), withMaxSuccess)

import           Test.StateMachine
import qualified Test.StateMachine.Parallel    as QSM
import qualified Test.StateMachine.Sequential  as QSM
import qualified Test.StateMachine.Types       as QSM
import qualified Test.StateMachine.Types.Rank2 as Rank2
import           Test.StateMachine.Utils
                   (Shrunk(..), shrinkListS',
                   shrinkListS', shrinkListS'', shrinkPairS')

tests :: TestTree
tests = testGroup "Shrinking properties" [
        testProperty "Sanity check: standard sequential test"        prop_sequential
      , testProperty "Sanity check: standard parallel test"          prop_parallel
      , testProperty "Sanity check: standard 3-parallel test"        $ withMaxSuccess 50 prop_3parallel
      , testProperty "Correct references after sequential shrinking" prop_sequential_subprog
      , testProperty "Correct references after parallel shrinking"   prop_parallel_subprog
      , testProperty "Correct references after 3-parallel shrinking" $ withMaxSuccess 50 prop_nparallel_subprog
      , testProperty "Correct references after parallel shrinking (buggyShrinkCmds)"   (prop_parallel_subprog' buggyShrinkCmds)
      , testProperty "Sequential shrinker provides correct model"    prop_sequential_model
      , testProperty "Parallel shrinker provides correct model"      $ withMaxSuccess 70 $ prop_parallel_model
      , testProperty "2-Parallel shrinker provides correct model"    $ prop_nparallel_model 2
      , testProperty "3-Parallel shrinker provides correct model"    $ withMaxSuccess 60 $ prop_nparallel_model 3
      , testProperty "1-Parallel is equivalent to sequential"        prop_one_thread
      , testProperty "2 Threads equivalence"                         $ withMaxSuccess 40 prop_pairs_round_trip
      , testProperty "shrink round trips"                            prop_shrink_round_trip
    ]

{-------------------------------------------------------------------------------
  Example set up

  This language is contrived, but designed to have lots of references, including
  commands that /use/ a variable number of references and commands that /create/
  a variable number of references.
-------------------------------------------------------------------------------}

-- | Unique command identifier
--
-- This is used when testing whether shrinking messes up references (see below)
newtype CmdID = CmdID Int
  deriving (Show, Eq, Ord, Generic)

-- | Commands
--
-- Commands have two somewhat unusual features that are just here for the
-- specific purpose of testing shrinking:
--
-- * The 'CmdID' fields are there so that we can build the reference graph
--   (see 'RefGraph') below to check that shrinking does not mess up references.
-- * The 'Maybe Model' field is there to check that the shrinker gets presented
--   with the right model.
data Cmd var =
    -- | Create @n@ new mutable variables
    CreateRef CmdID (Maybe (Model Symbolic)) Int

    -- | Increment the value of the specified variables
  | Incr CmdID (Maybe (Model Symbolic)) [var]

    -- | Get the value of the specified variables
  | Read CmdID (Maybe (Model Symbolic)) [var]
  deriving (Show, Eq, Functor, Foldable, Traversable, Generic1, CommandNames)

data Resp var =
    Refs [var]
  | Unit ()
  | Vals [Int]
  deriving (Show, Eq, Functor, Foldable, Traversable)

cmdID :: Cmd var -> CmdID
cmdID (CreateRef cid _ _) = cid
cmdID (Incr      cid _ _) = cid
cmdID (Read      cid _ _) = cid

cmdModel :: Cmd var -> Maybe (Model Symbolic)
cmdModel (CreateRef _ m _) = m
cmdModel (Incr      _ m _) = m
cmdModel (Read      _ m _) = m

{-------------------------------------------------------------------------------
  Mock implementation
-------------------------------------------------------------------------------}

-- | Mock variable
newtype MockVar = MockVar Int
  deriving (Show, Eq, Ord, Generic)

-- | Mock system state
newtype MockState = MockState (Map MockVar Int)
  deriving (Show, Eq, Ord, Generic)

newVar :: State MockState MockVar
newVar = state $ \(MockState m) ->
           let x = MockVar (Map.size m)
           in (x, MockState (Map.insert x 0 m))

incrVar :: MockVar -> State MockState ()
incrVar x = modify $ \(MockState m) ->
              let incr Nothing  = error "incrVar: undefined variable"
                  incr (Just v) = Just (v + 1)
              in MockState $ Map.alter incr x m

readVar :: MockVar -> State MockState Int
readVar x = gets $ \(MockState m) ->
              case Map.lookup x m of
                Just n  -> n
                Nothing -> error $ "readVar: variable " ++ show x ++ " not found"

runMock :: Cmd MockVar -> MockState -> (Resp MockVar, MockState)
runMock (CreateRef _ _ n)  = first Refs . runState (replicateM n newVar)
runMock (Incr      _ _ xs) = first Unit . runState (mapM_ incrVar xs)
runMock (Read      _ _ xs) = first Vals . runState (mapM  readVar xs)

{-------------------------------------------------------------------------------
  I/O implementation

  We use STM variables here so guarantee atomicity of 'Incr' command
  (we are testing the shrinker, not looking for atomicity bugs! :)
-------------------------------------------------------------------------------}

data IOVar = IOVar String (TVar Int)
  deriving (Eq)

instance Show IOVar where
  show (IOVar l _) = "<" ++ l ++ ">"

newIOVar :: CmdID -> Int -> STM IOVar
newIOVar cid n = IOVar (show (cid, n)) <$> newTVar 0

incrIOVar :: IOVar -> STM ()
incrIOVar (IOVar _ x) = modifyTVar x (+1)

readIOVar :: IOVar -> STM Int
readIOVar (IOVar _ x) = readTVar x

runIO :: Cmd IOVar -> IO (Resp IOVar)
runIO (CreateRef cid _ n)  = atomically $ Refs <$> mapM (newIOVar cid) [0 .. n - 1]
runIO (Incr      _   _ xs) = atomically $ Unit <$> mapM_ incrIOVar xs
runIO (Read      _   _ xs) = atomically $ Vals <$> mapM  readIOVar xs

{-------------------------------------------------------------------------------
  Instantiate to references
-------------------------------------------------------------------------------}

newtype At f r = At (f (Reference IOVar r))
  deriving (Generic1, Rank2.Functor, Rank2.Foldable, Rank2.Traversable)

type (:@) f r = At f r

{-------------------------------------------------------------------------------
  Model
-------------------------------------------------------------------------------}

type KnownRefs r = [(Reference IOVar r, MockVar)]

resolveRef :: (Eq1 r, Show1 r, HasCallStack)
           => KnownRefs r -> Reference IOVar r -> MockVar
resolveRef refs r =
    case lookup r refs of
      Just x  -> x
      Nothing -> error $ "resolveRef: reference " ++ show r
                      ++ "not found in environment " ++ show refs

-- | Model relating the mock state with the IO state
--
-- We include the CmdID so that we can reference it in the generator
data Model r = Model MockState (KnownRefs r) CmdID
  deriving (Generic, Eq)

initModel :: Model r
initModel = Model (MockState Map.empty) [] (CmdID 0)

toMock :: (Eq1 r, Show1 r, Functor f, HasCallStack)
       => Model r -> f :@ r -> f MockVar
toMock (Model _ knownRefs _) (At fr) = fmap (resolveRef knownRefs) fr

step :: (Eq1 r, Show1 r, HasCallStack) => Model r -> Cmd :@ r -> (Resp MockVar, MockState)
step model@(Model mockState _ _) cmd =
    let cs = callStack
    in let ?callStack = pushCallStack ("<stepping " ++ show cmd ++ ">", here) cs
       in runMock (toMock model cmd) mockState
  where
    here = SrcLoc "quickcheck-state-machine" "ShrinkingProps" "ShrinkingProps.hs" 0 0 0 0

{-------------------------------------------------------------------------------
  Events
-------------------------------------------------------------------------------}

data Event r = Event {
    eventBefore   :: Model  r
  , eventCmd      :: Cmd :@ r
  , eventAfter    :: Model  r
  , eventMockResp :: Resp MockVar
  }

event :: forall r. (Eq1 r, Show1 r, HasCallStack)
      => Model  r
      -> Cmd :@ r
      -> (Resp MockVar -> KnownRefs r)
      -> Event  r
event model@(Model _ knownRefs (CmdID n)) cmd newRefs = Event {
      eventBefore   = model
    , eventCmd      = cmd
    , eventAfter    = Model mock' (newRefs resp' ++ knownRefs) (CmdID (n + 1))
    , eventMockResp = resp'
    }
  where
    (resp', mock') = step model cmd

lockstep :: (Eq1 r, Show1 r, HasCallStack)
         => Model r -> Cmd :@ r -> Resp :@ r -> Event r
lockstep model cmd (At resp) = event model cmd $ \resp' ->
    zip (toList resp) (toList resp')

{-------------------------------------------------------------------------------
  Generator
-------------------------------------------------------------------------------}

generator :: Model Symbolic -> Maybe (Gen (Cmd :@ Symbolic))
generator (Model _ knownRefs cid) = Just $ oneof [
      At . CreateRef cid Nothing <$> small
    , small >>= \n -> At . Incr cid Nothing <$> replicateM n pickRef
    , small >>= \n -> At . Read cid Nothing <$> replicateM n pickRef
    ]
  where
    pickRef :: Gen (Reference IOVar Symbolic)
    pickRef = elements (map fst knownRefs)

    small :: Gen Int
    small = getSmall . getNonNegative <$> arbitrary

-- | Shrinker
--
-- The only thing the shrinker does is record the model we are given as part
-- of the shrunk command, so that we can check later we got the right model.
shrinker :: Model Symbolic -> Cmd :@ Symbolic -> [Cmd :@ Symbolic]
shrinker m (At cmd) =
    case cmd of
      CreateRef cid Nothing n  -> [At $ CreateRef cid (Just m) n ]
      Incr      cid Nothing xs -> [At $ Incr      cid (Just m) xs]
      Read      cid Nothing xs -> [At $ Read      cid (Just m) xs]
      _otherwise               -> []

{-------------------------------------------------------------------------------
  The state machine
-------------------------------------------------------------------------------}

transition :: (Eq1 r, Show1 r) => Model r -> Cmd :@ r -> Resp :@ r -> Model r
transition model cmd = eventAfter . lockstep model cmd

precondition :: Model Symbolic -> Cmd :@ Symbolic -> Logic
precondition (Model _ knownRefs _) (At cmd) =
    forall (toList cmd) (`member` map fst knownRefs)

postcondition :: HasCallStack
              => Model Concrete -> Cmd :@ Concrete -> Resp :@ Concrete -> Logic
postcondition model cmd resp = toMock (eventAfter ev) resp .== eventMockResp ev
  where
    ev = lockstep model cmd resp

mock :: Model Symbolic -> Cmd :@ Symbolic -> GenSym (Resp :@ Symbolic)
mock model cmd = At <$> traverse (const QSM.genSym) resp
  where
    (resp, _mock') = step model cmd

semantics :: Cmd :@ Concrete -> IO (Resp :@ Concrete)
semantics (At cmd) = (At . fmap QSM.reference) <$> runIO (QSM.concrete <$> cmd)

sm :: StateMachine Model (At Cmd) IO (At Resp)
sm = QSM.StateMachine {
         initModel     = initModel
       , transition    = transition
       , precondition  = precondition
       , postcondition = postcondition
       , generator     = generator
       , shrinker      = shrinker
       , semantics     = semantics
       , mock          = mock
       , invariant     = Nothing
       }

{-------------------------------------------------------------------------------
  The type class instances required by QSM
-------------------------------------------------------------------------------}

deriving instance Eq1 r => Eq (Cmd  :@ r)
deriving instance Eq1 r => Eq (Resp :@ r)

deriving instance Show1 r => Show (Cmd  :@ r)
deriving instance Show1 r => Show (Resp :@ r)
deriving instance Show1 r => Show (Model   r)

instance CommandNames (At Cmd) where
  cmdName  (At cmd) = cmdName cmd
  cmdNames _        = cmdNames (Proxy @(Cmd ()))

deriving instance ToExpr (Model Concrete)
deriving instance ToExpr MockState
deriving instance ToExpr MockVar
deriving instance ToExpr CmdID

instance ToExpr IOVar where
  toExpr = defaultExprViaShow

{-------------------------------------------------------------------------------
  The standard QSM tests (as a sanity check)
-------------------------------------------------------------------------------}

prop_sequential :: Property
prop_sequential = forAllCommands sm Nothing $ \cmds -> monadicIO $ do
    (hist, _model, res) <- runCommands sm cmds
    prettyCommands sm hist (checkCommandNames cmds (res === Ok))

prop_parallel :: Property
prop_parallel = forAllParallelCommands sm $ \cmds -> monadicIO $
    prettyParallelCommands cmds =<< runParallelCommands sm cmds

prop_3parallel :: Property
prop_3parallel = forAllNParallelCommands sm 3 $ \cmds -> monadicIO $
  prettyNParallelCommands cmds =<< runNParallelCommands sm cmds

{-------------------------------------------------------------------------------
  Test that shrinking does not mess up references

  We do this by translating the program to use references of an alternative
  shape: they explicitly say "the nth reference returned by command with ID id".
  Since command IDs do not change during shrinking, the translated program
  after shrinking should be a strict sublist of the translated original program.
-------------------------------------------------------------------------------}

data ExplicitRef = ExplicitRef CmdID Int
  deriving (Show, Eq, Ord)

type RefGraph = Map CmdID (Set ExplicitRef)

isSubGraphOf :: RefGraph -> RefGraph -> Bool
g `isSubGraphOf` g' = Map.isSubmapOfBy Set.isSubsetOf g g'

refGraph :: HasCallStack => QSM.Commands (At Cmd) (At Resp) -> RefGraph
refGraph (QSM.Commands cmds) = go Map.empty Map.empty cmds
  where
    go :: Map QSM.Var ExplicitRef
       -> RefGraph
       -> [QSM.Command (At Cmd) (At Resp)]
       -> RefGraph
    go _    !acc []                                     = acc
    go refs !acc (QSM.Command (At cmd) _resp vars : cs) =
        go (refs `union` newRefs)
           (Map.insert (cmdID cmd) (Set.fromList $ map deref (toList cmd)) acc)
           cs
      where
        deref :: Reference r Symbolic -> ExplicitRef
        deref (QSM.Reference (QSM.Symbolic x)) =
            case Map.lookup x refs of
              Just r  -> r
              Nothing -> error $ "deref: reference " ++ show x ++ " not found "
                      ++ "in environment " ++ show refs
                      ++ " with commands " ++ show cmds

        newRefs :: Map QSM.Var ExplicitRef
        newRefs = Map.fromList $ zipWith mkRef vars [0..]

        -- When adding new 'QSM.Var's, check that they are not already present
        -- in the map, as the same 'QSM.Var' may never be created by two
        -- different commands.
        union :: Map QSM.Var ExplicitRef -- ^ Known references
              -> Map QSM.Var ExplicitRef -- ^ New references
              -> Map QSM.Var ExplicitRef
        union known new = foldr insertUnlessKnown known (Map.toList new)
          where
            insertUnlessKnown (var, newRef) =
                Map.insertWith (\_ oldRef -> error $ mkMsg var oldRef newRef)
                var newRef
            mkMsg var oldRef newRef =   show var    ++
              " created by "         ++ show oldRef ++
              " already created by " ++ show newRef ++
              " with commands\n"     ++ ppShow cmds


        mkRef :: QSM.Var -> Int -> (QSM.Var, ExplicitRef)
        mkRef x i = (x, ExplicitRef (cmdID cmd) i)

data ShrinkSeqFailure = SSF {
      ssfOrig     :: QSM.Commands (At Cmd) (At Resp)
    , ssfShrunk   :: QSM.Commands (At Cmd) (At Resp)
    , ssfGrOrig   :: RefGraph
    , ssfGrShrunk :: RefGraph
    }
  deriving (Show)

-- | Test that sequential shrinking results in a program whose reference
-- graph is a subgraph of the reference graph of the original program
--
-- We don't use 'forAllCommands' directly as that would be circular (if the
-- shrinker is broken, we don't want to use it to test the shrinker!).
prop_sequential_subprog :: Property
prop_sequential_subprog =
    forAllShrinkShow (QSM.generateCommands sm Nothing) (const []) ppShow $ \cmds ->
      let cmds' = refGraph cmds in
      conjoin [ let shrunk' = refGraph shrunk in
                counterexample (ppShow (SSF cmds shrunk cmds' shrunk')) $
                  shrunk' `isSubGraphOf` cmds'
              | shrunk <- QSM.shrinkCommands sm cmds
              ]

{-------------------------------------------------------------------------------
  For parallel shrinking we do pretty much the same thing, we just need to
  walk over all commands in 'ParallelCommands'
-------------------------------------------------------------------------------}

data ShrinkParFailure t = SPF {
      spfOrig     :: QSM.ParallelCommandsF t (At Cmd) (At Resp)
    , spfShrunk   :: QSM.ParallelCommandsF t (At Cmd) (At Resp)
    , spfTrOrig   :: RefGraph
    , spfTrShrunk :: RefGraph
    }

deriving instance Show (ShrinkParFailure QSM.Pair)
deriving instance Show (ShrinkParFailure [])

-- | Compute reference graph for a parallel program
--
-- We do this by constructing the refernce graph of the sequential program
-- where we execute the left and right part of all suffices in interleaved
-- fashion.
refGraph' :: HasCallStack => QSM.ParallelCommands (At Cmd) (At Resp) -> RefGraph
refGraph' (QSM.ParallelCommands prefix suffixes) =
    refGraph (prefix <> mconcat (map (\(QSM.Pair l r) -> l `mappend` r) suffixes))

refGraph'' :: HasCallStack => QSM.NParallelCommands (At Cmd) (At Resp) -> RefGraph
refGraph'' (QSM.ParallelCommands prefix suffixes) =
    refGraph (prefix <> mconcat (mconcat suffixes))

prop_parallel_subprog :: Property
prop_parallel_subprog =
    forAllShrinkShow (QSM.generateParallelCommands sm) (const []) ppShow $
      prop_parallel_subprog'
  where
    -- TODO add as a test (?)
    -- genCmds = return buggyShrinkCmds

prop_parallel_subprog' :: QSM.ParallelCommands (At Cmd) (At Resp) -> Property
prop_parallel_subprog' cmds =
    conjoin [ let shrunk' = refGraph' shrunk in
              counterexample (ppShow (SPF cmds shrunk cmds' shrunk')) $
                shrunk' `isSubGraphOf` cmds'
            | shrunk <- QSM.shrinkParallelCommands sm cmds
            ]
  where
    cmds' = refGraph' cmds

prop_shrink_round_trip :: ([Int], [Int]) -> Property
prop_shrink_round_trip (ls1, ls2) =
  let
    ex = shrinkPairS' shrinkListS' (ls1, ls2)
    f (Shrunk wasShrunk [x,y]) = Shrunk wasShrunk (x,y)
    f (Shrunk _ _) = error "invariant violated! shrunk list should have length 2"
    val = f <$> shrinkListS'' shrinkListS' [ls1, ls2]
  in
    val === ex

prop_pairs_round_trip :: Property
prop_pairs_round_trip = forAllParallelCommands sm $ \pairCmds ->
  let
    pairShrunk = QSM.shrinkParallelCommands sm pairCmds
    listCmds = QSM.fromPair' pairCmds
    listShrunk = QSM.shrinkNParallelCommands sm listCmds
    listShrunkPair = QSM.toPairUnsafe' <$> listShrunk
  in
    listShrunkPair === pairShrunk

prop_nparallel_subprog :: Property
prop_nparallel_subprog =
    forAllShrinkShow (QSM.generateNParallelCommands sm 3) (const []) ppShow $
      prop_nparallel_subprog'

prop_nparallel_subprog' :: QSM.NParallelCommands (At Cmd) (At Resp) -> Property
prop_nparallel_subprog' cmds =
    conjoin [ let shrunk' = refGraph'' shrunk in
              counterexample (ppShow (SPF cmds shrunk cmds' shrunk')) $
                shrunk' `isSubGraphOf` cmds'
            | shrunk <- QSM.shrinkNParallelCommands sm cmds
            ]
  where
    cmds' = refGraph'' cmds

-- A set of valid commands to resulted in an invalid shrink
buggyShrinkCmds :: QSM.ParallelCommands (At Cmd) (At Resp)
buggyShrinkCmds = QSM.ParallelCommands (QSM.Commands [])
    [ QSM.Pair (QSM.Commands [mkCreateRef 0 [0]])
               (QSM.Commands [mkCreateRef 1 [1]])
               -- This Var 1 was shrunk to Var 0
    , QSM.Pair (QSM.Commands [mkRead 2 [0]])
               (QSM.Commands [mkRead 3 [1]])
    ]
  where
    mkCreateRef, mkRead :: Int -> [Int] -> QSM.Command (At Cmd) (At Resp)
    mkCreateRef cid vars =
      QSM.Command (At (CreateRef (CmdID cid) Nothing (length vars)))
                  (At (Refs (map mkRef vars)))
                  (map QSM.Var vars)
    mkRead cid vars =
      QSM.Command (At (Read (CmdID cid) Nothing (map mkRef vars)))
                  (At (Vals (map (const 0) vars)))
                  []

    mkRef :: Typeable a => Int -> Reference a Symbolic
    mkRef = QSM.Reference . QSM.Symbolic . QSM.Var


{-------------------------------------------------------------------------------
  Check that the shrinker gets presented with the right model
-------------------------------------------------------------------------------}

execCmd :: Model Symbolic -> QSM.Command (At Cmd) (At Resp) -> Event Symbolic
execCmd model (QSM.Command cmd resp _) = lockstep model cmd resp

checkCorrectModel :: QSM.Commands (At Cmd) (At Resp) -> Property
checkCorrectModel cmds =
    case runExcept (checkCorrectModel' initModel cmds) of
      Left err -> counterexample err $ property False
      Right _  -> property True

-- | Verify that all commands have been paired with the right model
-- (if they have been paired)
--
-- Returns the final model if successful.
checkCorrectModel' :: Model Symbolic
                   -> QSM.Commands (At Cmd) (At Resp)
                   -> Except String (Model Symbolic)
checkCorrectModel' = \model (QSM.Commands cmds) -> go model cmds
  where
    go :: Model Symbolic
       -> [QSM.Command (At Cmd) (At Resp)]
       -> Except String (Model Symbolic)
    go m []       = return m
    go m (c : cs) = do verifyModel m (cmdModel' c)
                       go (eventAfter (execCmd m c)) cs

    verifyModel :: Model Symbolic -> Maybe (Model Symbolic) -> Except String ()
    verifyModel _ Nothing   = return ()
    verifyModel m (Just m')
                | m == m'   = return ()
                | otherwise = throwError (show m ++ " /= " ++ show m')


    cmdModel' :: QSM.Command (At Cmd) (At Resp) -> Maybe (Model Symbolic)
    cmdModel' (QSM.Command (At cmd) _ _) = cmdModel cmd


prop_sequential_model :: Property
prop_sequential_model =
    forAllShrinkShow (QSM.generateCommands sm Nothing) (const []) ppShow $ \cmds ->
      conjoin [ checkCorrectModel shrunk
              | shrunk <- QSM.shrinkCommands sm cmds
              ]

{-------------------------------------------------------------------------------
  For the parallel case we do the same, but traversing the left and right
  suffix separately
-------------------------------------------------------------------------------}

checkCorrectModelNParallel :: QSM.NParallelCommands (At Cmd) (At Resp) -> Property
checkCorrectModelNParallel = \(QSM.ParallelCommands prefix suffixes) ->
    case runExcept (go prefix suffixes) of
      Left err -> counterexample err $ property False
      Right () -> property True
  where
    go :: QSM.Commands (At Cmd) (At Resp)
       -> [[(QSM.Commands (At Cmd) (At Resp))]]
       -> Except String ()
    go prefix suffixes = do
        modelAfterPrefix <- checkCorrectModel' initModel prefix
        go' modelAfterPrefix suffixes

    go' :: Model Symbolic
        -> [[(QSM.Commands (At Cmd) (At Resp))]]
        -> Except String ()
    go' _ []                        = return ()
    go' m ([] : suffixes) =
        go' m suffixes
    go' m ((headThread : suffix) : suffixes) = do
        modelAfterHead <- checkCorrectModel' m headThread
        -- The starting model for the right part is the /initial/ model:
        -- it should not be affected by the left part
        _ <- forM_ suffix $ checkCorrectModel' m
        -- But when we check the /next/ suffix, /both/ parts have been executed
        go' (foldl (\m' r -> QSM.advanceModel sm m' r) modelAfterHead suffix) suffixes

checkCorrectModelParallel :: QSM.ParallelCommands (At Cmd) (At Resp) -> Property
checkCorrectModelParallel = \(QSM.ParallelCommands prefix suffixes) ->
    case runExcept (go prefix suffixes) of
      Left err -> counterexample err $ property False
      Right () -> property True
  where
    go :: QSM.Commands (At Cmd) (At Resp)
       -> [QSM.Pair (QSM.Commands (At Cmd) (At Resp))]
       -> Except String ()
    go prefix suffixes = do
        modelAfterPrefix <- checkCorrectModel' initModel prefix
        go' modelAfterPrefix suffixes

    go' :: Model Symbolic
        -> [QSM.Pair (QSM.Commands (At Cmd) (At Resp))]
        -> Except String ()
    go' _ []                        = return ()
    go' m (QSM.Pair l r : suffixes) = do
        modelAfterLeft <- checkCorrectModel' m l
        -- The starting model for the right part is the /initial/ model:
        -- it should not be affected by the left part
        _ <- checkCorrectModel' m r
        -- But when we check the /next/ suffix, /both/ parts have been executed
        go' (QSM.advanceModel sm modelAfterLeft r) suffixes

prop_parallel_model :: Property
prop_parallel_model =
    forAllShrinkShow (QSM.generateParallelCommands sm) (const []) ppShow $ \cmds ->
      conjoin [ checkCorrectModelParallel shrunk
              | shrunk <- QSM.shrinkParallelCommands sm cmds
              ]

prop_nparallel_model :: Int -> Property
prop_nparallel_model n =
    forAllShrinkShow (QSM.generateNParallelCommands sm n) (const []) ppShow $ \cmds ->
      conjoin [ checkCorrectModelNParallel shrunk
              | shrunk <- QSM.shrinkNParallelCommands sm cmds
              ]

prop_one_thread :: Int -> Property
prop_one_thread n = forAllCommands sm Nothing $ \cmds -> monadicIO $ do
      let n' = 1 + (n `mod` 10)
      (hist, _model, _res) <- runCommands sm cmds
      let cmdsList = QSM.unCommands cmds
          (px, sx) = splitAt (div (length cmdsList) 3) cmdsList
          cmdsChucks = chunksOf n' sx
          sfxs = (\c -> [c]) . QSM.Commands <$> cmdsChucks
          nParallelCmd = QSM.ParallelCommands {prefix = QSM.Commands px, suffixes = sfxs}
      res <- runNParallelCommandsNTimes 1 sm $ nParallelCmd
      let (hist', _ret) = unzip res
      let events = snd <$> (QSM.unHistory hist)
          events' = snd <$> (concat (QSM.unHistory <$> hist'))
      return $ cmpList equalH events' events

{-------------------------------------------------------------------------------
  Testing equality between histories of different executions has to be
  different from the default equality check. This is because different
  executions will create different references, so we have to check them
  only by value.
-------------------------------------------------------------------------------}

type Hist = QSM.HistoryEvent (At Cmd) (At Resp)

equalH :: Hist -> Hist -> Bool
equalH (QSM.Invocation c sv) (QSM.Invocation c' sv') = equalCmd c c' && sv == sv'
equalH (QSM.Response r) (QSM.Response r') = equalResp r r'
equalH (QSM.Exception s) (QSM.Exception s') = s == s'
equalH _ _ = False

equalCmd :: Cmd :@ Concrete -> Cmd :@ Concrete -> Bool
equalCmd (At (CreateRef c m n)) (At (CreateRef c' m' n'))
    = c == c' && m == m' && n == n'
equalCmd (At (Incr c m vs)) (At (Incr c' m' vs'))
    = c == c' && m == m' && eqVars vs vs'
equalCmd (At (Read c m vs)) (At (Read c' m' vs'))
    = c == c' && m == m' && eqVars vs vs'
equalCmd _ _ = False

equalResp :: Resp :@ Concrete -> Resp :@ Concrete -> Bool
equalResp (At (Refs vs)) (At (Refs vs')) = eqVars vs vs'
equalResp (At (Unit ())) (At (Unit ())) = True
equalResp (At (Vals ns)) (At (Vals ns')) = ns == ns'
equalResp _ _ = False

cmpList :: (a -> a -> Bool) -> [a] -> [a] -> Bool
cmpList _cmp [] [] = True
cmpList cmp (a : as) (b : bs) =
  cmp a b && cmpList cmp as bs
cmpList _ _ _ = False

eqVars :: [Reference IOVar Concrete] -> [Reference IOVar Concrete] -> Bool
eqVars vs vs' = cmpList equalVar (concrete <$> vs) (concrete <$> vs')

equalVar :: IOVar -> IOVar -> Bool
equalVar (IOVar s _) (IOVar s' _) = s == s'
