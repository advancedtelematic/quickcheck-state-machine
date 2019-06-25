{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE ExplicitNamespaces   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE MonoLocalBinds       #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}

module MemoryReference
  ( prop_sequential
  , prop_runSavedCommands
  , prop_parallel
  , prop_parallel'
  , prop_nparallel
  , prop_precondition
  , prop_existsCommands
  , Bug(..)
  , prop_pairs_shrink_parallel_equivalence
  , prop_pairs_shrinkAndValidate_equivalence
  , prop_pairs_shrink_parallel
  )
  where

import           Control.Concurrent
                   (threadDelay)
import           Data.Functor.Classes
                   (Eq1)
import           Data.IORef
                   (IORef, atomicModifyIORef', newIORef, readIORef,
                   writeIORef)
import           GHC.Generics
                   (Generic, Generic1)
import           Prelude
import           System.Random
                   (randomIO, randomRIO)
import           Test.QuickCheck
                   (Gen, Property, arbitrary, elements, frequency,
                   once, shrink, (===))
import           Test.QuickCheck.Monadic
                   (monadicIO)

import           Test.StateMachine
import           Test.StateMachine.Parallel
                   (shrinkAndValidateNParallel, shrinkAndValidateParallel,
                   shrinkCommands', shrinkNParallelCommands, shrinkParallelCommands)
import           Test.StateMachine.Sequential (ShouldShrink (..))
import           Test.StateMachine.Types
                   (Commands(Commands), Reference(..), Symbolic(..),
                   Var(Var))
import qualified Test.StateMachine.Types       as Types
import qualified Test.StateMachine.Types.Rank2 as Rank2
import           Test.StateMachine.Utils
                   (Shrunk(..), shrinkListS, shrinkListS'', shrinkPairS,
                   shrinkPairS' )
import           Test.StateMachine.Z

------------------------------------------------------------------------

data Command r
  = Create
  | Read  (Reference (Opaque (IORef Int)) r)
  | Write (Reference (Opaque (IORef Int)) r) Int
  | Increment (Reference (Opaque (IORef Int)) r)
  deriving (Eq, Generic1, Rank2.Functor, Rank2.Foldable, Rank2.Traversable, CommandNames)

deriving instance Show (Command Symbolic)
deriving instance Read (Command Symbolic)
deriving instance Show (Command Concrete)

data Response r
  = Created (Reference (Opaque (IORef Int)) r)
  | ReadValue Int
  | Written
  | Incremented
  deriving (Eq, Generic1, Rank2.Foldable)

deriving instance Show (Response Symbolic)
deriving instance Read (Response Symbolic)
deriving instance Show (Response Concrete)

newtype Model r = Model [(Reference (Opaque (IORef Int)) r, Int)]
  deriving (Generic, Show)

instance ToExpr (Model Symbolic)
instance ToExpr (Model Concrete)

initModel :: Model r
initModel = Model empty

transition :: Eq1 r => Model r -> Command r -> Response r -> Model r
transition m@(Model model) cmd resp = case (cmd, resp) of
  (Create, Created ref)        -> Model ((ref, 0) : model)
  (Read _, ReadValue _)        -> m
  (Write ref x, Written)       -> Model (update ref x model)
  (Increment ref, Incremented) -> case lookup ref model of
    Just i  -> Model (update ref (succ i) model)
    Nothing -> error "transition: increment"
  _                            -> error "transition: impossible."

update :: Eq a => a -> b -> [(a, b)] -> [(a, b)]
update ref i m = (ref, i) : filter ((/= ref) . fst) m

precondition :: Model Symbolic -> Command Symbolic -> Logic
precondition (Model m) cmd = case cmd of
  Create        -> Top
  Read  ref     -> ref `member` domain m
  Write ref _   -> ref `member` domain m
  Increment ref -> ref `member` domain m

postcondition :: Model Concrete -> Command Concrete -> Response Concrete -> Logic
postcondition (Model m) cmd resp = case (cmd, resp) of
  (Create,        Created ref) -> m' ! ref .== 0 .// "Create"
    where
      Model m' = transition (Model m) cmd resp
  (Read ref,      ReadValue v)  -> v .== m ! ref .// "Read"
  (Write _ref _x, Written)      -> Top
  (Increment _ref, Incremented) -> Top
  _                             -> Bot

data Bug
  = None
  | Logic
  | Race
  | Crash
  | CrashAndLogic
  deriving Eq

semantics :: Bug -> Command Concrete -> IO (Response Concrete)
semantics bug cmd = case cmd of
  Create        -> Created     <$> (reference . Opaque <$> newIORef 0)
  Read ref      -> ReadValue   <$> readIORef  (opaque ref)
  Write ref i   ->
    case bug of

      -- One of the problems is a bug that writes a wrong value to the
      -- reference.
      Logic | i `elem` [5..10] -> Written <$ writeIORef (opaque ref) (i + 1)

      -- There's also the possibility that the program gets killed or crashes.
      Crash -> do
        bool <- randomIO
        if bool
        then do
          error "Crash before writing!"
          -- Written <$ writeIORef (opaque ref) i
        else do
          writeIORef (opaque ref) i
          error "Crash after writing!"
      CrashAndLogic -> do
        writeIORef (opaque ref) (i + 1)
        error "Crash after writing!"

      _otherwise -> Written <$ writeIORef (opaque ref) i
  Increment ref -> do
    -- Another problem is that we introduce a possible race condition
    -- when incrementing.
    if bug == Race
    then do
      i <- readIORef (opaque ref)
      threadDelay =<< randomRIO (0, 5000)
      writeIORef (opaque ref) (i + 1)
    else
      atomicModifyIORef' (opaque ref) (\i -> (i + 1, ()))
    return Incremented

mock :: Model Symbolic -> Command Symbolic -> GenSym (Response Symbolic)
mock (Model m) cmd = case cmd of
  Create      -> Created   <$> genSym
  Read ref    -> ReadValue <$> pure (m ! ref)
  Write _ _   -> pure Written
  Increment _ -> pure Incremented

generator :: Model Symbolic -> Maybe (Gen (Command Symbolic))
generator m@(Model []) = Just (genCreate m)
generator m            = Just $ frequency
  [ (1, genCreate m)
  , (4, genWrite m)
  , (4, genRead m)
  , (4, genIncr m)
  ]

genCreate, genRead, genWrite, genIncr :: Model Symbolic -> Gen (Command Symbolic)
genCreate _model        = return Create
genRead   (Model model) = Read  <$> elements (domain model)
genWrite  (Model model) = Write <$> elements (domain model) <*> arbitrary
genIncr   (Model model) = Increment <$> elements (domain model)

shrinker :: Model Symbolic -> Command Symbolic -> [Command Symbolic]
shrinker _ (Write ref i) = [ Write ref i' | i' <- shrink i ]
shrinker _ _             = []

sm :: Bug -> StateMachine Model Command IO Response
sm bug = StateMachine initModel transition precondition postcondition
           Nothing generator shrinker (semantics bug) mock

prop_sequential :: Bug -> Property
prop_sequential bug = forAllCommands sm' Nothing $ \cmds -> monadicIO $ do
  (hist, _model, res) <- runCommands sm' cmds
  prettyCommands sm' hist (saveCommands "/tmp" cmds
                             (checkCommandNames cmds (res === Ok)))
    where
      sm' = sm bug

prop_runSavedCommands :: Bug -> FilePath -> Property
prop_runSavedCommands bug fp = monadicIO $ do
  (_cmds, hist, _model, res) <- runSavedCommands (sm bug) fp
  prettyCommands (sm bug) hist (res === Ok)

prop_parallel :: Bug -> Property
prop_parallel bug = forAllParallelCommands sm' $ \cmds -> monadicIO $ do
  prettyParallelCommands cmds =<< runParallelCommands sm' cmds
    where
      sm' = sm bug

prop_parallel' :: Bug -> Property
prop_parallel' bug = forAllParallelCommands sm' $ \cmds -> monadicIO $ do
  prettyParallelCommands cmds =<< runParallelCommands' sm' complete cmds
    where
      sm' = sm bug
      complete :: Command Concrete -> Response Concrete
      complete Create       = Created (error "This reference will never be used.")

      complete Read {}      = ReadValue 0 -- Doesn't matter what value we read.
      complete Write {}     = Written
      complete Increment {} = Incremented

prop_nparallel :: Bug -> Int -> Property
prop_nparallel bug np = forAllNParallelCommands sm' np $ \cmds -> monadicIO $ do
  prettyNParallelCommands cmds =<< runNParallelCommands sm' cmds
    where
      sm' = sm bug

prop_precondition :: Property
prop_precondition = once $ monadicIO $ do
  (hist, _model, res) <- runCommands sm' cmds
  prettyCommands sm' hist
    (res === PreconditionFailed "PredicateC (NotMember (Reference (Symbolic (Var 0))) [])")
    where
      sm'  = sm None
      cmds = Commands
        [ Types.Command (Read (Reference (Symbolic (Var 0)))) (ReadValue 0) [] ]

prop_existsCommands :: Property
prop_existsCommands = existsCommands sm' gens $ \cmds -> monadicIO $ do
  (hist, _model, res) <- runCommands sm' cmds
  prettyCommands sm' hist (checkCommandNames cmds (res === Ok))
  where
    sm'  = sm None
    gens =
      [ genCreate
      , genWrite
      , genIncr
      , genRead
      ]

{-------------------------------------------------------------------------------
  Meta properties which test the testing framework.
-------------------------------------------------------------------------------}

prop_pairs_shrink_parallel_equivalence :: Property
prop_pairs_shrink_parallel_equivalence =
    forAllParallelCommands (sm None) $ \pairCmds ->
      let pairShrunk = shrinkParallelCommands (sm None) pairCmds
          listCmds = Types.fromPair' pairCmds
          listShrunk = shrinkNParallelCommands (sm None) listCmds
          listShrunkPair = Types.toPairUnsafe' <$> listShrunk
      in listShrunkPair === pairShrunk

prop_pairs_shrinkAndValidate_equivalence :: Property
prop_pairs_shrinkAndValidate_equivalence =
    forAllParallelCommands (sm None) $ \pairCmds ->
      let pairShrunk' = shrinkAndValidateParallel (sm None) DontShrink pairCmds
          listCmds = Types.fromPair' pairCmds
          listShrunk' = shrinkAndValidateNParallel (sm None) DontShrink listCmds
          listShrunkPair' = Types.toPairUnsafe' <$> listShrunk'
      in listShrunkPair' === pairShrunk'

prop_pairs_shrink_parallel :: Property
prop_pairs_shrink_parallel =
    forAllParallelCommands (sm None) $ \cmds@(Types.ParallelCommands prefix suffixes) ->
      let pair =
            [ Shrunk s (Types.ParallelCommands prefix' (map Types.toPair suffixes'))
            | Shrunk s (prefix', suffixes') <- shrinkPairS shrinkCommands' (shrinkListS (shrinkPairS' shrinkCommands'))
                (prefix, map Types.fromPair suffixes)]
          (Types.ParallelCommands _ listSuffixes) = Types.fromPair' cmds
          list =
            [ Shrunk s $ Types.toPairUnsafe' (Types.ParallelCommands prefix' suffixes')
            | Shrunk s (prefix', suffixes') <- shrinkPairS shrinkCommands' (shrinkListS (shrinkListS'' shrinkCommands'))
                (prefix, listSuffixes)]
      in list == pair
