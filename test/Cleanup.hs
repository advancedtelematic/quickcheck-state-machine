{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE ExplicitNamespaces   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE MonoLocalBinds       #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}

module Cleanup (
    Bug (..)
  , DoubleCleanup (..)
  , FinalTest (..)
  , prop_sequential_clean
  , prop_parallel_clean
  , prop_nparallel_clean
  ) where

import           Control.Concurrent.MVar
import           Control.Exception
import           Control.Monad
import           Control.Monad.IO.Class
import           Data.Functor.Classes
                   (Ord1, Show1)
import           Data.List
                   ((\\))
import           Data.Map.Strict
                   (Map)
import qualified Data.Map.Strict as Map
import           Prelude
import           System.Directory
import           System.IO
import           Test.QuickCheck
import           Test.QuickCheck.Monadic
                  (monadicIO)
import           GHC.Generics
                   (Generic, Generic1)
import           Test.StateMachine
import           Test.StateMachine.Types
                   (Reference(..), Symbolic(..))
import qualified Test.StateMachine.Types.Rank2 as Rank2
import           Test.StateMachine.Utils
                   (liftProperty, mkModel, whenFailM)
import           Text.Show.Pretty
                   (ppShow)
import           System.Random

{-----------------------------------------------------------------------------------
  This example in mainly used to check how well cleanup of recourses works. In our
  case recourses are files created on the @testDirectory@ (not open handles, just
  files). So it is easy, by the end of the tests to test if there any any recourses
  which are not cleaned up, by the end of the tests.

  We also test different scenarios, like injected exceptions in semantics
  (before and after the recourse is created). Tests also reveal what happens when
  cleaning up a recourse for the second time is not a no-op.

-----------------------------------------------------------------------------------}
data Command r
  = Create String
  | Delete (Reference (Opaque FileRef) r)
  | Ls
  | Write Int
  | Increment
  deriving (Eq, Generic1, Rank2.Functor, Rank2.Foldable, Rank2.Traversable, CommandNames)

deriving instance Show (Command Symbolic)
deriving instance Read (Command Symbolic)
deriving instance Show (Command Concrete)

data Response r
  = Created (Reference (Opaque FileRef) r)
  | Deleted
  | Contents [String]
  | ChangedValue Int
  deriving (Eq, Generic1, Rank2.Foldable)

deriving instance Show (Response Symbolic)
deriving instance Read (Response Symbolic)
deriving instance Show (Response Concrete)

data Model r = Model {
      files   :: Map (Reference (Opaque FileRef) r) String
    , counter :: Int
    , semanticsCounter :: Opaque (MVar Int)
    , ref     :: Opaque (MVar Int)
    , value   :: Int
  }
  deriving (Generic, Show, Eq)

instance ToExpr (Model Symbolic)
instance ToExpr (Model Concrete)

initModel :: MVar Int -> MVar Int -> Model r
initModel sc ref = Model Map.empty 0 (Opaque sc) (Opaque ref) 0

transition :: Ord1 r => Model r -> Command r -> Response r -> Model r
transition m@Model {..} cmd resp = case (cmd, resp) of
    (Create p, Created rf)      -> m {files = Map.insert rf p files, counter = counter + 1}
    (Delete rf, Deleted)        -> m {files = Map.delete rf files}
    (Ls, Contents _)            -> m
    (Write n, ChangedValue _)   -> m {value = n}
    (Increment, ChangedValue _) -> m {value = value + 1}
    _                           -> error "transition impossible"

precondition :: Model Symbolic -> Command Symbolic -> Logic
precondition Model {..} cmd = case cmd of
    Create p   -> Boolean $ notElem p (Map.elems files)
    Delete rf  -> Boolean $ Map.member rf files
    Ls         -> Top
    Write _    -> Top
    Increment  -> Top

sameElements :: Eq a => [a] -> [a] -> Bool
sameElements x y = null (x \\ y) && null (y \\ x)

postcondition :: Model Concrete -> Command Concrete -> Response Concrete -> Logic
postcondition  Model{..} cmd resp = case (cmd, resp) of
  (Create _,      Created _)  -> Top
  (Delete _, Deleted)         -> Top
  (Ls, Contents ls)           -> if sameElements ls (Map.elems files) then Top
        else Annotate ("Not same elements between " ++ show ls ++ "and " ++ show (Map.elems files)) Bot
  (Increment, ChangedValue _) -> Top
  (Write n, ChangedValue m)   -> m .== n
  _                           -> Bot

data MVarC a = MVarC (MVar a) Int
type FileRef = MVarC (String, Bool)

removeFileRef :: DoubleCleanup -> FileRef -> IO ()
removeFileRef dc (MVarC r _) = modifyMVar_ r $ \(file, isHere) -> do
      case (isHere, dc) of
        (_, ReDo) -> removeFile file
        (True, _) -> removeFile file
        (False, NoOp) -> return ()
      return (file, False)

instance Eq (MVarC a) where
    MVarC _ a == MVarC _ b = a == b

instance Ord (MVarC a) where
    compare (MVarC _ a) (MVarC _ b) = compare a b

semantics :: MVar Int -> MVar Int -> String -> Bug -> Command Concrete -> IO (Response Concrete)
semantics counter ref tstDir bug cmd = case cmd of
    Create f  -> createFile f
            `onException` removePathForcibly (makePath tstDir f)
    Delete rf -> do
        let MVarC lockedFile _ = unOpaque $ concrete rf
        modifyMVar_ lockedFile $ \(file, _) -> do
            removeFile file
            return (file, False)
        return Deleted
    Ls        -> do
        ls <- listDirectory tstDir
        return $ Contents ls
    Write n   ->
        modifyMVar ref (\_ -> return (n, ChangedValue n))
    Increment ->
        modifyMVar ref (\m -> return (m + 1, ChangedValue $ m + 1))
    where
        createFile :: String -> IO (Response Concrete)
        createFile f = do
            let path = makePath tstDir f
            c <- modifyMVar counter $ \n -> return (n + 1, n)
            when (c > 3 && bug == Exception) $
                throwIO $ userError "semantics injected bug"
            withFile path WriteMode (\_ -> return ())
            when (c > 3 && bug == ExcAfter) $
                throwIO $ userError "semantics injected bug"
            rf <- newMVar (path, True)
            return $ Created $ reference $ Opaque $ MVarC rf c

mock :: Model Symbolic -> Command Symbolic -> GenSym (Response Symbolic)
mock Model{..} cmd = case cmd of
    Create _  -> Created <$> genSym
    Delete _  -> return Deleted
    Ls        -> return $ Contents $ Map.elems files
    Write n   -> return $ ChangedValue n
    Increment -> return $ ChangedValue $ value + 1

generator :: Model Symbolic -> Maybe (Gen (Command Symbolic))
generator Model{..} = Just $ do
    n <- choose (1,10)
    frequency
        [ (7, return $ Create $ mkFileName counter)
        , (if Map.null files then 0 else 3, Delete . fst <$> elements (Map.toList files))
        , (1, return Ls)
        , (1, return $ Write n)
        , (1, return Increment)
        ]

shrinker :: Model Symbolic -> Command Symbolic -> [Command Symbolic]
shrinker _ _             = []

cleanup :: String -> DoubleCleanup -> Model Concrete -> IO ()
cleanup testDir dc Model{..} = do
    let cl = do
            forM_ (Map.keys files) $ \rf ->
                removeFileRef dc $ unOpaque $ concrete rf
            modifyMVar_ (unOpaque semanticsCounter) (\_ -> return 0)
            modifyMVar_ (unOpaque ref) (\_ -> return 0)
    -- onException here does not affect any tests. It just makes sure
    -- no leftover directories remain after the end of tests.
    -- We have it here, because we found no other way to handle the
    -- exceptions in the ProperyM level.
    cl `onException` removePathForcibly testDir

sm :: MVar Int -> MVar Int -> String -> Bug -> DoubleCleanup -> StateMachine Model Command IO Response
sm counter ref tstDir bug dc = StateMachine (initModel counter ref) transition precondition postcondition
           Nothing generator shrinker (semantics counter ref tstDir bug) mock (cleanup tstDir dc)

smUnused :: StateMachine Model Command IO Response
smUnused = sm undefined undefined undefined undefined undefined

prop_sequential_clean :: FinalTest -> Bug -> DoubleCleanup -> Property
prop_sequential_clean testing bug dc = forAllCommands smUnused Nothing $ \cmds -> monadicIO $ do
    folderId :: Word <- liftIO randomIO
    let testDir = testDirectoryBase ++ "-" ++ show folderId
    liftIO $ do
        removePathForcibly testDir
        createDirectory testDir
    c <- liftIO $ newMVar 0
    ref <- liftIO $ newMVar 0
    let sm' = sm c ref testDir bug dc
    (hist, model, res) <- runCommands sm' cmds
    ls <- liftIO $ listDirectory testDir
    liftIO $ removePathForcibly testDir
    case testing of
        Regular -> prettyCommands sm' hist $ checkCommandNames cmds (res === Ok)
        Files   -> printFiles ls `whenFailM` (ls === [])
        Eq _    -> liftProperty $ mkModel sm' hist === model

prop_parallel_clean :: FinalTest -> Bug -> DoubleCleanup -> Property
prop_parallel_clean testing bug dc = forAllParallelCommands smUnused Nothing $ \cmds -> monadicIO $ do
    folderId :: Word <- liftIO randomIO
    let testDir = testDirectoryBase ++ "-" ++ show folderId
    liftIO $ do
        removePathForcibly testDir
        createDirectory testDir
    c <- liftIO $ newMVar 0
    ref <- liftIO $ newMVar 0
    let sm' = sm c ref testDir bug dc
    ret <- runParallelCommandsNTimes 2 sm' cmds
    ls <- liftIO $ listDirectory testDir
    liftIO $ removePathForcibly testDir
    case testing of
        Regular -> prettyParallelCommands cmds ret
        Files   -> printFiles ls `whenFailM` (ls === [])
        Eq bl   -> do
            let (a, b) = case mkModel sm' . fst <$> ret of
                    (x : y : _) -> (x,y)
                    _           -> error "expected at least two histories"
            liftProperty $ printModels a b `whenFail`
                property (modelEquivalence bl a b)

prop_nparallel_clean :: Int -> FinalTest -> Bug -> DoubleCleanup -> Property
prop_nparallel_clean np testing bug dc = forAllNParallelCommands smUnused np $ \cmds -> monadicIO $ do
    folderId :: Word <- liftIO randomIO
    let testDir = testDirectoryBase ++ "-" ++ show folderId
    liftIO $ do
        removePathForcibly testDir
        createDirectory testDir
    c <- liftIO $ newMVar 0
    ref <- liftIO $ newMVar 0
    let sm' = sm c ref testDir bug dc
    ret <- runNParallelCommandsNTimes 2 sm' cmds
    ls <- liftIO $ listDirectory testDir
    liftIO $ removePathForcibly testDir
    case testing of
        Regular -> prettyNParallelCommands cmds ret
        Files   -> printFiles ls `whenFailM` (ls === [])
        Eq bl   -> do
            let (a, b) = case mkModel sm' . fst <$> ret of
                    (x : y : _) -> (x,y)
                    _           -> error "expected at least two histories"
            liftProperty $ printModels a b `whenFail`
                property (modelEquivalence bl a b)

printModels :: Show1 r => Model r -> Model r -> IO ()
printModels a b =
    putStrLn $ "Models are not equivalent: \n" ++ ppShow a ++ " \nand \n" ++ ppShow b

printFiles :: [String] -> IO ()
printFiles ls' =
    putStrLn $ "Cleanup was not complete. Found files " ++ show ls'

data Bug = NoBug
         | Exception
         | ExcAfter
         deriving (Eq, Show)

data DoubleCleanup = NoOp
                   | ReDo
                   deriving (Eq, Show)

data FinalTest = Regular
               | Files
               | Eq Bool
                 deriving (Eq, Show)

-- | This is meant to be used, in order to test equality of two
-- Models, created by two different executions of the same program.
-- Note that we don't test reference equality. This is because
-- different executions in the parallel case, may create references
-- with different order, so the counter assigned by the semantics
-- can be different.
modelEquivalence :: Bool -> Model Concrete -> Model Concrete -> Bool
modelEquivalence bl a b =
    sameElements (Map.elems $ files a) (Map.elems $ files b)
    && counter a == counter b
    && (not bl || value a == value b)

makePath :: String -> String -> String
makePath tstDir file = tstDir ++ "/" ++ file

mkFileName :: Int -> String
mkFileName n = "file" ++ show n

testDirectoryBase :: String
testDirectoryBase = "cleanup-test-folder"
