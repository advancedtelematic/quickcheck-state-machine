{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module SQLite
    ( prop_sequential_sqlite
    , prop_parallel_sqlite
    ) where

import           Control.Concurrent
import           Control.Concurrent.STM
import           Control.Exception
import           Control.Monad.IO.Class  (MonadIO, liftIO)
import           Control.Monad.IO.Unlift (MonadUnliftIO, withRunInIO)
import           Control.Monad.Logger
import           Control.Monad.Reader
import           Data.Bifoldable
import           Data.Bifunctor
import qualified Data.Bifunctor.TH as TH
import           Data.Bitraversable
import           Data.Functor.Classes
import           Data.Kind (Type)
import           Data.List hiding (insert)
import           Data.Maybe (fromMaybe)
import           Data.Pool
import           Data.Text (Text)
import           Data.TreeDiff.Expr
import           Database.Persist
import           Database.Persist.Sqlite
import           Database.Sqlite hiding (step)
import           GHC.Generics (Generic, Generic1)
import           Prelude
import           System.Directory
import           Test.QuickCheck
import           Test.QuickCheck.Monadic
import           Test.StateMachine
import           Test.StateMachine.DotDrawing
import           Test.StateMachine.Types
import qualified Test.StateMachine.Types.Rank2 as Rank2

import           Schema

newtype At t r = At {unAt :: t (PRef r) (CRef r)}
    deriving (Generic)

type PRef = Reference (Key Person)
type CRef = Reference (Key Car)

deriving instance Show1 r => Show (At Resp r)
deriving instance Show1 r => Show (At Cmd r)
deriving instance Eq1   r => Eq   (At Resp r)

data TableEntity = TPerson Person
                 | TCar Car
                 deriving (Eq, Show, Ord)

data Tag = SPerson | SCar
    deriving (Eq, Show)

data Cmd kp kh =
      Insert TableEntity
    | SelectList Tag
    deriving (Show, Generic1)

data Model (r :: Type -> Type) = Model
    { dbModel :: DBModel
    , knownPerson :: [(PRef r, Int)]
    , knownCars   :: [(CRef r, Int)]
    } deriving (Generic, Show)

data DBModel = DBModel {
            persons       :: [(Int, Person)]
          , nextPerson    :: Int
          , cars          :: [(Int, Car)]
          , nextCar       :: Int
          } deriving (Generic, Show)

initModelImpl :: Model r
initModelImpl = Model (DBModel [] 0 [] 0) [] []

newtype Resp kp kc = Resp {getResp :: Either SqliteException (Success kp kc)}
    deriving (Show, Generic1)

instance (Eq kp, Eq kc) => Eq (Resp kp kc) where
    (Resp (Left e1)) == (Resp (Left e2)) = seError e1 == seError e2
    (Resp (Right r1)) == (Resp (Right r2)) = r1 == r2
    _ == _ = False

getPers :: Resp kp kc -> [kp]
getPers (Resp (Right (InsertedPerson kp))) = [kp]
getPers _ = []

getCars :: Resp kp kc -> [kc]
getCars (Resp (Right (InsertedCar kc))) = [kc]
getCars _ = []

data Success kp kc =
    Unit ()
  | InsertedPerson kp
  | InsertedCar kc
  | List [TableEntity]
  deriving (Show, Eq, Generic1)

data Event r = Event
  { eventBefore   :: Model  r
  , eventCmd      :: At Cmd r
  , eventAfter    :: Model  r
  , eventMockResp :: Resp Int Int
  }

lockstep :: forall  r. (Show1 r, Ord1 r)
         => Model   r
         -> At Cmd  r
         -> At Resp r
         -> Event   r
lockstep model@Model {..} cmd resp = Event
    { eventBefore   = model
    , eventCmd      = cmd
    , eventAfter    = Model {
                        dbModel = dbModel'
                      , knownPerson = union' knownPerson newPerson
                      , knownCars = union' knownCars newCars
                    }
    , eventMockResp = mockResp
    }
  where
    (mockResp, dbModel') = step model cmd
    newPerson = zip (getPers $ unAt resp) (getPers mockResp)
    newCars = zip (getCars $ unAt resp) (getCars mockResp)

union' :: forall k v. (Eq k, Eq v, Show k, Show v)
              => [(k, v)] -- Mapping known to have duplicate keys
              -> [(k, v)] -- With potential duplicates
              -> [(k, v)]
union' acc []             = acc
union' acc ((k, v) : kvs) =
    case lookup k acc of
      Just v' | v /= v' -> error $ renderError v'
      _otherwise        -> union' ((k, v) : acc) kvs
  where
    renderError :: v -> String
    renderError v' = unwords [
          "Key"
        , show k
        , "with two different values"
        , show v
        , "and"
        , show v'
        ]

toMock :: Eq1 r => Model r -> At Resp r -> Resp Int Int
toMock Model{..} (At r) =
   bimap (\p -> fromMaybe (error "could not find person ref") $ lookup p knownPerson)
         (\c -> fromMaybe (error "could not find car ref") $ lookup c knownCars) r

canInsertP :: Person -> [Person] -> Bool
canInsertP p ps =  personName p `notElem` (personName <$> ps)

canInsertC :: Car -> [Car] -> Bool
canInsertC c cs = carCid c `notElem` (carCid <$> cs)

step :: Model r
     -> At Cmd r
     -> (Resp Int Int, DBModel)
step Model{..} =  runPure dbModel

runPure :: DBModel -> At Cmd r -> (Resp Int Int, DBModel)
runPure dbModel@DBModel{..} cmd  = case unAt cmd of
    Insert (TPerson person) ->
        if canInsertP person $ snd <$> persons
            then (Resp $ Right $ InsertedPerson nextPerson, dbModel{persons = (nextPerson, person) : persons, nextPerson = nextPerson + 1})
            else (Resp $ Left $ SqliteException ErrorConstraint ""  "constraint error Primary Key", dbModel)
    Insert (TCar car) -> if canInsertC car $ snd <$> cars
        then if carOwner car `elem` (PersonKey . personName . snd <$> persons)
                then (Resp $ Right $ InsertedCar nextCar, dbModel{cars = (nextCar, car) : cars, nextCar = nextCar + 1})
                else (Resp $ Left $ SqliteException ErrorConstraint ""  "constraint error Foreign Key", dbModel)
        else (Resp $ Left $ SqliteException ErrorConstraint ""  "constraint error Primary Key", dbModel)
    SelectList SPerson ->
        (Resp $ Right $ List $ TPerson . snd <$> persons, dbModel)
    SelectList SCar ->
        (Resp $ Right $ List $ TCar . snd <$> cars, dbModel)

mockImpl :: Model Symbolic -> At Cmd Symbolic -> GenSym (At Resp Symbolic)
mockImpl model cmdErr = At <$> bitraverse (const genSym) (const genSym) mockResp
    where
        (mockResp, _model') = step model cmdErr

shrinkerImpl :: Model Symbolic -> At Cmd Symbolic -> [At Cmd Symbolic]
shrinkerImpl _ _ = []

semanticsImpl ::  MonadIO m => AsyncWithPool SqlBackend -> MVar () -> At Cmd Concrete -> m (At Resp Concrete)
semanticsImpl poolBackend _lock cmd = At . Resp <$>
    case unAt cmd of
        Insert (TPerson person) -> do
            ret <- liftIO $ try $ runNoLoggingT $ flip runSqlAsyncWrite poolBackend $
                    insert person
            case ret of
                Right key -> return $ Right $ InsertedPerson $ reference key
                Left (e :: SqliteException) ->
                    return  $ Left e
        Insert (TCar car) -> do
            ret <- liftIO $ try $ runNoLoggingT $ flip runSqlAsyncWrite poolBackend $
                    insert car
            case ret of
                Right key -> return $ Right $ InsertedCar $ reference key
                Left (e :: SqliteException) ->
                    return $ Left e
        SelectList ts -> do
            ret <- liftIO $ try $ runNoLoggingT $ flip runSqlAsyncRead poolBackend $
                case ts of
                    SPerson -> do
                        (pers :: [Entity Person]) <- selectList [] []
                        return $ TPerson . entityVal <$> pers
                    SCar -> do
                        (pers :: [Entity Car]) <- selectList [] []
                        return $ TCar . entityVal <$> pers
            case ret of
                Right ls -> return $ Right $ List ls
                Left (e :: SqliteException) ->
                    return $ Left e

preconditionImpl :: Model Symbolic -> At Cmd Symbolic -> Logic
preconditionImpl Model{..} cmd = case unAt cmd of
    Insert (TPerson p) -> Boolean $ canInsertP p (snd <$> persons dbModel)
    Insert (TCar c)    -> Boolean $ canInsertC c (snd <$> cars dbModel)
                                 && let PersonKey p = carOwner c
                                    in (p `elem` (personName . snd <$> persons dbModel))
    _                  -> Top

equalResp' :: (Eq kp, Eq kc, Show kp, Show kc) => Resp kp kc -> Resp kp kc -> Logic
equalResp' (Resp (Right _)) (Resp (Right _)) = Top
equalResp' r1 r2 = r1 .== r2

postconditionImpl :: Model Concrete -> At Cmd Concrete -> At Resp Concrete -> Logic
postconditionImpl model cmd resp =
    equalResp' (toMock (eventAfter ev) resp) (eventMockResp ev)
  where
    ev = lockstep model cmd resp

transitionImpl :: (Show1 r, Ord1 r) => Model r -> At Cmd r -> At Resp r -> Model r
transitionImpl model cmd =  eventAfter . lockstep model cmd

deriving instance ToExpr DBModel
deriving instance ToExpr (Model Concrete)

sm :: MonadIO m => String -> AsyncWithPool SqlBackend -> MVar () -> StateMachine Model (At Cmd) m (At Resp)
sm folder poolBackend lock = StateMachine {
     initModel     = initModelImpl
   , transition    = transitionImpl
   , precondition  = preconditionImpl
   , postcondition = postconditionImpl
   , invariant     = Nothing
   , generator     = generatorImpl
   , shrinker      = shrinkerImpl
   , semantics     = semanticsImpl poolBackend lock
   , mock          = mockImpl
   , cleanup       = clean folder
   }

smUnused :: StateMachine Model (At Cmd) IO (At Resp)
smUnused = sm undefined undefined undefined

generatorImpl :: Model Symbolic -> Maybe (Gen (At Cmd Symbolic))
generatorImpl Model {..} = Just $ At <$>
    frequency [ (3, Insert <$> arbitrary)
              , (3, SelectList <$> arbitrary)
              ]

instance Arbitrary TableEntity where
    arbitrary = frequency [
                  (1, TPerson <$> arbitrary)
                , (1, TCar <$> arbitrary)
                ]

instance Arbitrary Tag where
    arbitrary = frequency
        [(1, return SPerson), (1, return SCar)]

deriving instance ToExpr Person
deriving instance ToExpr (Key Person)
deriving instance Generic (Key Person)
deriving instance ToExpr Car
deriving instance Generic Person
deriving instance Generic Car
deriving instance Generic (Key Car)
instance ToExpr (Key Car) where
  toExpr key = App (show key) []

clean :: MonadIO m => String -> Model Concrete -> m ()
clean folder _ = liftIO $ removePathForcibly folder

prop_sequential_sqlite :: Property
prop_sequential_sqlite =
    forAllCommands smUnused Nothing $ \cmds -> monadicIO $ do
        liftIO $ do
            removePathForcibly "sqlite-seq"
            createDirectory "sqlite-seq"
        db <- liftIO $ runNoLoggingT $ createSqliteAsyncPool "sqlite-seq/persons.db" 5
        _ <- liftIO $ flip runSqlAsyncWrite db $ do
            _ <- runMigrationSilent $ migrate entityDefs $ entityDef (Nothing :: Maybe Person)
            runMigrationSilent $ migrate entityDefs $ entityDef (Nothing :: Maybe Car)
        lock <- liftIO $ newMVar ()
        (hist, _model, res) <- runCommands (sm "sqlite-seq" db lock)  cmds
        prettyCommands smUnused hist $ res === Ok

prop_parallel_sqlite :: Property
prop_parallel_sqlite =
    forAllParallelCommands smUnused $ \cmds -> monadicIO $ do
        liftIO $ do
            removePathForcibly "sqlite-par"
            createDirectory "sqlite-par"
        qBackend <- liftIO $ runNoLoggingT $ createSqliteAsyncPool "sqlite-par/persons.db" 5
        _ <- liftIO $ flip runSqlAsyncWrite qBackend $ do
            _ <- runMigrationSilent $ migrate entityDefs $ entityDef (Nothing :: Maybe Person)
            runMigrationSilent $ migrate entityDefs $ entityDef (Nothing :: Maybe Car)
        lock <- liftIO $ newMVar ()
        ret <- runParallelCommandsNTimes 1 (sm "sqlite-par" qBackend lock) cmds
        prettyParallelCommandsWithOpts cmds (Just $ GraphOptions "sqlite.jpeg" Jpeg) ret
        liftIO $ closeSqlAsyncPool qBackend

instance Bifoldable t => Rank2.Foldable (At t) where
  foldMap = \f (At x) -> bifoldMap (app f) (app f) x
    where
      app :: (r x -> m) -> Reference x r -> m
      app f (Reference x) = f x

instance Bifunctor t => Rank2.Functor (At t) where
  fmap = \f (At x) -> At (bimap (app f) (app f) x)
    where
      app :: (r x -> r' x) -> Reference x r -> Reference x r'
      app f (Reference x) = Reference (f x)

instance Bitraversable t => Rank2.Traversable (At t) where
  traverse = \f (At x) -> At <$> bitraverse (app f) (app f) x
    where
      app :: Functor f
          => (r x -> f (r' x)) -> Reference x r -> f (Reference x r')
      app f (Reference x) = Reference <$> f x

{-------------------------------------------------------------------------------------------
    Async
-------------------------------------------------------------------------------------------}

data AsyncQueue r = AsyncQueue
  { asyncThreadId :: !ThreadId
                  -- ^ Returns the 'ThreadId' of the thread running

  , _asyncQueue   :: TBQueue (AsyncAction r)
                  -- ^ A queue which can be used to send actions
                  -- to the thread.

  , _serves       :: (TVar Bool)

  , _resource     :: r
                  -- ^ the resource. We may not want to give AsyncQueue
                  -- access to the resource and allow only the forked thread
                  -- to have access.
  }

instance Eq (AsyncQueue a) where
    a == b = asyncThreadId a == asyncThreadId b

data AsyncAction r = forall a. AsyncAction (r -> IO a) (TMVar (Either SomeException a))

asyncQueueBound :: Int -> IO r -> IO (AsyncQueue r)
asyncQueueBound = asyncQueueUsing forkOS

asyncQueueUsing :: (IO () -> IO ThreadId) -> Int
                -> IO r -> IO (AsyncQueue r)
asyncQueueUsing doFork queueSize createResource = do
    resVar :: TMVar (Either SomeException r) <- newEmptyTMVarIO
    servesVar <- newTVarIO True
    queue <- newTBQueueIO $ fromIntegral queueSize
    t <- doFork $
            handle (atomically . putTMVar resVar . Left) $ do
                r <- createResource
                atomically $ putTMVar resVar $ Right r
                serve queue servesVar r
    res <- atomically $ takeTMVar resVar -- we don't need readTMVar, since this TMVar will be shortly gone.
    case res of
        Left e -> throwIO e
        Right r -> return $ AsyncQueue t queue servesVar r

serve :: TBQueue (AsyncAction r) -> TVar Bool -> r -> IO ()
serve queue serves resource = go
    where
        go = do
            AsyncAction action mvar <- atomically $ readTBQueue queue
            ret <- try $ action resource
            atomically $ putTMVar mvar ret
            servesNow <- readTVarIO serves
            when servesNow go

waitQueue :: AsyncQueue r -> (r -> IO a) -> IO a
waitQueue async action = do
--    putStrLn "write to queue"
    resp <- newEmptyTMVarIO
    atomically $ do
        serves <- readTVar $ _serves async
        if serves then writeTBQueue (_asyncQueue async) $ AsyncAction action resp
        else throwSTM $ userError "Doesn't serve"
    ret <- atomically $ takeTMVar resp
    case ret of
        Left e -> throwIO e
        Right a -> return a

-- This doesn't belong here
data AsyncWithPool r = AsyncWithPool {
    queue :: AsyncQueue r
  , pool  :: Pool r
  }

-- This doesn't belong here
mkAsyncWithPool :: AsyncQueue r -> Pool r -> AsyncWithPool r
mkAsyncWithPool = AsyncWithPool

-- data DoesntServeError = DoesntServeError
--       deriving (Show, Exception)

createSqliteAsyncQueue :: (MonadLogger m, MonadUnliftIO m)
                       => Text -> m (AsyncQueue SqlBackend)
createSqliteAsyncQueue str = do
    logFunc <- askLogFunc
    liftIO $ asyncQueueBound 1000 $ open' str logFunc

createSqliteAsyncPool :: (MonadLogger m, MonadUnliftIO m)
    => Text -> Int -> m (AsyncWithPool SqlBackend)
createSqliteAsyncPool str n = do
    q <- createSqliteAsyncQueue str
    p <- createSqlitePool str n
    return $ mkAsyncWithPool q p

open' :: Text -> LogFunc -> IO SqlBackend
open' str logFunc = do
    conn <- open str
    wrapConnection conn logFunc `onException` close conn

runSqlAsyncWrite :: MonadUnliftIO m => ReaderT SqlBackend m a -> AsyncWithPool SqlBackend -> m a
runSqlAsyncWrite r a = runSqlAsyncQueue r (queue a)

runSqlAsyncRead :: MonadUnliftIO m => ReaderT SqlBackend m a -> AsyncWithPool SqlBackend -> m a
runSqlAsyncRead r a = runSqlPool r $ pool a

closeSqlAsyncPool :: AsyncWithPool SqlBackend -> IO ()
closeSqlAsyncPool (AsyncWithPool q p) = do
    closeSqlAsyncQueue q
    destroyAllResources p

runSqlAsyncQueue :: MonadUnliftIO m => ReaderT SqlBackend m a -> AsyncQueue SqlBackend -> m a
runSqlAsyncQueue r q = withRunInIO $ \run' ->
    waitQueue q $ run' . runSqlConn r

closeSqlAsyncQueue :: AsyncQueue SqlBackend -> IO ()
closeSqlAsyncQueue q = waitQueue q close'

TH.deriveBifunctor     ''Success
TH.deriveBifoldable    ''Success
TH.deriveBitraversable ''Success

TH.deriveBifunctor     ''Resp
TH.deriveBitraversable ''Resp
TH.deriveBifoldable    ''Resp

TH.deriveBifunctor     ''Cmd
TH.deriveBifoldable    ''Cmd
TH.deriveBitraversable ''Cmd
