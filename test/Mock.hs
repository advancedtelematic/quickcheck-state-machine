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

module Mock
    ( prop_sequential_mock
    , prop_parallel_mock
    , prop_nparallel_mock
    )
    where

import           Control.Concurrent
import           Control.Monad.IO.Class
                   (liftIO)
import           GHC.Generics
                   (Generic, Generic1)
import           Prelude
import           Test.QuickCheck
import           Test.QuickCheck.Monadic
                   (monadicIO)
import           Test.StateMachine
import           Test.StateMachine.DotDrawing
import qualified Test.StateMachine.Types.Rank2 as Rank2


data Command r
  = Create
  deriving (Eq, Generic1, Rank2.Functor, Rank2.Foldable, Rank2.Traversable, CommandNames)

deriving instance Show (Command Symbolic)
deriving instance Read (Command Symbolic)
deriving instance Show (Command Concrete)

data Response r
  = Created (Reference Int r)
  | NotCreated
  deriving (Eq, Generic1, Rank2.Foldable)

deriving instance Show (Response Symbolic)
deriving instance Read (Response Symbolic)
deriving instance Show (Response Concrete)

data Model r = Model {
      refs :: [Reference Int r]
    , c    :: Int
    }
  deriving (Generic, Show)

instance ToExpr (Model Symbolic)
instance ToExpr (Model Concrete)

initModel :: Model r
initModel = Model [] 0

transition :: Model r -> Command r -> Response r -> Model r
transition m@Model{..} cmd resp = case (cmd, resp, c) of
  (Create, Created ref, 0) -> Model (ref : refs) 1
  (Create, _, _)           -> m

precondition :: Model Symbolic -> Command Symbolic -> Logic
precondition _ cmd = case cmd of
    Create        -> Top

postcondition :: Model Concrete -> Command Concrete -> Response Concrete -> Logic
postcondition _ _ _ = Top

semantics :: MVar Int -> Command Concrete -> IO (Response Concrete)
semantics counter cmd = case cmd of
  Create        -> do
    c <- modifyMVar counter (\x -> return (x + 1, x))
    case c of
        0 -> return $ Created $ reference c
        _ -> return NotCreated

mock :: Model Symbolic -> Command Symbolic -> GenSym (Response Symbolic)
mock Model{..} cmd = case (cmd, c) of
  (Create, 0) -> Created   <$> genSym
  (Create, _) -> return NotCreated

generator :: Model Symbolic -> Maybe (Gen (Command Symbolic))
generator _            = Just $ frequency
    [(1, return Create)]

shrinker :: Model Symbolic -> Command Symbolic -> [Command Symbolic]
shrinker _ _ = []

sm :: MVar Int ->  StateMachine Model Command IO Response
sm counter = StateMachine initModel transition precondition postcondition
        Nothing generator shrinker (semantics counter) mock noCleanup

smUnused :: StateMachine Model Command IO Response
smUnused = sm undefined

prop_sequential_mock :: Property
prop_sequential_mock = forAllCommands smUnused Nothing $ \cmds -> monadicIO $ do
  counter <- liftIO $ newMVar 0
  (hist, _model, res) <- runCommands (sm counter) cmds
  prettyCommands smUnused hist (res === Ok)

prop_parallel_mock :: Property
prop_parallel_mock = forAllParallelCommands smUnused $ \cmds -> monadicIO $ do
    counter <- liftIO $ newMVar 0
    ret <- runParallelCommandsNTimes 1 (sm counter) cmds
    prettyParallelCommandsWithOpts cmds opts ret
      where opts = Just $ GraphOptions "mock.png" Png

prop_nparallel_mock :: Property
prop_nparallel_mock = forAllNParallelCommands smUnused 3 $ \cmds -> monadicIO $ do
    counter <- liftIO $ newMVar 0
    ret <- runNParallelCommandsNTimes 1 (sm counter) cmds
    prettyNParallelCommandsWithOpts cmds opts ret
      where opts = Just $ GraphOptions "mock-np.png" Png
