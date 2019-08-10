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


module Overflow
  ( prop_sequential_overflow
  , prop_parallel_overflow
  , prop_nparallel_overflow
  ) where

import           Control.Concurrent (threadDelay)
import           Control.Concurrent.MVar
import           Control.Monad
import           Data.Int
import           GHC.Generics
                   (Generic, Generic1)
import           Prelude
import           System.Random
                   (randomRIO)
import           Test.QuickCheck
import           Test.QuickCheck.Monadic (monadicIO)
import           Test.StateMachine
import           Test.StateMachine.DotDrawing
import           Test.StateMachine.Types(Reference(..), Symbolic(..))
import qualified Test.StateMachine.Types.Rank2 as Rank2

-- The Model is a set of references of Int8. Command BackAndForth picks a random reference and adds a
-- constant number (in an atomic way) and then substract the same number (in an atomic way).
-- If there are enough threads (4 in this case) the result can overflow.

data Command r
  = Create
  | Check (Reference (Opaque (MVar Int8)) r)
  | BackAndForth Int (Reference (Opaque (MVar Int8)) r)
  deriving (Eq, Generic1, Rank2.Functor, Rank2.Foldable, Rank2.Traversable, CommandNames)

deriving instance Show (Command Symbolic)
deriving instance Read (Command Symbolic)
deriving instance Show (Command Concrete)

data Response r
    = Created (Reference (Opaque (MVar Int8)) r)
    | IsNegative Bool
    | Unit
    deriving (Eq, Generic1, Rank2.Foldable)

deriving instance Show (Response Symbolic)
deriving instance Read (Response Symbolic)
deriving instance Show (Response Concrete)

newtype Model r = Model [(Reference (Opaque (MVar Int8)) r, Int8)]
  deriving (Generic, Show)

getVars :: Model r -> [Reference (Opaque (MVar Int8)) r]
getVars (Model ls) = fst <$> ls

instance ToExpr (Model Symbolic)
instance ToExpr (Model Concrete)

initModel :: Model r
initModel = Model []

transition :: Model r -> Command r -> Response r -> Model r
transition m@(Model model) cmd resp = case (cmd, resp) of
  (Create, Created var)    -> Model ((var, 0) : model)
  (Check _, IsNegative _)  -> m
  (BackAndForth _ _, Unit) -> m
  _                        -> error "impossible to transition!"

precondition :: Model Symbolic -> Command Symbolic -> Logic
precondition m cmd = case cmd of
  Create             -> Top
  Check var          -> var `member` getVars m
  BackAndForth _ var -> var `member` getVars m

postcondition :: Model Concrete -> Command Concrete -> Response Concrete -> Logic
postcondition _ cmd resp = case (cmd, resp) of
  (Create, Created _)      -> Top
  (Check _, IsNegative bl) -> bl .== False
  (BackAndForth _ _, Unit) -> Top
  _                        -> Bot

semantics :: Command Concrete -> IO (Response Concrete)
semantics cmd = case cmd of
  Create        -> Created <$> (reference . Opaque <$> newMVar 0)
  Check var     -> do
    val <- readMVar (opaque var)
    return $ IsNegative $ val < 0
  BackAndForth n var -> do
    modifyMVar_ (opaque var) $ \x -> return $ x + fromIntegral n
    threadDelay =<< randomRIO (0, 5000)
    modifyMVar_ (opaque var) $ \x -> return $ x - fromIntegral n
    return Unit

mock :: Model Symbolic -> Command Symbolic -> GenSym (Response Symbolic)
mock _ cmd = case cmd of
  Create           -> Created <$> genSym
  Check _var       -> return $ IsNegative False
  BackAndForth _ _ -> return $ Unit

generator :: Model Symbolic -> Maybe (Gen (Command Symbolic))
generator (Model []) = Just (return Create)
generator m          = Just $ frequency
                [ (1, return Create)
                , (3, genBackAndForth m)
                , (3, genCheck m)
                ]

genCheck :: Model Symbolic -> Gen (Command Symbolic)
genCheck m =
  Check <$> elements (getVars m)

genBackAndForth :: Model Symbolic -> Gen (Command Symbolic)
genBackAndForth m = do
  -- The upper limit here must have the property 2 * n < 128 <= 3 * n, so that
  -- there is a counter example for >= 4 threads.
  -- The lower limit only affects how fast a counterexample will be found.
  n <- choose (30,60)
  BackAndForth n <$> elements (getVars m)

shrinker :: Model Symbolic -> Command Symbolic -> [Command Symbolic]
shrinker _ (BackAndForth n var) = [ BackAndForth n' var | n' <- shrink n ]
shrinker _ _                    = []

sm :: StateMachine Model Command IO Response
sm = StateMachine initModel transition precondition postcondition
           Nothing generator shrinker semantics mock noCleanup

prop_sequential_overflow :: Property
prop_sequential_overflow = forAllCommands sm Nothing $ \cmds -> monadicIO $ do
  (hist, _model, res) <- runCommands sm cmds
  prettyCommands sm hist (res === Ok)

prop_parallel_overflow :: Property
prop_parallel_overflow = forAllParallelCommands sm $ \cmds -> monadicIO $ do
    prettyParallelCommandsWithOpts cmds opts =<< runParallelCommands sm cmds
      where opts = Just $ GraphOptions "overflow.png" Png

prop_nparallel_overflow :: Int -> Property
prop_nparallel_overflow np = forAllNParallelCommands sm np $ \cmds -> monadicIO $ do
    prettyNParallelCommandsWithOpts cmds opts =<< runNParallelCommands sm cmds
      where opts = Just $ GraphOptions ("overflow-" ++ show np ++ ".png") Png
