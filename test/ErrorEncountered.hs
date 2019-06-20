{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE PolyKinds          #-}
{-# LANGUAGE StandaloneDeriving #-}

module ErrorEncountered
  ( prop_error_sequential
  , prop_error_nparallel
  , prop_error_parallel
  )
  where

import           Data.Functor.Classes
                   (Eq1)
import           Data.IORef
                   (IORef, newIORef, readIORef, writeIORef)
import           GHC.Generics
                   (Generic, Generic1)
import           Prelude
import           Test.QuickCheck
                   (Gen, Property, arbitrary, elements, frequency,
                   shrink, (===))
import           Test.QuickCheck.Monadic
                   (monadicIO)

import           Test.StateMachine
import           Test.StateMachine.Types
                   (Reference(..), Symbolic(..))
import qualified Test.StateMachine.Types.Rank2 as Rank2
import           Test.StateMachine.Z

-----------------------------------------------------------------------------

-- Similar to MemoryReference, but with the possibilty of a 'Write' failing,
-- in which case the test should stop.
--
-- Writing a negative value will result in the 'WriteFailed' response. This
-- will transition the model into the 'ErrorEncountered' state, resulting in
-- the termination of the test. This is achieved by letting the 'generator'
-- return 'Nothing' when the model is in the 'ErrorEncountered' state.

-----------------------------------------------------------------------------

data Command r
  = Create
  | Read  (Reference (Opaque (IORef Int)) r)
  | Write (Reference (Opaque (IORef Int)) r) Int
  deriving (Eq, Generic1, Rank2.Functor, Rank2.Foldable, Rank2.Traversable, CommandNames)

deriving instance Show (Command Symbolic)
deriving instance Show (Command Concrete)

data Response r
  = Created (Reference (Opaque (IORef Int)) r)
  | ReadValue Int
  | Written
  | WriteFailed
  deriving (Generic1, Rank2.Foldable)

deriving instance Show (Response Symbolic)
deriving instance Show (Response Concrete)

data Model r
  = Model [(Reference (Opaque (IORef Int)) r, Int)]
  | ErrorEncountered
  deriving (Generic, Show)

instance ToExpr (Model Symbolic)
instance ToExpr (Model Concrete)

initModel :: Model r
initModel = Model empty

transition :: Eq1 r => Model r -> Command r -> Response r -> Model r
transition ErrorEncountered _  _    = ErrorEncountered
transition m@(Model model) cmd resp = case (cmd, resp) of
  (Create, Created ref)      -> Model ((ref, 0) : model)
  (Read _, ReadValue _)      -> m
  (Write ref x, Written)     -> Model (update ref x model)
  (Write _   _, WriteFailed) -> ErrorEncountered
  _                          -> error "transition: impossible."

update :: Eq a => a -> b -> [(a, b)] -> [(a, b)]
update ref i m = (ref, i) : filter ((/= ref) . fst) m

precondition :: Model Symbolic -> Command Symbolic -> Logic
precondition ErrorEncountered _ = Bot
precondition (Model m) cmd = case cmd of
  Create      -> Top
  Read  ref   -> ref `member` domain m
  Write ref _ -> ref `member` domain m

postcondition :: Model Concrete -> Command Concrete -> Response Concrete -> Logic
postcondition (Model m) cmd resp = case (cmd, resp) of
  (Create,        Created ref) -> m' ! ref .== 0 .// "Create"
    where
      m' = case transition (Model m) cmd resp of
          Model m1         -> m1
          ErrorEncountered -> error "postcondition ErrorEncountered"
          -- A Create cannot lead to ErrorEncountered
  (Read ref,      ReadValue v)  -> v .== m ! ref .// "Read"
  (Write _ref _x, Written)      -> Top
  (Write _ref  x, WriteFailed)
      | x < 0                   -> Top
  _                             -> Bot
postcondition ErrorEncountered _ _ = Bot

semantics :: Command Concrete -> IO (Response Concrete)
semantics cmd = case cmd of
  Create          -> Created   <$> (reference . Opaque <$> newIORef 0)
  Read ref        -> ReadValue <$> readIORef  (opaque ref)
  Write ref i
      | i >= 0    -> Written   <$  writeIORef (opaque ref) i
      | otherwise -> pure       $  WriteFailed


mock :: Model Symbolic -> Command Symbolic -> GenSym (Response Symbolic)
mock ErrorEncountered _ = error "mock ErrorEncountered"
mock (Model m) cmd = case cmd of
  Create          -> Created   <$> genSym
  Read ref        -> ReadValue <$> pure (m ! ref)
  Write _ i
      | i >= 0    -> pure Written
      | otherwise -> pure WriteFailed

generator :: Model Symbolic -> Maybe (Gen (Command Symbolic))
generator (Model model) = Just $ frequency
  [ (1, pure Create)
  , (4, Read  <$> elements (domain model))
  , (4, Write <$> elements (domain model) <*> arbitrary)
  ]
generator ErrorEncountered = Nothing

shrinker :: Model Symbolic -> Command Symbolic -> [Command Symbolic]
shrinker _ (Write ref i) = [ Write ref i' | i' <- shrink i ]
shrinker _ _             = []

sm :: StateMachine Model Command IO Response
sm = StateMachine initModel transition precondition postcondition
         Nothing generator shrinker semantics mock

prop_error_sequential :: Property
prop_error_sequential = forAllCommands sm Nothing $ \cmds -> monadicIO $ do
  (hist, _model, res) <- runCommands sm cmds
  prettyCommands sm hist (checkCommandNames cmds (res === Ok))

prop_error_parallel :: Property
prop_error_parallel = forAllParallelCommands sm $ \cmds -> monadicIO $ do
  prettyParallelCommands cmds =<< runParallelCommands sm cmds

prop_error_nparallel :: Int -> Property
prop_error_nparallel np = forAllNParallelCommands sm np $ \cmds -> monadicIO $ do
  prettyNParallelCommands cmds =<< runNParallelCommands sm cmds
