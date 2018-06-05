{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}

module Types
  ( StateMachine(..)
  , Command(..)
  , Commands(..)
  , unCommands
  , Reason(..)
  , module Types.Environment
  , module Types.GenSym
  , module Types.History
  , module Types.Reference
  ) where

import           Data.Constraint.Forall
                   (ForallF)
import           Data.Map
                   (Map)
import qualified Data.Map               as M
import           Test.QuickCheck
                   (Gen)

import           Types.Environment
import           Types.GenSym
import           Types.History
import           Types.Reference

------------------------------------------------------------------------

data StateMachine model cmd resp = StateMachine
  { initModel     :: forall r. model r
  , transition    :: forall r. ForallF Ord r => model r -> cmd r -> resp r -> model r
  , precondition  :: model Symbolic -> cmd Symbolic -> Bool
  , postcondition :: forall r. ForallF Ord r => model r -> cmd r -> resp r -> Bool
  , invariant     :: forall r. Maybe (model r -> Bool)
  , generator     :: model Symbolic -> [Gen (cmd Symbolic)]
  , weight        :: Maybe (model Symbolic -> cmd Symbolic -> Int)
  , shrinker      :: cmd Symbolic -> [cmd Symbolic]
  , semantics     :: cmd Concrete -> IO (resp Concrete)
  , mock          :: model Symbolic -> cmd Symbolic -> GenSym (resp Symbolic)
  }

data Command cmd resp = Command (cmd Symbolic) (resp Symbolic)

deriving instance (Show (cmd Symbolic), Show (resp Symbolic)) =>
  Show (Command cmd resp)

data Commands cmd resp = Commands { unCommands :: [Command cmd resp] }

deriving instance (Show (cmd Symbolic), Show (resp Symbolic)) =>
  Show (Commands cmd resp)

data Reason = Ok | PreconditionFailed | PostconditionFailed
  deriving (Eq, Show)
