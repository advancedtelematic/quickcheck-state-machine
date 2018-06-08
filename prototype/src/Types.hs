{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE MonoLocalBinds       #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}

module Types
  ( StateMachine(..)
  , Command(..)
  , Commands(..)
  , Reason(..)
  , module Types.Environment
  , module Types.GenSym
  , module Types.History
  , module Types.Reference
  ) where

import           Data.Constraint.Forall
                   (ForallF)
import           Data.Set
                   (Set)
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

data Command cmd = Command !(cmd Symbolic) !(Set Var)

deriving instance Show (cmd Symbolic) => Show (Command cmd)

data Commands cmd = Commands
  { unCommands :: [Command cmd] }

deriving instance Show (cmd Symbolic) => Show (Commands cmd)

data Reason = Ok | PreconditionFailed | PostconditionFailed
  deriving (Eq, Show)
