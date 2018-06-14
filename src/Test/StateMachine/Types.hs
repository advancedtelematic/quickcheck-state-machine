{-# LANGUAGE DeriveFoldable       #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE MonoLocalBinds       #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Types
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-----------------------------------------------------------------------------

module Test.StateMachine.Types
  ( StateMachine(..)
  , Command(..)
  , Commands(..)
  , ParallelCommandsF(..)
  , ParallelCommands
  , Pair(..)
  , Reason(..)
  , module Test.StateMachine.Types.Environment
  , module Test.StateMachine.Types.GenSym
  , module Test.StateMachine.Types.History
  , module Test.StateMachine.Types.References
  ) where

import           Data.Functor.Classes
                   (Ord1, Show1)
import           Data.Set
                   (Set)
import           Test.QuickCheck
                   (Gen, Property)

import           Test.StateMachine.Types.Environment
import           Test.StateMachine.Types.GenSym
import           Test.StateMachine.Types.History
import           Test.StateMachine.Types.References

------------------------------------------------------------------------

data StateMachine model cmd m resp = StateMachine
  { initModel     :: forall r. model r
  , transition    :: forall r. (Show1 r, Ord1 r) => model r -> cmd r -> resp r -> model r
  , precondition  :: model Symbolic -> cmd Symbolic -> Bool
  , postcondition :: forall r. (Show1 r, Ord1 r) => model r -> cmd r -> resp r -> Bool
  , invariant     :: Maybe (model Concrete -> Bool)
  , generator     :: model Symbolic -> [Gen (cmd Symbolic)]
  , weight        :: Maybe (model Symbolic -> cmd Symbolic -> Int)
  , shrinker      :: cmd Symbolic -> [cmd Symbolic]
  , semantics     :: cmd Concrete -> m (resp Concrete)
  , runner        :: m Property -> IO Property
  , mock          :: model Symbolic -> cmd Symbolic -> GenSym (resp Symbolic)
  }

data Command cmd = Command !(cmd Symbolic) !(Set Var)

deriving instance Show (cmd Symbolic) => Show (Command cmd)

data Commands cmd = Commands
  { unCommands :: [Command cmd] }

deriving instance Show (cmd Symbolic) => Show (Commands cmd)

data Reason = Ok | PreconditionFailed | PostconditionFailed | InvariantBroken
  deriving (Eq, Show)

data ParallelCommandsF t cmd = ParallelCommands
  { prefix   :: !(Commands cmd)
  , suffixes :: [t (Commands cmd)]
  }

data Pair a = Pair !a !a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

type ParallelCommands = ParallelCommandsF Pair
