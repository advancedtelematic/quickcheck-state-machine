{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MonoLocalBinds             #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE UndecidableInstances       #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Types
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan.andjelkovic@here.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-----------------------------------------------------------------------------

module Test.StateMachine.Types
  ( StateMachine
  , AdvancedStateMachine(..)
  , Command(..)
  , Commands(..)
  , lengthCommands
  , ParallelCommandsF(..)
  , ParallelCommands
  , Pair(..)
  , fromPair
  , toPair
  , Reason(..)
  , module Test.StateMachine.Types.Environment
  , module Test.StateMachine.Types.GenSym
  , module Test.StateMachine.Types.History
  , module Test.StateMachine.Types.References
  ) where

import           Data.Functor.Classes
                   (Ord1, Show1)
import           Data.Semigroup
                   (Semigroup)
import           Data.Set
                   (Set)
import           Data.Void
                   (Void)
import           Prelude
import           Test.QuickCheck
                   (Gen)

import           Test.StateMachine.Logic
import           Test.StateMachine.Markov
import           Test.StateMachine.Types.Environment
import           Test.StateMachine.Types.GenSym
import           Test.StateMachine.Types.History
import           Test.StateMachine.Types.References

------------------------------------------------------------------------

type StateMachine model cmd m resp = AdvancedStateMachine model Void cmd m resp

data AdvancedStateMachine model submodel cmd m resp = StateMachine
  { initModel      :: forall r. model r
  , transition     :: forall r. (Show1 r, Ord1 r) => model r -> cmd r -> resp r -> model r
  , precondition   :: model Symbolic -> cmd Symbolic -> Logic
  , postcondition  :: model Concrete -> cmd Concrete -> resp Concrete -> Logic
  , invariant      :: Maybe (model Concrete -> Logic)
  , generator      :: model Symbolic -> Gen (cmd Symbolic)
  , distribution   :: Maybe (Markov (model Symbolic) submodel (cmd Symbolic))
  , shrinker       :: cmd Symbolic -> [cmd Symbolic]
  , semantics      :: cmd Concrete -> m (resp Concrete)
  , mock           :: model Symbolic -> cmd Symbolic -> GenSym (resp Symbolic)
  }

data Command cmd = Command !(cmd Symbolic) !(Set Var)

deriving instance Show (cmd Symbolic) => Show (Command cmd)

newtype Commands cmd = Commands
  { unCommands :: [Command cmd] }
  deriving (Semigroup, Monoid)

deriving instance Show (cmd Symbolic) => Show (Commands cmd)

lengthCommands :: Commands cmd -> Int
lengthCommands = length . unCommands

data Reason
  = Ok
  | PreconditionFailed String
  | PostconditionFailed String
  | InvariantBroken String
  | ExceptionThrown
  deriving (Eq, Show)

data ParallelCommandsF t cmd = ParallelCommands
  { prefix   :: !(Commands cmd)
  , suffixes :: [t (Commands cmd)]
  }

deriving instance (Show (cmd Symbolic), Show (t (Commands cmd))) =>
  Show (ParallelCommandsF t cmd)

data Pair a = Pair
  { proj1 :: !a
  , proj2 :: !a
  }
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

fromPair :: Pair a -> (a, a)
fromPair (Pair x y) = (x, y)

toPair :: (a, a) -> Pair a
toPair (x, y) = Pair x y

type ParallelCommands = ParallelCommandsF Pair
