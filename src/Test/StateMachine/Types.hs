{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingStrategies         #-}
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
-- Maintainer  :  Stevan Andjelkovic <stevan.andjelkovic@strath.ac.uk>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-----------------------------------------------------------------------------

module Test.StateMachine.Types
  ( StateMachine(..)
  , Command(..)
  , getCommand
  , Commands(..)
  , NParallelCommands
  , lengthCommands
  , ParallelCommandsF(..)
  , ParallelCommands
  , Pair(..)
  , fromPair
  , toPair
  , fromPair'
  , toPairUnsafe'
  , Reason(..)
  , isOK
  , noCleanup
  , module Test.StateMachine.Types.Environment
  , module Test.StateMachine.Types.GenSym
  , module Test.StateMachine.Types.History
  , module Test.StateMachine.Types.References
  ) where

import           Data.Functor.Classes
                   (Ord1, Show1)
import           Data.Semigroup
import           Prelude
import           Test.QuickCheck
                   (Gen)

import           Test.StateMachine.Logic
import           Test.StateMachine.Types.Environment
import           Test.StateMachine.Types.GenSym
import           Test.StateMachine.Types.History
import           Test.StateMachine.Types.References

------------------------------------------------------------------------

data StateMachine model cmd m resp = StateMachine
  { initModel      :: forall r. model r
  , transition     :: forall r. (Show1 r, Ord1 r) => model r -> cmd r -> resp r -> model r
  , precondition   :: model Symbolic -> cmd Symbolic -> Logic
  , postcondition  :: model Concrete -> cmd Concrete -> resp Concrete -> Logic
  , invariant      :: Maybe (model Concrete -> Logic)
  , generator      :: model Symbolic -> Maybe (Gen (cmd Symbolic))
  , shrinker       :: model Symbolic -> cmd Symbolic -> [cmd Symbolic]
  , semantics      :: cmd Concrete -> m (resp Concrete)
  , mock           :: model Symbolic -> cmd Symbolic -> GenSym (resp Symbolic)
  , cleanup        :: model Concrete -> m ()
  }

noCleanup :: Monad m => model Concrete -> m ()
noCleanup _ = return ()

-- | Previously symbolically executed command
--
-- Invariant: the variables must be the variables in the response.
data Command cmd resp = Command !(cmd Symbolic) !(resp Symbolic) ![Var]

getCommand :: Command cmd resp -> cmd Symbolic
getCommand (Command cmd _resp _vars) = cmd

deriving
  stock
  instance (Show (cmd Symbolic), Show (resp Symbolic)) => Show (Command cmd resp)

deriving
  stock
  instance (Read (cmd Symbolic), Read (resp Symbolic)) => Read (Command cmd resp)

deriving
  stock
  instance ((Eq (cmd Symbolic)), (Eq (resp Symbolic))) => Eq (Command cmd resp)

newtype Commands cmd resp = Commands
  { unCommands :: [Command cmd resp] }
  deriving newtype (Semigroup, Monoid)

deriving
  stock
  instance (Show (cmd Symbolic), Show (resp Symbolic)) => Show (Commands cmd resp)

deriving
  stock
  instance (Read (cmd Symbolic), Read (resp Symbolic)) => Read (Commands cmd resp)

deriving
  stock
  instance ((Eq (cmd Symbolic)), (Eq (resp Symbolic))) => Eq (Commands cmd resp)

lengthCommands :: Commands cmd resp -> Int
lengthCommands = length . unCommands

data Reason
  = Ok
  | PreconditionFailed String
  | PostconditionFailed String
  | InvariantBroken String
  | ExceptionThrown String
  | MockSemanticsMismatch
  deriving stock (Eq, Show)

isOK :: Reason -> Bool
isOK Ok = True
isOK _  = False

data ParallelCommandsF t cmd resp = ParallelCommands
  { prefix   :: !(Commands cmd resp)
  , suffixes :: [t (Commands cmd resp)]
  }

deriving
  stock
  instance (Eq (cmd Symbolic), Eq (resp Symbolic), Eq (t (Commands cmd resp)))
  => Eq (ParallelCommandsF t cmd resp)

deriving
  stock
  instance (Show (cmd Symbolic), Show (resp Symbolic), Show (t (Commands cmd resp)))
  => Show (ParallelCommandsF t cmd resp)

data Pair a = Pair
  { proj1 :: !a
  , proj2 :: !a
  }
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)

fromPair :: Pair a -> (a, a)
fromPair (Pair x y) = (x, y)

toPair :: (a, a) -> Pair a
toPair (x, y) = Pair x y

type ParallelCommands = ParallelCommandsF Pair

type NParallelCommands = ParallelCommandsF []

fromPair' :: ParallelCommandsF Pair cmd resp -> ParallelCommandsF [] cmd resp
fromPair' p = p { suffixes = (\(Pair l r) -> [l, r]) <$> suffixes p}

toPairUnsafe' :: ParallelCommandsF [] cmd resp -> ParallelCommandsF Pair cmd resp
toPairUnsafe' p = p { suffixes = unsafePair <$> suffixes p}
    where
      unsafePair [a,b] = Pair a b
      unsafePair _ = error "invariant violation! Shrunk list should always have 2 elements."
