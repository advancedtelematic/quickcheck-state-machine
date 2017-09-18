{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE UndecidableInstances #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Internal.Types
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module exports some types that are used internally by the library.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Internal.Types
  ( Program(..)
  , programLength
  , ParallelProgram(..)
  , Pid(..)
  , Fork(..)
  , Internal(..)
  ) where

import           Data.List
                   (intercalate)
import           Data.Typeable
                   (Typeable)
import           Text.Read
                   (readListPrec, readListPrecDefault, readPrec)

import           Test.StateMachine.Types
                   (Untyped(Untyped))
import           Test.StateMachine.Types.HFunctor
import           Test.StateMachine.Types.References

------------------------------------------------------------------------

-- | A (sequential) program is an abstract datatype representing a list
--   of actions.
--
-- The idea is that the user shows how to generate, shrink, execute and
-- modelcheck individual actions, and then the below combinators lift
-- those things to whole programs.
newtype Program act = Program { unProgram :: [Internal act] }

instance Eq (Internal act) => Eq (Program act) where
  Program acts1 == Program acts2 = acts1 == acts2

instance Monoid (Program act) where
  mempty                                = Program []
  Program acts1 `mappend` Program acts2 = Program (acts1 ++ acts2)

instance (Show (Untyped act), HFoldable act) => Show (Program act) where
  show (Program iacts) = bracket . intercalate "," . map go $ iacts
    where

    go (Internal act (Symbolic var)) =
      show (Untyped act) ++ " " ++ show var

    bracket s = "[" ++ s ++ "]"

instance Read (Internal act) => Read (Program act) where
  readPrec     = Program <$> readPrec
  readListPrec = readListPrecDefault

programLength :: Program act -> Int
programLength = length . unProgram

------------------------------------------------------------------------

-- | A parallel program is an abstract datatype that represents three
--   sequences of actions; a sequential prefix and two parallel
--   suffixes. Analogous to the sequential case, the user shows how to
--   generate, shrink, execute and modelcheck individual actions, and
--   then the below combinators lift those things to whole parallel
--   programs.
newtype ParallelProgram act = ParallelProgram
  { unParallelProgram :: Fork (Program act) }

instance (Show (Untyped act), HFoldable act) => Show (ParallelProgram act) where
  show = show . unParallelProgram

-- | Forks are used to represent parallel programs.
data Fork a = Fork a a a
  deriving (Eq, Functor, Show, Ord, Read)

------------------------------------------------------------------------

-- | An internal action is an action together with the symbolic variable
--   that will hold its result.
data Internal (act :: (* -> *) -> * -> *) where
  Internal :: (Show resp, Typeable resp) =>
    act Symbolic resp -> Symbolic resp -> Internal act

------------------------------------------------------------------------

-- | A process id.
newtype Pid = Pid Int
  deriving (Eq, Show)
