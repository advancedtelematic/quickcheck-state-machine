{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE StandaloneDeriving   #-}
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
  , ParallelProgram'(..)
  , Pid(..)
  , Fork(..)
  , Internal(..)
  ) where

import           Data.Typeable
                   (Typeable)
import           Text.Read
                   (Lexeme(Ident), lexP, parens, prec, readPrec, step)

import           Test.StateMachine.Types
                   (Untyped(Untyped))
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

deriving instance Show (Untyped act) => Show (Program act)
deriving instance Read (Untyped act) => Read (Program act)

-- | Returns the number of actions in a program.
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

deriving instance Show (Untyped act) => Show (ParallelProgram act)
deriving instance Read (Untyped act) => Read (ParallelProgram act)

-- | Forks are used to represent parallel programs.
data Fork a = Fork a a a
  deriving (Eq, Functor, Show, Ord, Read)

data ParallelProgram' act = ParallelProgram' (Program act) [Program act]

deriving instance Eq   (Untyped act) => Eq   (ParallelProgram' act)
deriving instance Show (Untyped act) => Show (ParallelProgram' act)
deriving instance Read (Untyped act) => Read (ParallelProgram' act)

------------------------------------------------------------------------

-- | An internal action is an action together with the symbolic variable
--   that will hold its result.
data Internal (act :: (* -> *) -> * -> *) where
  Internal :: (Show resp, Typeable resp) =>
    act Symbolic resp -> Symbolic resp -> Internal act

instance Eq (Untyped act) => Eq (Internal act) where
  Internal a1 _ == Internal a2 _ = Untyped a1 == Untyped a2

instance Show (Untyped act) => Show (Internal act) where
  showsPrec p (Internal action v) = showParen (p > appPrec) $
    showString "Internal " .
    showsPrec (appPrec + 1) (Untyped action) .
    showString " " .
    showsPrec (appPrec + 1) v
    where
      appPrec = 10

instance Read (Untyped act) => Read (Internal act) where
  readPrec = parens $
    prec appPrec $ do
      Ident "Internal" <- lexP
      Untyped action <- step readPrec
      v <- step readPrec
      return (Internal action v)
    where
      appPrec = 10

------------------------------------------------------------------------

-- | A process id.
newtype Pid = Pid Int
  deriving (Eq, Show)
