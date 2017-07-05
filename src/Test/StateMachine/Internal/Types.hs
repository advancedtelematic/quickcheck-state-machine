{-# LANGUAGE DeriveFunctor    #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE KindSignatures   #-}

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
  ( Pid(..)
  , Fork(..)
  , Internal(..)
  ) where

import           Data.Monoid
                   ((<>))
import           Data.Typeable
                   (Typeable)
import           Text.PrettyPrint.ANSI.Leijen
                   (Pretty, align, dot, indent, int, pretty, text,
                   underline, vsep, (<+>))

import           Test.StateMachine.Types
                   (Symbolic)

------------------------------------------------------------------------

-- | A process id.
newtype Pid = Pid Int
  deriving (Eq, Show)

-- | Forks are used to represent parallel programs. They have a sequential
--   prefix (the middle argument of the constructor), and two parallel suffixes
--   (the left- and right-most argument of the constructor).
data Fork a = Fork a a a
  deriving (Eq, Functor, Show, Ord, Read)

instance Pretty a => Pretty (Fork a) where
  pretty (Fork l p r) = vsep
    [ underline $ text "Prefix:"
    , indent 5 $ pretty p
    , underline $ text "Parallel:"
    , indent 2 $ int 1 <> dot <+> align (pretty l)
    , indent 2 $ int 2 <> dot <+> align (pretty r)
    ]

-- | An internal action is an action together with the symbolic variable that
--   will hold its result.
data Internal (act :: (* -> *) -> * -> *) where
  Internal :: Typeable resp =>
    act Symbolic resp -> Symbolic resp -> Internal act
