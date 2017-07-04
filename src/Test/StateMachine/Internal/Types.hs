{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
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
  ( Pid(..)
  , Fork(..)
  ) where

import           Data.Monoid
                   ((<>))
import           Text.PrettyPrint.ANSI.Leijen
                   (Pretty, align, dot, indent, int, pretty, text,
                   underline, vsep, (<+>))

------------------------------------------------------------------------

-- | A process id is merely a natural number that keeps track of which
--   thread the reference comes from. In the sequential case the process
--   id is always @0@. Likewise the sequential prefix of a parallel
--   program also has process id @0@, while the left suffix has process
--   id @1@, and then right suffix has process id @2@.
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
