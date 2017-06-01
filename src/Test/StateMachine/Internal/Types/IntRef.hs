{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds                  #-}

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
-- This module provides internal refereces.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Internal.Types.IntRef
  ( IntRef(..)
  , Pid(..)
  , Ref(..)
  , ConstIntRef
  ) where

import           Data.Singletons.Prelude
                   (ConstSym1)

------------------------------------------------------------------------

-- | An internal (or integer) reference consists of a reference and a
--   process id.
data IntRef = IntRef Ref Pid
  deriving (Eq, Ord, Show, Read)

-- | A process id is merely a natural number that keeps track of which
--   thread the reference comes from. In the sequential case the process
--   id is always @0@. Likewise the sequential prefix of a parallel
--   program also has process id @0@, while the left suffix has process
--   id @1@, and then right suffix has process id @2@.
newtype Pid = Pid Int
  deriving (Eq, Ord, Show, Read, Num)

-- | A reference is natural number.
newtype Ref = Ref Int
  deriving (Eq, Ord, Show, Read, Num)

-- | Type-level function that constantly returns an internal reference.
type ConstIntRef = ConstSym1 IntRef
