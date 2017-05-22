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
-----------------------------------------------------------------------------

module Test.StateMachine.Internal.Types.IntRef
  ( IntRef(..)
  , Pid(..)
  , Ref(..)
  , ConstIntRef
  )
  where

import           Data.Singletons.Prelude
                   (ConstSym1)

------------------------------------------------------------------------

data IntRef = IntRef Ref Pid
  deriving (Eq, Ord, Show, Read)

newtype Pid = Pid Int
  deriving (Eq, Ord, Show, Read, Num)

newtype Ref = Ref Int
  deriving (Eq, Ord, Show, Read, Num)

type ConstIntRef = ConstSym1 IntRef
