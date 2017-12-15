-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Utils
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH, Li-yao Xia
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module exports some QuickCheck utility functions. Some of these should
-- perhaps be upstreamed.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Utils
  ( anyP
  , liftProperty
  , whenFailM
  , alwaysP
  , shrinkPropertyHelperC
  , shrinkPair
  , shrinkPair'
  , forAllShrinkShowC
  ) where

import Test.StateMachine.Internal.Utils
