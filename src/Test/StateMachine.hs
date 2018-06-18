-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- The main module for state machine based testing, it contains
-- combinators that help you build sequential and parallel properties.
--
-----------------------------------------------------------------------------

module Test.StateMachine

  ( -- * Sequential property combinators
    forAllShrinkCommands
  -- , modelCheck
  , runCommands
  , prettyCommands
  , checkActionNames
  , actionNames

    -- * Parallel property combinators
  , module Test.StateMachine.Parallel

    -- * Types
  , StateMachine(StateMachine)
  , Concrete
  , Symbolic
  , Reference
  , concrete
  , reference
  , Opaque(..)
  , opaque
  , Reason(..)
  , GenSym
  , genSym
  ) where

import           Test.StateMachine.Parallel
import           Test.StateMachine.Sequential
import           Test.StateMachine.Types
