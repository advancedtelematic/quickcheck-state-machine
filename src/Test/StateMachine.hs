-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan.andjelkovic@here.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- The main module for state machine based testing, it contains
-- combinators that help you build sequential and parallel properties.
--
-----------------------------------------------------------------------------

module Test.StateMachine

  ( -- * Sequential property combinators
    forAllCommands
  , runCommands
  , prettyCommands
  , checkCommandNames
  , commandNames
  , commandNamesInOrder
  , tabulateState

    -- * Parallel property combinators
  , forAllParallelCommands
  , runParallelCommands
  , runParallelCommandsNTimes
  , prettyParallelCommands

    -- * Types
  , AdvancedStateMachine(StateMachine)
  , StateMachine
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
  , CommandNames(..)

  , module Test.StateMachine.Logic

  , module Test.StateMachine.Markov

    -- * Re-export
  , FiniteEnum
  , GBounded
  , GEnum
  , ToExpr

  ) where

import           Data.TreeDiff
                   (ToExpr)
import           Generic.Data
                   (FiniteEnum, GBounded, GEnum)
import           Prelude
                   ()

import           Test.StateMachine.ConstructorName
import           Test.StateMachine.Logic
import           Test.StateMachine.Markov
import           Test.StateMachine.Parallel
import           Test.StateMachine.Sequential
import           Test.StateMachine.Types
