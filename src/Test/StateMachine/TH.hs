-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.TH
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH, Li-yao Xia
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Li-yao Xia <lysxia@gmail.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- Template Haskell functions to derive common type classes for
-- testing with quickcheck-state-machine.
--
-----------------------------------------------------------------------------

module Test.StateMachine.TH
  ( -- * Special classes for @Action@ types
    deriveTestClasses

    -- ** Components
  , deriveHClasses
  , deriveHFunctor
  , deriveHFoldable
  , deriveHTraversable
  , deriveConstructors

    -- * Show
  , deriveShows
  , deriveShow
  , deriveShowUntyped

    -- * Shrink
  , mkShrinker
  ) where

import           Language.Haskell.TH
                   (Dec, Name, Q)

import           Test.StateMachine.Types.Generics.TH
import           Test.StateMachine.Types.HFunctor.TH

-- | Derive instances of
-- 'Test.StateMachine.Types.HFunctor.HFunctor',
-- 'Test.StateMachine.Types.HFunctor.HFoldable',
-- 'Test.StateMachine.Types.HFunctor.HTraversable',
-- 'Test.StateMachine.Types.Generics.Constructor'.
deriveTestClasses :: Name -> Q [Dec]
deriveTestClasses = (fmap (fmap concat . sequence) . sequence)
  [ deriveHClasses
  , deriveConstructors
  ]
