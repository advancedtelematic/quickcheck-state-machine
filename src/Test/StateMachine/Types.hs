{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE Rank2Types     #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Types
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains the main types exposed to the user. The module
-- is perhaps best read indirectly, on a per need basis, via the main
-- module "Test.StateMachine".
--
-----------------------------------------------------------------------------

module Test.StateMachine.Types

  ( -- * The types of the main things the user needs to supply
    Generator
  , Shrinker
  , Precondition
  , Transition
  , Postcondition
  , Semantics
  , InitialModel

  -- * Untyped actions
  , Untyped(..)

  -- * Higher-order functors, foldables and traversables
  , module Test.StateMachine.Types.HFunctor

  -- * Referenses
  , module Test.StateMachine.Types.References
  )
  where

import           Data.Functor.Classes
                   (Ord1)
import           Data.Typeable
                   (Typeable)
import           Test.QuickCheck
                   (Gen, Property)

import           Test.StateMachine.Types.HFunctor
import           Test.StateMachine.Types.References

------------------------------------------------------------------------

-- | The type of the generating function of some actions.
type Generator model act = model Symbolic -> Gen (Untyped act)

-- | The type of the shrink function of some actions.
type Shrinker act = forall (v :: * -> *) resp.
  act v resp -> [act v resp]

-- | The type of pre-conditions of some actions.
type Precondition model act = forall resp.
  model Symbolic -> act Symbolic resp -> Bool

-- | The type of the transition functions of some actions.
type Transition model act = forall resp v. Ord1 v =>
  model v -> act v resp -> v resp -> model v

-- | The type of the post-conditions of some actions.
type Postcondition model act = forall resp.
  model Concrete -> act Concrete resp -> resp -> Property

-- | The type of the semantics of some actions.
type Semantics act m = forall resp. act Concrete resp -> m resp

-- | The initial model
type InitialModel m = forall (v :: * -> *). m v
------------------------------------------------------------------------

-- | Untyped actions pack up the response type using an existential type.
data Untyped (act :: (* -> *) -> * -> *) where
  Untyped :: (Show resp, Typeable resp) => act Symbolic resp -> Untyped act
