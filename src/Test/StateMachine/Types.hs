{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE Rank2Types           #-}

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
  ( -- * Untyped actions
    Untyped(..)

    -- * Type aliases
  , Generator
  , Shrinker
  , Precondition
  , Transition
  , Semantics
  , Postcondition
  , InitialModel

  -- * Higher-order functors, foldables and traversables
  , module Test.StateMachine.Types.HFunctor

  -- * References
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

-- | An untyped action is an action where the response type is hidden
--   away using an existential type.
--
--   We need to hide the response type when generating actions, because
--   in general the actions we want to generate will have different
--   response types; and thus we can only type the generating function
--   if we hide the response type.
data Untyped (act :: (* -> *) -> * -> *) where
  Untyped :: (Show resp, Typeable resp) => act Symbolic resp -> Untyped act

------------------------------------------------------------------------

-- | When generating actions we have access to a model containing
--   symbolic references.
type Generator model act = model Symbolic -> Gen (Untyped act)

-- | Shrinking should preserve the response type of the action.
type Shrinker act = forall (v :: * -> *) resp.
  act v resp -> [act v resp]

-- | Pre-conditions are checked while generating, at this stage we do
--   not yet have access to concrete references.
type Precondition model act = forall resp.
  model Symbolic -> act Symbolic resp -> Bool

-- | The transition function must be polymorphic in the type of
--   variables used, as it is used both while generating and executing.
type Transition model act = forall resp v. Ord1 v =>
  model v -> act v resp -> v resp -> model v

-- | When we execute our actions we have access to concrete references.
type Semantics act m = forall resp. act Concrete resp -> m resp

-- | Post-conditions are checked after the actions have been executed
--   and we got a response.
type Postcondition model act = forall resp.
  model Concrete -> act Concrete resp -> resp -> Property

-- | The initial model is polymorphic in the type of references it uses,
--   so that it can be used both in the pre- and the post-condition
--   check.
type InitialModel m = forall (v :: * -> *). m v
