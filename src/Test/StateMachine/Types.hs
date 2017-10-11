{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE UndecidableInstances #-}

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
  , StateMachine
  , stateMachine
  , StateMachine'(..)
  , Generator
  , Shrinker
  , Precondition
  , Transition
  , Postcondition
  , InitialModel
  , Result(..)
  , Semantics
  , Runner

  -- * Data type generic operations
  , module Test.StateMachine.Types.Generics

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
import           Data.Void
                   (Void)
import           Test.QuickCheck
                   (Gen, Property)

import           Test.StateMachine.Types.Generics
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

-- | A (non-failing) state machine record bundles up all functionality
--   needed to perform our tests.
type StateMachine model act m = StateMachine' model act Void m

-- | Same as above, but with possibily failing semantics.
data StateMachine' model act err m = StateMachine
  { generator'     :: Generator model act
  , shrinker'      :: Shrinker  act
  , precondition'  :: Precondition model act
  , transition'    :: Transition   model act
  , postcondition' :: Postcondition model act
  , model'         :: InitialModel model
  , semantics'     :: Semantics act err m
  , runner'        :: Runner m
  }

-- | Helper for lifting non-failing semantics to a possibily failing
--   state machine record.
stateMachine
  :: Functor m
  => Generator model act
  -> Shrinker act
  -> Precondition model act
  -> Transition   model act
  -> Postcondition model act
  -> InitialModel model
  -> (forall resp. act Concrete resp -> m resp)
  -> Runner m
  -> StateMachine' model act Void m
stateMachine gen shr precond trans post model sem run =
  StateMachine gen shr precond trans post model (fmap Ok . sem) run

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

-- | Post-conditions are checked after the actions have been executed
--   and we got a response.
type Postcondition model act = forall resp.
  model Concrete -> act Concrete resp -> resp -> Property

-- | The initial model is polymorphic in the type of references it uses,
--   so that it can be used both in the pre- and the post-condition
--   check.
type InitialModel m = forall (v :: * -> *). m v

-- | The result of executing an action.
data Result resp err = Ok resp | Fail err

-- | When we execute our actions we have access to concrete references.
type Semantics act err m = forall resp. act Concrete resp -> m (Result resp err)

-- | How to run the monad used by the semantics.
type Runner m = m Property -> IO Property
