{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Types.Environment
-- Copyright   :  (C) 2017, Jacob Stanley
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan.andjelkovic@here.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains environments that are used to translate between
-- symbolic and concrete references. It's taken from the Hedgehog
-- <https://hackage.haskell.org/package/hedgehog library>.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Types.Environment
  ( Environment(..)
  , EnvironmentError(..)
  , emptyEnvironment
  , insertConcrete
  , insertConcretes
  , reifyDynamic
  , reifyEnvironment
  , reify
  ) where

import           Data.Dynamic
                   (Dynamic, Typeable, dynTypeRep, fromDynamic)
import           Data.Map
                   (Map)
import qualified Data.Map                           as M
import           Data.Semigroup
                   (Semigroup)
import           Data.Typeable
                   (Proxy(Proxy), TypeRep, typeRep)
import           Prelude

import qualified Test.StateMachine.Types.Rank2      as Rank2
import           Test.StateMachine.Types.References

------------------------------------------------------------------------

-- | A mapping of symbolic values to concrete values.
newtype Environment = Environment
  { unEnvironment :: Map Var Dynamic
  }
  deriving (Semigroup, Monoid, Show)

-- | Environment errors.
data EnvironmentError
  = EnvironmentValueNotFound !Var
  | EnvironmentTypeError !TypeRep !TypeRep
  deriving (Eq, Ord, Show)

-- | Create an empty environment.
emptyEnvironment :: Environment
emptyEnvironment = Environment M.empty

-- | Insert a symbolic / concrete pairing in to the environment.
insertConcrete :: Var -> Dynamic -> Environment -> Environment
insertConcrete var dyn = Environment . M.insert var dyn . unEnvironment

insertConcretes :: [Var] -> [Dynamic] -> Environment -> Environment
insertConcretes []           []           env = env
insertConcretes (var : vars) (dyn : dyns) env =
  insertConcretes vars dyns (insertConcrete var dyn env)
insertConcretes _            _            _   =
  error "insertConcrets: impossible."

-- | Cast a 'Dynamic' in to a concrete value.
reifyDynamic :: forall a. Typeable a => Dynamic
             -> Either EnvironmentError (Concrete a)
reifyDynamic dyn =
  case fromDynamic dyn of
    Nothing ->
      Left (EnvironmentTypeError (typeRep (Proxy :: Proxy a)) (dynTypeRep dyn))
    Just x ->
      Right (Concrete x)

-- | Turns an environment in to a function for looking up a concrete value from
--   a symbolic one.
reifyEnvironment :: Environment
                 -> (forall a. Symbolic a -> Either EnvironmentError (Concrete a))
reifyEnvironment (Environment vars) (Symbolic n) =
  case M.lookup n vars of
    Nothing ->
      Left (EnvironmentValueNotFound n)
    Just dyn ->
      reifyDynamic dyn

-- | Convert a symbolic structure to a concrete one, using the provided
--   environment.
reify :: Rank2.Traversable t
      => Environment -> t Symbolic -> Either EnvironmentError (t Concrete)
reify vars = Rank2.traverse (reifyEnvironment vars)
