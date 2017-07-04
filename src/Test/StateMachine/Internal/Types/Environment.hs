{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Internal.Types.Environment
-- Copyright   :  (C) 2017, Jacob Stanley
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- Symbolic environments.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Internal.Types.Environment
  ( Environment(..)
  , EnvironmentError(..)
  , emptyEnvironment
  , insertConcrete
  , reifyDynamic
  , reifyEnvironment
  , reify
  ) where

import           Data.Dynamic
                   (Dynamic, Proxy(Proxy), TypeRep, Typeable,
                   dynTypeRep, fromDynamic, toDyn, typeRep)
import           Data.Map
                   (Map)
import qualified Data.Map                as M

import           Test.StateMachine.Types

------------------------------------------------------------------------

-- | A mapping of symbolic values to concrete values.
--
newtype Environment =
  Environment {
      unEnvironment :: Map Var Dynamic
    } deriving (Show)

-- | Environment errors.
--
data EnvironmentError =
    EnvironmentValueNotFound !Var
  | EnvironmentTypeError !TypeRep !TypeRep
    deriving (Eq, Ord, Show)

-- | Create an empty environment.
--
emptyEnvironment :: Environment
emptyEnvironment =
  Environment M.empty

-- | Insert a symbolic / concrete pairing in to the environment.
--
insertConcrete :: Symbolic a -> Concrete a -> Environment -> Environment
insertConcrete (Symbolic k) (Concrete v) =
  Environment . M.insert k (toDyn v) . unEnvironment

-- | Cast a 'Dynamic' in to a concrete value.
--
reifyDynamic :: forall a. Typeable a => Dynamic -> Either EnvironmentError (Concrete a)
reifyDynamic dyn =
  case fromDynamic dyn of
    Nothing ->
      Left $ EnvironmentTypeError (typeRep (Proxy :: Proxy a)) (dynTypeRep dyn)
    Just x ->
      Right $ Concrete x

-- | Turns an environment in to a function for looking up a concrete value from
--   a symbolic one.
--
reifyEnvironment :: Environment -> (forall a. Symbolic a -> Either EnvironmentError (Concrete a))
reifyEnvironment (Environment vars) (Symbolic n) =
  case M.lookup n vars of
    Nothing ->
      Left $ EnvironmentValueNotFound n
    Just dyn ->
      reifyDynamic dyn

-- | Convert a symbolic structure to a concrete one, using the provided environment.
--
reify :: HTraversable t => Environment -> t Symbolic b -> Either EnvironmentError (t Concrete b)
reify vars =
  htraverse (reifyEnvironment vars)
