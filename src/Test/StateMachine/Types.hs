{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE StandaloneDeriving         #-}

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

  -- * Higher-order functors, foldables and traversables
  , HFunctor
  , hfmap
  , HFoldable
  , hfoldMap
  , HTraversable
  , htraverse

  -- * Referenses
  , Opaque(..)
  , Symbolic(..)
  , Concrete(..)
  , Var(..)

  -- * Untyped actions
  , Untyped
  , Untyped'(..)

  -- * Show related stuff
  , ShowAction(..)
  , ShowSymbolic(..)
  , ShowResponse(..)
  , showVar
  )
  where

import           Control.Monad.Identity
                   (Identity(..), runIdentity)
import           Data.Functor.Classes
                   (Eq1(..), Ord1(..), Show1(..), showsPrec1)
import           Data.Functor.Const
                   (Const(..))
import           Data.Typeable
                   (Typeable)
import           Test.QuickCheck
                   (Gen, Property)
import           Text.Read
                   (readPrec)

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

------------------------------------------------------------------------

-- | Higher-order functors
class HFunctor (f :: (* -> *) -> * -> *) where
  hfmap :: (forall a. g a -> h a) -> f g b -> f h b

  default hfmap :: HTraversable f => (forall a. g a -> h a) -> f g b -> f h b
  hfmap f = runIdentity . htraverse (Identity . f)

-- | Higher-order foldables
class HFunctor t => HFoldable (t :: (* -> *) -> * -> *) where
  hfoldMap :: Monoid m => (forall a. v a -> m) -> t v b -> m

  default hfoldMap :: (HTraversable t, Monoid m) => (forall a. v a -> m) -> t v b -> m
  hfoldMap f = getConst . htraverse (Const . f)

-- | Higher-order traversables
class (HFunctor t, HFoldable t) => HTraversable (t :: (* -> *) -> * -> *) where
  htraverse :: Applicative f => (forall a. g a -> f (h a)) -> t g b -> f (t h b)

------------------------------------------------------------------------

-- Stuff taken from Hedgehog.

newtype Opaque a = Opaque
  { unOpaque :: a
  } deriving (Eq, Ord)

instance Show (Opaque a) where
  showsPrec _ (Opaque _) = showString "Opaque"

newtype Var = Var Int
  deriving (Eq, Ord, Show, Num, Read)

data Symbolic a where
  Symbolic :: Typeable a => Var -> Symbolic a

deriving instance Eq  (Symbolic a)
deriving instance Ord (Symbolic a)

instance Show (Symbolic a) where
  showsPrec p (Symbolic x) = showsPrec p x

instance Show1 Symbolic where
  liftShowsPrec _ _ p (Symbolic x) = showsPrec p x

instance Typeable a => Read (Symbolic a) where
  readPrec = Symbolic <$> readPrec

instance Eq1 Symbolic where
  liftEq _ (Symbolic x) (Symbolic y) = x == y

instance Ord1 Symbolic where
  liftCompare _ (Symbolic x) (Symbolic y) = compare x y

newtype Concrete a where
  Concrete :: a -> Concrete a
  deriving (Eq, Ord, Functor, Foldable, Traversable)

instance Show a => Show (Concrete a) where
  showsPrec = showsPrec1

instance Show1 Concrete where
  liftShowsPrec sp _ p (Concrete x) = sp p x

instance Eq1 Concrete where
  liftEq eq (Concrete x) (Concrete y) = eq x y

instance Ord1 Concrete where
  liftCompare comp (Concrete x) (Concrete y) = comp x y

------------------------------------------------------------------------

data ShowResponse resp = ShowResponse
  { theAction :: String
  , showResp  :: resp -> String
  }

class ShowAction (act :: (* -> *) -> * -> *) where
  showAction :: Show1 v => act v resp -> ShowResponse resp

newtype ShowSymbolic a = ShowSymbolic Var

showVar :: Var -> String
showVar (Var i) = "$" ++ show i

instance Show1 ShowSymbolic where
  liftShowsPrec _ _ _ (ShowSymbolic var) _ = showVar var

------------------------------------------------------------------------

type Untyped act = Untyped' act Symbolic

data Untyped' (act :: (* -> *) -> * -> *) (v :: * -> *) where
  Untyped :: Typeable resp => act v resp -> Untyped' act v
