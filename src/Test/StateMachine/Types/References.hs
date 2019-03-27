{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving         #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Types.References
-- Copyright   :  (C) 2017, Jacob Stanley
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan.andjelkovic@here.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains reference related types. It's taken almost verbatim from
-- the Hedgehog <https://hackage.haskell.org/package/hedgehog library>.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Types.References
  ( Var(Var)
  , Symbolic(Symbolic)
  , Concrete(Concrete)
  , Reference(Reference)
  , reference
  , concrete
  , opaque
  , Opaque(Opaque)
  , unOpaque
  )
  where

import           Data.Functor.Classes
                   (Eq1, Ord1, Show1, compare1, eq1, liftCompare,
                   liftEq, liftShowsPrec, showsPrec1)
import           Data.TreeDiff
                   (Expr(App), ToExpr, toExpr)
import           Data.Typeable
                   (Typeable)
import           GHC.Generics
                   (Generic)
import           Prelude

import qualified Test.StateMachine.Types.Rank2 as Rank2

------------------------------------------------------------------------

newtype Var = Var Int
  deriving (Eq, Ord, Show, Generic, ToExpr, Read)

data Symbolic a where
  Symbolic :: Typeable a => Var -> Symbolic a

deriving instance Show (Symbolic a)
deriving instance Typeable a => Read (Symbolic a)
deriving instance Eq   (Symbolic a)
deriving instance Ord  (Symbolic a)

instance Show1 Symbolic where
  liftShowsPrec _ _ p (Symbolic x) =
    showParen (p > appPrec) $
      showString "Symbolic " .
      showsPrec (appPrec + 1) x
    where
      appPrec = 10

instance ToExpr a => ToExpr (Symbolic a) where
  toExpr (Symbolic x) = toExpr x

instance Eq1 Symbolic where
  liftEq _ (Symbolic x) (Symbolic y) = x == y

instance Ord1 Symbolic where
  liftCompare _ (Symbolic x) (Symbolic y) = compare x y

data Concrete a where
  Concrete :: Typeable a => a -> Concrete a

deriving instance Show a => Show (Concrete a)

instance Show1 Concrete where
  liftShowsPrec sp _ p (Concrete x) =
    showParen (p > appPrec) $
      showString "Concrete " .
      sp (appPrec + 1) x
    where
      appPrec = 10

instance Eq1 Concrete where
  liftEq eq (Concrete x) (Concrete y) = eq x y

instance Ord1 Concrete where
  liftCompare comp (Concrete x) (Concrete y) = comp x y

instance ToExpr a => ToExpr (Concrete a) where
  toExpr (Concrete x) = toExpr x

data Reference a r = Reference (r a)
  deriving Generic

deriving instance Typeable a => Read (Reference a Symbolic)

instance ToExpr (r a) => ToExpr (Reference a r)

instance Rank2.Functor (Reference a) where
  fmap f (Reference r) = Reference (f r)

instance Rank2.Foldable (Reference a) where
  foldMap f (Reference r) = f r

instance Rank2.Traversable (Reference a) where
  traverse f (Reference r) = Reference <$> f r

instance (Eq a, Eq1 r) => Eq (Reference a r) where
  Reference x == Reference y = eq1 x y

instance (Ord a, Ord1 r) => Ord (Reference a r) where
  compare (Reference x) (Reference y) = compare1 x y

instance (Show1 r, Show a) => Show (Reference a r) where
  showsPrec p (Reference v) = showParen (p > appPrec) $
      showString "Reference " .
      showsPrec1 p v
    where
      appPrec = 10

reference :: Typeable a => a -> Reference a Concrete
reference = Reference . Concrete

concrete :: Reference a Concrete -> a
concrete (Reference (Concrete x)) = x

opaque :: Reference (Opaque a) Concrete -> a
opaque (Reference (Concrete (Opaque x))) = x

newtype Opaque a = Opaque
  { unOpaque :: a }
  deriving (Eq, Ord)

instance Show (Opaque a) where
  showsPrec _ (Opaque _) = showString "Opaque"

instance ToExpr (Opaque a) where
  toExpr _ = App "Opaque" []
