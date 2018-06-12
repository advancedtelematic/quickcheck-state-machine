{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE StandaloneDeriving #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Types.References
-- Copyright   :  (C) 2017, Jacob Stanley
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains reference related types. It's taken almost verbatim from
-- the Hedgehog <https://hackage.haskell.org/package/hedgehog library>.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Types.References where

import           Data.TreeDiff
                   (Expr(App), ToExpr, toExpr)
import           Data.Typeable
                   (Typeable)
import           Data.Unique
                   (Unique, hashUnique, newUnique)
import           GHC.Generics
                   (Generic)
import qualified Rank2

------------------------------------------------------------------------

newtype Var = Var Int
  deriving (Eq, Ord, Show)

data Symbolic a where
  Symbolic :: Typeable a => Var -> Symbolic a

deriving instance Show (Symbolic a)
deriving instance Eq   (Symbolic a)
deriving instance Ord  (Symbolic a)

data Concrete a where
  Concrete :: Typeable a => a -> Unique -> Concrete a

newtype UniqueWrapper = UniqueWrapper Unique

instance Show UniqueWrapper where
  show (UniqueWrapper u) = show (hashUnique u)

instance Show (Concrete a) where
  showsPrec p (Concrete _x u) = showParen (p > appPrec) $
    showString "Concrete <opaque> " .
    showsPrec (appPrec + 1) (UniqueWrapper u)
      where
        appPrec = 10

instance Eq (Concrete a) where
  Concrete _ u1 == Concrete _ u2 = u1 == u2

instance Ord (Concrete a) where
  Concrete _ u1 `compare` Concrete _ u2 = u1 `compare` u2

instance ToExpr (Concrete a) where
  toExpr (Concrete _x u) =
    App "Concrete" [App "<opaque>" [], App (show (hashUnique u)) [] ]

data Reference a r = Reference (r a)
  deriving Generic

instance ToExpr (r a) => ToExpr (Reference a r)

instance Rank2.Functor (Reference a) where
  f <$> Reference r = Reference (f r)

instance Rank2.Foldable (Reference a) where
  foldMap f (Reference r) = f r

instance Rank2.Traversable (Reference a) where
  traverse f (Reference r) = Reference <$> f r

instance Eq (r a) => Eq (Reference a r) where
  Reference r1 == Reference r2 = r1 == r2

instance Ord (r a) => Ord (Reference a r) where
  Reference r1 `compare` Reference r2 = r1 `compare` r2

instance Show (r a) => Show (Reference a r) where
  showsPrec p (Reference v) = showParen (p > appPrec) $
    showString "Reference " .
    showsPrec p v
      where
        appPrec = 10

reference :: Typeable a => a -> IO (Reference a Concrete)
reference x = Reference <$> (Concrete x <$> newUnique)

concrete :: Reference a Concrete -> a
concrete (Reference (Concrete x _)) = x
