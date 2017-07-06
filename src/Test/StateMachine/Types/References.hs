{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving         #-}

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
-- This module contains reference related types. It's taken verbatim from the
-- Hedgehog <https://hackage.haskell.org/package/hedgehog library>.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Types.References
  ( Opaque(..)
  , Symbolic(..)
  , Concrete(..)
  , Var(..)
  ) where

import           Data.Functor.Classes
                   (Eq1(..), Ord1(..), Show1(..), showsPrec1)
import           Data.Typeable
                   (Typeable)
import           Text.Read
                   (readPrec)

------------------------------------------------------------------------

-- | Opaque values.
--
--   Useful if you want to put something without a 'Show' instance inside
--   something which you'd like to be able to display.
--
newtype Opaque a = Opaque
  { unOpaque :: a
  } deriving (Eq, Ord)

instance Show (Opaque a) where
  showsPrec _ (Opaque _) = showString "Opaque"

-- | Symbolic variable names.
--
newtype Var = Var Int
  deriving (Eq, Ord, Show, Num, Read)

-- | Symbolic values.
--
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

-- | Concrete values.
--
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
