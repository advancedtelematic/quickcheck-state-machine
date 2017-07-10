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
  ( Reference(..)
  , concrete
  , opaque
  , Opaque(..)
  , Symbolic(..)
  , Concrete(..)
  , Var(..)
  ) where

import           Data.Functor.Classes
                   (Eq1(..), Ord1(..), Show1(..), compare1, eq1,
                   showsPrec1)
import           Data.Typeable
                   (Typeable)
import           Text.Read
                   (readPrec)

import           Test.StateMachine.Types.HFunctor

------------------------------------------------------------------------

-- | References are the potential or actual result of executing an action. They
--   are parameterised by either `Symbolic` or `Concrete` depending on the
--   phase of the test.
--
--   `Symbolic` variables are the potential results of actions. These are used
--   when generating the sequence of actions to execute. They allow actions
--   which occur later in the sequence to make use of the result of an action
--   which came earlier in the sequence.
--
--   `Concrete` variables are the actual results of actions. These are used
--   during test execution. They provide access to the actual runtime value of
--   a variable.
--
data Reference v a = Reference (v a)

-- | Take the value from a concrete variable.
--
concrete :: Reference Concrete a -> a
concrete (Reference (Concrete x)) = x

-- | Take the value from an opaque concrete variable.
--
opaque :: Reference Concrete (Opaque a) -> a
opaque (Reference (Concrete (Opaque x))) = x

instance (Eq1 v, Eq a) => Eq (Reference v a) where
  (==) (Reference x) (Reference y) = eq1 x y

instance (Ord1 v, Ord a) => Ord (Reference v a) where
  compare (Reference x) (Reference y) = compare1 x y

instance (Show a, Show1 v) => Show (Reference v a) where
  showsPrec p (Reference x) =
    showParen (p >= 11) $
      showsPrec1 11 x

instance HTraversable Reference where
  htraverse f (Reference v) = fmap Reference (f v)

instance HFunctor  Reference
instance HFoldable Reference

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
