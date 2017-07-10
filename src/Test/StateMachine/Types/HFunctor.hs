{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE Rank2Types        #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Types.HFunctor
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH, Jacob Stanley
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module exports a higher-order version of functors, foldable functors,
-- and traversable functors.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Types.HFunctor
  ( HFunctor
  , hfmap
  , HFoldable
  , hfoldMap
  , HTraversable
  , htraverse
  )
  where

import           Control.Monad.Identity
                   (Identity(..), runIdentity)
import           Data.Functor.Const
                   (Const(..))

------------------------------------------------------------------------

-- | Higher-order functors.
class HFunctor (f :: (* -> *) -> * -> *) where
  -- | Higher-order version of 'fmap'.
  hfmap :: (forall a. g a -> h a) -> f g b -> f h b

  default hfmap :: HTraversable f => (forall a. g a -> h a) -> f g b -> f h b
  hfmap f = runIdentity . htraverse (Identity . f)

-- | Higher-order foldable functors.
class HFunctor t => HFoldable (t :: (* -> *) -> * -> *) where
  -- | Higher-order version of 'foldMap'.
  hfoldMap :: Monoid m => (forall a. v a -> m) -> t v b -> m

  default hfoldMap :: (HTraversable t, Monoid m) => (forall a. v a -> m) -> t v b -> m
  hfoldMap f = getConst . htraverse (Const . f)

-- | Higher-order traversable functors.
class (HFunctor t, HFoldable t) => HTraversable (t :: (* -> *) -> * -> *) where
  -- | Higher-order version of 'traverse'.
  htraverse :: Applicative f => (forall a. g a -> f (h a)) -> t g b -> f (t h b)
