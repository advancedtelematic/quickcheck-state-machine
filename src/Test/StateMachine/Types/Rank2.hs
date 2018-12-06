{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE PolyKinds         #-}
{-# LANGUAGE Rank2Types        #-}
{-# LANGUAGE TypeOperators     #-}

module Test.StateMachine.Types.Rank2
  ( Functor
  , fmap
  , gfmap
  , (<$>)
  , Foldable
  , foldMap
  , gfoldMap
  , Traversable
  , traverse
  , gtraverse
  )
  where

import qualified Control.Applicative as Rank1
import qualified Control.Monad       as Rank1
import qualified Data.Foldable       as Rank1
import           Data.Kind
                   (Type)
import qualified Data.Traversable    as Rank1
import           GHC.Generics
                   ((:*:)((:*:)), (:+:)(L1, R1), Generic1, K1(K1),
                   M1(M1), Rec1(Rec1), Rep1, U1(U1), from1, to1, (:.:)(Comp1))
import           Prelude             hiding
                   (Applicative(..), Foldable(..), Functor(..),
                   Traversable(..), (<$>))

------------------------------------------------------------------------

class Functor (f :: (k -> Type) -> Type) where
  fmap :: (forall x. p x -> q x) -> f p -> f q
  default fmap :: (Generic1 f, Functor (Rep1 f))
               => (forall x. p x -> q x) -> f p -> f q
  fmap = gfmap

gfmap :: (Generic1 f, Functor (Rep1 f)) => (forall a. p a -> q a) -> f p -> f q
gfmap f = to1 . fmap f . from1

(<$>) :: Functor f => (forall x. p x -> q x) -> f p -> f q
(<$>) = fmap
{-# INLINE (<$>) #-}

instance Functor U1 where
  fmap _ U1 = U1

instance Functor (K1 i c) where
  fmap _ (K1 c) = K1 c

instance (Functor f, Functor g) => Functor (f :+: g) where
  fmap f (L1 x) = L1 (fmap f x)
  fmap f (R1 y) = R1 (fmap f y)

instance (Functor f, Functor g) => Functor (f :*: g) where
  fmap f (x :*: y) = fmap f x :*: fmap f y

instance (Rank1.Functor f, Functor g) => Functor (f :.: g) where
  fmap f (Comp1 fg) = Comp1 (Rank1.fmap (fmap f) fg)

instance Functor f => Functor (M1 i c f) where
  fmap f (M1 x) = M1 (fmap f x)

instance Functor f => Functor (Rec1 f) where
  fmap f (Rec1 x) = Rec1 (fmap f x)

------------------------------------------------------------------------

class Foldable (f :: (k -> Type) -> Type) where
  foldMap :: Monoid m => (forall x. p x -> m) -> f p -> m
  default foldMap :: (Generic1 f, Foldable (Rep1 f), Monoid m)
                  => (forall a. p a -> m) -> f p -> m
  foldMap = gfoldMap

gfoldMap :: (Generic1 f, Foldable (Rep1 f), Monoid m)
         => (forall a. p a -> m) -> f p -> m
gfoldMap f = foldMap f . from1

instance Foldable U1 where
  foldMap _ U1 = mempty

instance Foldable (K1 i c) where
  foldMap _ (K1 _) = mempty

instance (Foldable f, Foldable g) => Foldable (f :+: g) where
  foldMap f (L1 x) = foldMap f x
  foldMap f (R1 y) = foldMap f y

instance (Foldable f, Foldable g) => Foldable (f :*: g) where
  foldMap f (x :*: y) = foldMap f x `mappend` foldMap f y

instance (Rank1.Foldable f, Foldable g) => Foldable (f :.: g) where
  foldMap f (Comp1 fg) = Rank1.foldMap (foldMap f) fg

instance Foldable f => Foldable (M1 i c f) where
  foldMap f (M1 x) = foldMap f x

instance Foldable f => Foldable (Rec1 f) where
  foldMap f (Rec1 x) = foldMap f x

------------------------------------------------------------------------

class (Functor t, Foldable t) => Traversable (t :: (k -> Type) -> Type) where
  traverse :: Rank1.Applicative f => (forall a. p a -> f (q a)) -> t p -> f (t q)
  default traverse :: (Generic1 t, Traversable (Rep1 t), Rank1.Applicative f)
                   => (forall a. p a -> f (q a)) -> t p -> f (t q)
  traverse = gtraverse

gtraverse :: (Generic1 t, Traversable (Rep1 t), Rank1.Applicative f)
          => (forall a. p a -> f (q a)) -> t p -> f (t q)
gtraverse f = Rank1.fmap to1 . traverse f . from1

instance Traversable U1 where
  traverse _ U1 = Rank1.pure U1

instance Traversable (K1 i c) where
  traverse _ (K1 c) = Rank1.pure (K1 c)

instance (Traversable f, Traversable g) => Traversable (f :+: g) where
  traverse f (L1 x) = L1 Rank1.<$> traverse f x
  traverse f (R1 y) = R1 Rank1.<$> traverse f y

instance (Traversable f, Traversable g) => Traversable (f :*: g) where
  traverse f (x :*: y) = (:*:) Rank1.<$> traverse f x Rank1.<*> traverse f y

instance (Rank1.Traversable f, Traversable g) => Traversable (f :.: g) where
  traverse f (Comp1 fg) = Comp1 Rank1.<$> Rank1.traverse (traverse f) fg

instance Traversable f => Traversable (M1 i c f) where
  traverse f (M1 x) = M1 Rank1.<$> traverse f x

instance Traversable f => Traversable (Rec1 f) where
  traverse f (Rec1 x) = Rec1 Rank1.<$> traverse f x
