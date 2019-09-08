{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Test.StateMachine.Lockstep.Aux (
    Elem(..)
  , npAt
  , NTraversable(..)
  , ntraverse
  , ncfmap
  , nfmap
  , ncfoldMap
  , nfoldMap
  ) where

import Prelude
import Control.Monad.State
import Data.Kind (Type)
import Data.Monoid (Monoid)
import Data.Proxy
import Data.SOP

{-------------------------------------------------------------------------------
  Auxiliary
-------------------------------------------------------------------------------}

-- TODO: Could simulate by using @NS xs (K ())@
data Elem (xs :: [k]) (a :: k) where
  ElemHead :: Elem (k ': ks) k
  ElemTail :: Elem ks k -> Elem (k' ': ks) k

npAt' :: Elem xs a -> NP f xs -> f a
npAt' ElemHead      (f :* _)  = f
npAt' (ElemTail ix) (_ :* fs) = npAt' ix fs

npAt :: NP f xs -> Elem xs a -> f a
npAt = flip npAt'

-- | N-ary traversable functors
--
-- TODO: Don't provide Elem explicitly (just instantiate @c@)?
-- TODO: Introduce HTraverse into SOP?
class NTraversable (f :: (k -> Type) -> [k] -> Type) where
  nctraverse :: (Applicative m, All c xs)
             => proxy c
             -> (forall a. c a => Elem xs a -> g a -> m (h a))
             -> f g xs -> m (f h xs)

ntraverse :: (NTraversable f, Applicative m, SListI xs)
          => (forall a. Elem xs a -> g a -> m (h a))
          -> f g xs -> m (f h xs)
ntraverse = nctraverse (Proxy @Top)

ncfmap :: (NTraversable f, All c xs)
       => proxy c
       -> (forall a. c a => Elem xs a -> g a -> h a)
       -> f g xs -> f h xs
ncfmap p f xs = unI $ nctraverse p (\ix -> I . f ix) xs

nfmap :: (NTraversable f, SListI xs)
      => (forall a. Elem xs a -> g a -> h a)
      -> f g xs -> f h xs
nfmap f xs = ncfmap (Proxy @Top) f xs

ncfoldMap :: forall proxy f g m c xs.
             (NTraversable f, Monoid m, All c xs)
          => proxy c
          -> (forall a. c a => Elem xs a -> g a -> m)
          -> f g xs -> m
ncfoldMap p f = \xs -> execState (aux xs) mempty
  where
    aux :: f g xs -> State m (f g xs)
    aux xs = nctraverse p aux' xs

    aux' :: c a => Elem xs a -> g a -> State m (g a)
    aux' ix ga = modify (f ix ga `mappend`) >> return ga

nfoldMap :: (NTraversable f, Monoid m, SListI xs)
         => (forall a. Elem xs a -> g a -> m)
         -> f g xs -> m
nfoldMap f xs = ncfoldMap (Proxy @Top) f xs
