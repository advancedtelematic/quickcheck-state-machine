{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE DataKinds               #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE IncoherentInstances     #-}
{-# LANGUAGE KindSignatures          #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE PolyKinds               #-}
{-# LANGUAGE Rank2Types              #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE TypeInType              #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Test.QuickCheck.StateMachineModel.Utils where

import           Control.Concurrent.STM.TChan (TChan, tryReadTChan)
import           Control.Monad
import           Control.Monad.STM            (STM, atomically)
import           Data.Constraint
import           Data.Constraint.Forall
import           Data.Kind
import qualified Data.Maybe                   as May
import           Data.Proxy
import           Data.Singletons.Prelude      hiding ((:-))
import           Test.QuickCheck
import           Test.QuickCheck.Monadic
import           Test.QuickCheck.Property

------------------------------------------------------------------------

type Shrinker a = a -> [a]

genFromMaybe :: Gen (Maybe a) -> Gen a
genFromMaybe g = fmap (May.fromJust) (g `suchThat` May.isJust)

anyP :: (a -> Property) -> [a] -> Property
anyP p = foldr (\x ih -> p x .||. ih) (property False)

forAllShrinkShow
  :: Testable prop
  => Gen a -> Shrinker a -> (a -> String) -> (a -> prop) -> Property
forAllShrinkShow gen shrinker shower pf =
  again $
  MkProperty $
  gen >>= \x ->
    unProperty $
    shrinking shrinker x $ \x' ->
      counterexample (shower x') (pf x')

liftProperty :: Monad m => Property -> PropertyM m ()
liftProperty prop = MkPropertyM (\k -> liftM (prop .&&.) <$> k ())

shrinkPair :: (a -> [a]) -> (a, a) -> [(a, a)]
shrinkPair shrinker = shrinkPair' shrinker shrinker

shrinkPair' :: (a -> [a]) -> (b -> [b]) -> (a, b) -> [(a, b)]
shrinkPair' shrinkerA shrinkerB (x, y) =
  [ (x', y) | x' <- shrinkerA x ] ++
  [ (x, y') | y' <- shrinkerB y ]

------------------------------------------------------------------------

class p (f @@ a) =>
  IxComposeC (p :: k2 -> Constraint) (f :: TyFun k1 k2 -> *) (a :: k1)

instance p (f @@ a) => IxComposeC p f a

class Forall (IxComposeC p f) =>
  IxForallF (p :: k2 -> Constraint) (f :: TyFun k1 k2 -> *)

instance Forall (IxComposeC p f) => IxForallF p f

iinstF :: forall a p f. Proxy a -> IxForallF p f :- p (f @@ a)
iinstF _ = Sub $
  case inst :: Forall (IxComposeC p f) :- IxComposeC p f a of
    Sub Dict -> Dict

------------------------------------------------------------------------

getChanContents :: forall a. TChan a -> IO [a]
getChanContents chan = reverse <$> atomically (go [])
  where
  go :: [a] -> STM [a]
  go acc = do
    mx <- tryReadTChan chan
    case mx of
      Just x  -> go $ x : acc
      Nothing -> return acc

------------------------------------------------------------------------

data Ex (p :: TyFun a * -> *) = forall (x :: a). Ex (Sing x) (p @@ x)

class IxFunctor (f :: (TyFun ix * -> *) -> *) where
  ifmap :: (forall i. Sing (i :: ix) -> p @@ i -> q @@ i) -> f p -> f q

class IxFunctor1 (f :: k -> (TyFun ix * -> *) -> *) where
  ifmap1 :: (forall i. Sing (i :: ix) -> p @@ i -> q @@ i) -> forall j. f j p -> f j q

class IxFoldable (t :: (TyFun ix * -> *) -> *) where

  ifoldMap :: Monoid m => (forall i. Sing (i :: ix) -> p @@ i -> m) -> t p -> m

  itoList :: t p -> [Ex p]
  itoList = ifoldMap (\s px -> [Ex s px])

  ifoldr :: (forall i. Sing (i :: ix) -> p @@ i -> b -> b) -> b -> t p -> b
  ifoldr f z = foldr (\(Ex i x) -> f i x) z . itoList

iany
  :: forall
     (ix :: *)
     (t  :: (TyFun ix * -> *) -> *)
     (p  :: TyFun ix * -> *)
  .  IxFoldable t
  => (forall i. Sing (i :: ix) -> p @@ i -> Bool) -> t p -> Bool
iany p = ifoldr (\i x ih -> p i x || ih) False

iall
  :: forall
     (ix :: *)
     (t  :: (TyFun ix * -> *) -> *)
     (p  :: TyFun ix * -> *)
  .  IxFoldable t
  => (forall i. Sing (i :: ix) -> p @@ i -> Bool) -> t p -> Bool
iall p = ifoldr (\i x ih -> p i x && ih) True

class (IxFunctor t, IxFoldable t) => IxTraversable (t :: (TyFun ix * -> *) -> *) where
  itraverse :: Applicative f => Proxy q
    -> (forall x. Sing x -> p @@ x -> f (q @@ x))
    -> t p -> t q
