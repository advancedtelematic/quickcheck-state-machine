{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE StandaloneDeriving #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Types
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Daniel Gustafsson <daniel@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains the main types exposed to the user. The module
-- is perhaps best read indirectly, on a per need basis, via the main
-- module "Test.StateMachine".
--
-----------------------------------------------------------------------------

module Test.StateMachine.Compose where

import Control.Lens (Lens', (^.), (%~), (&))
import Data.Functor.Product (Product(..))
import Test.QuickCheck.Gen (oneof)

import Test.StateMachine.Types

data EitherAct act_a act_b (v :: * -> *) r where
  InlAct :: act_a v r -> EitherAct act_a act_b v r
  InrAct :: act_b v r -> EitherAct act_a act_b v r

deriving instance (Eq (act_a v resp), Eq (act_b v resp)) => Eq (EitherAct act_a act_b v resp)

instance (HFunctor act_a, HFunctor act_b) => HFunctor (EitherAct act_a act_b) where
  hfmap f (InlAct a) = InlAct (hfmap f a)
  hfmap f (InrAct b) = InrAct (hfmap f b)

instance (HFoldable act_a, HFoldable act_b) => HFoldable (EitherAct act_a act_b) where
  hfoldMap f (InlAct a) = hfoldMap f a
  hfoldMap f (InrAct b) = hfoldMap f b

instance (HTraversable act_a, HTraversable act_b) => HTraversable (EitherAct act_a act_b) where
  htraverse f (InlAct a) = InlAct <$> htraverse f a
  htraverse f (InrAct b) = InrAct <$> htraverse f b

-- this probably already exists in the lens library (indexed lens?)
type ModelLens model_a model_b = forall (v :: * -> *). Lens' (model_a v) (model_b v)

pi0 :: ModelLens (Product ma mb) ma
pi0 f (Pair ma mb) = flip Pair mb <$> f ma

pi1 :: ModelLens (Product ma mb) mb
pi1 f (Pair ma mb) = Pair ma <$> f mb

liftGen
  :: ModelLens model_c model_a
  -> ModelLens model_c model_b
  -> Generator model_a act_a
  -> Generator model_b act_b
  -> Generator model_c (EitherAct act_a act_b)
liftGen la lb ga gb mc = oneof [liftA, liftB]
  where
    liftA = do
      Untyped ca <- ga (mc^.la)
      return (Untyped (InlAct ca))
    liftB = do
      Untyped cb <- gb (mc^.lb)
      return (Untyped (InrAct cb))

liftGen'
  :: Generator model_a act_a
  -> Generator model_b act_b
  -> Generator (Product model_a model_b) (EitherAct act_a act_b)
liftGen' = liftGen pi0 pi1

liftPrecondition
  :: ModelLens model_c model_a
  -> ModelLens model_c model_b
  -> Precondition model_a act_a
  -> Precondition model_b act_b
  -> Precondition model_c (EitherAct act_a act_b)
liftPrecondition la lb pa pb mc (InlAct a) = pa (mc^.la) a
liftPrecondition la lb pa pb mc (InrAct b) = pb (mc^.lb) b

liftPrecondition'
  :: Precondition model_a act_a
  -> Precondition model_b act_b
  -> Precondition (Product model_a model_b) (EitherAct act_a act_b)
liftPrecondition' = liftPrecondition pi0 pi1

liftTransition
  :: ModelLens model_c model_a
  -> ModelLens model_c model_b
  -> Transition model_a act_a
  -> Transition model_b act_b
  -> Transition model_c (EitherAct act_a act_b)
liftTransition la lb ta tb mc (InlAct a) r = mc & la %~ (\ma -> ta ma a r)
liftTransition la lb ta tb mc (InrAct b) r = mc & lb %~ (\mb -> tb mb b r)

liftTransition'
  :: Transition model_a act_a
  -> Transition model_b act_b
  -> Transition (Product model_a model_b) (EitherAct act_a act_b)
liftTransition' = liftTransition pi0 pi1

liftPostcondition
  :: ModelLens model_c model_a
  -> ModelLens model_c model_b
  -> Postcondition model_a act_a
  -> Postcondition model_b act_b
  -> Postcondition model_c (EitherAct act_a act_b)
liftPostcondition la lb pa pb mc (InlAct a) r = pa (mc^.la) a r
liftPostcondition la lb pa pb mc (InrAct b) r = pb (mc^.lb) b r

liftPostcondition'
  :: Postcondition model_a act_a
  -> Postcondition model_b act_b
  -> Postcondition (Product model_a model_b) (EitherAct act_a act_b)
liftPostcondition' = liftPostcondition pi0 pi1

type Shrinker (act :: (* -> *) -> * -> *) = forall resp v. act v resp -> [act v resp]
liftShrinker
  :: Shrinker act_a
  -> Shrinker act_b
  -> Shrinker (EitherAct act_a act_b)
liftShrinker sa sb (InlAct a) = InlAct <$> sa a
liftShrinker sa sb (InrAct b) = InrAct <$> sb b

type Semantics m (act :: (* -> *) -> * -> *) = forall resp. act Concrete resp -> m resp
liftSemantics
  :: Semantics m act_a
  -> Semantics m act_b
  -> Semantics m (EitherAct act_a act_b)
liftSemantics sem_a sem_b (InlAct a) = sem_a a
liftSemantics sem_a sem_b (InrAct b) = sem_b b
