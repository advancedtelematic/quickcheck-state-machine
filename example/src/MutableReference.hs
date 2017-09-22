{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE StandaloneDeriving #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  MutableReference
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains a specification of mutable references.
--
-----------------------------------------------------------------------------

module MutableReference
  ( Action(..)
  , Problem(..)
  , precondition
  , transition
  , initModel
  , generator
  , shrinker
  , prop_references
  , prop_referencesParallel
  ) where

import           Control.Concurrent
                   (threadDelay)
import           Data.Functor.Classes
                   (Show1(..))
import           Data.IORef
                   (IORef, atomicModifyIORef', newIORef, readIORef,
                   writeIORef)
import           System.Random
                   (randomRIO)
import           Test.QuickCheck
                   (Property, arbitrary, elements, frequency, property,
                   shrink, (===))

import           Test.StateMachine

------------------------------------------------------------------------

-- Mutable references can be created, read from, written to and
-- incremented.

data Action (v :: * -> *) :: * -> * where
  New   ::                                     Action v (Opaque (IORef Int))
  Read  :: Reference v (Opaque (IORef Int)) -> Action v Int
  Write :: Reference v (Opaque (IORef Int)) -> Int -> Action v ()
  Inc   :: Reference v (Opaque (IORef Int)) -> Action v ()

------------------------------------------------------------------------

-- The model is a map from the references to their current value. (We
-- can't actually use @Data.Map@ here, because we don't have an @Ord@
-- instance on @IORef@s.)

newtype Model v = Model [(Reference v (Opaque (IORef Int)), Int)]

initModel :: Model v
initModel = Model []

precondition :: Precondition Model Action
precondition _         New           = True
precondition (Model m) (Read  ref)   = ref `elem` map fst m
precondition (Model m) (Write ref _) = ref `elem` map fst m
precondition (Model m) (Inc   ref)   = ref `elem` map fst m

transition :: Transition Model Action
transition (Model m) New           ref = Model (m ++ [(Reference ref, 0)])
transition m         (Read  _)     _   = m
transition (Model m) (Write ref i) _   = Model (update ref i         m)
transition (Model m) (Inc   ref)   _   = Model (update ref (old + 1) m)
  where
  Just old = lookup ref m

update :: Eq a => a -> b -> [(a, b)] -> [(a, b)]
update ref i m = (ref, i) : filter ((/= ref) . fst) m

postcondition :: Postcondition Model Action
postcondition _         New         _    = property True
postcondition (Model m) (Read ref)  resp = lookup ref m === Just resp
postcondition _         (Write _ _) _    = property True
postcondition _         (Inc _)     _    = property True

------------------------------------------------------------------------

generator :: Generator Model Action
generator (Model m)
  | null m    = pure (Untyped New)
  | otherwise = frequency
      [ (1, pure (Untyped New))
      , (8, Untyped .    Read  <$> elements (map fst m))
      , (8, Untyped <$> (Write <$> elements (map fst m) <*> arbitrary))
      , (8, Untyped .    Inc   <$> elements (map fst m))
      ]

shrinker :: Action v resp -> [Action v resp]
shrinker (Write ref i) = [ Write ref i' | i' <- shrink i ]
shrinker _             = []

------------------------------------------------------------------------

-- To make things interesting we parametrise the semantics by a possible
-- problem.

data Problem = None | Bug | RaceCondition
  deriving Eq

semantics :: Problem -> Action Concrete resp -> IO resp
semantics _   New           = Opaque <$> newIORef 0
semantics _   (Read  ref)   = readIORef  (opaque ref)
semantics prb (Write ref i) = writeIORef (opaque ref) i'
  where
  -- One of the problems is a bug that writes a wrong value to the
  -- reference.
  i' | i `elem` [5..10] = if prb == Bug then i + 1 else i
     | otherwise        = i
semantics prb (Inc   ref)   =
  -- The other problem is that we introduce a possible race condition
  -- when incrementing.
  if prb == RaceCondition
  then do
    i <- readIORef (opaque ref)
    threadDelay =<< randomRIO (0, 5000)
    writeIORef (opaque ref) (i + 1)
  else
    atomicModifyIORef' (opaque ref) (\i -> (i + 1, ()))

------------------------------------------------------------------------

deriving instance Show1 v => Show (Action v resp)

instance Show (Untyped Action) where
  show (Untyped act) = show act

instance HTraversable Action where
  htraverse _ New           = pure New
  htraverse f (Read  ref)   = Read  <$> htraverse f ref
  htraverse f (Write ref i) = Write <$> htraverse f ref <*> pure i
  htraverse f (Inc   ref)   = Inc   <$> htraverse f ref

instance HFunctor  Action
instance HFoldable Action

------------------------------------------------------------------------

-- If we run @quickCheck (prop_references None)@, then the property
-- passes.
--
-- If we however run @quickCheck (prop_references Bug), it will fail
-- with the minimal counterexample: @New, Write (Var 0) 5, Read (Var 0)@.
--
-- Running @quickCheck (prop_references RaceCondition)@ will not uncover
-- the race condition, but @quickCheck (prop_parallelReferences
-- RaceCondition)@ will!

sm :: Problem -> StateMachine Model Action IO
sm prb = StateMachine
  generator shrinker precondition transition
  postcondition initModel (semantics prb) id

prop_references :: Problem -> Property
prop_references prb = monadicSequential (sm prb) $ \prog -> do
  (hist, model, prop) <- runCommands (sm prb) prog
  prettyCommands prog hist model $
    checkCommandNames prog numberOfConstructors prop
  where
  numberOfConstructors = 4

prop_referencesParallel :: Problem -> Property
prop_referencesParallel prb = monadicParallel (sm prb) $ \prog -> do
  hps <- runParallelCommands' (sm prb) prog
  prettyParallelCommands' prog hps
