{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}

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
  , Ref(..)
  , precondition
  , transition
  , initModel
  , generator
  , shrink1
  , prop_references
  , prop_referencesParallel
  ) where

import           Control.Concurrent
                   (threadDelay)
import           Data.Functor.Classes
                   (Eq1(..), Show1(..), showsPrec1)
import           Data.IORef
                   (IORef, atomicModifyIORef', newIORef, readIORef,
                   writeIORef)
import           System.Random
                   (randomRIO)
import           Test.QuickCheck
                   (Property, arbitrary, elements, frequency,
                   ioProperty, property, shrink, (===))

import           Test.StateMachine

------------------------------------------------------------------------

-- Mutable references can be created, read from, written to and
-- incremented.

data Action (v :: * -> *) :: * -> * where
  New   ::          Action v (Opaque (IORef Int))
  Read  :: Ref v -> Action v Int
  Write :: Ref v -> Int -> Action v ()
  Inc   :: Ref v -> Action v ()

deriving instance Eq1 v => Eq (Action v resp)

data Ref v = Ref (v (Opaque (IORef Int)))

unRef :: Ref Concrete -> IORef Int
unRef (Ref (Concrete (Opaque ref))) = ref

instance Eq1 v => Eq (Ref v) where
  Ref v1 == Ref v2 = liftEq (==) v1 v2

instance Show1 v => Show (Ref v) where
  show (Ref v) = showsPrec1 10 v ""

instance Show (Internal Action) where
  show (Internal New           sym) = "New (" ++ show sym ++ ")"
  show (Internal (Read  ref)   sym) =
    "Read ("  ++ show ref ++ ") (" ++ show sym ++ ")"
  show (Internal (Write ref i) sym) =
    "Write (" ++ show ref ++ ") (" ++ show i ++ ") (" ++ show sym ++ ")"
  show (Internal (Inc   ref)   sym) =
    "Inc ("   ++ show ref ++ ") (" ++ show sym ++ ")"

instance ShowAction Action where
  showAction New           = ShowResponse "New"                                   show
  showAction (Read ref)    = ShowResponse ("Read " ++ show ref)                   show
  showAction (Write ref i) = ShowResponse ("Write " ++ show ref ++ " " ++ show i) show
  showAction (Inc ref)     = ShowResponse ("Inc " ++ show ref)                    show

instance HFunctor Action
instance HFoldable Action

instance HTraversable Action where
  htraverse _ New                 = pure New
  htraverse f (Read  (Ref ref))   = Read  . Ref <$> f ref
  htraverse f (Write (Ref ref) i) = Write . Ref <$> f ref <*> pure i
  htraverse f (Inc   (Ref ref))   = Inc   . Ref <$> f ref

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

shrink1 :: Action v resp -> [Action v resp]
shrink1 (Write ref i) = [ Write ref i' | i' <- shrink i ]
shrink1 _             = []

------------------------------------------------------------------------

-- The model is a map from the references to their current value. (We
-- can't actually use @Data.Map@ here, because we don't have an @Ord@
-- instance on @IORef@s.)

newtype Model v = Model [(Ref v, Int)]

initModel :: Model v
initModel = Model []

precondition :: Precondition Model Action
precondition _         New           = True
precondition (Model m) (Read  ref)   = ref `elem` map fst m
precondition (Model m) (Write ref _) = ref `elem` map fst m
precondition (Model m) (Inc   ref)   = ref `elem` map fst m

transition :: Transition Model Action
transition (Model m) New           ref = Model (m ++ [(Ref ref, 0)])
transition m         (Read  _)     _   = m
transition (Model m) (Write ref i) _   = Model ((ref, i) : filter ((/= ref) . fst) m)
transition (Model m) (Inc   ref)   _   = Model ((ref, old + 1) : filter ((/= ref) . fst) m)
  where
  Just old = lookup ref m

postcondition :: Postcondition Model Action
postcondition _         New         _    = property True
postcondition (Model m) (Read ref)  resp = lookup ref m === Just resp
postcondition _         (Write _ _) _    = property True
postcondition _         (Inc _)     _    = property True

------------------------------------------------------------------------

-- To make things interesting we parametrise the semantics by a possible
-- problem.

data Problem = None | Bug | RaceCondition
  deriving Eq

semantics :: Problem -> Action Concrete resp -> IO resp
semantics _   New           = Opaque <$> newIORef 0
semantics _   (Read  ref)   = readIORef  (unRef ref)
semantics prb (Write ref i) = writeIORef (unRef ref) i'
  where
  -- One of the problems is a bug that writes a wrong value to the
  -- reference.
  i' | i `elem` [5..10] = if prb == Bug then i + 1 else i
     | otherwise        = i
semantics prb (Inc   ref)   = do
  -- The other problem is that we introduce a possible race condition
  -- when incrementing.
  if prb == RaceCondition
  then do
    i <- readIORef (unRef ref)
    threadDelay =<< randomRIO (0, 5000)
    writeIORef (unRef ref) (i + 1)
  else
    atomicModifyIORef' (unRef ref) (\i -> (i + 1, ()))

------------------------------------------------------------------------

-- If we run @quickCheck (prop_references None)@, then the property
-- passes.
--
-- If we however run @quickCheck (prop_references Bug), it will fail
-- with the minimal counterexample: @New, Write $0 5, Read $0@.
--
-- Running @quickCheck (prop_references RaceCondition)@ will not uncover
-- the race condition, but @quickCheck (prop_parallelReferences
-- RaceCondition)@ will!

prop_references :: Problem -> Property
prop_references prb = sequentialProperty generator shrink1 precondition
  transition postcondition initModel (semantics prb) ioProperty


prop_referencesParallel :: Problem -> Property
prop_referencesParallel prb = parallelProperty generator shrink1 precondition
  transition postcondition initModel (semantics prb)
