{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE ExplicitNamespaces    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}

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
  ( MemStep(..)
  , Problem(..)
  , gen
  , shrink1
  , prop_sequential
  , prop_parallel
  ) where

import           Control.Concurrent
                   (threadDelay)
import           Control.Monad.IO.Class
                   (MonadIO, liftIO)
import           Data.IORef
                   (IORef, atomicModifyIORef', newIORef, readIORef,
                   writeIORef)
import           Data.Map
                   (Map)
import qualified Data.Map                as M
import           Data.Singletons.Prelude
                   (type (@@), ConstSym1, Proxy(..), Sing(STuple0))
import           System.Random
                   (randomRIO)
import           Test.QuickCheck
                   (Gen, Property, arbitrary, frequency, ioProperty,
                   property, shrink)

import           Test.StateMachine

------------------------------------------------------------------------

-- Mutable references can be created, read from, written to and
-- incremented. Note that the @New@ action returns a @Reference '()@,
-- and all other actions take references, @refs \@\@ '()@, as arguments
-- -- these are special library constructs that help you work with
-- actions that have a reference-like nature.

data MemStep :: Signature () where
  New   ::                       MemStep refs ('Reference '())
  Read  :: refs @@ '() ->        MemStep refs ('Response Int)
  Write :: refs @@ '() -> Int -> MemStep refs ('Response   ())
  Inc   :: refs @@ '() ->        MemStep refs ('Response   ())

------------------------------------------------------------------------

-- The model is a map from the references to their current value.

newtype Model refs = Model (Map (refs @@ '()) Int)

instance Show (Model refs) where
  show _ = "Model <...>"

initModel :: Model ref
initModel = Model M.empty

preconditions
  :: forall refs resp. IxForallF Ord refs
  => Model refs -> MemStep refs resp -> Bool
preconditions (Model m) cmd = (case cmd of
  New         -> True
  Read  ref   -> M.member ref m
  Write ref _ -> M.member ref m
  Inc   ref   -> M.member ref m) \\ (iinstF @'() Proxy :: Ords refs)

transitions
  :: forall refs resp. IxForallF Ord refs
  => Model refs -> MemStep refs resp -> Response_ refs resp -> Model refs
transitions (Model m) cmd resp = (case cmd of
  New         -> Model (M.insert resp 0 m)
  Read  _     -> Model m
  Write ref i -> Model (M.insert ref i m)
  Inc   ref   -> Model (M.insert ref (m M.! ref + 1) m)
  ) \\ (iinstF @'() Proxy :: Ords refs)

postconditions
  :: forall refs resp. IxForallF Ord refs
  => Model refs -> MemStep refs resp -> Response_ refs resp -> Property
postconditions (Model m) cmd resp = (case cmd of
  New         -> property True
  Read  ref   -> property $ m  M.! ref == resp
  Write ref i -> property $ m' M.! ref == i
  Inc   ref   -> property $ m' M.! ref == m M.! ref + 1
  ) \\ (iinstF @'() Proxy :: Ords refs)
  where
  Model m' = transitions (Model m) cmd resp

-- The occurences of @iinstF \@'() Proxy :: Ords refs@ are needed
-- because @refs@ is a indexed family of references in general and
-- Haskell has no way to express universal constraint -- so we have to
-- use the <https://hackage.haskell.org/package/constraints constraints>
-- library.

smm :: StateMachineModel Model MemStep
smm = StateMachineModel preconditions postconditions transitions initModel

------------------------------------------------------------------------

-- To make things interesting we parametrised the semantics on a
-- problems.

data Problem = None | Bug | RaceCondition
  deriving Eq

semStep
  :: MonadIO m
  => Problem -> MemStep (ConstSym1 (IORef Int)) resp
  -> m (Response_ (ConstSym1 (IORef Int)) resp)
semStep _   New           = liftIO (newIORef 0)
semStep _   (Read  ref)   = liftIO (readIORef  ref)
semStep prb (Write ref i) = liftIO (writeIORef ref i')
  where

  -- One of the problems is a bug that writes a wrong value to the
  -- reference.
  i' | i `elem` [5..10] = if prb == Bug then i + 1 else i
     | otherwise        = i
semStep prb (Inc ref)     = liftIO $

  -- The other problem is that we introduce a possible race condition
  -- when incrementing.
  if prb == RaceCondition
  then do
    i <- readIORef ref
    threadDelay =<< randomRIO (0, 5000)
    writeIORef ref (i + 1)
  else
    atomicModifyIORef' ref (\i -> (i + 1, ()))

------------------------------------------------------------------------

-- We don't have to generate references, merely indicate which reference
-- the library should generate. In this case we only have one type of
-- reference and hence @STuple0@, constructor for the singleton type of
-- @()@, is used.

gen :: Gen (Untyped MemStep (RefPlaceholder ()))
gen = frequency
  [ (1, return . Untyped $ New)
  , (5, return . Untyped $ Read STuple0)
  , (5, Untyped . Write STuple0 <$> arbitrary)
  , (5, return . Untyped $ Inc STuple0)
  ]

-- The only thing we shrink is the value that we write.

shrink1 :: MemStep refs resp -> [MemStep refs resp]
shrink1 (Write ref i) = [ Write ref i' | i' <- shrink i ]
shrink1 _             = []

------------------------------------------------------------------------

instance HasResponse MemStep where
  response New   {} = SReference STuple0
  response Read  {} = SResponse
  response Write {} = SResponse
  response Inc   {} = SResponse

instance IxFunctor MemStep where
  ifmap _ New           = New
  ifmap f (Read  ref)   = Read  (f STuple0 ref)
  ifmap f (Write ref i) = Write (f STuple0 ref) i
  ifmap f (Inc   ref)   = Inc   (f STuple0 ref)

instance IxFoldable MemStep where
  ifoldMap _ New           = mempty
  ifoldMap f (Read  ref)   = f STuple0 ref
  ifoldMap f (Write ref _) = f STuple0 ref
  ifoldMap f (Inc   ref)   = f STuple0 ref

instance IxTraversable MemStep where
  ifor _ New             _ = pure New
  ifor _ (Read  ref)     f = Read  <$> f STuple0 ref
  ifor _ (Write ref val) f = Write <$> f STuple0 ref <*> pure val
  ifor _ (Inc   ref)     f = Inc   <$> f STuple0 ref

instance ShowCmd MemStep where
  showCmd New           = "New"
  showCmd (Read  ref)   = "Read "  ++ ref
  showCmd (Write ref i) = "Write " ++ ref ++ " " ++ show i
  showCmd (Inc   ref)   = "Inc "   ++ ref

------------------------------------------------------------------------

-- If we run @quickCheck (prop_sequential None)@, then the property
-- passes.
--
-- If we however run @quickCheck (prop_sequential Bug), it will fail
-- with the minimal counterexample: @New, Write $0 5, Read $0@.
--
-- Running @quickCheck (prop_sequential RaceCondition)@ will not uncover
-- the race condition, but @quickCheck (prop_parallel RaceCondition)@
-- will!

prop_sequential :: Problem -> Property
prop_sequential prb = sequentialProperty
  smm
  gen
  shrink1
  (semStep prb)
  ioProperty

prop_parallel :: Problem -> Property
prop_parallel prb = parallelProperty
  smm
  gen
  shrink1
  (semStep prb)
