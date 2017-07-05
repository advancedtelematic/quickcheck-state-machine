{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Internal.Sequential
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains the building blocks needed to implement the
-- 'Test.StateMachine.sequentialProperty' helper.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Internal.Sequential
  ( liftGen
  , liftShrinkInternal
  , liftShrink
  , getUsedVars
  , filterInvalid
  , liftModel
  )
  where

import           Control.Monad.State
                   (StateT, get, lift, modify)
import           Data.Bifunctor
                   (bimap)
import           Data.Set
                   (Set)
import qualified Data.Set                                     as S
import           Test.QuickCheck
                   (Gen, shrinkList, sized, suchThat)
import           Test.QuickCheck.Monadic
                   (PropertyM, pre, run)

import           Test.StateMachine.Internal.Types
import           Test.StateMachine.Internal.Types.Environment
import           Test.StateMachine.Internal.Utils
import           Test.StateMachine.Types

------------------------------------------------------------------------

-- | Given a generator, precondition, transition function and an initial
--   model we can generate a list of internal actions which respect the
--   precondition together with the resulting model.
liftGen
  :: forall model act
  .  Generator model act
  -> Precondition model act
  -> Transition model act
  -> model Symbolic
  -> Int                     -- ^ Name supply for symbolic variables.
  -> Gen (Program act, model Symbolic)
liftGen gen precond next model0 n = sized $ \size ->
  bimap Program id <$> go size n model0
  where
  go :: Int -> Int -> model Symbolic -> Gen ([Internal act], model Symbolic)
  go 0  _ model = return ([], model)
  go sz i model = do
    Untyped act <- gen model `suchThat` \(Untyped act) -> precond model act
    let sym = Symbolic (Var i)
    (acts, model') <- go (sz - 1) (i + 1) (next model act sym)
    return (Internal act sym : acts, model')

-- | Given a shrinker of typed actions we can lift it to a shrinker of
--   internal actions.
liftShrinkInternal :: Shrinker act -> (Internal act -> [Internal act])
liftShrinkInternal shrinker (Internal act sym) =
  [ Internal act' sym | act' <- shrinker act ]

liftShrink
  :: HFoldable act
  => Shrinker act
  -> Precondition model act
  -> Transition model act
  -> model Symbolic
  -> Program act
  -> [Program act]
liftShrink shrinker precond trans model
  = map (Program . snd . filterInvalid precond trans model S.empty)
  . shrinkList (liftShrinkInternal shrinker)
  . unProgram

-- | Returns the set of references an action uses.
getUsedVars :: HFoldable act => act Symbolic a -> Set Var
getUsedVars = hfoldMap (\(Symbolic v) -> S.singleton v)

-- | Remove actions whose pre-conditions are false, or if they use
--   references that are not in scope.
filterInvalid
  :: HFoldable act
  => Precondition model act
  -> Transition model act
  -> model Symbolic
  -> Set Var        -- ^ References in scope.
  -> [Internal act] -> ((model Symbolic, Set Var), [Internal act])
filterInvalid precond trans = go
 where
   go m known [] = ((m, known), [])
   go m known (x@(Internal act sym@(Symbolic var)) : xs)
     | getUsedVars act `S.isSubsetOf` known && precond m act =
         (x :) <$> go (trans m act sym) (S.insert var known) xs
     | otherwise = go m known xs

liftModel
  :: Monad m
  => HFunctor act
  => model Symbolic  -- ^ The model with symbolic references is used to
                     -- check pre-conditions against.
  -> model Concrete  -- ^ While the one with concrete referenes is used
                     -- for checking post-conditions.
  -> Program act
  -> Precondition model act
  -> Semantics act m
  -> Transition model act
  -> Postcondition model act
  -> PropertyM (StateT Environment m) ()
liftModel _ _  (Program [])                        _       _   _     _        = return ()
liftModel m m' (Program (Internal act sym : acts)) precond sem trans postcond = do
  pre (precond m act)
  env <- run get
  let act' = hfmap (fromSymbolic env) act
  resp <- run (lift (sem act'))
  liftProperty (postcond m' act' resp)
  run (modify (insertConcrete sym (Concrete resp)))

  liftModel
    (trans m  act sym)
    (trans m' act' (Concrete resp))
    (Program acts) precond sem trans postcond

  where
  fromSymbolic :: Environment -> Symbolic v ->  Concrete v
  fromSymbolic env sym' = case reifyEnvironment env sym' of
    Left  err -> error (show err)
    Right con -> con
