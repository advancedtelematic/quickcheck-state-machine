{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Labelling
-- Copyright   :  (C) 2019, Edsko de Vries
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan.andjelkovic@here.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module exports helpers that are useful for labelling properties.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Labelling
  ( Predicate(..)
  , predicate
  , maximum
  , classify
  , Event(..)
  , execCmds
  , execHistory
  )
  where

import           Data.Either
                   (partitionEithers)
import           Data.Kind
                   (Type)
import           Data.Maybe
                   (catMaybes)
import           Prelude                       hiding
                   (maximum)

import           Test.StateMachine.Types
                   (Command(..), Commands(..), Concrete, History,
                   Operation(..), StateMachine(..), Symbolic,
                   makeOperations, unHistory)

------------------------------------------------------------------------

data Predicate a b = Predicate {
    -- | Given an @a@, either successfully classify as @b@ or continue looking
    predApply  :: a -> Either b (Predicate a b)

    -- | End of the string
    --
    -- The predicate is given a final chance to return a value.
  , predFinish :: Maybe b
  }

instance Functor (Predicate a) where
  fmap f Predicate{..} = Predicate {
        predApply  = either (Left . f) (Right . fmap f) . predApply
      , predFinish = f <$> predFinish
      }

-- | Construct simply predicate that returns 'Nothing' on termination
predicate :: (a -> Either b (Predicate a b)) -> Predicate a b
predicate f = Predicate f Nothing

-- | Maximum value found, if any
maximum :: forall a b. Ord b => (a -> Maybe b) -> Predicate a b
maximum f = go Nothing
  where
    go :: Maybe b -> Predicate a b
    go maxSoFar = Predicate {
          predApply  = \a -> Right $ go (upd maxSoFar (f a))
        , predFinish = maxSoFar
        }

    upd :: Maybe b -> Maybe b -> Maybe b
    upd Nothing         mb       = mb
    upd (Just maxSoFar) Nothing  = Just maxSoFar
    upd (Just maxSoFar) (Just b) = Just (max maxSoFar b)

-- | Do a linear scan over the list, returning all successful classifications
classify :: forall a b. [Predicate a b] -> [a] -> [b]
classify = go []
  where
    go :: [b] -> [Predicate a b] -> [a] -> [b]
    go acc ps [] = acc ++ bs
      where
        bs = catMaybes $ map predFinish ps
    go acc ps (a : as) = go (acc ++ bs) ps' as
      where
        (bs, ps') = partitionEithers $ map (`predApply` a) ps

------------------------------------------------------------------------

data Event model cmd resp (r :: Type -> Type) = Event
  { eventBefore :: model r
  , eventCmd    :: cmd   r
  , eventAfter  :: model r
  , eventResp   :: resp  r
  }
  deriving Show

-- | Step the model using a 'Command' (i.e., a command associated with an
-- explicit set of variables).
execCmd :: StateMachine model cmd m resp
        -> model Symbolic -> Command cmd resp -> Event model cmd resp Symbolic
execCmd StateMachine { transition } model (Command cmd resp _vars) =
  Event
    { eventBefore = model
    , eventCmd    = cmd
    , eventAfter  = transition model cmd resp
    , eventResp   = resp
    }

-- | 'execCmds' is just the repeated form of 'execCmd'.
execCmds :: forall model cmd m resp. StateMachine model cmd m resp
         -> Commands cmd resp -> [Event model cmd resp Symbolic]
execCmds sm@StateMachine { initModel } = go initModel . unCommands
  where
    go :: model Symbolic -> [Command cmd resp] -> [Event model cmd resp Symbolic]
    go _ []       = []
    go m (c : cs) = let ev = execCmd sm m c in ev : go (eventAfter ev) cs

execOp :: StateMachine model cmd m resp -> model Concrete -> Operation cmd resp
       -> Maybe (Event model cmd resp Concrete)
execOp _sm                        _model (Crash _cmd _err _pid)    = Nothing
execOp StateMachine { transition } model (Operation cmd resp _pid) = Just $
  Event
    { eventBefore = model
    , eventCmd    = cmd
    , eventAfter  = transition model cmd resp
    , eventResp   = resp
    }

execHistory :: forall model cmd m resp. StateMachine model cmd m resp
            -> History cmd resp -> [Event model cmd resp Concrete]
execHistory sm@StateMachine { initModel } = go initModel . makeOperations . unHistory
  where
    go :: model Concrete -> [Operation cmd resp] -> [Event model cmd resp Concrete]
    go _ []       = []
    go m (o : os) = let mev = execOp sm m o in
      case (mev, os) of
        (Nothing, []) -> []
        (Nothing, _)  -> error "execHistory: impossible, there are no more ops after a crash."
        (Just ev, _)  -> ev : go (eventAfter ev) os
