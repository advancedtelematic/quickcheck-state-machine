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
  , showLabelledExamples'
  , showLabelledExamples
  )
  where

import           Data.Either
                   (partitionEithers)
import           Data.Kind
                   (Type)
import           Data.List
                   (foldl')
import           Data.Maybe
                   (catMaybes)
import           Prelude                       hiding
                   (maximum)
import           System.Random
                   (getStdRandom, randomR)
import           Test.QuickCheck
                   (Property, collect, forAllShrinkShow,
                   labelledExamplesWith, maxSuccess, property, replay,
                   stdArgs)
import           Test.QuickCheck.Random
                   (mkQCGen)
import           Text.Show.Pretty
                   (ppShow)

import           Test.StateMachine.Sequential
                   (generateCommands, shrinkCommands)
import           Test.StateMachine.Types
                   (Command(..), Commands(..), StateMachine(..),
                   Symbolic)
import qualified Test.StateMachine.Types.Rank2 as Rank2

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
  deriving (Show)

-- | Step the model using a 'Command' (i.e., a command associated with an
-- explicit set of variables).
execCmd :: StateMachine model cmd m resp
        -> model Symbolic -> Command cmd resp -> Event model cmd resp Symbolic
execCmd sm model (Command cmd resp _vars) = Event
  { eventBefore = model
  , eventCmd    = cmd
  , eventAfter  = transition sm model cmd resp
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

-- | Show minimal examples for each of the generated tags.
showLabelledExamples' :: (Show tag, Show (model Symbolic))
                      => (Show (cmd Symbolic), Show (resp Symbolic))
                      => (Rank2.Traversable cmd, Rank2.Foldable resp)
                      => StateMachine model cmd m resp
                      -> Maybe Int
                      -- ^ Seed
                      -> Int
                      -- ^ Number of tests to run to find examples
                      -> ([Event model cmd resp Symbolic] -> [tag])
                      -> (tag -> Bool)
                      -- ^ Tag filter (can be @const True@)
                      -> IO ()
showLabelledExamples' sm mReplay numTests tag focus = do
    replaySeed <- case mReplay of
      Nothing   -> getStdRandom (randomR (1, 999999))
      Just seed -> return seed

    labelledExamplesWith (stdArgs { replay     = Just (mkQCGen replaySeed, 0)
                                  , maxSuccess = numTests
                                  }) $
      forAllShrinkShow (generateCommands sm Nothing)
                       (shrinkCommands   sm)
                       ppShow $ \cmds ->
        collects (filter focus . tag . execCmds sm $ cmds) $
          property True

    putStrLn $ "Used replaySeed " ++ show replaySeed
  where
    collects :: Show a => [a] -> Property -> Property
    collects = repeatedly collect
      where
        repeatedly :: (a -> b -> b) -> ([a] -> b -> b)
        repeatedly = flip . foldl' . flip

showLabelledExamples :: (Show tag, Show (model Symbolic))
                     => (Show (cmd Symbolic), Show (resp Symbolic))
                     => (Rank2.Traversable cmd, Rank2.Foldable resp)
                     => StateMachine model cmd m resp
                     -> ([Event model cmd resp Symbolic] -> [tag])
                     -> IO ()
showLabelledExamples sm tag = showLabelledExamples' sm Nothing 1000 tag (const True)
