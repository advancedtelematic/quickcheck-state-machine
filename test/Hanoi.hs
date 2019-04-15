{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE PolyKinds          #-}
{-# LANGUAGE StandaloneDeriving #-}

------------------------------------------------------------------------
-- |
-- Module      :  Hanoi
-- Copyright   :  (C) 2019, Adam Boniecki
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Adam Boniecki <adambonie@gmail.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- Solution to the famous Tower of Hanoi puzzle using tools for state
-- machine property-based testing.
--
-- The puzzle is to move N discs of different sizes from one peg to
-- another, with one auxiliary peg and a restriction that no disc may ever
-- be placed on top of a smaller disc. Only one disc can be moved at a time.

------------------------------------------------------------------------

module Hanoi
  ( prop_hanoi
  ) where

import           Data.Array
import           Data.Kind
                   (Type)
import           Data.Maybe
import           Data.TreeDiff.Expr
                   ()
import           GHC.Generics
                   (Generic, Generic1)
import           Prelude
import           Test.QuickCheck
                   (Arbitrary(arbitrary), Gen, Property, choose,
                   suchThat, (===))
import           Test.QuickCheck.Monadic
                   (monadicIO)

import           Test.StateMachine
import qualified Test.StateMachine.Types.Rank2 as Rank2

------------------------------------------------------------------------

-- The model keeps track of which disc is on which peg

newtype Model (r :: Type -> Type) = Model (Array Int [Int])
  deriving (Show, Eq, Generic)

-- There are 3 pegs, so the bounds are (0, 2)

pegsBounds :: (Int,Int)
pegsBounds = (0, 2)

instance ToExpr (Model r) where
  toExpr (Model a) = toExpr $ elems a

initModel :: Int -> Model r
initModel discs = Model $ listArray pegsBounds [[1..discs], [], []]

-- Allowed action is to move one disc from the top of one peg to the top of another

data Command (r :: Type -> Type) = Move (Int,Int)
  deriving (Eq, Show, Generic1, Rank2.Functor, Rank2.Foldable, Rank2.Traversable, CommandNames)

instance Arbitrary (Command r) where
  arbitrary = do
    x <- choose pegsBounds
    y <- choose pegsBounds `suchThat` (/= x)
    return $ Move (x,y)

data Response (r :: Type -> Type) = Done
  deriving (Show, Generic1, Rank2.Foldable)

------------------------------------------------------------------------

transitions :: Model r -> Command r -> Response r -> Model r
transitions (Model pegs) (Move (from_, to_)) _ = case pegs ! from_ of
  (x : xs) -> Model $ pegs // [(from_, xs), (to_, x : pegs ! to_)]
  _        -> error "transition: impossible, due to preconditon"

preconditions :: Model Symbolic -> Command Symbolic -> Logic
preconditions (Model pegs) (Move (from_, to_)) = Boolean (isJust x) .&& x .<= y
  where
    x = listToMaybe (pegs ! from_)
    -- Any disc can be placed on empty peg, so no disc counts as largest disc.
    y = listToMaybe (pegs ! to_ ++ [maxBound])

-- Check if all discs are at the last peg. The invariant states that this is not
-- the case, so when it is not satisfied, we have a counter example that is a
-- solution to our puzzle.

postconditions :: Model Concrete -> Command Concrete -> Response Concrete -> Logic
postconditions m c r = length lst ./= sum (fmap length pegs)
  where
    lst = pegs ! (snd $ bounds pegs)
    Model pegs = transitions m c r

------------------------------------------------------------------------

generator :: Model Symbolic -> Maybe (Gen (Command Symbolic))
generator _ = Just $ arbitrary

shrinker :: Model r -> Command r -> [Command r]
shrinker _ _ = []

------------------------------------------------------------------------

semantics :: Command Concrete -> IO (Response Concrete)
semantics _ = return Done

mock :: Model Symbolic -> Command Symbolic -> GenSym (Response Symbolic)
mock _ _ = return Done

------------------------------------------------------------------------

sm :: Int -> StateMachine Model Command IO Response
sm discs = StateMachine (initModel discs) transitions preconditions postconditions
       Nothing generator shrinker semantics mock

-- A sequential property for Tower of Hanoi with n discs.

-- Note that optimal solution requires 2^n-1 moves and this is not guaranteeed
-- to find an optimal one (or any at all).

prop_hanoi :: Int -> Property
prop_hanoi n = forAllCommands (sm n) Nothing $ \cmds -> monadicIO $ do
  (hist, _model, res) <- runCommands (sm n) cmds
  prettyCommands (sm n) hist (checkCommandNames cmds (res === Ok))
