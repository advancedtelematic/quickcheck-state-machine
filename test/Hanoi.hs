{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE PolyKinds          #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances  #-}

------------------------------------------------------------------------

-- Solution to the famous Tower of Hanoi puzzle using tools for state
-- machine property-based testing.
--
-- The puzzle is to move N discs of different sizes from one peg to
-- another, with one auxiliary peg and a restriction that no disc may ever
-- be placed on top of a smaller disc. Only one disc can be moved at a time.

------------------------------------------------------------------------

module Hanoi
  ( Command(..)
  , Model(..)
  , initModel
  , transitions
  , prop_hanoi
  ) where

import Data.Kind
         (Type)
import Data.Array
import Data.Maybe
import Data.TreeDiff.Expr ()
import GHC.Generics
         (Generic, Generic1)
import Prelude
import Test.QuickCheck
         (Gen, Property, (===), Arbitrary (arbitrary), choose, suchThat)
import Test.QuickCheck.Monadic
         (monadicIO)
import Test.StateMachine
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
transitions (Model pegs) (Move (from,to)) _ =
  Model $ pegs // [(from, xs), (to, x:(pegs!to))]
    where (x, xs) = (head pegs_from, tail pegs_from)
          pegs_from = pegs!from

preconditions :: Model Symbolic -> Command Symbolic -> Logic
preconditions (Model pegs) (Move (from,to)) = (Boolean $ isJust x) :&& (x .<= y)
  where x = listToMaybe $ pegs!from
        -- Any disc can be placed on empty peg, so no disc counts as largest disc
        y = listToMaybe $ (pegs!to) ++ [maxBound]

-- Check if all discs are at the last peg. The invariant states that this is not
-- the case, so when it is not satisfied, we have a counter example that is a
-- solution to our puzzle.

postconditions :: Model Concrete -> Command Concrete -> Response Concrete -> Logic
postconditions m c r = length lst ./= (sum $ fmap length pegs)
  where lst = pegs ! (snd $ bounds pegs)
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
