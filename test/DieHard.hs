{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE PolyKinds          #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  DieHard
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan.andjelkovic@here.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains a solution to the water jug puzzle featured in
-- /Die Hard 3/.
--
-----------------------------------------------------------------------------

module DieHard
  ( Command(..)
  , Model(..)
  , initModel
  , transitions
  , prop_dieHard
  ) where

import           Data.Kind
                   (Type)
import           GHC.Generics
                   (Generic, Generic1)
import           Prelude
import           Test.QuickCheck
                   (Gen, Property, oneof, (===))
import           Test.QuickCheck.Monadic
                   (monadicIO)

import           Test.StateMachine
import qualified Test.StateMachine.Types.Rank2 as Rank2

------------------------------------------------------------------------

-- The problem is to measure exactly 4 liters of water given a 3- and
-- 5-liter jug.

-- We start of defining the different actions that are allowed:

data Command (r :: Type -> Type)
  = FillBig      -- Fill the 5-liter jug.
  | FillSmall    -- Fill the 3-liter jug.
  | EmptyBig     -- Empty the 5-liter jug.
  | EmptySmall
  | SmallIntoBig -- Pour the contents of the 3-liter jug
                 -- into 5-liter jug.
  | BigIntoSmall
  deriving (Eq, Show, Generic1, Rank2.Functor, Rank2.Foldable, Rank2.Traversable, CommandNames)

data Response (r :: Type -> Type) = Done
  deriving (Show, Generic1, Rank2.Foldable)

------------------------------------------------------------------------

-- The model (or state) keeps track of what amount of water is in the
-- two jugs.

data Model (r :: Type -> Type) = Model
  { bigJug   :: Int
  , smallJug :: Int
  } deriving (Show, Eq, Generic)

deriving instance ToExpr (Model Concrete)

initModel :: Model r
initModel = Model 0 0

------------------------------------------------------------------------

-- There are no pre-conditions for our actions. That simply means that
-- any action can happen at any state.

preconditions :: Model Symbolic -> Command Symbolic -> Logic
preconditions _ _ = Top

-- The transitions describe how the actions change the state.

transitions :: Model r -> Command r -> Response r -> Model r
transitions m FillBig   _  = m { bigJug   = 5 }
transitions m FillSmall _  = m { smallJug = 3 }
transitions m EmptyBig  _  = m { bigJug   = 0 }
transitions m EmptySmall _ = m { smallJug = 0 }
transitions (Model big small) SmallIntoBig _ =
            let big' = min 5 (big + small) in
            Model { bigJug = big'
                  , smallJug = small - (big' - big) }
transitions (Model big small) BigIntoSmall _ =
    let small' = min 3 (big + small) in
    Model { bigJug = big - (small' - small)
          , smallJug = small'
          }

-- The post-condition is used in a bit of a funny way. Recall that we
-- want to find a series of actions that leads to the big jug containing
-- 4 liters. So the idea is to state an invariant saying that the big
-- jug is NOT equal to 4 after we performed any action. If we happen to
-- find a series of actions where this is not true, i.e. the big jug
-- actually does contain 4 liters, then a minimal counter example will
-- be presented -- this will be our solution.

postconditions :: Model Concrete -> Command Concrete -> Response Concrete -> Logic
postconditions s c r = bigJug (transitions s c r) ./= 4

------------------------------------------------------------------------

-- The generator of actions is simple, with equal distribution pick an
-- action.

generator :: Model Symbolic -> Maybe (Gen (Command Symbolic))
generator _ = Just $ oneof
  [ return FillBig
  , return FillSmall
  , return EmptyBig
  , return EmptySmall
  , return SmallIntoBig
  , return BigIntoSmall
  ]

-- There's nothing to shrink.

shrinker :: Model r -> Command r -> [Command r]
shrinker _ _ = []

------------------------------------------------------------------------

-- We are not modelling an actual program here, so there's no semantics
-- for our actions. We are merely doing model checking.

semantics :: Command Concrete -> IO (Response Concrete)
semantics _ = return Done

mock :: Model Symbolic -> Command Symbolic -> GenSym (Response Symbolic)
mock _ _ = return Done

------------------------------------------------------------------------

-- Finally we have all the pieces needed to get the sequential property!

-- To make the code fit on a line, we first group all things related to
-- generation and execution of programs respectively.

sm :: StateMachine Model Command IO Response
sm = StateMachine initModel transitions preconditions postconditions
       Nothing generator shrinker semantics mock

prop_dieHard :: Property
prop_dieHard = forAllCommands sm Nothing $ \cmds -> monadicIO $ do
  (hist, _model, res) <- runCommands sm cmds
  prettyCommands sm hist (checkCommandNames cmds (res === Ok))

-- If we run @quickCheck prop_dieHard@ we get:
--
-- @
-- *** Failed! Falsifiable (after 43 tests and 4 shrinks):
-- Commands
--   { unCommands =
--       [ Command FillBig (fromList [])
--       , Command BigIntoSmall (fromList [])
--       , Command EmptySmall (fromList [])
--       , Command BigIntoSmall (fromList [])
--       , Command FillBig (fromList [])
--       , Command BigIntoSmall (fromList [])
--       ]
--   }
--
-- Model {bigJug = 0,smallJug = 0}
--
--    == FillBig ==> Done [ 0 ]
--
-- Model {bigJug = -0 +5
--       ,smallJug = 0}
--
--    == BigIntoSmall ==> Done [ 0 ]
--
-- Model {bigJug = -5 +2
--       ,smallJug = -0 +3}
--
--    == EmptySmall ==> Done [ 0 ]
--
-- Model {bigJug = 2
--       ,smallJug = -3 +0}
--
--    == BigIntoSmall ==> Done [ 0 ]
--
-- Model {bigJug = -2 +0
--       ,smallJug = -0 +2}
--
--    == FillBig ==> Done [ 0 ]
--
-- Model {bigJug = -0 +5
--       ,smallJug = 2}
--
--    == BigIntoSmall ==> Done [ 0 ]
--
-- Model {bigJug = -5 +4
--       ,smallJug = -2 +3}
--
-- PostconditionFailed "PredicateC (4 :== 4)" /= Ok
-- @
--
-- The counterexample is our solution.
