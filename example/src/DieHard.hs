{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  DieHard
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains a solution to the water jug puzzle featured in
-- /Die Hard 3/.
--
-----------------------------------------------------------------------------

module DieHard
  ( Action(..)
  , Model(..)
  , initModel
  , transitions
  , prop_dieHard
  ) where

import           Data.Functor.Classes
                   (Show1, liftShowsPrec)
import           Test.QuickCheck
                   (elements, (===))
import           Test.QuickCheck.Counterexamples
                   (PropertyOf)

import           Test.StateMachine
import           Test.StateMachine.TH
                   (deriveTestClasses)

------------------------------------------------------------------------

-- The problem is to measure exactly 4 liters of water given a 3- and
-- 5-liter jug.

-- We start of defining the different actions that are allowed:

data Action (v :: * -> *) :: * -> * where
  FillBig      :: Action v ()  -- Fill the 5-liter jug.
  FillSmall    :: Action v ()  -- Fill the 3-liter jug.
  EmptyBig     :: Action v ()  -- Empty the 5-liter jug.
  EmptySmall   :: Action v ()
  SmallIntoBig :: Action v ()  -- Pour the contents of the 3-liter jug
                               -- into 5-liter jug.
  BigIntoSmall :: Action v ()

deriving instance Show1 v => Show (Action v resp)

instance Show1 (Action Symbolic) where
  liftShowsPrec _ _ _ act _ = show act

------------------------------------------------------------------------

-- The model (or state) keeps track of what amount of water is in the
-- two jugs.

data Model (v :: * -> *) = Model
  { bigJug   :: Int
  , smallJug :: Int
  } deriving (Show, Eq)

initModel :: Model v
initModel = Model 0 0

------------------------------------------------------------------------

-- There are no pre-conditions for our actions. That simply means that
-- any action can happen at any state.

preconditions :: Precondition Model Action
preconditions _ _ = True

-- The transitions describe how the actions change the state.

transitions :: Transition Model Action
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

postconditions :: Postcondition Model Action
postconditions s c r = bigJug (transitions s c (Concrete r)) /= 4

------------------------------------------------------------------------

-- The generator of actions is simple, with equal distribution pick an
-- action.

generator :: Generator Model Action
generator _ = elements
  [ Untyped FillBig
  , Untyped FillSmall
  , Untyped EmptyBig
  , Untyped EmptySmall
  , Untyped SmallIntoBig
  , Untyped BigIntoSmall
  ]

-- There's nothing to shrink.

shrinker :: Action v resp -> [Action v resp ]
shrinker _ = []

------------------------------------------------------------------------

-- We are not modeling an actual program here, so there's no semantics
-- for our actions. We are merely doing model-checking here.

semantics :: Action v resp -> IO resp
semantics FillBig      = return ()
semantics FillSmall    = return ()
semantics EmptyBig     = return ()
semantics EmptySmall   = return ()
semantics SmallIntoBig = return ()
semantics BigIntoSmall = return ()

------------------------------------------------------------------------

deriveTestClasses ''Action

------------------------------------------------------------------------

-- Finally we have all the pieces needed to get the sequential property!

-- To make the code fit on a line, we first group all things related to
-- generation and execution of programs respectively.

sm :: StateMachine Model Action IO
sm = stateMachine
  generator shrinker preconditions transitions
  postconditions initModel semantics id

prop_dieHard :: PropertyOf (Program Action)
prop_dieHard = monadicSequentialC sm $ \prog -> do
  (hist, _, res) <- runProgram sm prog
  prettyProgram sm hist $
    checkActionNames prog (res === Ok)

-- If we run @quickCheck prop_dieHard@ we get:
--
-- @
--     *** Failed! Falsifiable (after 32 tests and 16 shrinks):
--     [FillBig,BigIntoSmall,EmptySmall,BigIntoSmall,FillBig,BigIntoSmall]
-- @
--
-- Let's check if that's a valid solution by writing out the state after each action:
--
--   { bigJug   = 0
--   , smallJug = 0
--   }
--
--   == FillBig ==>
--
--   { bigJug   = 5
--   , smallJug = 0
--   }
--
--   == BigIntoSmall ==>
--
--   { bigJug   = 2
--   , smallJug = 3
--   }
--
--   == EmptySmall ==>
--
--   { bigJug   = 2
--   , smallJug = 0
--   }
--
--   == BigIntoSmall ==>
--
--   { bigJug   = 0
--   , smallJug = 2
--   }
--
--   == FillBig ==>
--
--   { bigJug   = 5
--   , smallJug = 2
--   }
--
--   == BigIntoSmall ==>
--
--   { bigJug   = 4
--   , smallJug = 3
--   }
--
-- Good.
