{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE GADTs      #-}
{-# LANGUAGE TypeInType #-}

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
-- /Die Hard 2/.
--
-----------------------------------------------------------------------------

module DieHard
  ( Step(..)
  , State(..)
  , initState
  , transitions
  , prop_dieHard
  ) where

import           Control.Monad.Identity
                   (Identity, runIdentity)
import           Data.Singletons.Prelude
                   (ConstSym1)
import           Data.Void
                   (Void)
import           Test.QuickCheck
                   (Gen, Property, elements, property)

import           Test.StateMachine

------------------------------------------------------------------------

-- The problem is to measure exactly 4 liters of water given a 3- and
-- 5-liter jug.

-- We start of defining the different actions (or commands) that are
-- allowed:

data Step :: Signature Void where
  FillBig      :: Step refs ('Response ())  -- Fill the 5-liter jug.
  FillSmall    :: Step refs ('Response ())  -- Fill the 3-liter jug.
  EmptyBig     :: Step refs ('Response ())  -- Empty the 5-liter jug.
  EmptySmall   :: Step refs ('Response ())
  SmallIntoBig :: Step refs ('Response ())  -- Pour the contents of
                                            -- the 3-liter jug into
                                            -- 5-liter jug.
  BigIntoSmall :: Step refs ('Response ())

------------------------------------------------------------------------

-- The state (or model) keeps track of what amount of water is in the
-- two jugs.

data State refs = State
  { bigJug   :: Int
  , smallJug :: Int
  } deriving (Show, Eq)

initState :: State refs
initState = State 0 0

------------------------------------------------------------------------

-- There are no pre-conditions for our actions. That simply means that
-- any action can happen at any state.

preconditions :: State refs -> Step refs resp -> Bool
preconditions _ _ = True

-- The transitions describe how the actions change the state.

transitions :: State refs -> Step refs resp -> Response_ refs resp -> State refs
transitions s FillBig   _  = s { bigJug   = 5 }
transitions s FillSmall _  = s { smallJug = 3 }
transitions s EmptyBig  _  = s { bigJug   = 0 }
transitions s EmptySmall _ = s { smallJug = 0 }
transitions (State big small) SmallIntoBig _ =
            let big' = min 5 (big + small) in
            State { bigJug = big'
                  , smallJug = small - (big' - big) }
transitions (State big small) BigIntoSmall _ =
    let small' = min 3 (big + small) in
    State { bigJug = big - (small' - small)
          , smallJug = small' }

-- The post-condition is used in a bit of a funny way. Recall that we
-- want to find a series of actions that leads to the big jug containing
-- 4 liters. So the idea is to state an invariant saying that the big
-- jug is NOT equal to 4 after we performed any action. If we happen to
-- find a series of actions where this is not true, i.e. the big jug
-- actually does contain 4 liters, then a minimal counter example will
-- be presented -- this will be our solution.

postconditions :: State refs -> Step refs resp -> Response_ refs resp -> Property
postconditions s c r = property (bigJug (transitions s c r) /= 4)

-- (We pack all our model related stuff up into a record is it's easier
-- to pass around.)
smm :: StateMachineModel State Step
smm = StateMachineModel preconditions postconditions transitions initState

------------------------------------------------------------------------

-- The generator of actions is simple, with equal distribution pick an
-- action.

gen :: Gen (Untyped Step (RefPlaceholder Void))
gen = elements
  [ Untyped FillBig
  , Untyped FillSmall
  , Untyped EmptyBig
  , Untyped EmptySmall
  , Untyped SmallIntoBig
  , Untyped BigIntoSmall
  ]

-- There's nothing to shrink.

shrink1 :: Step refs resp -> [Step refs resp ]
shrink1 _ = []

------------------------------------------------------------------------

-- We are not modeling an actual program here, so there's no semantics
-- for our actions. We are merely doing model-checking here.

semStep :: Step (ConstSym1 Void) resp -> Identity (Response_ (ConstSym1 Void) resp)
semStep FillBig      = return ()
semStep FillSmall    = return ()
semStep EmptyBig     = return ()
semStep EmptySmall   = return ()
semStep SmallIntoBig = return ()
semStep BigIntoSmall = return ()

------------------------------------------------------------------------

-- What follows are a bunch of bolierplate instances, we hope to
-- automate these away in the future.

instance HasResponse Step where
  response FillBig      = SResponse
  response FillSmall    = SResponse
  response EmptyBig     = SResponse
  response EmptySmall   = SResponse
  response SmallIntoBig = SResponse
  response BigIntoSmall = SResponse

instance IxFoldable Step where
  ifoldMap _ _ = mempty -- (Not needed, since there are no references.)

instance IxTraversable Step where
  ifor _ FillBig      _ = pure FillBig
  ifor _ FillSmall    _ = pure FillSmall
  ifor _ EmptyBig     _ = pure EmptyBig
  ifor _ EmptySmall   _ = pure EmptySmall
  ifor _ SmallIntoBig _ = pure SmallIntoBig
  ifor _ BigIntoSmall _ = pure BigIntoSmall

instance IxFunctor Step where
  ifmap _ FillBig      = FillBig
  ifmap _ FillSmall    = FillSmall
  ifmap _ EmptyBig     = EmptyBig
  ifmap _ EmptySmall   = EmptySmall
  ifmap _ SmallIntoBig = SmallIntoBig
  ifmap _ BigIntoSmall = BigIntoSmall

instance ShowCmd Step where
  showCmd FillBig      = "FillBig"
  showCmd FillSmall    = "FillSmall"
  showCmd EmptyBig     = "EmptyBig"
  showCmd EmptySmall   = "EmptySmall"
  showCmd SmallIntoBig = "SmallIntoBig"
  showCmd BigIntoSmall = "BigIntoSmall"

------------------------------------------------------------------------

-- Finally we have all the pieces needed to get the sequential property!

prop_dieHard :: Property
prop_dieHard = sequentialProperty
  smm
  gen
  shrink1
  semStep
  runIdentity

-- If we run @quickCheck prop_dieHard@ we get:
--
-- @
--     *** Failed! Falsifiable (after 32 tests and 16 shrinks):
--     [FillBig (),BigIntoSmall (),EmptySmall (),BigIntoSmall (),FillBig (),BigIntoSmall ()]
--
--     The model when the post-condition for `BigIntoSmall' fails is:
--
--         State {bigJug = 5, smallJug = 2}
--
--     The model transitions into:
--
--         State {bigJug = 4, smallJug = 3}
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
