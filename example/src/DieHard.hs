{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE GADTs      #-}
{-# LANGUAGE TypeInType #-}

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
import           Test.QuickCheck
                   (Gen, Property, elements, property)

import           Test.StateMachine
import           Test.StateMachine.Types

------------------------------------------------------------------------

data Step :: Signature () where
  FillBig      :: Step refs ('Response ())
  FillSmall    :: Step refs ('Response ())
  EmptyBig     :: Step refs ('Response ())
  EmptySmall   :: Step refs ('Response ())
  SmallIntoBig :: Step refs ('Response ())
  BigIntoSmall :: Step refs ('Response ())

------------------------------------------------------------------------

data State refs = State
  { bigJug   :: Int
  , smallJug :: Int
  } deriving (Show, Eq)

initState :: State refs
initState = State 0 0

------------------------------------------------------------------------

preconditions :: State refs -> Step refs resp -> Bool
preconditions _ _ = True

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

postconditions :: State refs -> Step refs resp -> Response_ refs resp -> Property
postconditions s c r = property (bigJug (transitions s c r) /= 4)

smm :: StateMachineModel State Step
smm = StateMachineModel preconditions postconditions transitions initState

------------------------------------------------------------------------

gen :: Gen (Untyped Step (RefPlaceholder ()))
gen = elements
  [ Untyped FillBig
  , Untyped FillSmall
  , Untyped EmptyBig
  , Untyped EmptySmall
  , Untyped SmallIntoBig
  , Untyped BigIntoSmall
  ]

shrink1 :: Step refs resp -> [Step refs resp ]
shrink1 _ = []

------------------------------------------------------------------------

semStep :: Step (ConstSym1 ()) resp -> Identity (Response_ (ConstSym1 ()) resp)
semStep FillBig      = return ()
semStep FillSmall    = return ()
semStep EmptyBig     = return ()
semStep EmptySmall   = return ()
semStep SmallIntoBig = return ()
semStep BigIntoSmall = return ()

------------------------------------------------------------------------

instance HasResponse Step where
  response FillBig      = SResponse
  response FillSmall    = SResponse
  response EmptyBig     = SResponse
  response EmptySmall   = SResponse
  response SmallIntoBig = SResponse
  response BigIntoSmall = SResponse

instance IxFoldable Step where
  ifoldMap _ _ = mempty -- Not needed, since there are no references.

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

prop_dieHard :: Property
prop_dieHard = sequentialProperty
  smm
  gen
  shrink1
  semStep
  runIdentity
