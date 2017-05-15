{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}

module DieHard
  ( Step(..)
  , State(..)
  , initState
  , transitions
  , prop_dieHard
  ) where

import           Control.Monad.Identity  (Identity, runIdentity)
import           Data.Singletons.Prelude (ConstSym1, TyFun)
import           Test.QuickCheck         (Gen, Property, property)

import           Test.StateMachine
import           Test.StateMachine.Types
import           Test.StateMachine.Utils

------------------------------------------------------------------------

data Step :: Signature () where
  FillBig      :: Step ('Response ()) refs
  FillSmall    :: Step ('Response ()) refs
  EmptyBig     :: Step ('Response ()) refs
  EmptySmall   :: Step ('Response ()) refs
  SmallIntoBig :: Step ('Response ()) refs
  BigIntoSmall :: Step ('Response ()) refs

------------------------------------------------------------------------

data State refs = State
  { bigJug   :: Int
  , smallJug :: Int
  } deriving (Show, Eq)

initState :: State refs
initState = State 0 0

------------------------------------------------------------------------

preconditions :: State refs -> Step resp refs -> Bool
preconditions _ _ = True

transitions :: State refs -> Step resp refs -> Response_ refs resp -> State refs
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

postconditions :: State refs -> Step resp refs -> Response_ refs resp -> Property
postconditions s c r = property (bigJug (transitions s c r) /= 4)

smm :: StateMachineModel State Step
smm = StateMachineModel preconditions postconditions transitions initState

------------------------------------------------------------------------

gens :: [(Int, Gen (Untyped Step (RefPlaceholder ())))]
gens =
  [ (1, return $ Untyped FillBig)
  , (1, return $ Untyped FillSmall)
  , (1, return $ Untyped EmptyBig)
  , (1, return $ Untyped EmptySmall)
  , (1, return $ Untyped SmallIntoBig)
  , (1, return $ Untyped BigIntoSmall)
  ]

shrink1 :: Step resp refs -> [Step resp refs ]
shrink1 _ = []

------------------------------------------------------------------------

semStep :: Step resp (ConstSym1 ()) -> Identity (Response_ (ConstSym1 ()) resp)
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
  gens
  shrink1
  semStep
  runIdentity
