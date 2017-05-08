{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE PolyKinds          #-}
{-# LANGUAGE Rank2Types         #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators      #-}

module DieHard where

import           Data.List
import           Data.Singletons.Prelude (type (@@), ConstSym1, Proxy, Sing,
                                          TyFun)
import           Test.QuickCheck         (Gen, Property, ioProperty, label,
                                          property)

import           Test.StateMachine
import           Test.StateMachine.Types
import           Test.StateMachine.Utils

------------------------------------------------------------------------

data Step :: Response () -> (TyFun () * -> *) -> * where
  FillBig      :: Step ('Response ()) refs
  FillSmall    :: Step ('Response ()) refs
  EmptyBig     :: Step ('Response ()) refs
  EmptySmall   :: Step ('Response ()) refs
  SmallIntoBig :: Step ('Response ()) refs
  BigIntoSmall :: Step ('Response ()) refs

deriving instance Show (Step resp refs)

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

gens :: [(Int, Gen (Untyped Step (IxRefs ())))]
gens =
  [ (1, return . Untyped $ FillBig)
  , (1, return . Untyped $ FillSmall)
  , (1, return . Untyped $ EmptyBig)
  , (1, return . Untyped $ EmptySmall)
  , (1, return . Untyped $ SmallIntoBig)
  , (1, return . Untyped $ BigIntoSmall)
  ]

shrink1 :: Untyped' Step refs -> [Untyped' Step refs ]
shrink1 _ = []

------------------------------------------------------------------------

semStep :: Step resp (ConstSym1 ()) -> IO (Response_ (ConstSym1 ()) resp)
semStep FillBig      = return ()
semStep FillSmall    = return ()
semStep EmptyBig     = return ()
semStep EmptySmall   = return ()
semStep SmallIntoBig = return ()
semStep BigIntoSmall = return ()

------------------------------------------------------------------------

prop_dieHard :: Property
prop_dieHard = sequentialProperty
  smm
  gens
  shrink1
  returns
  semStep
  ixfor
  ioProperty

validSolutions :: [[Step ('Response ()) (ConstSym1 ())]]
validSolutions =
  [ [ FillBig
    , BigIntoSmall
    , EmptySmall
    , BigIntoSmall
    , FillBig
    , BigIntoSmall
    ]
  , [ FillSmall
    , SmallIntoBig
    , FillSmall
    , SmallIntoBig
    , EmptyBig
    , SmallIntoBig
    , FillSmall
    , SmallIntoBig
    ]
  , [ FillSmall
    , SmallIntoBig
    , FillSmall
    , SmallIntoBig
    , EmptySmall
    , BigIntoSmall
    , EmptySmall
    , BigIntoSmall
    , FillBig
    , BigIntoSmall
    ]
  , [ FillBig
    , BigIntoSmall
    , EmptyBig
    , SmallIntoBig
    , FillSmall
    , SmallIntoBig
    , EmptyBig
    , SmallIntoBig
    , FillSmall
    , SmallIntoBig
    ]
  ]

testValidSolutions :: Bool
testValidSolutions = all ((/= 4) . bigJug . run) validSolutions
  where
  run = foldr (\c s -> transitions s c ()) initState

prop_bigJug4 :: Property
prop_bigJug4 = shrinkPropertyHelper' prop_dieHard $ \output ->
  let counterExample = lines output !! 1 in
  case find (== counterExample) (map show validSolutions) of
    Nothing -> property False
    Just ex -> label ex (property True)

------------------------------------------------------------------------

returns :: Step resp refs -> SResponse () resp
returns FillBig      = SResponse
returns FillSmall    = SResponse
returns EmptyBig     = SResponse
returns EmptySmall   = SResponse
returns SmallIntoBig = SResponse
returns BigIntoSmall = SResponse

ixfor :: Applicative f => Proxy q -> Step resp p
  -> (forall x. Sing x -> p @@ x -> f (q @@ x))
  -> f (Step resp q)
ixfor _ FillBig      _ = pure FillBig
ixfor _ FillSmall    _ = pure FillSmall
ixfor _ EmptyBig     _ = pure EmptyBig
ixfor _ EmptySmall   _ = pure EmptySmall
ixfor _ SmallIntoBig _ = pure SmallIntoBig
ixfor _ BigIntoSmall _ = pure BigIntoSmall

deriving instance Eq (Step resp (ConstSym1 IntRef))

instance IxFunctor1 Step where
  ifmap1 _ FillBig      = FillBig
  ifmap1 _ FillSmall    = FillSmall
  ifmap1 _ EmptyBig     = EmptyBig
  ifmap1 _ EmptySmall   = EmptySmall
  ifmap1 _ SmallIntoBig = SmallIntoBig
  ifmap1 _ BigIntoSmall = BigIntoSmall

instance IxFoldable (Untyped' Step) where
  ifoldMap _ = undefined

instance Show (Untyped' Step (ConstSym1 IntRef)) where
  show (Untyped' FillBig      _) = "FillBig"
  show (Untyped' FillSmall    _) = "FillSmall"
  show (Untyped' EmptyBig     _) = "EmptyBig"
  show (Untyped' EmptySmall   _) = "EmptySmall"
  show (Untyped' SmallIntoBig _) = "SmallIntoBig"
  show (Untyped' BigIntoSmall _) = "BigIntoSmall"
