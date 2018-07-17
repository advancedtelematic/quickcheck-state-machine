{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module Test.StateMachine.ConstructorName
  ( GConName
  , gconName
  , gconNames
  )
  where

import           GHC.Generics
                   ((:*:)((:*:)), (:+:)(L1, R1), C, Constructor, D, K1,
                   M1, Rec1, S, U1, conName, unM1, unRec1)

import           Test.StateMachine.Types.References

------------------------------------------------------------------------

class GConName f where
  gconName  :: f a -> String
  gconNames :: f a -> [String]

instance GConName U1 where
  gconName  _ = ""
  gconNames _ = []

instance GConName (K1 i c) where
  gconName  _ = ""
  gconNames _ = []

instance Constructor c => GConName (M1 C c f) where
  gconName  = conName
  gconNames = (: []) . conName

instance GConName f => GConName (M1 D d f) where
  gconName  = gconName  . unM1
  gconNames = gconNames . unM1

instance GConName f => GConName (M1 S d f) where
  gconName  = gconName  . unM1
  gconNames = gconNames . unM1

instance (GConName f, GConName g) => GConName (f :+: g) where
  gconName (L1 x) = gconName x
  gconName (R1 y) = gconName y

  gconNames (_ :: (f :+: g) a) = gconNames (undefined :: f a) ++
                                 gconNames (undefined :: g a)

instance (GConName f, GConName g) => GConName (f :*: g) where
  gconName  (x :*: y) = gconName  x ++ gconName  y
  gconNames (x :*: y) = gconNames x ++ gconNames y

instance GConName f => GConName (Rec1 f) where
  gconName  = gconName  . unRec1
  gconNames = gconNames . unRec1

instance GConName (Reference a) where
  gconName  _ = ""
  gconNames _ = []
