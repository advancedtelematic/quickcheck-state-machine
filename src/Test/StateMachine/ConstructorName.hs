{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.StateMachine.ConstructorName
  ( GConName
  , gconName
  , gconNames
  , GConName1
  , gconName1
  , gconNames1
  )
  where

import           GHC.Generics
                   ((:*:)((:*:)), (:+:)(L1, R1), C, Constructor, D,
                   Generic1, K1, M1, Rec1, Rep1, S, U1, conName, from1,
                   unM1, unRec1)

import           Test.StateMachine.Types
                   (Command(..), Reference)

------------------------------------------------------------------------

class GConName a where
  gconName  :: a -> String
  gconNames :: a -> [String]

class GConName1 f where
  gconName1  :: f a -> String
  gconNames1 :: f a -> [String]

instance GConName1 U1 where
  gconName1  _ = ""
  gconNames1 _ = []

instance GConName1 (K1 i c) where
  gconName1  _ = ""
  gconNames1 _ = []

instance Constructor c => GConName1 (M1 C c f) where
  gconName1  = conName
  gconNames1 = (: []) . conName

instance GConName1 f => GConName1 (M1 D d f) where
  gconName1  = gconName1  . unM1
  gconNames1 = gconNames1 . unM1

instance GConName1 f => GConName1 (M1 S d f) where
  gconName1  = gconName1  . unM1
  gconNames1 = gconNames1 . unM1

instance (GConName1 f, GConName1 g) => GConName1 (f :+: g) where
  gconName1 (L1 x) = gconName1 x
  gconName1 (R1 y) = gconName1 y

  gconNames1 (_ :: (f :+: g) a) = gconNames1 (undefined :: f a) ++
                                 gconNames1 (undefined :: g a)

instance (GConName1 f, GConName1 g) => GConName1 (f :*: g) where
  gconName1  (x :*: y) = gconName1  x ++ gconName1  y
  gconNames1 (x :*: y) = gconNames1 x ++ gconNames1 y

instance GConName1 f => GConName1 (Rec1 f) where
  gconName1  = gconName1  . unRec1
  gconNames1 = gconNames1 . unRec1

------------------------------------------------------------------------

instance GConName1 (Reference a) where
  gconName1  _ = ""
  gconNames1 _ = []

instance (Generic1 cmd, GConName1 (Rep1 cmd)) => GConName (Command cmd) where
  gconName  (Command cmd _) = gconName1  (from1 cmd)
  gconNames (Command cmd _) = gconNames1 (from1 cmd)
