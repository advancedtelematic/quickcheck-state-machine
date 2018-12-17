{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
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

import           Data.Proxy
                   (Proxy(Proxy))
import           GHC.Generics
                   ((:*:)((:*:)), (:+:)(L1, R1), C, Constructor, D, K1,
                   M1, Rec1, S, U1, conName, unM1, unRec1)
import           Prelude

------------------------------------------------------------------------

type ConstructorName = String

class GConName a where
  gconName  :: a -> ConstructorName
  gconNames :: Proxy a -> [ConstructorName]

class GConName1 f where
  gconName1  :: f a -> ConstructorName
  gconNames1 :: Proxy (f a) -> [ConstructorName]

instance GConName1 U1 where
  gconName1  _ = ""
  gconNames1 _ = []

instance GConName1 (K1 i c) where
  gconName1  _ = ""
  gconNames1 _ = []

instance Constructor c => GConName1 (M1 C c f) where
  gconName1                            = conName
  gconNames1 (_ :: Proxy (M1 C c f p)) = [ conName @c undefined ] -- Can we do
                                                                  -- better
                                                                  -- here?

instance GConName1 f => GConName1 (M1 D c f) where
  gconName1                            = gconName1  . unM1
  gconNames1 (_ :: Proxy (M1 D c f p)) = gconNames1 (Proxy :: Proxy (f p))

instance GConName1 f => GConName1 (M1 S c f) where
  gconName1                            = gconName1  . unM1
  gconNames1 (_ :: Proxy (M1 S c f p)) = gconNames1 (Proxy :: Proxy (f p))

instance (GConName1 f, GConName1 g) => GConName1 (f :+: g) where
  gconName1 (L1 x) = gconName1 x
  gconName1 (R1 y) = gconName1 y

  gconNames1 (_ :: Proxy ((f :+: g) a)) =
    gconNames1 (Proxy :: Proxy (f a)) ++
    gconNames1 (Proxy :: Proxy (g a))

instance (GConName1 f, GConName1 g) => GConName1 (f :*: g) where
  gconName1  (x :*: y)                  = gconName1 x ++ gconName1 y
  gconNames1 (_ :: Proxy ((f :*: g) a)) =
    gconNames1 (Proxy :: Proxy (f a)) ++
    gconNames1 (Proxy :: Proxy (g a))

instance GConName1 f => GConName1 (Rec1 f) where
  gconName1                          = gconName1  . unRec1
  gconNames1 (_ :: Proxy (Rec1 f p)) = gconNames1 (Proxy :: Proxy (f p))
