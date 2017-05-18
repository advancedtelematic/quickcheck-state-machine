{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE PolyKinds          #-}
{-# LANGUAGE Rank2Types         #-}
{-# LANGUAGE TypeInType         #-}
{-# LANGUAGE TypeOperators      #-}

module Test.StateMachine.Internal.IxMap
  ( IxMap
  , empty
  , (!)
  , lookup
  , member
  , insert
  , size
  ) where

import           Data.Kind
                   (Type)
import           Data.Map
                   (Map)
import qualified Data.Map                as M
import           Data.Proxy
                   (Proxy(Proxy))
import           Data.Singletons.Decide
                   ((:~:)(Refl), Decision(Proved), SDecide, (%~))
import           Data.Singletons.Prelude
                   (type (@@), Sing, TyFun)
import           Prelude                 hiding
                   (lookup)

------------------------------------------------------------------------

newtype IxMap (ix :: Type) (k :: Type) (vs :: TyFun ix Type -> Type)
  = IxMap (forall i. Proxy vs -> Sing (i :: ix) -> Map k (vs @@ i))

empty :: IxMap i k vs
empty = IxMap (\_ _ -> M.empty)

(!) :: Ord k => IxMap ix k vs -> (Sing i, k) -> vs @@ i
IxMap m ! (i, k) = m Proxy i M.! k

lookup :: Ord k => Sing i -> k -> IxMap ix k vs -> Maybe (vs @@ i)
lookup i k (IxMap m) = M.lookup k (m Proxy i)

member :: Ord k => Sing (i :: ix) -> k -> IxMap ix k vs -> Bool
member i k (IxMap m) = M.member k (m Proxy i)

insert
  :: (Ord k, SDecide ix)
  => Sing i -> k -> vs @@ i -> IxMap ix k vs -> IxMap ix k vs
insert i k v (IxMap m) = IxMap $ \_ j -> case i %~ j of
  Proved Refl -> M.insert k v (m Proxy i)
  _           -> m Proxy j

size :: Sing (i :: ix) -> IxMap ix k vs -> Int
size i (IxMap m) = M.size (m Proxy i)
