{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE PolyKinds          #-}
{-# LANGUAGE Rank2Types         #-}
{-# LANGUAGE TypeInType         #-}
{-# LANGUAGE TypeOperators      #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Internal.IxMap
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module provides indexed maps. These are used to implement support for
-- multiple references.
--
-----------------------------------------------------------------------------

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

-- | An 'ix'-indexed family of maps.
newtype IxMap (ix :: Type) (k :: Type) (vs :: TyFun ix Type -> Type)
  = IxMap (forall i. Proxy vs -> Sing (i :: ix) -> Map k (vs @@ i))

-- | The empty map.
empty :: IxMap i k vs
empty = IxMap (\_ _ -> M.empty)

-- | Partial lookup function.
(!) :: Ord k => IxMap ix k vs -> (Sing i, k) -> vs @@ i
IxMap m ! (i, k) = m Proxy i M.! k

-- | Total version of the above.
lookup :: Ord k => Sing i -> k -> IxMap ix k vs -> Maybe (vs @@ i)
lookup i k (IxMap m) = M.lookup k (m Proxy i)

-- | Key membership check.
member :: Ord k => Sing (i :: ix) -> k -> IxMap ix k vs -> Bool
member i k (IxMap m) = M.member k (m Proxy i)

-- | Map insertion.
insert
  :: (Ord k, SDecide ix)
  => Sing i -> k -> vs @@ i -> IxMap ix k vs -> IxMap ix k vs
insert i k v (IxMap m) = IxMap $ \_ j -> case i %~ j of
  Proved Refl -> M.insert k v (m Proxy i)
  _           -> m Proxy j

-- | Size of the key set.
size :: Sing (i :: ix) -> IxMap ix k vs -> Int
size i (IxMap m) = M.size (m Proxy i)
