{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module Test.StateMachine.Internal.IxMap where

import           Data.Kind
import           Data.Map                (Map)
import qualified Data.Map                as M
import           Data.Proxy
import           Data.Singletons.Decide
import           Data.Singletons.Prelude hiding (Map)

------------------------------------------------------------------------

newtype IxMap (ix :: *) (k :: *) (vs :: TyFun ix * -> *) = IxMap
  (forall i. Proxy vs -> Sing (i :: ix) -> Map k (vs @@ i))

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

------------------------------------------------------------------------

data ValuesSym :: (TyFun Bool *) -> *

type instance Apply ValuesSym 'True  = Char
type instance Apply ValuesSym 'False = Int

test0 :: IxMap Bool String ValuesSym
test0
  = insert SFalse "k1" 1
  $ insert STrue  "k1" 'a'
  $ empty

test1 :: Char
test1 = test0 ! (STrue, "k1")

test2 :: Int
test2 = test0 ! (SFalse, "k1")

test3 :: Int
test3 = size STrue test0
