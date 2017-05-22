{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ExplicitNamespaces        #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE IncoherentInstances       #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeInType                #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE UndecidableSuperClasses   #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Types
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-----------------------------------------------------------------------------

module Test.StateMachine.Types
  ( CommandConstraint
  , Signature
  , Response(..)
  , SResponse(..)
  , Response_
  , HasResponse
  , response
  , Untyped(..)
  , RefPlaceholder
  , StateMachineModel(..)
  , ShowCmd
  , showCmd
  , IxForallF
  , Ords
  , iinstF
  , Ex(..)
  , IxFunctor
  , ifmap
  , IxFoldable
  , ifoldMap
  , itoList
  , iany
  , IxTraversable
  , ifor
  ) where

import           Data.Constraint
import           Data.Constraint.Forall
import           Data.Kind
                   (Type)
import           Data.Proxy
                   (Proxy(..))
import           Data.Singletons.Prelude
                   (type (@@), Apply, Sing, TyFun)
import           Data.Singletons.TH
                   (DemoteRep, SDecide, SingKind)
import           Data.Typeable
                   (Typeable)
import           Test.QuickCheck.Property
                   (Property)

import           Test.StateMachine.Internal.Types.IntRef

------------------------------------------------------------------------

type CommandConstraint ix cmd =
  ( Ord       ix
  , SDecide   ix
  , SingKind  ix
  , DemoteRep ix ~ ix
  , ShowCmd       cmd
  , IxTraversable cmd
  , HasResponse   cmd
  )

------------------------------------------------------------------------
-- * Signatures.

type Signature ix = (TyFun ix Type -> Type) -> Response ix -> Type

------------------------------------------------------------------------
-- * Response related types.

data Response ix
  = Response Type
  | Reference ix

data SResponse ix :: Response ix -> Type where
  SResponse  ::                     SResponse ix ('Response  t)
  SReference :: Sing (i :: ix)   -> SResponse ix ('Reference i)

type family Response_ (refs :: TyFun ix k -> Type) (resp :: Response ix) :: k where
  Response_ refs ('Response  t) = t
  Response_ refs ('Reference i) = refs @@ i

class HasResponse cmd where
  response :: cmd refs resp -> SResponse ix resp

------------------------------------------------------------------------

data Untyped (f :: Signature ix) refs where
  Untyped :: ( Show     (Response_ ConstIntRef resp)
             , Typeable (Response_ ConstIntRef resp)
             , Typeable resp
             ) => f refs resp -> Untyped f refs

------------------------------------------------------------------------

data RefPlaceholder ix :: (TyFun ix k) -> Type

type instance Apply (RefPlaceholder _) i = Sing i

------------------------------------------------------------------------

data StateMachineModel model cmd = StateMachineModel
  { precondition  :: forall refs resp. IxForallF Ord refs =>
      model refs -> cmd refs resp -> Bool
  , postcondition :: forall refs resp. IxForallF Ord refs =>
      model refs -> cmd refs resp -> Response_ refs resp -> Property
  , transition    :: forall refs resp. IxForallF Ord refs =>
      model refs -> cmd refs resp -> Response_ refs resp -> model refs
  , initialModel  :: forall refs. model refs
  }

class ShowCmd (cmd :: Signature ix) where
  showCmd :: forall resp. cmd ConstIntRef resp -> String

------------------------------------------------------------------------

class p (f @@ a) =>
  IxComposeC (p :: k2 -> Constraint) (f :: TyFun k1 k2 -> Type) (a :: k1)

instance p (f @@ a) => IxComposeC p f a

class Forall (IxComposeC p f) =>
  IxForallF (p :: k2 -> Constraint) (f :: TyFun k1 k2 -> Type)

instance Forall (IxComposeC p f) => IxForallF p f

iinstF :: forall a p f. Proxy a -> IxForallF p f :- p (f @@ a)
iinstF _ = Sub $
  case inst :: Forall (IxComposeC p f) :- IxComposeC p f a of
    Sub Dict -> Dict

type Ords refs = IxForallF Ord refs :- Ord (refs @@ '())

------------------------------------------------------------------------

data Ex (p :: TyFun a Type -> Type) = forall (x :: a). Ex (Sing x) (p @@ x)

class IxFunctor (f :: (TyFun ix Type -> Type) -> jx -> Type) where
  ifmap :: forall p q j. (forall i. Sing (i :: ix) -> p @@ i -> q @@ i) -> f p j -> f q j

class IxFoldable (t :: (TyFun ix Type -> Type) -> jx -> Type) where

  ifoldMap :: Monoid m => (forall i. Sing (i :: ix) -> p @@ i -> m) -> t p j -> m

  itoList :: t p j -> [Ex p]
  itoList = ifoldMap (\s px -> [Ex s px])

  ifoldr :: (forall i. Sing (i :: ix) -> p @@ i -> b -> b) -> b -> t p j -> b
  ifoldr f z = foldr (\(Ex i x) -> f i x) z . itoList

  iany :: (forall i. Sing (i :: ix) -> p @@ i -> Bool) -> t p j -> Bool
  iany p = ifoldr (\i x ih -> p i x || ih) False

class (IxFunctor t, IxFoldable t) => IxTraversable (t :: (TyFun ix Type -> Type) -> jx -> Type) where

  itraverse
    :: Applicative f
    => Proxy q
    -> (forall x. Sing x -> p @@ x -> f (q @@ x))
    -> t p j
    -> f (t q j)
  itraverse pq f tp = ifor pq tp f

  ifor
    :: Applicative f
    => Proxy q
    -> t p j
    -> (forall x. Sing x -> p @@ x -> f (q @@ x))
    -> f (t q j)
  ifor pq tp f = itraverse pq f tp

  {-# MINIMAL itraverse | ifor #-}
