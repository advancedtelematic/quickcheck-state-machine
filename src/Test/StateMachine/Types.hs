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
-- This module contains the main types exposed to the user. The module
-- is perhaps best read indirectly, on a per need basis, via the main
-- module "Test.StateMachine".
--
-----------------------------------------------------------------------------

module Test.StateMachine.Types
  ( StateMachineModel(..)
  , ShowCmd
  , showCmd
  , Signature
  , Response(..)
  , SResponse(..)
  , Response_
  , HasResponse
  , response
  , CommandConstraint
  , Untyped(..)
  , RefPlaceholder
  -- * Indexed variant of 'Functor', 'Foldable' and 'Traversable'.
  , Ex(..)
  , IxFunctor
  , ifmap
  , IxFoldable
  , ifoldMap
  , itoList
  , iany
  , IxTraversable
  , itraverse
  , ifor
  -- * Indexed variants of some 'constraints' package combinators.
  , IxForallF
  , Ords
  , Ords'
  , iinstF
  -- * Re-export
  , (\\)
  , type (@@)
  , Property
  , property
  , Proxy(..)
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
                   (Property, property)

import           Test.StateMachine.Internal.Types.IntRef

------------------------------------------------------------------------

-- | A state machine based model.
data StateMachineModel model cmd = StateMachineModel
  { precondition :: forall refs resp. IxForallF Ord refs =>
      model refs -> cmd refs resp -> Bool
  , postcondition :: forall refs resp. IxForallF Ord refs =>
      model refs -> cmd refs resp -> Response_ refs resp -> Property
  , transition    :: forall refs resp. IxForallF Ord refs =>
      model refs -> cmd refs resp -> Response_ refs resp -> model refs
  , initialModel  :: forall refs. model refs
  }

-- | Given a command, how can we show it?
class ShowCmd (cmd :: Signature ix) where

  -- | How to show a typed command with internal refereces.
  showCmd :: forall resp. cmd ConstIntRef resp -> String

------------------------------------------------------------------------

-- | Signatures of commands contain a family of references and a
--   response type.
type Signature ix = (TyFun ix Type -> Type) -> Response ix -> Type

------------------------------------------------------------------------

-- | A response of a command is either of some type or a referece at
--   some index.
data Response ix
  = Response Type
  | Reference ix

-- | The singleton type of responses.
data SResponse ix :: Response ix -> Type where
  SResponse  ::                     SResponse ix ('Response  t)
  SReference :: Sing (i :: ix)   -> SResponse ix ('Reference i)

-- | Given a command, what kind of response does it have?
class HasResponse cmd where

  -- | What type of response a typed command has.
  response :: cmd refs resp -> SResponse ix resp

-- | Type-level function that returns a response type.
type family Response_ (refs :: TyFun ix Type -> Type)
                      (resp :: Response ix) :: Type where
  Response_ refs ('Response  t) = t
  Response_ refs ('Reference i) = refs @@ i

------------------------------------------------------------------------

-- | The constraints on commands (and their indices) that the
--   'Test.StateMachine.sequentialProperty' and
--   'Test.StateMachine.parallelProperty' helpers require.
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

-- | Untyped commands are command where we hide the response type. This
--   is used in generation of commands.
data Untyped (f :: Signature ix) refs where
  Untyped :: ( Show     (Response_ ConstIntRef resp)
             , Typeable (Response_ ConstIntRef resp)
             , Typeable resp
             ) => f refs resp -> Untyped f refs

------------------------------------------------------------------------

-- | When generating commands it is enough to provide a reference
--   placeholder.
data RefPlaceholder ix :: (TyFun ix k) -> Type

type instance Apply (RefPlaceholder _) i = Sing i

------------------------------------------------------------------------

-- | Dependent pairs.
data Ex (p :: TyFun a Type -> Type) = forall (x :: a). Ex (Sing x) (p @@ x)

-- | Predicate transformers.
class IxFunctor (f :: (TyFun ix Type -> Type) -> jx -> Type) where

  -- | Indexed 'fmap'.
  ifmap
    :: forall p q j. (forall i. Sing (i :: ix) -> p @@ i -> q @@ i)
    -> f p j -> f q j

-- | Foldable for predicate transformers.
class IxFoldable (t :: (TyFun ix Type -> Type) -> jx -> Type) where

  -- | Indexed 'foldMap'.
  ifoldMap :: Monoid m => (forall i. Sing (i :: ix) -> p @@ i -> m) -> t p j -> m

  -- | Indexed 'toList'.
  itoList :: t p j -> [Ex p]
  itoList = ifoldMap (\s px -> [Ex s px])

  -- | Indexed 'foldr'.
  ifoldr :: (forall i. Sing (i :: ix) -> p @@ i -> b -> b) -> b -> t p j -> b
  ifoldr f z = foldr (\(Ex i x) -> f i x) z . itoList

  -- | Indexed 'any'.
  iany :: (forall i. Sing (i :: ix) -> p @@ i -> Bool) -> t p j -> Bool
  iany p = ifoldr (\i x ih -> p i x || ih) False

-- | Tranversable for predicate transformers.
class (IxFunctor t, IxFoldable t) =>
  IxTraversable (t :: (TyFun ix Type -> Type) -> jx -> Type) where

  -- | Indexed traverse function.
  itraverse
    :: Applicative f
    => Proxy q
    -> (forall x. Sing x -> p @@ x -> f (q @@ x))
    -> t p j
    -> f (t q j)
  itraverse pq f tp = ifor pq tp f

  -- | Same as above, with arguments flipped.
  ifor
    :: Applicative f
    => Proxy q
    -> t p j
    -> (forall x. Sing x -> p @@ x -> f (q @@ x))
    -> f (t q j)
  ifor pq tp f = itraverse pq f tp

  {-# MINIMAL itraverse | ifor #-}

------------------------------------------------------------------------

class p (f @@ a) =>
  IxComposeC (p :: k2 -> Constraint) (f :: TyFun k1 k2 -> Type) (a :: k1)

instance p (f @@ a) => IxComposeC p f a

-- | Indexed variant of 'ForallF'.
class Forall (IxComposeC p f) =>
  IxForallF (p :: k2 -> Constraint) (f :: TyFun k1 k2 -> Type)

instance Forall (IxComposeC p f) => IxForallF p f

-- | Indexed variant of 'instF'.
iinstF :: forall a p f. Proxy a -> IxForallF p f :- p (f @@ a)
iinstF _ = Sub $
  case inst :: Forall (IxComposeC p f) :- IxComposeC p f a of
    Sub Dict -> Dict

-- | Type alias that is helpful when defining state machine models.
type Ords refs = IxForallF Ord refs :- Ord (refs @@ '())

-- | Same as the above.
type Ords' refs i = IxForallF Ord refs :- Ord (refs @@ i)
