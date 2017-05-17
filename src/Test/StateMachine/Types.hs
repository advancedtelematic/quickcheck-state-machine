{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE ExplicitNamespaces         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE TypeOperators              #-}

module Test.StateMachine.Types where

import           Data.Kind                        (Type)
import           Data.Singletons.Prelude          (type (@@), Apply,
                                                   Sing, TyFun)
import           Data.Typeable                    (Typeable)
import           Test.QuickCheck.Property         (Property)

import           Test.StateMachine.Internal.Types.IntRef
import           Test.StateMachine.Utils

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
