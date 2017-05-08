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

import           Data.Kind                    (type (*), Type)
import           Data.Monoid                  ((<>))
import           Data.Singletons.Prelude      (type (@@), Apply, ConstSym1,
                                               Sing, TyFun)
import           Data.Typeable                (Typeable)
import           Test.QuickCheck.Property     (Property)
import           Text.PrettyPrint.ANSI.Leijen (Pretty, align, dot, indent, int,
                                               pretty, prettyList, text,
                                               underline, vsep, (<+>))

import           Test.StateMachine.Utils

------------------------------------------------------------------------

data Response ix
  = Response Type
  | Reference ix

data SResponse ix :: Response ix -> * where
  SResponse  ::                     SResponse ix ('Response  t)
  SReference :: Sing (i :: ix)   -> SResponse ix ('Reference i)

type family Response_ (refs :: TyFun ix k -> *) (resp :: Response ix) :: k where
  Response_ refs ('Response  t) = t
  Response_ refs ('Reference i) = refs @@ i

type family MayResponse_ (refs :: TyFun ix k -> *) (resp :: Response ix) :: k where
  MayResponse_ refs ('Response  t) = ()
  MayResponse_ refs ('Reference i) = refs @@ i

newtype Pid = Pid Int
  deriving (Eq, Ord, Show, Read, Num)

newtype Ref = Ref Int
  deriving (Eq, Ord, Show, Read, Enum, Num)

data IntRef = IntRef Ref Pid
  deriving (Eq, Ord, Show, Read)

data Untyped (f :: Response resp -> (TyFun i * -> *) -> *) refs where
  Untyped :: (Show (Response_ (ConstSym1 IntRef) resp),
               Typeable (Response_ (ConstSym1 IntRef) resp),
               Typeable resp) => f resp refs -> Untyped f refs

data Untyped' (f :: Response resp -> (TyFun i * -> *) -> *) refs where
  Untyped' :: (Show     (Response_ refs resp),
                Typeable (Response_ refs resp),
                Typeable resp
               ) =>
    f resp refs -> MayResponse_ (ConstSym1 IntRef) resp -> Untyped' f refs

data IxRefs ix :: (TyFun ix *) -> *

type instance Apply (IxRefs _) i = Sing i

data StateMachineModel model cmd = StateMachineModel
  { precondition  :: forall refs resp. IxForallF Ord refs =>
      model refs -> cmd resp refs -> Bool
  , postcondition :: forall refs resp. IxForallF Ord refs =>
      model refs -> cmd resp refs -> Response_ refs resp -> Property
  , transition    :: forall refs resp. IxForallF Ord refs =>
      model refs -> cmd resp refs -> Response_ refs resp -> model refs
  , initialModel  :: forall refs.      model refs
  }

data Fork a = Fork a a a
  deriving (Eq, Functor, Show, Ord, Read)

instance Pretty a => Pretty (Fork a) where
  pretty (Fork l p r) = vsep
    [ underline $ text "Prefix:"
    , indent 5 $ pretty p
    , underline $ text "Parallel:"
    , indent 2 $ int 1 <> dot <+> align (pretty l)
    , indent 2 $ int 2 <> dot <+> align (pretty r)
    ]

class ShowCmd (cmd :: Response ix -> (TyFun ix * -> *) -> *) (refs :: TyFun ix * -> *) where
  showCmd :: forall resp. cmd resp refs -> String

data Rose a = Rose a [Rose a]
  deriving Show

fromRose :: Rose a -> [a]
fromRose (Rose x xs) = x : concatMap fromRose xs
