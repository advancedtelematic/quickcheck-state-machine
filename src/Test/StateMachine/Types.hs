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

import           Data.Kind                    (type (*), Type)
import           Data.Monoid                  ((<>))
import           Data.Singletons.Prelude      (type (@@), Apply, ConstSym1,
                                               Sing, TyFun)
import           Data.Typeable                (Typeable)
import           Test.QuickCheck.Property     (Property)
import           Text.PrettyPrint.ANSI.Leijen (Pretty, align, dot, indent, int,
                                               pretty, text, underline, vsep,
                                               (<+>))

import           Test.StateMachine.Utils

------------------------------------------------------------------------
-- * Signatures.

type Signature ix = Response ix -> (TyFun ix * -> *) -> *

------------------------------------------------------------------------
-- * Response related types.

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

class HasResponse cmd where
  response :: cmd resp refs -> SResponse ix resp

------------------------------------------------------------------------
-- * Internal/integer references.

data IntRef = IntRef Ref Pid
  deriving (Eq, Ord, Show, Read)

newtype Pid = Pid Int
  deriving (Eq, Ord, Show, Read, Num)

newtype Ref = Ref Int
  deriving (Eq, Ord, Show, Read, Enum, Num)

type ConstIntRef = ConstSym1 IntRef

------------------------------------------------------------------------

data Untyped (f :: Signature ix) refs where
  Untyped :: ( Show     (Response_ ConstIntRef resp)
             , Typeable (Response_ ConstIntRef resp)
             , Typeable resp
             ) => f resp refs -> Untyped f refs

data IntRefed (f :: Signature ix) where
  IntRefed :: ( Show     (Response_ ConstIntRef resp)
              , Typeable (Response_ ConstIntRef resp)
              , Typeable resp
              ) => f resp ConstIntRef -> MayResponse_ ConstIntRef resp -> IntRefed f

------------------------------------------------------------------------

data RefPlaceholder ix :: (TyFun ix *) -> *

type instance Apply (RefPlaceholder _) i = Sing i

------------------------------------------------------------------------

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

class ShowCmd (cmd :: Signature ix) where
  showCmd :: forall resp. cmd resp (ConstSym1 IntRef) -> String

------------------------------------------------------------------------

showFork:: (a -> String) -> Fork a -> String
showFork showx (Fork l p r) =
  "Fork (" ++ showx l ++ ") (" ++ showx p ++ ") (" ++ showx r ++ ")"

showIntRefedList :: (ShowCmd cmd, HasResponse cmd) => [IntRefed cmd] -> String
showIntRefedList = showList'
  (\(IntRefed cmd miref) -> showCmd cmd ++ " " ++
       case response cmd of
         SResponse    -> "()"
         SReference _ -> "(" ++ show miref ++ ")")
  where
  showList' :: (a -> String) ->  [a] -> String
  showList' _     []       = "[]"
  showList' showx (x : xs) = '[' : showx x ++ showl xs
    where
    showl []       = "]"
    showl (y : ys) = ',' : showx y ++ showl ys
