{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE PolyKinds          #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeInType         #-}
{-# LANGUAGE TypeOperators      #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Internal.Types
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-----------------------------------------------------------------------------

module Test.StateMachine.Internal.Types
  ( IntRef(..)
  , Pid(..)
  , Ref(..)
  , ConstIntRef
  , IntRefed(..)
  , Fork(..)
  , showFork
  , showIntRefedList
  , MayResponse_
  ) where

import           Data.Kind
                   (Type)
import           Data.Monoid
                   ((<>))
import           Data.Singletons.Prelude
                   (type (@@), TyFun)
import           Data.Typeable
                   (Typeable)
import           Text.PrettyPrint.ANSI.Leijen
                   (Pretty, align, dot, indent, int, pretty, text,
                   underline, vsep, (<+>))

import           Test.StateMachine.Internal.Types.IntRef
import           Test.StateMachine.Types

------------------------------------------------------------------------

type family MayResponse_ (refs :: TyFun ix k -> Type) (resp :: Response ix) :: k where
  MayResponse_ refs ('Response  t) = ()
  MayResponse_ refs ('Reference i) = refs @@ i

data IntRefed (f :: Signature ix) where
  IntRefed :: ( Show     (Response_ ConstIntRef resp)
              , Typeable (Response_ ConstIntRef resp)
              , Typeable resp
              ) => f ConstIntRef resp -> MayResponse_ ConstIntRef resp -> IntRefed f

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
