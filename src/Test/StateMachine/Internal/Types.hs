{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE UndecidableInstances #-}

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
-- This module exports some types that are used internally by the library.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Internal.Types
  ( Pid(..)
  , Fork(..)
  , Internal(..)
  , Program(..)
  ) where

import           Data.List
                   (intercalate)
import           Data.Set
                   (Set)
import qualified Data.Set                as S
import           Data.Typeable
                   (Typeable)
import           Text.Read
                   (readListPrec, readListPrecDefault, readPrec)

import           Test.StateMachine.Types

------------------------------------------------------------------------

-- | A process id.
newtype Pid = Pid Int
  deriving (Eq, Show)

-- | Forks are used to represent parallel programs. They have a
--   sequential prefix (the middle argument of the constructor), and two
--   parallel suffixes (the left- and right-most argument of the
--   constructor).
data Fork a = Fork a a a
  deriving (Eq, Functor, Show, Ord, Read)

------------------------------------------------------------------------

-- | An internal action is an action together with the symbolic variable that
--   will hold its result.
data Internal (act :: (* -> *) -> * -> *) where
  Internal :: Typeable resp =>
    act Symbolic resp -> Symbolic resp -> Internal act

-- | A program as a list of internal actions.
data Program act = Program { unProgram :: [Internal act] }

instance Monoid (Program act) where
  mempty                                = Program []
  Program acts1 `mappend` Program acts2 = Program (acts1 ++ acts2)

instance Read (Internal act) => Read (Program act) where
  readPrec     = Program <$> readPrec
  readListPrec = readListPrecDefault

instance Eq (Internal act) => Eq (Program act) where
  Program acts1 == Program acts2 = acts1 == acts2

instance (ShowAction act, HFoldable act) => Show (Program act) where
  show (Program iacts) = bracket . intercalate "," . map go $ iacts
    where

    go (Internal act (Symbolic var))
      | var `S.member` usedRefs = sact ++ " (" ++ show var ++ ")"
      | otherwise               = sact ++ " (" ++ show var ++ ")"
      where
      sact = theAction (showAction act)

    bracket s = "[" ++ s ++ "]"

    usedRefs :: Set Var
    usedRefs = foldMap (\(Internal act _) ->
                 hfoldMap (\(Symbolic v) -> S.singleton v) act) iacts
