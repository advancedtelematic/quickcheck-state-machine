{-# LANGUAGE KindSignatures #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Types.Generics
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH, Li-yao Xia
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Li-yao Xia <lysxia@gmail.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- Datatype-generic utilities.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Types.Generics where

-- | A constructor name is a string.
newtype Constructor = Constructor String
  deriving (Eq, Ord)

instance Show Constructor where
  show (Constructor c) = c

-- | Extracting constructors from actions.
class Constructors (act :: (* -> *) -> * -> *) where

  -- | Constructor of a given action.
  constructor :: act v a -> Constructor

  -- | Total number of constructors in the action type.
  nConstructors :: proxy act -> Int
