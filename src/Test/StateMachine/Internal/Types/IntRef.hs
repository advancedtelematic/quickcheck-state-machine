{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Test.StateMachine.Internal.Types.IntRef
  ( IntRef(..)
  , Pid(..)
  , Ref(..)
  , ConstIntRef
  )
  where

import           Data.Singletons.Prelude          (ConstSym1)

------------------------------------------------------------------------

data IntRef = IntRef Ref Pid
  deriving (Eq, Ord, Show, Read)

newtype Pid = Pid Int
  deriving (Eq, Ord, Show, Read, Num)

newtype Ref = Ref Int
  deriving (Eq, Ord, Show, Read, Num)

type ConstIntRef = ConstSym1 IntRef
