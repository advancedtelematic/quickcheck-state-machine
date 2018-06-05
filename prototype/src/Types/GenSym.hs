{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Types.GenSym where

import           Control.Monad.State
                   (State, get, put, runState)
import           Data.Typeable
                   (Typeable)

import           Types.Reference

------------------------------------------------------------------------

newtype GenSym a = GenSym (State Counter a)
  deriving (Functor, Applicative, Monad)

runGenSym :: GenSym a -> Counter -> (a, Counter)
runGenSym (GenSym m) counter = runState m counter

genSym :: Typeable a => GenSym (Reference a Symbolic)
genSym  = GenSym $ do
  Counter i <- get
  put (Counter (i + 1))
  return (Reference (Symbolic (Var i)))

newtype Counter = Counter Int

newCounter :: Counter
newCounter = Counter 0
