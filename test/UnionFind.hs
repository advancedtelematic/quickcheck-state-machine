{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE UndecidableInstances  #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  UnionFind
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains a specification for an imperative-style union/find
-- algorithm.
--
-----------------------------------------------------------------------------

module UnionFind where

import           Data.Functor.Classes
                   (Eq1(..), Show1(..), showsPrec1)
import           Data.IORef
                   (IORef, newIORef, readIORef, writeIORef)
import           Data.Typeable
                   (Typeable)
import           Test.QuickCheck
                   (Arbitrary, Property, arbitrary, elements,
                   frequency, ioProperty, property, shrink, (.&&.),
                   (.||.), (===))

import           Test.StateMachine
import           Test.StateMachine.Types.References

------------------------------------------------------------------------

-- The union/find algorithm is basically an efficient way of
-- implementing an equivalence relation.
--
-- This example is borrowed from the paper
-- <http://www.cse.chalmers.se/~rjmh/Papers/QuickCheckST.ps *Testing
-- monadic code with QuickCheck*> by Koen Claessen and John Hughes
-- (2002).
--
-- Let's start with the implementation of the algorithm, which we have
-- taken from the paper.

-- Our implementation is slightly different in that we use @IORef@s
-- instead of @STRef@s (see issue #84).
data Element a = Element a (IORef (Link a))

data Link a
  = Weight Int
  | Next (Element a)

newElement :: a -> IO (Element a)
newElement x = do
  ref <- newIORef (Weight 1)
  return (Element x ref)

findElement :: Element a -> IO (Element a)
findElement (Element x ref) = do
  e <- readIORef ref
  case e of
    Weight _  -> return (Element x ref)
    Next next -> do
      last' <- findElement next
      writeIORef ref (Next last')
      return last'

unionElements :: Element a -> Element a -> IO ()
unionElements e1 e2 = do

  Element x1 ref1 <- findElement e1
  Element x2 ref2 <- findElement e2
  Weight w1       <- readIORef ref1
  Weight w2       <- readIORef ref2

  if w1 <= w2
  then do
    writeIORef ref1 (Next (Element x2 ref2))
    writeIORef ref2 (Weight (w1 + w2))
  else do
    writeIORef ref2 (Next (Element x1 ref1))
    writeIORef ref1 (Weight (w1 + w2))

instance Eq (Element a) where
  Element _ ref1 == Element _ ref2 = ref1 == ref2

instance Show a => Show (Element a) where
  show (Element x _) = "Element " ++ show x

------------------------------------------------------------------------

-- We represent actions in the same way as they do in section 11 of the
-- paper.

data Ref a = Ref (Concrete (Opaque (Element a)))

unRef :: Ref a -> Element a
unRef (Ref (Concrete (Opaque ref))) = ref

data Action a
  = New
  | Find (Ref a)
  | Union (Ref a) (Ref a)

data Response a
  = -- | New element was created.
    Created (Ref a)
    -- | Action 'Find' was successful with a return value.
  | Found (Element a)
    -- | Action 'Find' was unsuccessful.
  | NotFound
    -- | Action 'Union' was successful.
  | UnionSucceed
    -- | Action 'Union' was unsuccessful as the two argument already belonged to the same tree.
  | IdenticalRoot

instance Eq a => Eq (Ref a) where
  Ref v1 == Ref v2 = liftEq (==) v1 v2

instance Show a => Show (Ref a) where
  show (Ref v) = showsPrec1 10 v ""

instance Show a => Show (Action a) where
  show New               = "New"
  show (Find ref)        = "Find ("  ++ show ref ++ ")"
  show (Union ref1 ref2) = "Union (" ++ show ref1 ++ ") (" ++ show ref2 ++ ")"
