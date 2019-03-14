{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
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
import           Test.StateMachine.Z (empty)

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

type Ref a r = Reference (Opaque (Element a)) r

data Command a r
  = New a
  | Find (Ref a r)
  | Union (Ref a r) (Ref a r)
  deriving (Show)

data Response a r
  = -- | New element was created.
    Created (Ref a r)
    -- | Command 'Find' was successful with a return value.
  | Found (Element a)
    -- | Command 'Union' was successful.
  | United

------------------------------------------------------------------------

-- The model corresponds closely to the *relational specification* given
-- in section 12 of the paper.

newtype Model a r = Model [(Ref a r, Ref a r)]
    deriving Eq

initModel :: Model a r
initModel = Model empty

(!) :: (Eq a, Eq1 r) => Model a r -> Ref a r -> Ref a r
Model m ! ref = case lookup ref m of
  Just ref' | ref == ref' -> ref
            | otherwise   -> Model m ! ref'
  Nothing                 -> error "(!): couldn't find key"

extend :: (Eq a, Eq1 r) => Model a r -> (Ref a r, Ref a r) -> Model a r
extend (Model m) p@(ref1, ref2) = Model (p : filter ((/=) ref1 . fst) m)

------------------------------------------------------------------------

precondition :: Eq a => Model a Symbolic -> Command a Symbolic -> Logic
precondition m@(Model model) cmd = case cmd of
  New _           -> Top
  Find ref        -> ref   `member` map fst model
  Union ref1 ref2 -> (ref1 `member` map fst model) :&&
                     (ref2 `member` map fst model) :&&
                     (m ! ref1 ./= m ! ref2)

transition :: (Show a, Eq a, Eq1 r) => Model a r -> Command a r -> Response a r -> Model a r
transition m cmd resp = case (cmd, resp) of
  (New _,           Created ref) -> m `extend` (ref, ref)
  (Find ref,        _)           -> m
  (Union ref1 ref2, _)           -> m `extend` (ref1, ref2)

postcondition :: (Show a, Eq a) => Model a Concrete -> Command a Concrete -> Response a Concrete -> Logic
postcondition m cmd resp = case (cmd, resp) of
  (New _,           Created ref)  -> m' ! ref .== ref
      where
          m' = transition m cmd resp
  (Find ref,        Found ref')   -> opaque (m ! ref) .== ref'
  (Union ref1 ref2, United) -> m' ! ref1 .== m' ! ref2
      where
          m' = transition m cmd resp

semantics :: Typeable a => Command a Concrete -> IO (Response a Concrete)
semantics (New x)           = Created . Reference . Concrete . Opaque <$> newElement x
semantics (Find ref)        = Found  <$> findElement (opaque ref)
semantics (Union ref1 ref2) = United <$  unionElements (opaque ref1) (opaque ref2)
