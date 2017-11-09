{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

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

module UnionFind
  ( prop_unionFind
  )
  where

import           Data.Functor.Classes
                   (Eq1(..), Show1(..))
import           Data.IORef
                   (IORef, newIORef, readIORef, writeIORef)
import           Data.Typeable
                   (Typeable)
import           Test.QuickCheck
                   (Arbitrary, Property, arbitrary, elements,
                   frequency, shrink, (===))

import           Test.StateMachine
import           Test.StateMachine.TH
                   (deriveTestClasses)

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

data Action a (v :: * -> *) :: * -> * where
  New   :: a                  -> Action a v (Opaque (Element a))
  Find  :: Ref a v            -> Action a v (Opaque (Element a))
  Union :: Ref a v -> Ref a v -> Action a v ()

deriving instance (Show a, Show1 v) => Show (Action a v resp)

instance Show a => Show1 (Action a Symbolic) where
  liftShowsPrec _ _ _ x _ = show x

type Ref a v = Reference v (Opaque (Element a))

------------------------------------------------------------------------

-- The model corresponds closely to the *relational specification* given
-- in section 12 of the paper.

newtype Model a (v :: * -> *) = Model [(Ref a v, Ref a v)]
  deriving (Eq, Show)

initModel :: Model a v
initModel = Model []

(!) :: (Eq a, Eq1 v) => Model a v -> Ref a v -> Ref a v
Model m ! ref = case lookup ref m of
  Just ref' | ref == ref' -> ref
            | otherwise   -> Model m ! ref'
  Nothing                 -> error "(!): couldn't find key"

extend :: (Eq a, Eq1 v) => Model a v -> (Ref a v, Ref a v) -> Model a v
extend (Model m) p@(ref1, _) = Model (p : filter ((==) ref1 . fst) m)

------------------------------------------------------------------------

preconditions :: Eq a => Precondition (Model a) (Action a)
preconditions (Model m) act = case act of
  New   _         -> True
  Find  ref       -> ref  `elem` map fst m
  Union ref1 ref2 -> ref1 `elem` map fst m &&
                     ref2 `elem` map fst m

transitions :: Eq a => Transition (Model a) (Action a)
transitions m act resp = case act of
  New   _         -> m `extend` (Reference resp, Reference resp)
  Find  _         -> m
  Union ref1 ref2 -> m `extend` (m ! ref1, m ! ref2)

postconditions :: (Eq a, Show a) => Postcondition (Model a) (Action a)
postconditions m act resp = case act of
  New   _         -> True
  Find  ref       -> opaque (m ! ref) == unOpaque resp && m == m'
    where
    m' = transitions m act (Concrete resp)
  Union ref1 ref2 ->
    let z = m' ! ref1
    in (z == m ! ref1 || z == m ! ref2) && z == m' ! ref2
    where
    m' = transitions m act (Concrete resp)

------------------------------------------------------------------------

generator :: (Arbitrary a, Typeable a) => Generator (Model a) (Action a)
generator (Model m)
  | null m    = Untyped . New <$> arbitrary
  | otherwise = frequency
      [ (1, Untyped . New <$> arbitrary)
      , (8, Untyped .    Find  <$> ref m)
      , (8, Untyped <$> (Union <$> ref m <*> ref m))
      ]
    where
    ref = elements . map fst

shrinker :: Arbitrary a => Action a v resp -> [Action a v resp]
shrinker (New x) = [ New x' | x' <- shrink x ]
shrinker _       = []

------------------------------------------------------------------------

semantics :: Action a Concrete resp -> IO resp
semantics (New   x)         = Opaque <$> newElement x
semantics (Find  ref)       = Opaque <$> findElement (opaque ref)
semantics (Union ref1 ref2) = unionElements (opaque ref1) (opaque ref2)

------------------------------------------------------------------------

deriveTestClasses ''Action

sm :: StateMachine (Model Int) (Action Int) IO
sm = stateMachine
  generator shrinker preconditions transitions
  postconditions initModel semantics id

prop_unionFind :: Property
prop_unionFind = monadicSequential sm $ \prog -> do
  (hist, _, res) <- runProgram sm prog
  prettyProgram sm hist $
    checkActionNames prog (res === Ok)
