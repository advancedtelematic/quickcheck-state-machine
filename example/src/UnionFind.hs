{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE KindSignatures    #-}

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
import           Test.StateMachine.Internal.Types
                   (Internal(Internal))

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

newtype Ref a v = Ref (v (Opaque (Element a)))

unRef :: Ref a Concrete -> Element a
unRef (Ref (Concrete (Opaque ref))) = ref

instance (Eq a, Eq1 v) => Eq (Ref a v) where
  Ref v1 == Ref v2 = liftEq (==) v1 v2

instance Show1 v => Show (Ref a v) where
  show (Ref v) = showsPrec1 10 v ""

instance Show a => Show (Internal (Action a)) where
  show (Internal (New x)           sym) = "New " ++ show x ++ " (" ++ show sym ++ ")"
  show (Internal (Find ref)        _)   =
    "Find ("  ++ show ref ++ ")"
  show (Internal (Union ref1 ref2) _)   =
    "Union (" ++ show ref1 ++ ") (" ++ show ref2 ++ ")"

------------------------------------------------------------------------

-- The model corresponds closely to the *relational specification* given
-- in section 12 of the paper.

newtype Model a (v :: * -> *) = Model [(Ref a v, Ref a v)]
  deriving Eq

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
  New   _         -> m `extend` (Ref resp, Ref resp)
  Find  _         -> m
  Union ref1 ref2 -> m `extend` (m ! ref1, m ! ref2)

postconditions :: (Eq a, Show a) => Postcondition (Model a) (Action a)
postconditions m act resp = case act of
  New   _         -> property True
  Find  ref       -> unRef (m ! ref) === unOpaque resp .&&. m == m'
    where
    m' = transitions m act (Concrete resp)
  Union ref1 ref2 ->
    let z = m' ! ref1
    in property ((z === m ! ref1 .||. z === m ! ref2) .&&. z === m' ! ref2)
    where
    m' = transitions m act (Concrete resp)

------------------------------------------------------------------------

gen :: (Arbitrary a, Typeable a) => Generator (Model a) (Action a)
gen (Model m)
  | null m    = Untyped . New <$> arbitrary
  | otherwise = frequency
      [ (1, Untyped . New <$> arbitrary)
      , (8, Untyped .    Find  <$> ref m)
      , (8, Untyped <$> (Union <$> ref m <*> ref m))
      ]
    where
    ref = elements . map fst

shrink1 :: Arbitrary a => Action a v resp -> [Action a v resp]
shrink1 (New x) = [ New x' | x' <- shrink x ]
shrink1 _       = []

------------------------------------------------------------------------

semantics :: Action a Concrete resp -> IO resp
semantics (New   x)         = Opaque <$> newElement x
semantics (Find  ref)       = Opaque <$> findElement (unRef ref)
semantics (Union ref1 ref2) = unionElements (unRef ref1) (unRef ref2)

------------------------------------------------------------------------

instance HTraversable (Action a) where
  htraverse _ (New   x)                     = pure (New x)
  htraverse f (Find  (Ref ref))             = Find . Ref <$> f ref
  htraverse f (Union (Ref ref1) (Ref ref2)) = Union <$> (Ref <$> f ref1)
                                                    <*> (Ref <$> f ref2)

instance HFunctor  (Action a)
instance HFoldable (Action a)

instance Show a => ShowAction (Action a) where
  showAction (New   x)         =
    ShowResponse ("New "    ++ show x)                                 show
  showAction (Find  ref)       =
    ShowResponse ("Find ("  ++ show ref ++ ")")                        show
  showAction (Union ref1 ref2) =
    ShowResponse ("Union (" ++ show ref1 ++ ") (" ++ show ref2 ++ ")") show

------------------------------------------------------------------------

prop_unionFind :: Property
prop_unionFind = sequentialProperty
  gen
  shrink1
  preconditions
  transitions
  postconditions
  (initModel :: Model Int v)
  semantics
  ioProperty
