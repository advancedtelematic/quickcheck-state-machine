{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeApplications      #-}
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

import           Control.Monad.State
                   (StateT, evalStateT, get, liftIO, modify)
import           Data.Functor.Classes
                   (Eq1(..), Show1(..), showsPrec1)
import           Data.IORef
                   (IORef, newIORef, readIORef, writeIORef)
import           Test.QuickCheck
                   (Arbitrary, Property, arbitrary, choose, frequency,
                   ioProperty, property, shrink)

import           Test.StateMachine.Prototype

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
  New   :: a                  -> Action a v (Opaque (Ref a v))
  Find  :: Ref a v            -> Action a v (Opaque (Ref a v))
  Union :: Ref a v -> Ref a v -> Action a v ()

data Ref a v = Ref (v (Opaque (Element a)))

unRef :: Ref a Concrete -> Element a
unRef (Ref (Concrete (Opaque ref))) = ref

instance (Eq a, Eq1 v) => Eq (Ref a v) where
  Ref v1 == Ref v2 = liftEq (==) v1 v2

instance Show1 v => Show (Ref a v) where
  show (Ref v) = showsPrec1 10 v ""

instance Show a => Show (Internal (Action a)) where
  show (Internal (New x)           _) = "New " ++ show x
  show (Internal (Find ref)        _) = "Find ("  ++ show ref ++ ")"
  show (Internal (Union ref1 ref2) _) = "Union (" ++ show ref1 ++ ") (" ++ show ref2 ++ ")"

------------------------------------------------------------------------

-- The model corresponds closely to the *relational specification* given
-- in section 12 of the paper.

newtype Model a (v :: * -> *) = Model [(Ref a v, Element a)]
  deriving Show

initModel :: Model a v
initModel = Model []

------------------------------------------------------------------------

preconditions :: Precondition (Model a) (Action a)
preconditions (Model m) cmd = case cmd of
  New   _         -> True
  Find  ref       -> undefined -- ref  < length m
  Union ref1 ref2 -> undefined -- ref1 < length m && ref2 < length m

transitions :: Transition (Model a) (Action a)
transitions (Model m) cmd resp = undefined {- case cmd of
  New   _         -> Model (m ++ [resp])
  Find  _         -> Model m
  Union ref1 ref2 ->
    let z  = resp -- In the relational specifiaction in the paper @m' !!
                  -- ref1@ is used instead of @resp@ here. With our
                  -- modification to the return type of union, we see
                  -- that this is the same thing.
        m' = [ if z' == m !! ref1 || z' == m !! ref2
               then z else z'
             | z' <- m
             ]
    in Model m'
-}

postconditions :: Postcondition (Model a) (Action a)
postconditions (Model m) cmd resp = undefined {- case cmd of
  New   _         -> property True
  Find  ref       -> property (resp == m !! ref)
  Union ref1 ref2 ->
    let z = m' !! ref1
    in property $ (z == m !! ref1 || z == m !! ref2) && z == m' !! ref2
  where
  Model m' = transitions (Model m) cmd (Concrete resp)
-}

------------------------------------------------------------------------

-- The generation of actions is parametrised by the number of @New@'s
-- that have been generated.

gen :: Generator (Model a) (Action a)
gen = undefined
  {-
  { generator     = \n -> frequency
     [ (1, Untyped .    New   <$> arbitrary)
     , (5, Untyped .    Find  <$> choose (0, n - 1))
     , (5, Untyped <$> (Union <$> choose (0, n - 1) <*> choose (0, n - 1)))
     ]
  , gprecondition = gprecondition'
  , gtransition   = gtransition'
  , initGenState  = 0
  }
  where
  gprecondition' :: Int -> Action refs resp -> Bool
  gprecondition' _ (New   _)   = True
  gprecondition' n (Find  i)   = withIn n i
  gprecondition' n (Union i j) = withIn n i && withIn n j

  withIn n i = 0 <= i && i < n

  gtransition' :: Int -> Action refs resp -> Int
  gtransition' n (New _) = n + 1
  gtransition' n _       = n
-}

shrink1 :: Arbitrary a => Action a v resp -> [Action a v resp]
shrink1 (New x) = [ New x' | x' <- shrink x ]
shrink1 _       = []

------------------------------------------------------------------------

semantics :: Action a Concrete resp -> StateT (Model a Concrete) IO resp
semantics (New   x)         = do
  el <- liftIO (newElement x)
  modify undefined
  return undefined

semantics (Find  ref)       = undefined -- findElement ref
semantics (Union ref1 ref2) = undefined -- unionElements ref1 ref2

------------------------------------------------------------------------

instance HTraversable (Action a) where
  htraverse _ (New   x)                     = undefined -- pure (New x)
  htraverse f (Find  (Ref ref))             = undefined -- Find . Ref <$> f ref
  htraverse f (Union (Ref ref1) (Ref ref2)) = undefined

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
  (ioProperty . flip evalStateT initModel)
