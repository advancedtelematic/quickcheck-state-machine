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
                   (Arbitrary, Gen, Property, arbitrary, elements,
                   frequency, ioProperty, property, shrink, (.&&.),
                   (.||.), (===))

import           Test.StateMachine
import           Test.StateMachine.Types.References
import           Test.StateMachine.Z (empty, domain)

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
data Element = Element Int (IORef Link)

data Link
  = Weight Int
  | Next Element

instance Eq Element where
  Element _ ref1 == Element _ ref2 = ref1 == ref2

instance Show Element where
  show (Element x _) = "Element " ++ show x

type Ref r = Reference (Opaque Element) r

-- We represent actions in the same way as they do in section 11 of the
-- paper.
data Command r
  = New Int
  | Find (Ref r)
  | Union (Ref r) (Ref r)
  deriving (Show)

data Response r
  = -- | New element was created.
    Created (Ref r)
    -- | Command 'Find' was successful with a return value.
  | Found (Ref r)
    -- | Command 'Union' was successful.
  | United

------------------------------------------------------------------------

-- The model corresponds closely to the *relational specification* given
-- in section 12 of the paper.

newtype Model r = Model [(Ref r, Ref r)]
    deriving Eq

initModel :: Model r
initModel = Model empty

-- Find representative of 'ref'
(!) :: Eq1 r => Model r -> Ref r -> Ref r
Model m ! ref = case lookup ref m of
  Just ref' | ref == ref' -> ref
            | otherwise   -> Model m ! ref'
  Nothing                 -> error "(!): couldn't find key"

extend :: Eq1 r => Model r -> (Ref r, Ref r) -> Model r
extend (Model m) p@(ref1, ref2) = Model (p : filter ((/=) ref1 . fst) m)

------------------------------------------------------------------------

precondition :: Model Symbolic -> Command Symbolic -> Logic
precondition m@(Model model) cmd = case cmd of
  New _           -> Top
  Find ref        -> ref   `member` map fst model
  Union ref1 ref2 -> (ref1 `member` map fst model) :&&
                     (ref2 `member` map fst model) :&&
                     -- TODO: Should we add this condition, or let Union fail
                     -- when the two node belonged to the same equivalence set?
                     (m ! ref1 ./= m ! ref2)

transition :: Eq1 r => Model r -> Command r -> Response r -> Model r
transition m cmd resp = case (cmd, resp) of
  (New _,           Created ref) -> m `extend` (ref, ref)
  (Find ref,        _)           ->
      -- The equivalence relation should be the same after 'find' command.
      m
  (Union ref1 ref2, _)           ->
      -- It doesn't matter whether ref1's root is pointed to ref2's root or vice versa.
      m `extend` (ref1, ref2)

postcondition :: Model Concrete -> Command Concrete -> Response Concrete -> Logic
postcondition m cmd resp = case (cmd, resp) of
  (New _,           Created ref)  -> m' ! ref .== ref
  (Find ref,        Found ref')   -> m ! ref .== ref'
  (Union ref1 ref2, United)       -> m' ! ref1 .== m' ! ref2
  where
      m' = transition m cmd resp

------------------------------------------------------------------------

newElement :: Int -> IO Element
newElement x = do
  ref <- newIORef (Weight 1)
  return (Element x ref)

findElement :: Element -> IO Element
findElement (Element x ref) = do
  e <- readIORef ref
  case e of
    Weight _  -> return (Element x ref)
    Next next -> do
      last' <- findElement next
      writeIORef ref (Next last')
      return last'

unionElements :: Element -> Element -> IO ()
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

semantics :: Command Concrete -> IO (Response Concrete)
semantics (New x)           = Created . Reference . Concrete . Opaque <$> newElement x
semantics (Find ref)        = Found   . Reference . Concrete . Opaque <$> findElement (opaque ref)
semantics (Union ref1 ref2) = United <$  unionElements (opaque ref1) (opaque ref2)

mock :: Model Symbolic -> Command Symbolic -> GenSym (Response Symbolic)
mock (Model m) cmd = case cmd of
  New _           -> Created <$> genSym
  Find ref        -> Found <$> pure (Model m ! ref)
  Union ref1 ref2 -> pure United

generator :: Model Symbolic -> Maybe (Gen (Command Symbolic))
generator (Model m)
  | null m    = Just $ New <$> arbitrary
  | otherwise = Just $ frequency
    [ (1, New <$> arbitrary)
    , (4, Find <$> elements (domain m))
    , (4, Union <$> elements (domain m) <*> elements (domain m))
    ]
