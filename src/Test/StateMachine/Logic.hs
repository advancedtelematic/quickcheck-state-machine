{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StandaloneDeriving        #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Logic
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan.andjelkovic@here.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module defines a predicate logic-like language and its counterexample
-- semantics.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Logic
  ( Logic(..)
  , LogicPredicate(..)
  , dual
  , strongNeg
  , Counterexample(..)
  , Value(..)
  , boolean
  , logic
  , evalLogicPredicate
  , gatherAnnotations
  , (.==)
  , (./=)
  , (.<)
  , (.<=)
  , (.>)
  , (.>=)
  , member
  , notMember
  , (.//)
  , (.&&)
  , (.||)
  , (.=>)
  , forall
  , exists
  )
  where

import Prelude

------------------------------------------------------------------------

data Logic
  = Bot
  | Top
  | Logic :&& Logic
  | Logic :|| Logic
  | Logic :=> Logic
  | Not Logic
  | LogicPredicate LogicPredicate
  | forall a. Show a => Forall [a] (a -> Logic)
  | forall a. Show a => Exists [a] (a -> Logic)
  | Boolean Bool
  | Annotate String Logic

data LogicPredicate
  = forall a. (Eq  a, Show a) => a :== a
  | forall a. (Eq  a, Show a) => a :/= a
  | forall a. (Ord a, Show a) => a :<  a
  | forall a. (Ord a, Show a) => a :<= a
  | forall a. (Ord a, Show a) => a :>  a
  | forall a. (Ord a, Show a) => a :>= a
  | forall t a. (Foldable t, Eq a, Show a, Show (t a)) => Member    a (t a)
  | forall t a. (Foldable t, Eq a, Show a, Show (t a)) => NotMember a (t a)

deriving instance Show LogicPredicate

dual :: LogicPredicate -> LogicPredicate
dual p = case p of
  x :== y          -> x :/= y
  x :/= y          -> x :== y
  x :<  y          -> x :>= y
  x :<= y          -> x :>  y
  x :>  y          -> x :<= y
  x :>= y          -> x :<  y
  x `Member`    xs -> x `NotMember` xs
  x `NotMember` xs -> x `Member`    xs

-- See Yuri Gurevich's "Intuitionistic logic with strong negation" (1977).
strongNeg :: Logic -> Logic
strongNeg l0 = case l0 of
  Bot              -> Top
  Top              -> Bot
  l :&& r          -> strongNeg l :|| strongNeg r
  l :|| r          -> strongNeg l :&& strongNeg r
  l :=> r          ->           l :&& strongNeg r
  Not l            -> l
  LogicPredicate p -> LogicPredicate (dual p)
  Forall xs p      -> Exists xs (strongNeg . p)
  Exists xs p      -> Forall xs (strongNeg . p)
  Boolean b        -> Boolean (not b)
  Annotate s l     -> Annotate s (strongNeg l)

data Counterexample
  = BotC
  | Fst Counterexample
  | Snd Counterexample
  | EitherC Counterexample Counterexample
  | ImpliesC Counterexample
  | NotC Counterexample
  | PredicateC LogicPredicate
  | forall a. Show a => ForallC a Counterexample
  | forall a. Show a => ExistsC [a] [Counterexample]
  | BooleanC
  | AnnotateC String Counterexample

deriving instance Show Counterexample

data Value
  = VFalse Counterexample
  | VTrue
  deriving Show

boolean :: Logic -> Bool
boolean l = case logic l of
  VFalse _ -> False
  VTrue    -> True

logic :: Logic -> Value
logic Bot            = VFalse BotC
logic Top            = VTrue
logic (l :&& r)      = case logic l of
  VFalse ce -> VFalse (Fst ce)
  VTrue     -> case logic r of
    VFalse ce' -> VFalse (Snd ce')
    VTrue      -> VTrue
logic (l :|| r)      = case logic l of
  VTrue     -> VTrue
  VFalse ce -> case logic r of
    VTrue      -> VTrue
    VFalse ce' -> VFalse (EitherC ce ce')
logic (l :=> r)      = case logic l of
  VFalse _ -> VTrue
  VTrue    -> case logic r of
    VTrue     -> VTrue
    VFalse ce -> VFalse (ImpliesC ce)
logic (Not l)        = case logic (strongNeg l) of
  VTrue     -> VTrue
  VFalse ce -> VFalse (NotC ce)
logic (LogicPredicate p) = evalLogicPredicate p
logic (Forall xs0 p) = go xs0
  where
    go []       = VTrue
    go (x : xs) = case logic (p x) of
      VTrue     -> go xs
      VFalse ce -> VFalse (ForallC x ce)
logic (Exists xs0 p) = go xs0 []
  where
    go []       ces = VFalse (ExistsC xs0 (reverse ces))
    go (x : xs) ces = case logic (p x) of
      VTrue     -> VTrue
      VFalse ce -> go xs (ce : ces)
logic (Boolean b)    = if b then VTrue else VFalse BooleanC
logic (Annotate s l) = case logic l of
  VTrue     -> VTrue
  VFalse ce -> VFalse (AnnotateC s ce)

evalLogicPredicate :: LogicPredicate -> Value
evalLogicPredicate p0 = let b = go p0 in case p0 of
  x :== y          -> b (x == y)
  x :/= y          -> b (x /= y)
  x :<  y          -> b (x <  y)
  x :<= y          -> b (x <= y)
  x :>  y          -> b (x >  y)
  x :>= y          -> b (x >= y)
  x `Member`    xs -> b (x `elem`    xs)
  x `NotMember` xs -> b (x `notElem` xs)
  where
    go :: LogicPredicate -> Bool -> Value
    go _ True  = VTrue
    go p False = VFalse (PredicateC (dual p))

-- | Gather user annotations of a true logic expression.
--
-- >>> gatherAnnotations (Top .// "top")
-- ["top"]
--
-- >>> gatherAnnotations ((Bot .// "bot") .|| (Top .// "top"))
-- ["top"]
--
-- >>> gatherAnnotations (Top .// "top1" .&& Top .// "top2")
-- ["top1","top2"]
--
-- >>> gatherAnnotations (Bot .// "bot" .&& Top .// "top")
-- []
--
-- >>> gatherAnnotations (forall [1,2,3] (\i -> 0 .< i .// "positive"))
-- ["positive","positive","positive"]
--
-- >>> gatherAnnotations (forall [0,1,2,3] (\i -> 0 .< i .// "positive"))
-- []
--
-- >>> gatherAnnotations (exists [1,2,3] (\i -> 0 .< i .// "positive"))
-- ["positive"]
gatherAnnotations :: Logic -> [String]
gatherAnnotations = go []
  where
    go _acc Bot = []
    go acc  Top = acc
    go acc (l :&& r) | boolean l && boolean r = go (go acc l) r
                     | otherwise              = acc
    go acc (l :|| r) | boolean l = go acc l
                     | boolean r = go acc r
                     | otherwise = acc
    go acc (l :=> r) | boolean (l :=> r) = go (go acc l) r
                     | otherwise         = acc
    go acc (Not l) | not (boolean l) = go acc l
                   | otherwise       = acc
    go acc (LogicPredicate _p) = acc
    go acc (Forall xs p)
      | boolean (Forall xs p) = acc ++ concat [ go [] (p x)
                                              | x <- xs, boolean (p x)
                                              ]
      | otherwise             = acc
    go acc (Exists xs p)
      | boolean (Exists xs p) = acc ++ concat (take 1 [ go [] (p x)
                                                      | x <- xs, boolean (p x)
                                                      ])
      | otherwise             = acc
    go acc (Boolean _b)   = acc
    go acc (Annotate s l) = go (acc ++ [s]) l

------------------------------------------------------------------------

infix  5 .==
infix  5 ./=
infix  5 .<
infix  5 .<=
infix  5 .>
infix  5 .>=
infix  8 `member`
infix  8 `notMember`
infixl 4 .//
infixr 3 .&&
infixr 2 .||
infixr 1 .=>

(.==) :: (Eq a, Show a) => a -> a -> Logic
x .== y = LogicPredicate (x :== y)

(./=) :: (Eq a, Show a) => a -> a -> Logic
x ./= y = LogicPredicate (x :/= y)

(.<) :: (Ord a, Show a) => a -> a -> Logic
x .< y = LogicPredicate (x :< y)

(.<=) :: (Ord a, Show a) => a -> a -> Logic
x .<= y = LogicPredicate (x :<= y)

(.>) :: (Ord a, Show a) => a -> a -> Logic
x .> y = LogicPredicate (x :> y)

(.>=) :: (Ord a, Show a) => a -> a -> Logic
x .>= y = LogicPredicate (x :>= y)

member :: (Foldable t, Eq a, Show a, Show (t a)) => a -> t a -> Logic
member x xs = LogicPredicate (Member x xs)

notMember :: (Foldable t, Eq a, Show a, Show (t a)) => a -> t a -> Logic
notMember x xs = LogicPredicate (NotMember x xs)

(.//) :: Logic -> String -> Logic
l .// s = Annotate s l

(.&&) :: Logic -> Logic -> Logic
(.&&) = (:&&)

(.||) :: Logic -> Logic -> Logic
(.||) = (:||)

(.=>) :: Logic -> Logic -> Logic
(.=>) = (:=>)

forall :: Show a => [a] -> (a -> Logic) -> Logic
forall = Forall

exists :: Show a => [a] -> (a -> Logic) -> Logic
exists = Exists
