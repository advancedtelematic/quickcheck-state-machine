{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators   #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Z
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan@advancedtelematic.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- This module contains Z-inspried combinators for working with relations. The
-- idea is that they can be used to define concise and showable models. This
-- module is an experiment and will likely change or move to its own package.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Z where

import qualified Data.List as List

------------------------------------------------------------------------

infixr 1 ==>

-- | Logical implication.
(==>) :: Bool -> Bool -> Bool
True  ==> p  = p
False ==> _  = True

infix 0 <==>

-- | Logical equivalence.
(<==>) :: Bool -> Bool -> Bool
p <==> q = p ==> q && q ==> p

forall :: [a] -> (a -> Bool) -> Bool
forall = flip all

exists :: [a] -> (a -> Bool) -> Bool
exists = flip any

------------------------------------------------------------------------

-- | Power set.
type Pow a = [a]

-- | Union.
(\/) :: Eq a => [a] -> [a] -> [a]
(\/) = List.union

unions :: Eq a => [[a]] -> [a]
unions = foldr (\xs ih -> xs \/ ih) []

union :: Eq b => [a] -> (a -> [b]) -> [b]
union xs f = unions [ f x | x <- xs ]

-- | Intersection.
(/\) :: Eq a => [a] -> [a] -> [a]
(/\) = List.intersect

-- | Cartesian product.
x :: [a] -> [b] -> Rel a b
xs `x` ys = [ (x, y)
            | x <- xs
            , y <- ys
            ]

-- | Subset.
(<:) :: Eq a => [a] -> [a] -> Bool
r <: s = r == r /\ s

-- | Set equality.
(~=) :: Eq a => [a] -> [a] -> Bool
xs ~= ys = xs <: ys && ys <: xs

------------------------------------------------------------------------

type Finite a = (Bounded a, Enum a, Eq a)

universe :: Finite a => [a]
universe = enumFrom minBound

------------------------------------------------------------------------

-- * Pairs and binary relations.

-- | Maplet.
(|->) :: a -> b -> (a, b)
x |-> y = (x, y)

-- | Binary relations.
type Rel a b = Pow (a, b)
type a <-> b = Rel a b

domain :: Rel a b -> [a]
domain xys = [ x | (x, _) <- xys ]

codomain :: Rel a b -> [b]
codomain xys = [ y | (_, y) <- xys ]

singleton :: a -> b -> Rel a b
singleton x y = [x |-> y]

identity :: [a] -> Rel a a
identity xs = [ (x, x) | x <- xs ]

compose :: Eq b => Rel b c -> Rel a b -> Rel a c
compose yzs xys =
  [ (x, z)
  | (x, y)  <- xys
  , (y', z) <- yzs
  , y == y'
  ]

fcompose :: Eq b => Rel a b -> Rel b c -> Rel a c
fcompose r s = compose s r

inverse :: Rel a b -> Rel b a
inverse xys = [ (y, x) | (x, y) <- xys ]

------------------------------------------------------------------------

-- | Domain restriction.
--
-- >>> ['a'] <| [ ('a', "apa"), ('b', "bepa") ]
-- [('a',"apa")]
--
(<|) :: Eq a => [a] -> Rel a b -> Rel a b
xs <| xys = [ (x, y) | (x, y) <- xys, x `elem` xs ]

-- | Codomain restriction.
--
-- >>> [ ('a', "apa"), ('b', "bepa") ] |> ["apa"]
-- [('a',"apa")]
--
(|>) :: Eq b => Rel a b -> [b] -> Rel a b
xys |> ys = [ (x, y) | (x, y) <- xys, y `elem` ys ]

-- | Domain substraction.
--
-- >>> ['a'] <<| [ ('a', "apa"), ('b', "bepa") ]
-- [('b',"bepa")]
--
(<<|) :: Eq a => [a] -> Rel a b -> Rel a b
xs <<| xys = [ (x, y) | (x, y) <- xys, x `notElem` xs ]

-- | Codomain substraction.
--
-- >>> [ ('a', "apa"), ('b', "bepa") ] |>> ["apa"]
-- [('b',"bepa")]
--
(|>>) :: Eq b => Rel a b -> [b] -> Rel a b
xys |>> ys = [ (x, y) | (x, y) <- xys, y `notElem` ys ]

-- | The image of a relation.
image :: Eq a => Rel a b -> [a] -> [b]
image r xs = codomain (xs <| r)

-- | Overriding.
--
-- >>> [('a', "apa")] <+ [('a', "bepa")]
-- [('a',"bepa")]
--
-- >>> [('a', "apa")] <+ [('b', "bepa")]
-- [('a',"apa"),('b',"bepa")]
--
(<+) :: (Eq a, Eq b) => Rel a b -> Rel a b -> Rel a b
r <+ s  = domain s <<| r \/ s

-- | Direct product.
(><) :: Eq a => Rel a b -> Rel a c -> Rel a (b, c)
xys >< xzs =
  [ (x, (y, z))
  | (x , y) <- xys
  , (x', z) <- xzs
  , x == x'
  ]

-- | Parallel product.
--
-- >>> [(1, 2), (3, 4)] <||> [(5, 6), (7, 8), (9, 10)]
-- [((1,5),(2,6)),((1,7),(2,8)),((1,9),(2,10)),((3,5),(4,6)),((3,7),(4,8)),((3,9),(4,10))]
--
(<||>) :: Rel a c -> Rel b d -> Rel (a, b) (c, d)
acs <||> bds =
  [ ((a, b), (c, d))
  | (a, c) <- acs
  , (b, d) <- bds
  ]

-- | Division.
(-:-) :: Rel a b -> [b] -> [a]
r -:- xs = undefined

------------------------------------------------------------------------

-- | (Partial) functions.
type Fun a b = Rel a b

-- | Application.
(!) :: Eq a => Rel a b -> a -> Maybe b
xys ! x = lookup x xys

(.!) :: Rel a b -> a -> (Rel a b, a)
f .! x = (f, x)

-- | Assignment.
--
-- >>> singleton 'a' "apa" .! 'a' .= "bepa"
-- [('a',"bepa")]
--
-- >>> singleton 'a' "apa" .! 'b' .= "bepa"
-- [('a',"apa"),('b',"bepa")]
--
(.=) :: (Eq a, Eq b) => (Rel a b, a) -> b -> Rel a b
(f, x) .= y = f <+ singleton x y

------------------------------------------------------------------------

-- * Closure.

-- | Reflexive closure.
rcl :: Eq a => Rel a a -> [a] -> Rel a a
rcl r xs = r \/ identity xs

rcl' :: Finite a => Rel a a -> Rel a a
rcl' r = rcl r universe

-- | Symmetric closure.
scl :: Eq a => Rel a a -> Rel a a
scl r = r \/ inverse r

-- | Iteration.
iter :: Eq a => Int -> Rel a a -> [a] -> Rel a a
iter 0 _ xs         = identity xs
iter 1 r _          = r
iter n r xs | n > 1 = r `fcompose` iter (n - 1) r xs
            | n < 0 = iter n (inverse r) xs

-- | Transitive closure.
plus :: Eq a => Rel a a -> Rel a a
plus r = union [1..] (\n -> iter n r [])

-- | Reflexive transitive closure.
star :: Eq a => Rel a a -> [a] -> Rel a a
star r xs = plus r \/ identity xs

------------------------------------------------------------------------

isTotalRel :: Eq a => Rel a b -> [a] -> Bool
isTotalRel r xs = domain r ~= xs

isSurjRel :: Eq b => Rel a b -> [b] -> Bool
isSurjRel r ys = codomain r ~= ys

isTotalSurjRel :: (Eq a, Eq b) => Rel a b -> [a] -> [b] -> Bool
isTotalSurjRel r xs ys = isTotalRel r xs && isSurjRel r ys

isPartialFun :: (Eq a, Eq b) => Rel a b -> Bool
isPartialFun f  = (f `compose` inverse f) ~= identity (codomain f)

isTotalFun :: (Eq a, Eq b) => Rel a b -> [a] -> Bool
isTotalFun r xs = isPartialFun r && isTotalRel r xs

isPartialInj :: (Eq a, Eq b) => Rel a b -> Bool
isPartialInj r = isPartialFun r && isPartialFun (inverse r)

isTotalInj :: (Eq a, Eq b) => Rel a b -> [a] -> Bool
isTotalInj r xs = isTotalFun r xs && isPartialFun (inverse r)

isPartialSurj :: (Eq a, Eq b) => Rel a b -> [b] -> Bool
isPartialSurj r ys = isPartialFun r && isSurjRel r ys

isTotalSurj :: (Eq a, Eq b) => Rel a b -> [a] -> [b] -> Bool
isTotalSurj r xs ys = isTotalFun r xs && isSurjRel r ys

isBijection :: (Eq a, Eq b) => Rel a b -> [a] -> [b] -> Bool
isBijection r xs ys = isTotalInj r xs && isTotalSurj r xs ys

-- | Application.
(!) :: Eq a => Fun a b -> a -> b
f ! x = maybe (error "!: lookup failed.") id (lookup x f)

(.%) :: (Eq a, Eq b) => (Fun a b, a) -> (b -> b) -> Fun a b
(f, x) .% g = f .! x .= g (f ! x)

select :: (a -> b -> Bool) -> Rel a b -> Rel a b
select p = filter (uncurry p)
