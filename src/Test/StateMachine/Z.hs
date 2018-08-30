{-# LANGUAGE TypeOperators #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Z
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan.andjelkovic@here.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- This module contains Z-inspried combinators for working with relations. The
-- idea is that they can be used to define concise and showable models. This
-- module is an experiment and will likely change or move to its own package.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Z
  ( cons
  , union
  , intersect
  , isSubsetOf
  , (~=)
  , Rel
  , Fun
  , (:<->)
  , (:->)
  , (:/->)
  , empty
  , identity
  , singleton
  , domain
  , codomain
  , compose
  , fcompose
  , inverse
  , lookupDom
  , lookupCod
  , (<|)
  , (|>)
  , (<-|)
  , (|->)
  , image
  , (<+)
  , (<**>)
  , (<||>)
  , isTotalRel
  , isSurjRel
  , isTotalSurjRel
  , isPartialFun
  , isTotalFun
  , isPartialInj
  , isTotalInj
  , isPartialSurj
  , isTotalSurj
  , isBijection
  , (!)
  , (!?)
  , (.%)
  , (.!)
  , (.=)
  ) where

import qualified Data.List               as L
import           Prelude                 hiding
                   (elem, notElem)
import qualified Prelude                 as P

import           Test.StateMachine.Logic

------------------------------------------------------------------------

infixr 6 `union`
infixr 7 `intersect`
infix  5 `isSubsetOf`
infix  5 ~=
infixr 4 <|
infixl 4 |>
infixr 4 <-|
infixl 4 |->
infixr 4 <+
infixl 4 <**>
infixl 4 <||>
infixr 4 .%
infixr 9 .!
infix  4 .=

------------------------------------------------------------------------

cons :: a -> [a] -> [a]
cons = (:)

union :: Eq a => [a] -> [a] -> [a]
union = L.union

intersect :: Eq a => [a] -> [a] -> [a]
intersect = L.intersect

-- | Subset.
--
-- >>> boolean ([1, 2] `isSubsetOf` [3, 2, 1])
-- True
isSubsetOf :: (Eq a, Show a) => [a] -> [a] -> Logic
r `isSubsetOf` s = r .== r `intersect` s

-- | Set equality.
--
-- >>> boolean ([1, 1, 2] ~= [2, 1])
-- True
(~=) :: (Eq a, Show a) => [a] -> [a] -> Logic
xs ~= ys = xs `isSubsetOf` ys .&& ys `isSubsetOf` xs

------------------------------------------------------------------------

-- | Relations.
type Rel a b = [(a, b)]

-- | (Partial) functions.
type Fun a b = Rel a b

infixr 1 :->
type a :-> b = Fun a b

-- Partial function.
infixr 1 :/->
type a :/-> b = Fun a b

infixr 1 :<->
type a :<-> b = Rel a b

------------------------------------------------------------------------

empty :: Rel a b
empty = []

identity :: [a] -> Rel a a
identity xs = [ (x, x) | x <- xs ]

singleton :: a -> b -> Rel a b
singleton x y = [(x, y)]

domain :: Rel a b -> [a]
domain xys = [ x | (x, _) <- xys ]

codomain :: Rel a b -> [b]
codomain xys = [ y | (_, y) <- xys ]

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

lookupDom :: Eq a => a -> Rel a b -> [b]
lookupDom x xys = xys >>= \(x', y) -> [ y | x == x' ]

lookupCod :: Eq b => b -> Rel a b -> [a]
lookupCod y xys = xys >>= \(x, y') -> [ x | y == y' ]

------------------------------------------------------------------------

-- | Domain restriction.
--
-- >>> ['a'] <| [ ('a', "apa"), ('b', "bepa") ]
-- [('a',"apa")]
--
(<|) :: Eq a => [a] -> Rel a b -> Rel a b
xs <| xys = [ (x, y) | (x, y) <- xys, x `P.elem` xs ]

-- | Codomain restriction.
--
-- >>> [ ('a', "apa"), ('b', "bepa") ] |> ["apa"]
-- [('a',"apa")]
--
(|>) :: Eq b => Rel a b -> [b] -> Rel a b
xys |> ys = [ (x, y) | (x, y) <- xys, y `P.elem` ys ]

-- | Domain substraction.
--
-- >>> ['a'] <-| [ ('a', "apa"), ('b', "bepa") ]
-- [('b',"bepa")]
--
(<-|) :: Eq a => [a] -> Rel a b -> Rel a b
xs <-| xys = [ (x, y) | (x, y) <- xys, x `P.notElem` xs ]

-- | Codomain substraction.
--
-- >>> [ ('a', "apa"), ('b', "bepa"), ('c', "cepa") ] |-> ["apa"]
-- [('b',"bepa"),('c',"cepa")]
--
-- >>> [ ('a', "apa"), ('b', "bepa"), ('c', "cepa") ] |-> ["apa", "cepa"]
-- [('b',"bepa")]
--
-- >>> [ ('a', "apa"), ('b', "bepa"), ('c', "cepa") ] |-> ["apa"] |-> ["cepa"]
-- [('b',"bepa")]
--
(|->) :: Eq b => Rel a b -> [b] -> Rel a b
xys |-> ys = [ (x, y) | (x, y) <- xys, y `P.notElem` ys ]

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
r <+ s  = (domain s <-| r) `union` s

-- | Direct product.
(<**>) :: Eq a => Rel a b -> Rel a c -> Rel a (b, c)
xys <**> xzs =
  [ (x, (y, z))
  | (x , y) <- xys
  , (x', z) <- xzs
  , x == x'
  ]

-- | Parallel product.
(<||>) :: Rel a c -> Rel b d -> Rel (a, b) (c, d)
acs <||> bds =
  [ ((a, b), (c, d))
  | (a, c) <- acs
  , (b, d) <- bds
  ]

------------------------------------------------------------------------

isTotalRel :: (Eq a, Show a) => Rel a b -> [a] -> Logic
isTotalRel r xs = domain r ~= xs

isSurjRel :: (Eq b, Show b) => Rel a b -> [b] -> Logic
isSurjRel r ys = codomain r ~= ys

isTotalSurjRel :: (Eq a, Eq b, Show a, Show b) => Rel a b -> [a] -> [b] -> Logic
isTotalSurjRel r xs ys = isTotalRel r xs :&& isSurjRel r ys

isPartialFun :: (Eq a, Eq b, Show b) => Rel a b -> Logic
isPartialFun f  = (f `compose` inverse f) ~= identity (codomain f)

isTotalFun :: (Eq a, Eq b, Show a, Show b) => Rel a b -> [a] -> Logic
isTotalFun r xs = isPartialFun r :&& isTotalRel r xs

isPartialInj :: (Eq a, Eq b, Show a, Show b) => Rel a b -> Logic
isPartialInj r = isPartialFun r :&& isPartialFun (inverse r)

isTotalInj :: (Eq a, Eq b, Show a, Show b) => Rel a b -> [a] -> Logic
isTotalInj r xs = isTotalFun r xs :&& isPartialFun (inverse r)

isPartialSurj :: (Eq a, Eq b, Show b) => Rel a b -> [b] -> Logic
isPartialSurj r ys = isPartialFun r :&& isSurjRel r ys

isTotalSurj :: (Eq a, Eq b, Show a, Show b) => Rel a b -> [a] -> [b] -> Logic
isTotalSurj r xs ys = isTotalFun r xs :&& isSurjRel r ys

isBijection :: (Eq a, Eq b, Show a, Show b) => Rel a b -> [a] -> [b] -> Logic
isBijection r xs ys = isTotalInj r xs :&& isTotalSurj r xs ys

-- | Application.
(!) :: (Eq a, Show a, Show b) => Fun a b -> a -> b
f ! x = maybe (error msg) Prelude.id (lookup x f)
  where
    msg = "!: failed to lookup `" ++ show x ++ "' in `" ++ show f ++ "'"

(!?) :: Eq a => Fun a b -> a -> Maybe b
f !? x = lookup x f

(.%) :: (Eq a, Eq b, Show a, Show b) => (Fun a b, a) -> (b -> b) -> Fun a b
(f, x) .% g = f .! x .= g (f ! x)

------------------------------------------------------------------------


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
