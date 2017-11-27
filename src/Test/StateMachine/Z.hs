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

union :: Eq a => [a] -> [a] -> [a]
union = List.union

intersect :: Eq a => [a] -> [a] -> [a]
intersect = List.intersect

isSubsetOf :: Eq a => [a] -> [a] -> Bool
r `isSubsetOf` s = r == r `intersect` s

(~=) :: Eq a => [a] -> [a] -> Bool
xs ~= ys = xs `isSubsetOf` ys && ys `isSubsetOf` xs

------------------------------------------------------------------------

-- | Relations.
type Rel a b = [(a, b)]

-- | (Partial) functions.
type Fun a b = Rel a b

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
-- >>> ['a'] <-| [ ('a', "apa"), ('b', "bepa") ]
-- [('b',"bepa")]
--
(<-|) :: Eq a => [a] -> Rel a b -> Rel a b
xs <-| xys = [ (x, y) | (x, y) <- xys, x `notElem` xs ]

-- | Codomain substraction.
--
-- >>> [ ('a', "apa"), ('b', "bepa") ] |-> ["apa"]
-- [('b',"bepa")]
--
(|->) :: Eq b => Rel a b -> [b] -> Rel a b
xys |-> ys = [ (x, y) | (x, y) <- xys, y `notElem` ys ]

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
r <+ s  = domain s <-| r `union` s

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
(!) :: (Eq a, Show a, Show b) => Fun a b -> a -> b
f ! x = maybe (error msg) Prelude.id (lookup x f)
  where
  msg = "!: failed to lookup `" ++ show x ++ "' in `" ++ show f ++ "'"

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
