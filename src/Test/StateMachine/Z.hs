{-# LANGUAGE RecordWildCards #-}

module Test.StateMachine.Z where

import qualified Data.List       as List
import           Test.QuickCheck
                   (Arbitrary, Property, arbitrary, elements, (===))

------------------------------------------------------------------------

type Rel a b = [(a, b)]

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

isTotalRel :: Eq a => Rel a b -> [a] -> Bool
isTotalRel r xs = domain r == xs

isSurjRel :: Eq b => Rel a b -> [b] -> Bool
isSurjRel r ys = codomain r == ys

isTotalSurjRel :: (Eq a, Eq b) => Rel a b -> [a] -> [b] -> Bool
isTotalSurjRel r xs ys = isTotalRel r xs && isSurjRel r ys

compose :: Eq b => Rel b c -> Rel a b -> Rel a c
compose yzs xys =
  [ (x, z)
  | (x, y)  <- xys
  , (y', z) <- yzs
  , y == y'
  ]

fcompose :: Eq b => Rel a b -> Rel b c -> Rel a c
fcompose r s = compose s r

prop_composeAssoc :: Rel FinSetC FinSetD -> Rel FinSetB FinSetC -> Rel FinSetA FinSetB -> Property
prop_composeAssoc t s r = (t `compose` s) `compose` r === t `compose` (s `compose` r)

union :: Eq a => [a] -> [a] -> [a]
union = List.union

intersect :: Eq a => [a] -> [a] -> [a]
intersect = List.intersect

prop_intersectIdempotent :: Rel FinSetA FinSetB -> Property
prop_intersectIdempotent r = r `intersect` r === r

prop_intersectCommutative :: Rel FinSetA FinSetB -> Rel FinSetA FinSetB -> Property
prop_intersectCommutative r s = r `intersect` s === s `intersect` r

  {-
associative (R∩S)∩T = R∩(S∩T);
anti-involution distributes over intersection ((R∩S)° = S°∩R°);
-}

isSubsetOf :: (Eq a, Eq b) => Rel a b -> Rel a b -> Bool
r `isSubsetOf` s = r == r `intersect` s

{-
composition is semi-distributive over intersection (R(S∩T)⊆RS∩RT, (R∩S)T⊆RT∩ST); and
the modularity law is satisfied: (RS∩T⊆(R∩TS°)S).
-}


inverse :: Rel a b -> Rel b a
inverse xys = [ (y, x) | (x, y) <- xys ]

prop_inverseIdempotent :: Rel FinSetA FinSetB -> Property
prop_inverseIdempotent r = inverse (inverse r) === r

-- Fails, because the list of pairs in the relation are not sorted.
prop_inverseCompose :: Rel FinSetB FinSetC -> Rel FinSetA FinSetB -> Property
prop_inverseCompose s r = inverse (s `compose` r) === inverse r `compose` inverse s

lookupDom :: Eq a => a -> Rel a b -> [b]
lookupDom x xys = xys >>= \(x', y) -> if x == x' then [y] else []

lookupCod :: Eq b => b -> Rel a b -> [a]
lookupCod y xys = xys >>= \(x, y') -> if y == y' then [x] else []

------------------------------------------------------------------------

-- | Domain restriction.
(<|) :: Eq a => [a] -> Rel a b -> Rel a b
xs <| xys = [ (x, y) | (x, y) <- xys, x `elem` xs ]

ex0 :: Rel Char String
ex0 = ['a'] <| [ ('a', "apa"), ('b', "bepa") ]
-- > [('a',"apa")]

-- | Codomain restriction.
(|>) :: Eq b => Rel a b -> [b] -> Rel a b
xys |> ys = [ (x, y) | (x, y) <- xys, y `elem` ys ]

-- | Domain substraction.
(<-|) :: Eq a => [a] -> Rel a b -> Rel a b
xs <-| xys = [ (x, y) | (x, y) <- xys, x `notElem` xs ]

-- | Codomain substraction.
(|->) :: Eq b => Rel a b -> [b] -> Rel a b
xys |-> ys = [ (x, y) | (x, y) <- xys, y `notElem` ys ]

-- | The image of a relation.
image :: Eq a => Rel a b -> [a] -> [b]
image r xs = codomain (xs <| r)

-- | Overriding.
(<+) :: (Eq a, Eq b) => Rel a b -> Rel a b -> Rel a b
r <+ s  = domain s <-| r `union` s

ex1, ex2 :: Rel Char String
ex1 = [('a', "apa")] <+ [('a', "bepa")]
-- [('a',"bepa")]
ex2 = [('a', "apa")] <+ [('b', "bepa")]
-- [('a',"apa"),('b',"bepa")]

-- Direct product.
(<**>) :: Eq a => Rel a b -> Rel a c -> Rel a (b, c)
xys <**> xzs =
  [ (x, (y, z))
  | (x , y) <- xys
  , (x', z) <- xzs
  , x == x'
  ]

-- Parallel product.
(<||>) :: Rel a c -> Rel b d -> Rel (a, b) (c, d)
acs <||> bds =
  [ ((a, b), (c, d))
  | (a, c) <- acs
  , (b, d) <- bds
  ]

------------------------------------------------------------------------

isPartialFun :: (Eq a, Eq b) => Rel a b -> Bool
isPartialFun f  = (f `compose` inverse f) == identity (codomain f)

isTotalFun :: (Eq a, Eq b) => Rel a b -> [a] -> Bool
isTotalFun r xs = isPartialFun r && domain r == xs

isPartialInj :: (Eq a, Eq b) => Rel a b -> Bool
isPartialInj r = isPartialFun r && isPartialFun (inverse r)

isTotalInj :: (Eq a, Eq b) => Rel a b -> [a] -> Bool
isTotalInj r xs = isTotalFun r xs && isPartialFun (inverse r)

isPartialSurj :: (Eq a, Eq b) => Rel a b -> [b] -> Bool
isPartialSurj r ys = isPartialFun r && codomain r == ys

isTotalSurj :: (Eq a, Eq b) => Rel a b -> [a] -> [b] -> Bool
isTotalSurj r xs ys = isTotalFun r xs && codomain r == ys

isBijection :: (Eq a, Eq b) => Rel a b -> [a] -> [b] -> Bool
isBijection r xs ys = isTotalInj r xs && isTotalSurj r xs ys

(!) :: Eq a => Rel a b -> a -> Maybe b
xys ! x = lookup x xys

(.=) :: (Eq a, Eq b) => (Rel a b, a) -> b -> Rel a b
(f, x) .= y = f <+ singleton x y

(.!) :: Rel a b -> a -> (Rel a b, a)
f .! x = (f, x)

ex3 :: Rel Char String
ex3 = f .! 'a' .= "bepa"
  where
  f = singleton 'a' "apa"
-- > [('a', "bepa")]

ex4 :: Rel Char String
ex4 = f .! 'b' .= "bepa"
  where
  f = singleton 'a' "apa"
-- [('a',"apa"),('b',"bepa")]

------------------------------------------------------------------------

data Account = Account Int
  deriving (Eq, Show)

data Person = Person String
  deriving (Eq, Show)

data Model = Model
  { act   :: [Account]
  , owner :: Rel Account Person
  }
  deriving Show

m0 :: Model
m0 = Model [] empty

invariants :: Model -> Bool
invariants Model {..} = isTotalFun owner act

data Action = Open Person Account

transition :: Bool -> Model -> Action -> Model
transition bug Model {..} (Open p a) = Model
  { owner = owner .! a .= p
  , act   = if bug then act else act ++ [a]
  }

act0 :: Action
act0 = Open (Person "a") (Account 0)

ex5, ex6 :: Bool
ex5 = invariants (transition True  m0 act0)
-- > False
ex6 = invariants (transition False m0 act0)
-- > True

------------------------------------------------------------------------

iteration :: Eq a => Int -> Rel a a -> [a] -> Rel a a
iteration n r xs = case compare n 0 of
  EQ -> identity xs
  GT -> r `fcompose` iteration (n - 1) r xs
  LT -> iteration (abs n) (inverse r) xs

------------------------------------------------------------------------

data FinSetA = A1 | A2 | A3 | A4 | A5
  deriving (Bounded, Enum, Eq, Ord, Show)

instance Arbitrary FinSetA where
  arbitrary = elements [ minBound .. ]

data FinSetB = B1 | B2 | B3 | B4 | B5
  deriving (Bounded, Enum, Eq, Ord, Show)

instance Arbitrary FinSetB where
  arbitrary = elements [ minBound .. ]

data FinSetC = C1 | C2 | C3 | C4 | C5
  deriving (Bounded, Enum, Eq, Ord, Show)

instance Arbitrary FinSetC where
  arbitrary = elements [ minBound .. ]

data FinSetD = D1 | D2 | D3 | D4 | D5
  deriving (Bounded, Enum, Eq, Ord, Show)

instance Arbitrary FinSetD where
  arbitrary = elements [ minBound .. ]
