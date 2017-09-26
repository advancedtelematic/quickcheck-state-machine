{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE StandaloneDeriving #-}

module Test.StateMachine.Z where

import qualified Data.List       as List
import           Test.QuickCheck
                   (Arbitrary, Property, arbitrary, choose, elements,
                   frequency, shrink, vectorOf, (.&&.), (===))

------------------------------------------------------------------------

data Rel :: * -> * -> * where
  Id  :: Rel a a
  Rel :: [(a, b)] -> Rel a b

deriving instance (Eq   a, Eq   b) => Eq   (Rel a b)
deriving instance (Show a, Show b) => Show (Rel a b)

instance (Arbitrary a, Arbitrary b) => Arbitrary (Rel a b) where
  arbitrary = do
    n <- frequency
      [ (1,  pure 0)
      , (20, choose (1, 20))
      ]
    Rel <$> vectorOf n arbitrary

  shrink Id        = []
  shrink (Rel xys) = [ Rel xys' | xys' <- shrink xys ]

identity :: Rel a a
identity = Id

empty :: Rel a b
empty = Rel []

singleton :: a -> b -> Rel a b
singleton x y = Rel [(x, y)]

fromList :: [(a, b)] -> Rel a b
fromList = Rel

toList :: Rel a b -> [(a, b)]
toList Id        = error "toList: Id"
toList (Rel xys) = xys

filterRel :: (a -> b -> Bool) -> Rel a b -> Rel a b
filterRel _ Id        = error "filterRel: Id"
filterRel p (Rel xys) = Rel (filter (uncurry p) xys)

domain :: Rel a b -> [a]
domain Id        = error "domain: Id"
domain (Rel xys) = map fst xys

codomain :: Rel a b -> [b]
codomain Id        = error "codomain: Id"
codomain (Rel xys) = map snd xys

isTotalRel :: Eq a => Rel a b -> [a] -> Bool
isTotalRel r xs = domain r == xs

isSurjRel :: Eq b => Rel a b -> [b] -> Bool
isSurjRel r ys = codomain r == ys

isTotalSurjRel :: (Eq a, Eq b) => Rel a b -> [a] -> [b] -> Bool
isTotalSurjRel r xs ys = isTotalRel r xs && isSurjRel r ys

compose :: Eq b => Rel b c -> Rel a b -> Rel a c
compose Id        r         = r
compose r         Id        = r
compose (Rel yzs) (Rel xys) = Rel
  [ (x, z)
  | (x, y)  <- xys
  , (y', z) <- yzs
  , y == y'
  ]

fcompose :: Eq b => Rel a b -> Rel b c -> Rel a c
fcompose r s = compose s r

prop_composeAssoc :: Rel FinSetC FinSetD -> Rel FinSetB FinSetC -> Rel FinSetA FinSetB -> Property
prop_composeAssoc t s r = (t `compose` s) `compose` r === t `compose` (s `compose` r)

union :: (Eq a, Eq b) => Rel a b -> Rel a b -> Rel a b
union Id         _         = error "union: Id"
union _          Id        = error "union: Id"
union (Rel xys) (Rel xys') = Rel (List.union xys xys')

intersection :: (Eq a, Eq b) => Rel a b -> Rel a b -> Rel a b
intersection Id        Id         = Id
intersection Id        r@(Rel _)  = filterRel (==) r
intersection r@(Rel _) Id         = filterRel (==) r
intersection (Rel xys) (Rel xys') = Rel (List.intersect xys xys')

prop_intersectIdempotent :: Rel FinSetA FinSetB -> Property
prop_intersectIdempotent r = r `intersection` r === r

prop_intersectCommutative :: Rel FinSetA FinSetB -> Rel FinSetA FinSetB -> Property
prop_intersectCommutative r s = r `intersection` s === s `intersection` r

  {-
associative (R∩S)∩T = R∩(S∩T);
anti-involution distributes over intersection ((R∩S)° = S°∩R°);
-}

isSubsetOf :: (Eq a, Eq b) => Rel a b -> Rel a b -> Bool
r `isSubsetOf` s = r == r `intersection` s

{-
composition is semi-distributive over intersection (R(S∩T)⊆RS∩RT, (R∩S)T⊆RT∩ST); and
the modularity law is satisfied: (RS∩T⊆(R∩TS°)S).
-}

inverse :: Rel a b -> Rel b a
inverse Id        = Id
inverse (Rel xys) = Rel (map (\(x, y) -> (y, x)) xys)

prop_inverseIdempotent :: Rel FinSetA FinSetB -> Property
prop_inverseIdempotent r = inverse (inverse r) === r

-- Fails, because the list of pairs in the relation are not sorted.
prop_inverseCompose :: Rel FinSetB FinSetC -> Rel FinSetA FinSetB -> Property
prop_inverseCompose s r = inverse (s `compose` r) === inverse r `compose` inverse s

elemRel :: (Eq a, Eq b) => a -> b -> Rel a b -> Bool
elemRel x y Id        = x == y
elemRel x y (Rel xys) = (x, y) `elem` xys

lookupDom :: Eq a => a -> Rel a b -> [b]
lookupDom x Id        = [x]
lookupDom x (Rel xys) = xys >>= \(x', y) -> if x == x' then [y] else []

lookupCod :: Eq b => b -> Rel a b -> [a]
lookupCod y Id        = [y]
lookupCod y (Rel xys) = xys >>= \(x, y') -> if y == y' then [x] else []

------------------------------------------------------------------------

-- | Domain restriction.
(<|) :: Eq a => [a] -> Rel a b -> Rel a b
xs <| Id        = Rel (map (\x -> (x, x)) xs)
xs <| r@(Rel _) = filterRel (\x _ -> x `elem` xs) r

ex0 :: Rel Char String
ex0 = ['a'] <| fromList [ ('a', "apa"), ('b', "bepa")]
-- > Rel [('a',"apa")]

-- | Codomain restriction.
(|>) :: Eq b => Rel a b -> [b] -> Rel a b
Id        |> ys = Rel (map (\y -> (y, y)) ys)
r@(Rel _) |> ys = filterRel (\_ y -> y `elem` ys) r

prop_restriction :: Rel FinSetA FinSetB -> Property
prop_restriction r = domain r <| r |> codomain r === r

-- | Domain substraction.
(<-|) :: Eq a => [a] -> Rel a b -> Rel a b
_  <-| Id        = error "<-|: Id"
xs <-| r@(Rel _) = filterRel (\x _ -> x `notElem` xs) r

-- | Codomain substraction.
(|->) :: Eq b => Rel a b -> [b] -> Rel a b
Id        |-> _  = error "|->: Id"
r@(Rel _) |-> ys = filterRel (\_ y -> y `notElem` ys) r

prop_subtraction :: Rel FinSetA FinSetB -> Property
prop_subtraction r =
  domain r <-| r          === empty .&&.
  []       <-| r          === r     .&&.
  r        |-> codomain r === empty .&&.
  r        |-> []         === r

-- | The image of a relation.
image :: Eq a => Rel a b -> [a] -> [b]
image Id        xs = xs
image r@(Rel _) xs = codomain (xs <| r)

-- | Overriding.
(<+) :: (Eq a, Eq b) => Rel a b -> Rel a b -> Rel a b
Id <+ _  = error "<+: Id"
_  <+ Id = Id
r  <+ s  = domain s <-| r `union` s

ex1, ex2 :: Fun Char String
ex1 = fromList [('a', "apa")] <+ fromList [('a', "bepa")]
-- Rel (fromList [('a',"bepa")])
ex2 = fromList [('a', "apa")] <+ fromList [('b', "bepa")]
-- Rel (fromList [('a',"apa"),('b',"bepa")])

-- Direct product.
(<**>) :: Eq a => Rel a b -> Rel a c -> Rel a (b, c)
Id      <**> _       = error "<**>: Id"
_       <**> Id      = error "<**>: Id"
Rel xys <**> Rel xzs = Rel
  [ (x, (y, z))
  | (x , y) <- xys
  , (x', z) <- xzs
  , x == x'
  ]

-- Parallel product.
(<||>) :: Rel a c -> Rel b d -> Rel (a, b) (c, d)
Id      <||> _       = error "<||>: Id"
_       <||> Id      = error "<||>: Id"
Rel acs <||> Rel bds = Rel
  [ ((a, b), (c, d))
  | (a, c) <- acs
  , (b, d) <- bds
  ]

------------------------------------------------------------------------

type Fun a b = Rel a b

isPartialFun :: (Eq a, Eq b) => Rel a b -> Bool
isPartialFun Id = True
isPartialFun r  = (inverse r `fcompose` r) `isSubsetOf` Id

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

isIso :: (Eq a, Eq b) => Rel a b -> [a] -> [b] -> Bool
isIso r xs ys = isTotalInj r xs && isTotalSurj r xs ys

(!) :: Eq a => Fun a b -> a -> Maybe b
Id      ! x = Just x
Rel xys ! x = lookup x xys

(.=) :: (Eq a, Eq b) => (Fun a b, a) -> b -> Fun a b
(f, x) .= y = f <+ singleton x y

(.!) :: Fun a b -> a -> (Fun a b, a)
f .! x = (f, x)

ex3 :: Fun Char String
ex3 = f .! 'a' .= "bepa"
  where
  f = singleton 'a' "apa"
-- > Rel [('a', "bepa")]

ex4 :: Fun Char String
ex4 = f .! 'b' .= "bepa"
  where
  f = singleton 'a' "apa"
-- Rel [('a',"apa"),('b',"bepa")]

------------------------------------------------------------------------

data Account = Account Int
  deriving (Eq, Show)

data Person = Person String
  deriving (Eq, Show)

data Model = Model
  { act   :: [Account]
  , owner :: Fun Account Person
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
