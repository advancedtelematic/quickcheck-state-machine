{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE ScopedTypeVariables #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Utils
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH, Li-yao Xia
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan.andjelkovic@here.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module exports some QuickCheck utility functions. Some of these should
-- perhaps be upstreamed.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Utils
  ( liftProperty
  , whenFailM
  , anyP
  , suchThatEither
  , collects
  , Shrunk(..)
  , shrinkS
  , shrinkListS
  , shrinkListS'
  , shrinkListS''
  , shrinkPairS
  , shrinkPairS'
  , pickOneReturnRest
  , pickOneReturnRest2
  , pickOneReturnRestL
  )
  where

import           Prelude

import           Control.Arrow
                   ((***))
import           Data.List
                   (foldl')
import           Test.QuickCheck
                   (Arbitrary, Gen, Property, resize, shrink,
                   shrinkList, sized, whenFail, collect)
import           Test.QuickCheck.Monadic
                   (PropertyM(MkPropertyM))
import           Test.QuickCheck.Property
                   (property, (.&&.), (.||.))

------------------------------------------------------------------------

-- | Lifts a plain property into a monadic property.
liftProperty :: Monad m => Property -> PropertyM m ()
liftProperty prop = MkPropertyM (\k -> fmap (prop .&&.) <$> k ())

-- | Lifts 'whenFail' to 'PropertyM'.
whenFailM :: Monad m => IO () -> Property -> PropertyM m ()
whenFailM m prop = liftProperty (m `whenFail` prop)

-- | Lifts 'Prelude.any' to properties.
anyP :: (a -> Property) -> [a] -> Property
anyP p = foldr (\x ih -> p x .||. ih) (property False)

suchThatEither :: forall a. Gen a -> (a -> Bool) -> Gen (Either [a] a)
gen `suchThatEither` p = sized (try [] 0 . max 100)
  where
    try :: [a] -> Int -> Int -> Gen (Either [a] a)
    try ces _ 0 = return (Left (reverse ces))
    try ces k n = do
      x <- resize (2 * k + n) gen
      if p x
      then return (Right x)
      else try (x : ces) (k + 1) (n - 1)

collects :: Show a => [a] -> Property -> Property
collects = repeatedly collect
  where
    repeatedly :: (a -> b -> b) -> ([a] -> b -> b)
    repeatedly = flip . foldl' . flip

-----------------------------------------------------------------------------

-- | More permissive notion of shrinking where a value can shrink to itself
--
-- For example
--
-- > shrink  3 == [0, 2] -- standard QuickCheck shrink
-- > shrinkS 3 == [Shrunk True 0, Shrunk True 2, Shrunk False 3]
--
-- This is primarily useful when shrinking composite structures: the combinators
-- here keep track of whether something was shrunk /somewhere/ in the structure.
-- For example, we have
--
-- >    shrinkListS (shrinkPairS shrinkS shrinkS) [(1,3),(2,4)]
-- > == [ Shrunk True  []             -- removed all elements of the list
-- >    , Shrunk True  [(2,4)]        -- removed the first
-- >    , Shrunk True  [(1,3)]        -- removed the second
-- >    , Shrunk True  [(0,3),(2,4)]  -- shrinking the '1'
-- >    , Shrunk True  [(1,0),(2,4)]  -- shrinking the '3'
-- >    , Shrunk True  [(1,2),(2,4)]  -- ..
-- >    , Shrunk True  [(1,3),(0,4)]  -- shrinking the '2'
-- >    , Shrunk True  [(1,3),(1,4)]  -- ..
-- >    , Shrunk True  [(1,3),(2,0)]  -- shrinking the '4'
-- >    , Shrunk True  [(1,3),(2,2)]  -- ..
-- >    , Shrunk True  [(1,3),(2,3)]  -- ..
-- >    , Shrunk False [(1,3),(2,4)]  -- the original unchanged list
-- >    ]
data Shrunk a = Shrunk { wasShrunk :: Bool, shrunk :: a }
  deriving (Eq, Show, Functor)

shrinkS :: Arbitrary a => a -> [Shrunk a]
shrinkS a = map (Shrunk True) (shrink a) ++ [Shrunk False a]

shrinkListS :: forall a. (a -> [Shrunk a]) -> [a] -> [Shrunk [a]]
shrinkListS f = \xs -> concat [
      map (Shrunk True) (shrinkList (const []) xs)
    , shrinkOne xs
    , [Shrunk False xs]
    ]
  where
    shrinkOne :: [a] -> [Shrunk [a]]
    shrinkOne []     = []
    shrinkOne (x:xs) = [Shrunk True (x' : xs) | Shrunk True x'  <- f x]
                    ++ [Shrunk True (x : xs') | Shrunk True xs' <- shrinkOne xs]

-- | Shrink list without shrinking elements.
shrinkListS' :: [a] -> [Shrunk [a]]
shrinkListS' = shrinkListS (\a -> [Shrunk False a])

-- | Shrink list by only shrinking elements.
shrinkListS'' :: forall a. (a -> [Shrunk a]) -> [a] -> [Shrunk [a]]
shrinkListS'' f xs =
  let shr = shrinkListS f xs
      len = length xs
  in filter (\s -> length (shrunk s) == len) shr

shrinkPairS :: (a -> [Shrunk a])
            -> (b -> [Shrunk b])
            -> (a, b) -> [Shrunk (a, b)]
shrinkPairS f g (a, b) =
       [Shrunk True (a', b) | Shrunk True a' <- f a ]
    ++ [Shrunk True (a, b') | Shrunk True b' <- g b ]
    ++ [Shrunk False (a, b)]

shrinkPairS' :: (a -> [Shrunk a]) -> (a, a) -> [Shrunk (a, a)]
shrinkPairS' f = shrinkPairS f f

-- >    pickOneReturnRest2 ([], []) == []
-- >    pickOneReturnRest2 ([1,2], [3,4])
-- > == [ (1,([2],[3,4])), (2,([1],[3,4])), (3,([1,2],[4])), (4,([1,2],[3])) ]
pickOneReturnRest2 :: ([a], [a]) -> [(a, ([a],[a]))]
pickOneReturnRest2 (xs, ys) =
  map (id *** flip (,) ys) (pickOneReturnRest xs) ++
  map (id ***      (,) xs) (pickOneReturnRest ys)

-- >    pickOneReturnRest []     == []
-- >    pickOneReturnRest [1]    == [ (1,[]) ]
-- >    pickOneReturnRest [1..3] == [ (1,[2,3]), (2,[1,3]), (3,[1,2]) ]
pickOneReturnRest :: [a] -> [(a, [a])]
pickOneReturnRest []       = []
pickOneReturnRest (x : xs) = (x, xs) : map (id *** (x :)) (pickOneReturnRest xs)

-- >    pickOneReturnRestL [[]] == []
-- >    pickOneReturnRestL [[1]] == [(1,[[]])]
-- >    pickOneReturnRestL [[1],[],[]] == [(1,[[],[],[]])]
-- >    pickOneReturnRestL [[1,2]] == [(1,[[2]]), (2,[[1]])]
-- >    pickOneReturnRestL [[1,2], [3,4]]
-- > == [ (1,[[2],[3,4]]), (2,[[1],[3,4]]), (3,[[1,2],[4]]), (4,[[1,2],[3]]) ]
pickOneReturnRestL :: [[a]] -> [(a, [[a]])]
pickOneReturnRestL ls = concatMap
  (\(prev, as, next) -> fmap (\(a, rest) -> (a, prev ++ [rest] ++ next)) $ pickOneReturnRest as)
  $ splitEach ls
    where
      splitEach :: [a] -> [([a], a, [a])]
      splitEach []       = []
      splitEach (a : as) = fmap (\(prev, a', next) -> (prev, a', next)) $
        go' [([], a, as)] ([], a, as)
          where
            go' :: [([a], a, [a])] -> ([a], a, [a]) -> [([a], a, [a])]
            go' acc (_, _, []) = reverse acc
            go' acc (prev, a', b : next) =
              let newElem = (a' : prev, b, next)
              in go' (newElem : acc) newElem
