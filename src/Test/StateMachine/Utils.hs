{-# OPTIONS_GHC -Wno-orphans #-}

{-# LANGUAGE CPP                 #-}
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
  , forAllShrinkShow
  , anyP
  , suchThatMaybeN
  , suchThatOneOf
  , oldCover
  , Shrunk(..)
  , shrinkS
  , shrinkListS
  , shrinkListS'
  , shrinkPairS
  , shrinkPairS'
  )
  where

import           Prelude

import           Test.QuickCheck
                   (Arbitrary, Gen, Property, Testable, again,
                   counterexample, frequency, resize, shrink,
                   shrinkList, shrinking, sized, suchThatMaybe,
                   whenFail)
import           Test.QuickCheck.Monadic
                   (PropertyM(MkPropertyM))
import           Test.QuickCheck.Property
                   (Property(MkProperty), cover, property, unProperty,
                   (.&&.), (.||.))
#if !MIN_VERSION_QuickCheck(2,10,0)
import           Test.QuickCheck.Property
                   (succeeded)
#endif

------------------------------------------------------------------------

-- | Lifts a plain property into a monadic property.
liftProperty :: Monad m => Property -> PropertyM m ()
liftProperty prop = MkPropertyM (\k -> fmap (prop .&&.) <$> k ())

-- | Lifts 'whenFail' to 'PropertyM'.
whenFailM :: Monad m => IO () -> Property -> PropertyM m ()
whenFailM m prop = liftProperty (m `whenFail` prop)

-- | A variant of 'Test.QuickCheck.Monadic.forAllShrink' with an explicit show
--   function. This function was upstreamed and is part of QuickCheck >= 2.12.
forAllShrinkShow
  :: Testable prop
  => Gen a -> (a -> [a]) -> (a -> String) -> (a -> prop) -> Property
forAllShrinkShow gen shrinker shower pf =
  again $
  MkProperty $
  gen >>= \x ->
    unProperty $
    shrinking shrinker x $ \x' ->
      counterexample (shower x') (pf x')

-- | Lifts 'Prelude.any' to properties.
anyP :: (a -> Property) -> [a] -> Property
anyP p = foldr (\x ih -> p x .||. ih) (property False)

#if !MIN_VERSION_QuickCheck(2,10,0)
instance Testable () where
  property = property . liftUnit
    where
    liftUnit () = succeeded
#endif

-- | Like 'Test.QuickCheck.suchThatMaybe', but retries @n@ times.
suchThatMaybeN :: Int -> Gen a -> (a -> Bool) -> Gen (Maybe a)
suchThatMaybeN 0 _   _ = return Nothing
suchThatMaybeN n gen p = do
  mx <- gen `suchThatMaybe` p
  case mx of
    Just x  -> return (Just x)
    Nothing -> sized (\m -> resize (m + 1) (suchThatMaybeN (n - 1) gen p))

suchThatOneOf :: [(Int, Gen a)] -> (a -> Bool) -> Gen (Maybe a)
gens0 `suchThatOneOf` p = go gens0 (length gens0 - 1)
  where
    go []   _ = return Nothing
    go gens n = do
      i <- frequency (zip (map fst gens) (map return [0 .. n]))
      case splitAt i gens of
        (_,     [])           -> error ("suchThatOneOf: impossible, as we" ++
                                       " split the list on its length - 1.")
        (gens', gen : gens'') -> do
           mx <- suchThatMaybeN 20 (snd gen) p
           case mx of
             Just x  -> return (Just x)
             Nothing -> go (gens' ++ gens'') (n - 1)

-- | Pre-QuickCheck-2.12 version of cover.
oldCover :: Testable prop => Bool -> Int -> String -> prop -> Property
oldCover x n s p =
#if !MIN_VERSION_QuickCheck(2,12,0)
  cover x n s p
#else
  -- QuickCheck-2.12 introduced a breaking change in the cover
  -- combinator, see issue #248 for details.
  cover (fromIntegral n) x s p
#endif

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
  deriving (Show, Functor)

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

-- | Shrink list without shrinking elements
shrinkListS' :: [a] -> [Shrunk [a]]
shrinkListS' = shrinkListS (\a -> [Shrunk False a])

shrinkPairS :: (a -> [Shrunk a])
            -> (b -> [Shrunk b])
            -> (a, b) -> [Shrunk (a, b)]
shrinkPairS f g (a, b) =
       [Shrunk True (a', b) | Shrunk True a' <- f a ]
    ++ [Shrunk True (a, b') | Shrunk True b' <- g b ]
    ++ [Shrunk False (a, b)]

shrinkPairS' :: (a -> [Shrunk a]) -> (a, a) -> [Shrunk (a, a)]
shrinkPairS' f = shrinkPairS f f
