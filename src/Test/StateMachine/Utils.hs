{-# OPTIONS_GHC -Wno-orphans #-}

{-# LANGUAGE CPP #-}

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
  , shrinkPair
  , shrinkPair'
  , suchThatMaybeN
  , suchThatOneOf
  , oldCover
  , suchThatEither
  , bigSample
  )
  where

import           Prelude
import           Test.QuickCheck
                   (Gen, Property, Testable, again, counterexample,
                   frequency, resize, shrinking, sized, suchThatMaybe,
                   whenFail, generate)
import           Test.QuickCheck.Monadic
                   (PropertyM(MkPropertyM))
import           Test.QuickCheck.Property
                   (Property(MkProperty), property, unProperty, (.&&.),
                   (.||.), cover)
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

-- | A variant of 'Test.QuickCheck.Monadic.forAllShrink' with an
--   explicit show function.
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

-- | Given shrinkers for the components of a pair we can shrink the pair.
shrinkPair' :: (a -> [a]) -> (b -> [b]) -> ((a, b) -> [(a, b)])
shrinkPair' shrinkerA shrinkerB (x, y) =
  [ (x', y) | x' <- shrinkerA x ] ++
  [ (x, y') | y' <- shrinkerB y ]

-- | Same above, but for homogeneous pairs.
shrinkPair :: (a -> [a]) -> ((a, a) -> [(a, a)])
shrinkPair shrinker = shrinkPair' shrinker shrinker

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

-- QuickCheck-2.12.0 introduced a breaking change in the cover combinator, see
-- issue #248 for details.
oldCover :: Testable prop => Bool -> Int -> String -> prop -> Property
oldCover x n s p =
#if !MIN_VERSION_QuickCheck(2,12,0)
  cover x n s p
#else
  cover (fromIntegral n) x s p
#endif

suchThatEither :: Gen a -> (a -> Bool) -> Gen (Either [a] a)
gen `suchThatEither` p = sized (try [] 0 . max 1)
  where
    try ces _ 0 = return (Left (reverse ces))
    try ces k n = do
      x <- resize (2 * k + n) gen
      if p x
      then return (Right x)
      else try (x : ces) (k + 1) (n - 1)
