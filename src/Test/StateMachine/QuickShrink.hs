{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}


module Test.StateMachine.QuickShrink where

import Control.Monad.IO.Class
import Data.Bifunctor
import Test.QuickCheck
import Test.QuickCheck.Monadic
import Test.QuickCheck.Property
import Test.QuickCheck.Gen.Unsafe

import Control.Monad.Trans.State.Lazy

-- Monadic case

quickShrinkShowM :: Testable prop => Gen a -> (a -> [a]) -> (a -> String)
                  -> (a -> PropertyM (StateT (Maybe a) IO) prop) -> Property
quickShrinkShowM gen shrinker shower f =
    again $
    MkProperty $
    gen >>= \x ->
        unProperty <$>
            quickShrinkingM shrinker x $ \x' ->
                (flip runStateT Nothing) <$> (fmap (fmap $ counterexample (shower x')) (monadic' $ f x'))


quickShrinkingM :: forall a prop. Testable prop =>
               (a -> [a])  -- ^ 'shrink'-like function.
            -> a            -- ^ The original argument
            -> (a -> Gen (IO (prop, Maybe a))) -> Property
quickShrinkingM shrinker x0 pf = rose' $ prop x0 -- undefined -- property $ prop x0
  where
      prop :: a -> Rose Property
      prop x =
       let
        gmpa = pf x
        p :: Property = property $ ioProperty . fmap fst <$> gmpa -- Rose Property
        gma :: Gen (IO a) = fmap (\t -> case snd t of Nothing -> x ; Just x' -> x') <$> gmpa -- Gen (IO a)
        gmta = fmap shrinker <$> gma
        gmtrp = fmap (fmap prop) <$> gmta
        gmrp :: Gen (IO (Rose Property)) = fmap (\t -> MkRose p t) <$> gmtrp
        grp :: Gen (Rose Property) = fmap IORose gmrp
        gp = fmap rose' grp
        p' = property gp
       in MkRose p' []

rose' :: Rose Property -> Property
rose' r = MkProperty (fmap (MkProp . joinRose . fmap unProp) (promote (unProperty <$> r)))

-- Pure Case (not actually needed for qsm)

-- A property that not only returns if it failed or not, but also returns a minimal
-- counter example, which can make shrinking faster. Especially useful for a's with a
-- Foldablw structure, which need to be folded in order to test their properties.

-- TODO can we do this an instance of Testable? Probably not.
data QuickProperty prop a = QuickProperty prop (Maybe a)

instance Bifunctor QuickProperty where
    bimap f g (QuickProperty p ma) = QuickProperty (f p) (g <$> ma)

unQProp' :: QuickProperty prop a -> prop
unQProp' (QuickProperty p _) = p

mapQProp :: (prop -> prop) -> QuickProperty prop a -> QuickProperty prop a
mapQProp f (QuickProperty p ma) = QuickProperty (f p) ma

quickShrinkShow :: Testable prop => Gen a -> (a -> [a]) -> (a -> String) -> (a -> QuickProperty prop a) -> Property
quickShrinkShow gen shrinker shower f =
  again $
  MkProperty $
  gen >>= \x ->
        unProperty $
            quickShrinking shrinker x $ \x' ->
                first (counterexample (shower x')) (f x')

quickShrinking :: forall prop a. Testable prop
               => (a -> [a])  -- ^ 'shrink'-like function.
               -> a           -- ^ The original argument
               -> (a -> QuickProperty prop a) -> Property
quickShrinking shrinker x0 pf = MkProperty (fmap (MkProp . joinRose . fmap unProp) (promote (props x0)))
     where
         props :: a -> Rose (Gen Prop)
         props x =
             let QuickProperty p ma = pf x
                 shr = case ma of
                     Nothing -> shrinker x
                     Just a  -> a : shrinker x
             in MkRose (unProperty (property p)) [ props x' | x' <- shr ]


-- A simple example which uses QuickProperty

prop1 :: Property
prop1 = quickShrinkShow arbitrary shrink show test

test :: [Int] -> QuickProperty Property [Int]
test ls = go [] ls
    where
        go _ [] = QuickProperty (property True) Nothing
        go acc (x:xs) = if x == 5
            then case xs of
                [] -> QuickProperty (property False) Nothing -- this avoids shrinking loops
                _  -> QuickProperty (property False) (Just $ reverse $ x : acc)
            else go (x : acc) xs
