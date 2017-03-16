module Test.QuickCheck.StateMachineModel.Utils where

import           Control.Monad
import           Test.QuickCheck
import           Test.QuickCheck.Monadic
import           Test.QuickCheck.Property

------------------------------------------------------------------------

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

liftProperty :: Monad m => Property -> PropertyM m ()
liftProperty prop = MkPropertyM (\k -> liftM (prop .&&.) <$> k ())

shrinkPair :: (a -> [a]) -> (a, a) -> [(a, a)]
shrinkPair shrinker = shrinkPair' shrinker shrinker

shrinkPair' :: (a -> [a]) -> (b -> [b]) -> (a, b) -> [(a, b)]
shrinkPair' shrinkerA shrinkerB (x, y) =
  [ (x', y) | x' <- shrinkerA x ] ++
  [ (x, y') | y' <- shrinkerB y ]
