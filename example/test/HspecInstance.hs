{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies      #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module HspecInstance where

import           Test.Hspec.Core.Spec
import           Test.QuickCheck
                   (property)
import           Test.QuickCheck.Counterexamples
                   (PropertyOf)

instance Example (PropertyOf a) where
  evaluateExample = evaluateExample . property

instance Example (a -> PropertyOf b) where
  type Arg (a ->  PropertyOf b) = a
  evaluateExample = evaluateExample . fmap property
