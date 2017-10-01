module Test.StateMachine.TH
  ( deriveTestClasses
  , module TH
  ) where

import           Language.Haskell.TH
                   (Dec, Name, Q)

import           Test.StateMachine.Types.Generics.TH as TH
import           Test.StateMachine.Types.HFunctor.TH as TH

-- | Derive instances of 'HFunctor', 'HFoldable', 'HTraversable', 'Constructor'.
deriveTestClasses :: Name -> Q [Dec]
deriveTestClasses = (fmap (fmap concat . sequence) . sequence)
  [ deriveHClasses
  , deriveConstructors
  ]
