module Test.StateMachine.TH
  ( deriveTestClasses
  , module TH
  ) where

import           Language.Haskell.TH
                   (Dec, Name, Q)

import           Test.StateMachine.Types.HFunctor.TH as TH

deriveTestClasses :: Name -> Q [Dec]
deriveTestClasses = deriveHClasses
