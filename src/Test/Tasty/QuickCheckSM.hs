{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}

module Test.Tasty.QuickCheckSM
  ( testProperty
  , successful
  ) where

import           Data.Bifunctor
                   (bimap)
import           Data.Proxy
                   (Proxy(..))
import           Generic.Data
                   (FiniteEnum, GBounded, GEnum)
import           GHC.Generics
                   (Generic, Rep)
import           Prelude
import qualified Test.QuickCheck          as QC
import qualified Test.Tasty.Options       as Tasty
import qualified Test.Tasty.Providers     as Tasty
import qualified Test.Tasty.QuickCheck    as QC

import           Test.StateMachine.Markov
                   (Markov, ppSomeMatrix, results)

---------------------------------------------------------------------------------

data QCSM
  = forall model state cmd.
      ( Ord state, Read state
      , Generic state
      , GEnum FiniteEnum (Rep state), GBounded (Rep state)
      ) => QCSM (Proxy state) (Markov model state cmd) QC.Property

testProperty
  :: forall model state cmd a.
     (Read state, Ord state)
  => Generic state
  => (GEnum FiniteEnum (Rep state), GBounded (Rep state))
  => QC.Testable a
  => Markov model state cmd
  -> Tasty.TestName
  -> (Markov model state cmd -> a)
  -> Tasty.TestTree
testProperty markov name prop
  = Tasty.singleTest name $ QCSM (Proxy @state) markov (QC.property (prop markov))

instance Tasty.IsTest QCSM where
  testOptions = return
    [ Tasty.Option (Proxy :: Proxy QC.QuickCheckTests)
    , Tasty.Option (Proxy :: Proxy QC.QuickCheckReplay)
    , Tasty.Option (Proxy :: Proxy QC.QuickCheckShowReplay)
    , Tasty.Option (Proxy :: Proxy QC.QuickCheckMaxSize)
    , Tasty.Option (Proxy :: Proxy QC.QuickCheckMaxRatio)
    , Tasty.Option (Proxy :: Proxy QC.QuickCheckVerbose)
    -- XXX import prior reliabilities
    ]

  run opts (QCSM proxy _markov prop) _yieldProgress = do
    (_, args) <- QC.optionSetToArgs opts

    let
      QC.QuickCheckVerbose verbose = Tasty.lookupOption opts
      testRunner = if verbose
                     then QC.verboseCheckWithResult
                     else QC.quickCheckWithResult

    r <- testRunner args prop

    let qcOutput = show (bimap ppSomeMatrix ppSomeMatrix (results proxy (QC.tables r)))
        testSuccessful = successful r
    return $
      (if testSuccessful then Tasty.testPassed else Tasty.testFailed)
      qcOutput

successful :: QC.Result -> Bool
successful QC.Success {} = True
successful _             = False
