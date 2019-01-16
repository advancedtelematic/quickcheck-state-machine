{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeOperators             #-}

module Test.Tasty.QuickCheckSM
  ( testProperty
  , successful
  ) where

import           Data.Proxy
                   (Proxy(..))
import           Generic.Data
                   (FiniteEnum, GBounded, GEnum)
import           GHC.Generics
                   (Generic, Rep)
import           Prelude
import qualified Test.QuickCheck              as QC
import qualified Test.Tasty.Options           as Tasty
import qualified Test.Tasty.Providers         as Tasty
import qualified Test.Tasty.QuickCheck        as QC
import           Test.Tasty.Runners
                   (formatMessage)
import           Text.Printf
                   (printf)

import           Data.Maybe
                   (fromMaybe)
import           Generic.Data
                   (gfiniteEnumFromTo, gmaxBound, gminBound)
import           GHC.TypeLits
                   (SomeNat (..), type (-), someNatVal)
import           Numeric.LinearAlgebra.Static
                   (L)

import           MarkovChain
                   (reduceRow, singleUseReliability)
import           Test.StateMachine.Markov
                   (CompatibleMatrices(..), Markov, compatibleMatrices,
                   results, transitionMatrix)

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

  run opts (QCSM proxy markov prop) _yieldProgress = do
    (replaySeed, args) <- QC.optionSetToArgs opts

    let
      QC.QuickCheckShowReplay showReplay = Tasty.lookupOption opts
      QC.QuickCheckVerbose verbose       = Tasty.lookupOption opts
      testRunner = if verbose
                     then QC.verboseCheckWithResult
                     else QC.quickCheckWithResult
      replayMsg = makeReplayMsg replaySeed (QC.maxSize args)

    res <- testRunner args prop

    qcOutput <- formatMessage $ QC.output res
    let qcRel = fromMaybe "error: dimensions mismatch" (formatRel proxy markov res)
        testSuccessful = successful res
        putReplayInDesc = (not testSuccessful) || showReplay

    return $
      (if testSuccessful then Tasty.testPassed else Tasty.testFailed)
      (qcOutput ++ "\n" ++ qcRel ++ "\n" ++
        if putReplayInDesc then replayMsg else "")

formatRel
  :: forall proxy state model cmd
   . (Read state, Ord state)
  => (Generic state, GEnum FiniteEnum (Rep state), GBounded (Rep state))
  => proxy state -> Markov model state cmd -> QC.Result -> Maybe String
formatRel proxy markov res = do
  SomeNat pn@(Proxy :: Proxy n) <- someNatVal dim'
  SomeNat (Proxy :: Proxy m) <- someNatVal (pred dim')
  let mobs  = results proxy (QC.tables res)
      usage = transitionMatrix markov

  CompatibleMatrices (Proxy :: Proxy n) p s f <- compatibleMatrices pn usage mobs
  let q   :: L (n - 1) n
      q   = reduceRow p
      rel = singleUseReliability q Nothing (s, f) -- XXX prior
  return $ "Single use reliability: " ++ show rel
  where
    dim' :: Integer
    dim' = toInteger $ length states

    states :: [state]
    states = gfiniteEnumFromTo gminBound gmaxBound

successful :: QC.Result -> Bool
successful QC.Success {} = True
successful _             = False

makeReplayMsg :: Int -> Int -> String
makeReplayMsg seed size' = let
    sizeStr = if (size' /= QC.maxSize QC.stdArgs)
                 then printf " --quickcheck-max-size=%d" size'
                 else ""
  in printf "Use --quickcheck-replay=%d%s to reproduce." seed sizeStr
