{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE ExplicitNamespaces         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}

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
import           Options.Applicative
                   (metavar)
import           Prelude
import           System.FilePath
                   ((<.>), (</>))
import qualified Test.QuickCheck              as QC
import qualified Test.Tasty.Options           as Tasty
import qualified Test.Tasty.Providers         as Tasty
import qualified Test.Tasty.QuickCheck        as QC
import           Test.Tasty.Runners
                   (formatMessage)
import           Text.Printf
                   (printf)

import           Generic.Data
                   (gfiniteEnumFromTo, gmaxBound, gminBound)
import           GHC.TypeLits
                   (type (-), SomeNat(..), someNatVal)
import           MarkovChain
                   (reduceRow, singleUseReliability,
                   singleUseReliabilityIO)
import           Numeric.LinearAlgebra.Static
                   (L)

import           Test.StateMachine.Markov
                   (CompatibleMatrices(..), Markov, compatibleMatrices,
                   handle, results, transitionMatrix)

---------------------------------------------------------------------------------

data QCSM
  = forall model state cmd.
      ( Ord state, Read state
      , Generic state
      , GEnum FiniteEnum (Rep state), GBounded (Rep state)
      ) => QCSM Tasty.TestName (Proxy state) (Markov model state cmd) QC.Property

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
  = Tasty.singleTest name $ QCSM name (Proxy @state) markov (QC.property (prop markov))


-- | Maximum ratio of failed tests before giving up
newtype StateMachineMaxFailPercent = StateMachineMaxFailPercent Int
  deriving (Num, Ord, Eq, Real, Enum, Integral)

instance Tasty.IsOption StateMachineMaxFailPercent where
  defaultValue = 0
  parseValue = fmap StateMachineMaxFailPercent . Tasty.safeRead
  optionName = return "statemachine-max-fail-percent"
  optionHelp = return "Maximum ratio of failed tests before giving up"
  optionCLParser = Tasty.mkOptionCLParser $ metavar "NUMBER"

-- | Path to priors and observations
newtype StateMachinePath = StateMachinePath (Maybe FilePath)

instance Tasty.IsOption StateMachinePath where
  defaultValue = StateMachinePath Nothing
  parseValue = fmap (StateMachinePath . Just) . Tasty.safeRead
  optionName = return "statemachine-path"
  optionHelp = return "Path to priors and observations"
  optionCLParser = Tasty.mkOptionCLParser $ metavar "FILEPATH"


optionSetToArgs :: Tasty.OptionSet -> IO (Int, QC.Args)
optionSetToArgs opts = do
  (seed, args) <- QC.optionSetToArgs opts
  let args' = args { QC.maxFailPercent = maxFail }
  return (seed, args')
  where
    StateMachineMaxFailPercent maxFail = Tasty.lookupOption opts

instance Tasty.IsTest QCSM where
  testOptions = pure
    [ Tasty.Option (Proxy :: Proxy QC.QuickCheckTests)
    , Tasty.Option (Proxy :: Proxy QC.QuickCheckReplay)
    , Tasty.Option (Proxy :: Proxy QC.QuickCheckShowReplay)
    , Tasty.Option (Proxy :: Proxy QC.QuickCheckMaxSize)
    , Tasty.Option (Proxy :: Proxy QC.QuickCheckMaxRatio)
    , Tasty.Option (Proxy :: Proxy QC.QuickCheckVerbose)
    , Tasty.Option (Proxy :: Proxy StateMachineMaxFailPercent)
    , Tasty.Option (Proxy :: Proxy StateMachinePath)
    ]

  run opts (QCSM name proxy markov prop) _yieldProgress = do
    (replaySeed, args) <- optionSetToArgs opts

    let
      QC.QuickCheckShowReplay showReplay = Tasty.lookupOption opts
      QC.QuickCheckVerbose verbose       = Tasty.lookupOption opts
      StateMachinePath mfp               = Tasty.lookupOption opts
      testRunner = if verbose
                     then QC.verboseCheckWithResult
                     else QC.quickCheckWithResult
      replayMsg = makeReplayMsg replaySeed (QC.maxSize args)

    res <- testRunner args prop
    qcOutput <- formatMessage $ QC.output res

    rel <- case mfp of
      Just fp -> do
        obs <- reliabilityWithPrior name fp proxy markov res
        return $ either id formatReliability obs
      Nothing -> do
        let obs = reliability proxy markov res
        return $ either id formatReliability obs

    let testSuccessful  = successful res
        putReplayInDesc = (not testSuccessful) || showReplay
    return $
      (if testSuccessful then Tasty.testPassed else Tasty.testFailed)
      (qcOutput ++ "\n" ++ rel ++ "\n" ++
        if putReplayInDesc then replayMsg else "")

reliabilityWithPrior
  :: forall proxy state model cmd
   . (Read state, Ord state)
  => (Generic state, GEnum FiniteEnum (Rep state), GBounded (Rep state))
  => Tasty.TestName -> FilePath -> proxy state -> Markov model state cmd -> QC.Result
  -> IO (Either String Double)
reliabilityWithPrior name fp proxy markov res = do
  let succsFp = fp </> name <> "-succs" <.> "matrix"
      failsFp = fp </> name <> "-fails" <.> "matrix"
  case someNatVal dim' of
    Nothing -> error "validation error: dim n"
    Just (SomeNat pn@(Proxy :: Proxy n)) -> do
      let usage = transitionMatrix markov
          obs   = results proxy (QC.tables res)
      case compatibleMatrices pn usage obs of
        Left err -> return (fail err)
        Right (CompatibleMatrices (Proxy :: Proxy n) p s f) -> do
          let q   :: L (n - 1) n
              q   = reduceRow p
          rel <- singleUseReliabilityIO pn q succsFp failsFp (s, f)
          return (return rel)
  where
    dim' :: Integer
    dim' = succ $ toInteger $ length states

    states :: [state]
    states = gfiniteEnumFromTo gminBound gmaxBound

reliability
  :: forall proxy state model cmd
   . (Read state, Ord state)
  => (Generic state, GEnum FiniteEnum (Rep state), GBounded (Rep state))
  => proxy state -> Markov model state cmd -> QC.Result
  -> Either String Double
reliability proxy markov res = do
  SomeNat pn@(Proxy :: Proxy n) <- handle (someNatVal dim') "validation error: dim n"
  let obs   = results proxy (QC.tables res)
      usage = transitionMatrix markov
  CompatibleMatrices (Proxy :: Proxy n) p s f <- compatibleMatrices pn usage obs
  let q   :: L (n - 1) n
      q   = reduceRow p
  return $ singleUseReliability pn q Nothing (s, f)
  where
    dim' :: Integer
    dim' = succ $ toInteger $ length states

    states :: [state]
    states = gfiniteEnumFromTo gminBound gmaxBound

formatReliability :: Double -> String
formatReliability d = "Single use reliability: " ++ show d

successful :: QC.Result -> Bool
successful QC.Success {} = True
successful _             = False

makeReplayMsg :: Int -> Int -> String
makeReplayMsg seed size' = let
    sizeStr = if (size' /= QC.maxSize QC.stdArgs)
                 then printf " --quickcheck-max-size=%d" size'
                 else ""
  in printf "Use --quickcheck-replay=%d%s to reproduce." seed sizeStr
