{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE ExplicitNamespaces         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}

module Test.Tasty.QuickCheckSM
  ( ToState (..)
  , testProperty
  , successful
  ) where

import qualified Data.Map                 as Map
import           Data.Proxy
                   (Proxy(..))
import           Generic.Data
                   (FiniteEnum, GBounded, GEnum)
import           Generic.Data
                   (gfiniteEnumFromTo, gmaxBound, gminBound)
import           GHC.Generics
                   (Generic, Rep)
import           GHC.TypeLits
                   (SomeNat(..), someNatVal)
import           MarkovChain
                   (singleUseReliability, singleUseReliabilityIO)
import           Options.Applicative
                   (metavar)
import           Prelude
import           System.FilePath
                   ((<.>), (</>))
import qualified Test.QuickCheck          as QC
import           Test.StateMachine.Markov
import qualified Test.Tasty.Options       as Tasty
import qualified Test.Tasty.Providers     as Tasty
import qualified Test.Tasty.QuickCheck    as QC
import           Test.Tasty.Runners
                   (formatMessage)
import           Text.Printf
                   (printf)

---------------------------------------------------------------------------------

data QCSM
  =  forall state.
     ( Show state, Read state, Ord state
     , Generic state, GEnum FiniteEnum (Rep state), GBounded (Rep state)
     )
  => QCSM Tasty.TestName (Proxy state) QC.Property

testProperty
  :: forall state a.
     (Show state, Read state, Ord state)
  => (Generic state, GEnum FiniteEnum (Rep state), GBounded (Rep state))
  => QC.Testable a
  => Tasty.TestName
  -> (Proxy state)
  -> a
  -> Tasty.TestTree
testProperty name proxy prop
  = Tasty.singleTest name $ QCSM name proxy (QC.property prop)


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

  run opts (QCSM name (proxy :: Proxy state) prop) _yieldProgress = do
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
        obs <- reliabilityWithPrior name fp proxy res
        return $ either id formatReliability obs
      Nothing -> do
        let obs = reliability proxy res
        return $ either id formatReliability obs

    let testSuccessful  = successful res
        putReplayInDesc = (not testSuccessful) || showReplay
    return $
      (if testSuccessful then Tasty.testPassed else Tasty.testFailed)
      (qcOutput ++ "\n" ++ rel ++ "\n" ++
        if putReplayInDesc then replayMsg else "")

reliabilityWithPrior
  :: forall proxy state
   . (Read state, Ord state)
  => (Generic state, GEnum FiniteEnum (Rep state), GBounded (Rep state))
  => Tasty.TestName -> FilePath -> proxy state -> QC.Result
  -> IO (Either String Double)
reliabilityWithPrior name fp proxy res = do
  let succsFp = fp </> name <> "-succs" <.> "matrix"
      failsFp = fp </> name <> "-fails" <.> "matrix"

  case someNatVal dim' of
    Nothing -> fail "validation error: dim n"
    Just (SomeNat pn@(Proxy :: Proxy n)) -> do
      case usage proxy <$> Map.lookup "Usage" (QC.tables res) of
        Nothing -> fail "reliability: no 'Usage' table"
        Just usg -> do
          case results proxy <$> (Map.lookup "Observations" (QC.tables res)) of
            Nothing -> fail "reliability: no 'Observations' table"
            Just obs -> do
              case compatibleMatrices pn usg obs of
                Left err -> fail err
                Right (CompatibleMatrices (Proxy :: Proxy n) q s f) -> do
                  rel <- singleUseReliabilityIO pn q succsFp failsFp (s, f)
                  return (pure rel)
  where
    dim' :: Integer
    dim' = succ $ toInteger $ length states

    states :: [state]
    states = gfiniteEnumFromTo gminBound gmaxBound

reliability
  :: forall state.
     (Read state, Ord state)
  => (Generic state, GEnum FiniteEnum (Rep state), GBounded (Rep state))
  => Proxy state -> QC.Result
  -> Either String Double
reliability proxy res = do
  SomeNat pn@(Proxy :: Proxy n) <- maybeToRight (someNatVal dim')
    "validation error: dim n"
  usg <- usage proxy <$> maybeToRight (Map.lookup "Usage" (QC.tables res))
    "reliability: no 'Usage' table"
  obs <- results proxy <$> maybeToRight (Map.lookup "Observations" (QC.tables res))
    "reliability: no 'Observations' table"
  CompatibleMatrices (Proxy :: Proxy n) q s f <- compatibleMatrices pn usg obs
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
                 then " --quickcheck-max-size=" ++ show size'
                 else ""
  in printf "Use --quickcheck-replay=%d%s to reproduce." seed sizeStr
