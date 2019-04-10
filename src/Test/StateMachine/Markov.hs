{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.StateMachine.Markov
  ( Markov(..)
  , runMarkov
  , MarkovTable(..)
  , Continue(..)
  , markovTable
  , checkStochastic
  , forAllMarkov
  , generateMarkov
  , generateMarkovState

  , tabulateMarkov
  , coverTransitions
  , (-<)
  , (>-)

  -- * Re-export
  , FiniteEnum
  , GBounded
  , GEnum
  )
  where

import           Control.Arrow
                   ((&&&))
import           Control.Monad.State.Strict
                   (StateT, evalStateT, get, lift, put)
import           Generic.Data
                   (FiniteEnum, GBounded, GEnum, gfiniteEnumFromTo,
                   gmaxBound, gminBound)
import           GHC.Generics
                   (Generic, Rep)
import           Prelude
import           System.Random
                   (RandomGen, mkStdGen, randomR)
import           Test.QuickCheck
                   (Property, Testable, coverTable)
import           Test.QuickCheck.Gen
                   (Gen, chooseAny)
import           Text.Show.Pretty
                   (ppShow)

import           Test.StateMachine.Logic
                   (boolean)
import           Test.StateMachine.Sequential
                   (deadlockError, getUsedVars, shrinkCommands)
import           Test.StateMachine.Types
                   (Command(Command), Commands(Commands), Counter,
                   StateMachine(..), getCommand, newCounter,
                   unCommands)
import           Test.StateMachine.Types.GenSym
                   (runGenSym)
import qualified Test.StateMachine.Types.Rank2      as Rank2
import           Test.StateMachine.Types.References
                   (Symbolic)
import           Test.StateMachine.Utils
                   (forAllShrinkShow, newTabulate, suchThatEither)

------------------------------------------------------------------------

type ConstructorName = String

data Continue model state cmd
  = Stop
  | Continue ConstructorName (model Symbolic -> Gen (cmd Symbolic)) state

data Markov model state cmd = Markov
  { unMarkov :: state -> [(Int, Continue model state cmd)] }

newtype MarkovTable model state cmd = MarkovTable
  { unMarkovTable :: [(state, [(Int, Continue model state cmd)])] }

markovTable :: (Generic s, GEnum FiniteEnum (Rep s), GBounded (Rep s))
            => Markov m s a -> MarkovTable m s a
markovTable (Markov f) = MarkovTable
  [ (s, f s) | s <- gfiniteEnumFromTo gminBound gmaxBound ]

checkStochastic :: MarkovTable model state cmd -> Bool
checkStochastic = all (\is -> all (>= 0) is && sum is == 100)
                . filter (not . null)
                . map (map fst)
                . map snd
                . unMarkovTable

runMarkov :: forall model state cmd. Generic state
          => (GEnum FiniteEnum (Rep state), GBounded (Rep state))
          => Markov model state cmd -> model Symbolic -> state
          -> Gen (Maybe (cmd Symbolic, state))
runMarkov markov m s
  | checkStochastic (markovTable markov) = pickGen (unMarkov markov s)
  | otherwise                            = error "The probabilities don't add up to 100."
  where
    pickGen :: [(Int, Continue model state cmd)]
            -> Gen (Maybe (cmd Symbolic, state))
    pickGen gens = do
      stdGen <- mkStdGen <$> chooseAny
      frequencyR [ (prob, go gen) | (prob, gen) <- gens ] stdGen
      where
        go :: Continue model state cmd -> Gen (Maybe (cmd Symbolic, state))
        go Stop               = return Nothing
        go (Continue _c k s') = fmap (\x -> Just (x, s')) (k m)

    frequencyR :: RandomGen g => [(Int, b)] -> g -> b
    frequencyR []  _ = error "There are paths in the Markov chain which contain no generators."
    frequencyR xs0 g =
      let
        (n, _g') = randomR (1, 100) g
      in
        lookupRange n (makeRanges xs0)
      where
        makeRanges :: [(Int, b)] -> [((Int, Int), b)]
        makeRanges = go 1
          where
            go _   []               = []
            go low [(_, x)]         = [((low, 100), x)]
            go low ((high, x) : xs) = ((low, low + high), x) : go (low + high) xs

        lookupRange :: Int -> [((Int, Int), b)] -> b
        lookupRange needle = go
          where
            go [] = error "lookupRange: number not in any range"
            go (((low, high), x) : xs)
              | low <= needle && needle <= high = x
              | otherwise                       = go xs

------------------------------------------------------------------------

forAllMarkov :: (Testable prop, Show state)
             => (Show (cmd Symbolic), Show (resp Symbolic), Show (model Symbolic))
             => (Rank2.Traversable cmd, Rank2.Foldable resp)
             => (Generic state, GEnum FiniteEnum (Rep state), GBounded (Rep state))
             => StateMachine model cmd m resp
             -> Markov model state cmd
             -> state                           -- ^ Start state.
             -> (Commands cmd resp -> prop)     -- ^ Predicate.
             -> Property
forAllMarkov sm markov start =
  forAllShrinkShow (generateMarkov sm markov start) (shrinkCommands sm) ppShow

generateMarkov :: (Rank2.Foldable resp, Show (model Symbolic), Show state)
               => (Show (cmd Symbolic), Show (resp Symbolic))
               => (Generic state, GEnum FiniteEnum (Rep state), GBounded (Rep state))
               => StateMachine model cmd m resp
               -> Markov model state cmd
               -> state
               -> Gen (Commands cmd resp)
generateMarkov sm@StateMachine { initModel } markov start =
  evalStateT (generateMarkovState sm markov start newCounter) initModel

generateMarkovState :: forall model state cmd m resp. (Show state, Rank2.Foldable resp)
                    => (Generic state, GEnum FiniteEnum (Rep state), GBounded (Rep state))
                    => (Show (model Symbolic), Show (cmd Symbolic), Show (resp Symbolic))
                    => StateMachine model cmd m resp
                    -> Markov model state cmd
                    -> state
                    -> Counter
                    -> StateT (model Symbolic) Gen (Commands cmd resp)
generateMarkovState StateMachine { precondition, transition, mock } markov start counter0 =
  go counter0 [] start
  where
    go :: Counter -> [Command cmd resp] -> state
       -> StateT (model Symbolic) Gen (Commands cmd resp)
    go counter cmds state = do
      model <- get
      let gen = runMarkov markov model state
      ecmd  <- lift (gen `suchThatEither` \case
                       Nothing       -> True
                       Just (cmd, _) -> boolean (precondition model cmd))
      case ecmd of
        Left ces                   -> deadlockError model (reverse cmds) (ppShow ces)
        Right Nothing              -> return (Commands (reverse cmds))
        Right (Just (cmd, state')) -> do
          let (resp, counter') = runGenSym (mock model cmd) counter
          put (transition model cmd resp)
          go counter' (Command cmd resp (getUsedVars resp) : cmds) state'


------------------------------------------------------------------------

data TransitionF state cmd_ prob = Transition
  { from        :: state
  , command     :: cmd_
  , probability :: prob
  , to          :: state
  }

type Transition state cmd_ = TransitionF state cmd_ (Maybe Double)

infixl 5 -<
infixl 5 >-

(-<) :: state -> (cmd_, prob) -> (state, (cmd_, prob))
(-<) = (,)

(>-) :: (state, (cmd_, prob)) -> state -> TransitionF state cmd_ prob
(from, (command, probability)) >- to = Transition {..}

tableTag :: String
tableTag = "Transitions"

coverTransitions :: (Show state, Show cmd_, Testable prop)
                 => [TransitionF state cmd_ Double] -> prop -> Property
coverTransitions ts =
  coverTable tableTag (map (transitionToString &&& probability) ts)

commandsToTransitions :: forall model state cmd cmd_ m resp.
                         StateMachine model cmd m resp
                      -> (model Symbolic -> state)
                      -> (forall r. cmd r -> cmd_)
                      -> Commands cmd resp
                      -> [Transition state cmd_]
commandsToTransitions StateMachine { initModel, transition, mock } partition constructor =
  go initModel newCounter [] . unCommands
  where
    go :: model Symbolic -> Counter -> [Transition state cmd_] -> [Command cmd resp]
       -> [Transition state cmd_]
    go _model _counter acc []           = acc
    go  model  counter acc (cmd : cmds) = go model' counter' (t : acc) cmds
      where
        cmd'   = getCommand cmd
        model' = transition model cmd' resp

        (resp, counter') = runGenSym (mock model cmd') counter

        t = Transition
              { from        = partition model
              , command     = constructor cmd'
              , probability = Nothing
              , to          = partition model'
              }

tabulateTransitions :: (Show cmd_, Show state, Testable prop)
                    => [Transition state cmd_]
                    -> prop
                    -> Property
tabulateTransitions ts = newTabulate tableTag (map transitionToString ts)

transitionToString :: (Show state, Show cmd_) => TransitionF state cmd_ prob -> String
transitionToString Transition {..} =
  show from ++ " -< " ++ show command ++ " >- " ++ show to

tabulateMarkov :: (Show cmd_, Show state, Testable prop)
               => StateMachine model cmd m resp
               -> (model Symbolic -> state)
               -> (forall r. cmd r -> cmd_)
               -> Commands cmd resp
               -> prop
               -> Property
tabulateMarkov sm partition constructor cmds =
  tabulateTransitions (commandsToTransitions sm partition constructor cmds)
