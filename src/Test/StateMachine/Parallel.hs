{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Parallel
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan.andjelkovic@here.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains helpers for generating, shrinking, and checking
-- parallel programs.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Parallel
  ( forAllParallelCommands
  , generateParallelCommands
  , shrinkParallelCommands
  , shrinkAndValidateParallel
  , prop_splitCombine
  , runParallelCommands
  , runParallelCommandsNTimes
  , executeParallelCommands
  , linearise
  , toBoxDrawings
  , prettyParallelCommands
  ) where

import           Control.Arrow
                   ((***))
import           Control.Monad
                   (foldM, replicateM)
import           Control.Monad.Catch
                   (MonadCatch)
import           Control.Monad.State
                   (runStateT)
import           Data.Bifunctor
                   (bimap)
import           Data.List
                   (partition, permutations)
import           Data.List.Split
                   (splitPlaces, splitPlacesBlanks)
import           Data.Maybe
                   (mapMaybe)
import           Data.Monoid
                   ((<>))
import           Data.Set
                   (Set)
import qualified Data.Set                          as S
import           Data.Tree
                   (Tree(Node))
import           Prelude
import           Test.QuickCheck
                   (Gen, Property, Testable, choose, property, sized)
import           Test.QuickCheck.Monadic
                   (PropertyM, run)
import           Text.PrettyPrint.ANSI.Leijen
                   (Doc)
import           Text.Show.Pretty
                   (ppShow)
import           UnliftIO
                   (MonadIO, MonadUnliftIO, concurrently, newTChanIO)

import           Test.StateMachine.BoxDrawer
import           Test.StateMachine.ConstructorName
import           Test.StateMachine.Logic
import           Test.StateMachine.Sequential
import           Test.StateMachine.Types
import qualified Test.StateMachine.Types.Rank2     as Rank2
import           Test.StateMachine.Utils

------------------------------------------------------------------------

forAllParallelCommands :: Testable prop
                       => (Show (cmd Symbolic), Show (model Symbolic))
                       => CommandNames cmd
                       => (Rank2.Traversable cmd, Rank2.Foldable resp)
                       => StateMachine model cmd m resp
                       -> (ParallelCommands cmd -> prop)     -- ^ Predicate.
                       -> Property
forAllParallelCommands sm =
  forAllShrinkShow (generateParallelCommands sm) (shrinkParallelCommands sm) ppShow

generateParallelCommands :: forall model cmd m resp
                          . (Rank2.Foldable resp, Show (model Symbolic))
                         => CommandNames cmd
                         => StateMachine model cmd m resp
                         -> Gen (ParallelCommands cmd)
generateParallelCommands sm@StateMachine { initModel } = do
  Commands cmds      <- generateCommands sm Nothing
  prefixLength       <- sized (\k -> choose (0, k `div` 3))
  let (prefix, rest) =  bimap Commands Commands (splitAt prefixLength cmds)
  return (ParallelCommands prefix
            (makeSuffixes (advanceModel sm initModel newCounter prefix) rest))
  where
    makeSuffixes :: (model Symbolic, Counter) -> Commands cmd -> [Pair (Commands cmd)]
    makeSuffixes (model0, counter0) = go (model0, counter0) [] . unCommands
      where
        go _                acc []   = reverse acc
        go (model, counter) acc cmds = go (advanceModel sm model counter (Commands safe))
                                          (Pair (Commands safe1) (Commands safe2) : acc)
                                          rest
          where
            (safe, rest)   = spanSafe model counter [] cmds
            (safe1, safe2) = splitAt (length safe `div` 2) safe

        suffixLength = 5

        spanSafe :: model Symbolic -> Counter -> [Command cmd] -> [Command cmd]
                 -> ([Command cmd], [Command cmd])
        spanSafe _     _       safe []                         = (reverse safe, [])
        spanSafe model counter safe (cmd@(Command _ _) : cmds)
          | length safe <= suffixLength &&
              parallelSafe sm model counter (Commands (cmd : safe)) =
                spanSafe model counter (cmd : safe) cmds
          | otherwise = (reverse safe, cmd : cmds)

-- | A list of commands is parallel safe if the pre-conditions for all commands
--   hold in all permutations of the list.
parallelSafe :: StateMachine model cmd m resp -> model Symbolic
             -> Counter -> Commands cmd -> Bool
parallelSafe StateMachine { precondition, transition, mock } model0 counter0
  = and
  . map (preconditionsHold model0 counter0)
  . permutations
  . unCommands
  where
    preconditionsHold _     _       []                         = True
    preconditionsHold model counter (Command cmd _vars : cmds) =
      let
        (resp, counter') = runGenSym (mock model cmd) counter
      in
        boolean (precondition model cmd) &&
          preconditionsHold (transition model cmd resp) counter' cmds

-- | Apply the transition of some commands to a model.
advanceModel :: StateMachine model cmd m resp
             -> model Symbolic  -- ^ The model.
             -> Counter
             -> Commands cmd    -- ^ The commands.
             -> (model Symbolic, Counter)
advanceModel StateMachine { transition, mock } model0 counter0 =
  go model0 counter0 . unCommands
  where
    go model counter []                         = (model, counter)
    go model counter (Command cmd _vars : cmds) =
      let
        (resp, counter') = runGenSym (mock model cmd) counter
      in
        go (transition model cmd resp) counter' cmds

------------------------------------------------------------------------

-- | Shrink a parallel program in a pre-condition and scope respecting
--   way.
shrinkParallelCommands
  :: forall cmd model m resp. Rank2.Traversable cmd
  => Rank2.Foldable resp
  => StateMachine model cmd m resp
  -> (ParallelCommands cmd -> [ParallelCommands cmd])
shrinkParallelCommands sm@StateMachine { initModel }
                       (ParallelCommands prefix suffixes)
  = concatMap go
      [ Shrunk s (ParallelCommands prefix' (map toPair suffixes'))
      | Shrunk s (prefix', suffixes') <- shrinkPairS shrinkCommands' shrinkSuffixes
                                                     (prefix, map fromPair suffixes)
      ]
      ++
      shrinkMoveSuffixToPrefix
  where
    go :: Shrunk (ParallelCommands cmd) -> [ParallelCommands cmd]
    go (Shrunk shrunk cmds) =
        shrinkAndValidateParallel sm
                                  (if shrunk then DontShrink else MustShrink)
                                  (initValidateEnv initModel)
                                  cmds

    shrinkCommands' :: Commands cmd -> [Shrunk (Commands cmd)]
    shrinkCommands' = map (fmap Commands) . shrinkListS' . unCommands

    shrinkSuffixes :: [(Commands cmd, Commands cmd)] -> [Shrunk [(Commands cmd, Commands cmd)]]
    shrinkSuffixes = shrinkListS (shrinkPairS' shrinkCommands')

    -- Moving a command from a suffix to the prefix preserves validity
    shrinkMoveSuffixToPrefix :: [ParallelCommands cmd]
    shrinkMoveSuffixToPrefix = case suffixes of
      []                   -> []
      (suffix : suffixes') ->
        [ ParallelCommands (prefix <> Commands [prefix'])
                           (fmap Commands (toPair suffix') : suffixes')
        | (prefix', suffix') <- pickOneReturnRest2 (unCommands (proj1 suffix),
                                                    unCommands (proj2 suffix))
        ]

    -- >    pickOneReturnRest []     == []
    -- >    pickOneReturnRest [1]    == [ (1,[]) ]
    -- >    pickOneReturnRest [1..3] == [ (1,[2,3]), (2,[1,3]), (3,[1,2]) ]
    pickOneReturnRest :: [a] -> [(a, [a])]
    pickOneReturnRest []       = []
    pickOneReturnRest (x : xs) = (x, xs) : map (id *** (x :)) (pickOneReturnRest xs)

    -- >    pickOneReturnRest2 ([], []) == []
    -- >    pickOneReturnRest2 ([1,2], [3,4])
    -- > == [ (1,([2],[3,4])), (2,([1],[3,4])), (3,([1,2],[4])), (4,([1,2],[3])) ]
    pickOneReturnRest2 :: ([a], [a]) -> [(a, ([a],[a]))]
    pickOneReturnRest2 (xs, ys) =
      map (id *** flip (,) ys) (pickOneReturnRest xs) ++
      map (id ***      (,) xs) (pickOneReturnRest ys)

-- | Wrapper around 'shrinkAndValidate' for chunks of commands
--
-- This is used internally in 'shrinkAndValidateParallel'.
--
-- Continuing the example discussed in 'shrinkAndValidate', suppose we are given
-- a list of 'Commands' (i.e., a list of lists)
--
-- > [ [A, B, C], [D, E], [F, G, H] ]
--
-- we concenate them together and pass
--
-- > [A, B, C, D, E, F, G, H]
--
-- to 'shrinkAndValidate'. We then rechunk all results of the form
--
-- > [A', B1', C', D', E' , F', G', H']
--
-- to
--
-- > [ [A', B1', C'], [D', E'], [F', G', H'] ]
--
-- I.e., the result now is a list of list of 'Commands'. We can always do this
-- because 'shrinkAndValidate' has the property that it does not change the
-- number of commands in any single result.
shrinkAndValidateChunks :: forall model cmd m resp. (Rank2.Traversable cmd, Rank2.Foldable resp)
                        => StateMachine model cmd m resp
                        -> ShouldShrink
                        -> ValidateEnv model
                        -> [Commands cmd]
                        -> [[Commands cmd]]
shrinkAndValidateChunks sm shouldShrink env chunks =
    map (rechunk . snd) $ shrinkAndValidate sm shouldShrink env (mconcat chunks)
  where
    chunkLengths :: [Int]
    chunkLengths = map lengthCommands chunks

    rechunk :: Commands cmd -> [Commands cmd]
    rechunk = map Commands . splitPlaces chunkLengths . unCommands

shrinkAndValidateParallel :: forall model cmd m resp. (Rank2.Traversable cmd, Rank2.Foldable resp)
                          => StateMachine model cmd m resp
                          -> ShouldShrink
                          -> ValidateEnv model
                          -> ParallelCommands cmd
                          -> [ParallelCommands cmd]
shrinkAndValidateParallel sm shouldShrink env (ParallelCommands prefix suffixes) =
    case shouldShrink of
      DontShrink -> concatMap (uncurry (goWithPrefix DontShrink)) (shrinkAndValidate sm DontShrink env prefix)
      MustShrink -> concatMap (uncurry (goWithPrefix DontShrink)) (shrinkAndValidate sm MustShrink env prefix)
                 ++ concatMap (uncurry (goWithPrefix MustShrink)) (shrinkAndValidate sm DontShrink env prefix)
  where
    (lftSuffixes, rgtSuffixes) = unzip (map fromPair suffixes)

    goWithPrefix :: ShouldShrink       -- should we /still/ shrink something?
                 -> ValidateEnv model  -- environment after the prefix
                 -> Commands cmd       -- validated prefix
                 -> [ParallelCommands cmd]
    goWithPrefix shouldShrink' env' prefix' =
      case shouldShrink' of
        DontShrink ->
          mapMaybe (postProcess env' prefix') $
            cartesian (shrinkAndValidateChunks sm DontShrink env' lftSuffixes)
                      (shrinkAndValidateChunks sm DontShrink env' rgtSuffixes)
        MustShrink -> concat [
             mapMaybe (postProcess env' prefix') $
               cartesian (shrinkAndValidateChunks sm MustShrink env' lftSuffixes)
                         (shrinkAndValidateChunks sm DontShrink env' rgtSuffixes)
          , mapMaybe (postProcess env' prefix') $
               cartesian (shrinkAndValidateChunks sm DontShrink env' lftSuffixes)
                         (shrinkAndValidateChunks sm MustShrink env' rgtSuffixes)
          ]

    postProcess :: ValidateEnv model -- environment after the prefix
                -> Commands cmd      -- validated prefix
                -> ([Commands cmd], [Commands cmd])
                -> Maybe (ParallelCommands cmd)
    postProcess (ValidateEnv model _ counter) prefix' (lftSuffixes', rgtSuffixes') =
        if parallelSafeMany sm model counter suffixes'
          then Just $ ParallelCommands prefix' suffixes'
          else Nothing
      where
        suffixes' = zipWith Pair lftSuffixes' rgtSuffixes'

    -- Cartesian product
    --
    -- NOTE: When we call 'cartesian', only /one/ of the lists will possibly
    -- have more than 1 element; the other lists are either empty (meaning
    -- validation failed and this shrink candidate is invalid) or singleton lists
    -- (validation successful).
    cartesian :: [a] -> [b] -> [(a,b)]
    cartesian as bs = [(a, b) | a <- as, b <- bs]

parallelSafeMany :: StateMachine model cmd m resp -> model Symbolic
                 -> Counter -> [Pair (Commands cmd)] -> Bool
parallelSafeMany sm = go
  where
    go _ _ []                                   = True
    go model counter (Pair cmds1 cmds2 : cmdss) = parallelSafe sm model counter cmds
                                                && go model' counter' cmdss
      where
        cmds               = cmds1 <> cmds2
        (model', counter') = advanceModel sm model counter cmds

prop_splitCombine :: [[Int]] -> Bool
prop_splitCombine xs = splitPlacesBlanks (map length xs) (concat xs) == xs

------------------------------------------------------------------------

runParallelCommands :: (Show (cmd Concrete), Show (resp Concrete))
                    => (Rank2.Traversable cmd, Rank2.Foldable resp)
                    => (MonadCatch m, MonadUnliftIO m)
                    => StateMachine model cmd m resp
                    -> ParallelCommands cmd
                    -> PropertyM m [(History cmd resp, Logic)]
runParallelCommands sm = runParallelCommandsNTimes 10 sm

runParallelCommandsNTimes :: (Show (cmd Concrete), Show (resp Concrete))
                          => (Rank2.Traversable cmd, Rank2.Foldable resp)
                          => (MonadCatch m, MonadUnliftIO m)
                          => Int -- ^ How many times to execute the parallel program.
                          -> StateMachine model cmd m resp
                          -> ParallelCommands cmd
                          -> PropertyM m [(History cmd resp, Logic)]
runParallelCommandsNTimes n sm cmds =
  replicateM n $ do
    (hist, _reason) <- run (executeParallelCommands sm cmds)
    return (hist, linearise sm hist)

executeParallelCommands :: (Rank2.Traversable cmd, Rank2.Foldable resp)
                        => (MonadCatch m, MonadUnliftIO m)
                        => StateMachine model cmd m resp
                        -> ParallelCommands cmd
                        -> m (History cmd resp, Reason)
executeParallelCommands sm@StateMachine{ initModel } (ParallelCommands prefix suffixes) = do

  hchan <- newTChanIO

  (reason0, (env0, _smodel, _counter, _cmodel)) <- runStateT
    (executeCommands sm hchan (Pid 0) True prefix)
    (emptyEnvironment, initModel, newCounter, initModel)

  if reason0 /= Ok
  then do
    hist <- getChanContents hchan
    return (History hist, reason0)
  else do
    (reason, _) <- foldM (go hchan) (reason0, env0) suffixes
    hist <- getChanContents hchan
    return (History hist, reason)
  where
    go hchan (_, env) (Pair cmds1 cmds2) = do
      ((reason1, (env1, _, _, _)), (reason2, (env2, _, _, _))) <- concurrently

        -- XXX: Post-conditions not checked, so we can pass in initModel here...
        -- It would be better if we made executeCommands take a Maybe model
        -- instead of the boolean...

        (runStateT (executeCommands sm hchan (Pid 1) False cmds1) (env, initModel, newCounter, initModel))
        (runStateT (executeCommands sm hchan (Pid 2) False cmds2) (env, initModel, newCounter, initModel))
      return ( reason1 `combineReason` reason2
             , env1 <> env2
             )
      where
        combineReason :: Reason -> Reason -> Reason
        combineReason Ok r2 = r2
        combineReason r1 _  = r1

------------------------------------------------------------------------

-- | Try to linearise a history of a parallel program execution using a
--   sequential model. See the *Linearizability: a correctness condition for
--   concurrent objects* paper linked to from the README for more info.
linearise :: forall model cmd m resp. (Show (cmd Concrete), Show (resp Concrete))
          => StateMachine model cmd m resp -> History cmd resp -> Logic
linearise StateMachine { transition,  postcondition, initModel } = go . unHistory
  where
    go :: [(Pid, HistoryEvent cmd resp)] -> Logic
    go [] = Top
    go es = exists (interleavings es) (step initModel)

    step :: model Concrete -> Tree (Operation cmd resp) -> Logic
    step _model (Node (Crash _cmd _err _pid) _roses) =
      error "Not implemented yet, see issue #162 for more details."
    step model (Node (Operation cmd resp _) roses)   =
      postcondition model cmd resp .&&
        exists' roses (step (transition model cmd resp))

exists' :: Show a => [a] -> (a -> Logic) -> Logic
exists' [] _ = Top
exists' xs p = exists xs p

------------------------------------------------------------------------

-- | Takes the output of parallel program runs and pretty prints a
--   counterexample if any of the runs fail.
prettyParallelCommands :: (MonadIO m, Rank2.Foldable cmd)
                       => (Show (cmd Concrete), Show (resp Concrete))
                       => ParallelCommands cmd
                       -> [(History cmd resp, Logic)] -- ^ Output of 'runParallelCommands'.
                       -> PropertyM m ()
prettyParallelCommands cmds =
  mapM_ (\(hist, l) -> printCounterexample hist (logic l) `whenFailM` property (boolean l))
    where
      printCounterexample hist  (VFalse ce) = do
        print (toBoxDrawings cmds hist)
        putStrLn ""
        print (simplify ce)
        putStrLn ""
      printCounterexample _hist _
        = error "prettyParallelCommands: impossible, because `boolean l` was False."

      simplify :: Counterexample -> Counterexample
      simplify (ExistsC _ [Fst ce])       = ce
      simplify (ExistsC x (Fst ce : ces)) = ce `EitherC` simplify (ExistsC x ces)
      simplify (ExistsC _ (Snd ce : _))   = simplify ce
      simplify _                          = error "simplify: impossible,\
                                                  \ because of the structure of linearise."

-- | Draw an ASCII diagram of the history of a parallel program. Useful for
--   seeing how a race condition might have occured.
toBoxDrawings :: forall cmd resp. Rank2.Foldable cmd
              => (Show (cmd Concrete), Show (resp Concrete))
              => ParallelCommands cmd -> History cmd resp -> Doc
toBoxDrawings (ParallelCommands prefix suffixes) = toBoxDrawings'' allVars
  where
    allVars = getAllUsedVars prefix `S.union`
                foldMap (foldMap getAllUsedVars) suffixes

    toBoxDrawings'' :: Set Var -> History cmd resp -> Doc
    toBoxDrawings'' knownVars (History h) = exec evT (fmap (out . snd) <$> Fork l p r)
      where
        (p, h') = partition (\e -> fst e == Pid 0) h
        (l, r)  = partition (\e -> fst e == Pid 1) h'

        out :: HistoryEvent cmd resp -> String
        out (Invocation cmd vars)
          | vars `S.isSubsetOf` knownVars = show (S.toList vars) ++ " ← " ++ show cmd
          | otherwise                     = show cmd
        out (Response resp) = show resp
        out (Exception err) = err

        toEventType :: History' cmd resp -> [(EventType, Pid)]
        toEventType = map go
          where
            go e = case e of
              (pid, Invocation _ _) -> (Open,  pid)
              (pid, Response   _)   -> (Close, pid)
              (pid, Exception  _)   -> (Close, pid)

        evT :: [(EventType, Pid)]
        evT = toEventType (filter (\e -> fst e `Prelude.elem` map Pid [1, 2]) h)

getAllUsedVars :: Rank2.Foldable cmd => Commands cmd -> Set Var
getAllUsedVars = S.fromList . foldMap (\(Command cmd _) -> getUsedVars cmd) . unCommands
