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
  , runParallelCommands
  , runParallelCommandsNTimes
  , executeParallelCommands
  , linearise
  , toBoxDrawings
  , prettyParallelCommands
  , advanceModel
  ) where

import           Control.Arrow
                   ((***))
import           Control.Monad
                   (foldM, replicateM)
import           Control.Monad.Catch
                   (MonadCatch)
import           Control.Monad.State.Strict
                   (runStateT)
import           Data.Bifunctor
                   (bimap)
import           Data.List
                   (partition, permutations)
import qualified Data.Map.Strict               as Map
import           Data.Monoid
                   ((<>))
import           Data.Set
                   (Set)
import qualified Data.Set                      as S
import           Data.Tree
                   (Tree(Node))
import           Prelude
import           Test.QuickCheck
                   (Gen, Property, Testable, choose, property, sized, forAllShrinkShow)
import           Test.QuickCheck.Monadic
                   (PropertyM, run)
import           Text.PrettyPrint.ANSI.Leijen
                   (Doc)
import           Text.Show.Pretty
                   (ppShow)
import           UnliftIO
                   (MonadIO, MonadUnliftIO, concurrently, newTChanIO)

import           Test.StateMachine.BoxDrawer
import           Test.StateMachine.Logic
import           Test.StateMachine.Sequential
import           Test.StateMachine.Types
import qualified Test.StateMachine.Types.Rank2 as Rank2
import           Test.StateMachine.Utils

------------------------------------------------------------------------

forAllParallelCommands :: Testable prop
                       => (Show (cmd Symbolic), Show (resp Symbolic), Show (model Symbolic))
                       => (Rank2.Traversable cmd, Rank2.Foldable resp)
                       => StateMachine model cmd m resp
                       -> (ParallelCommands cmd resp -> prop)     -- ^ Predicate.
                       -> Property
forAllParallelCommands sm =
  forAllShrinkShow (generateParallelCommands sm) (shrinkParallelCommands sm) ppShow

-- | Generate parallel commands.
--
-- Parallel commands are generated as follows. We begin by generating
-- sequential commands and then splitting this list in two at some index. The
-- first half will be used as the prefix.
--
-- The second half will be used to build suffixes. For example, starting from
-- the following sequential commands:
--
-- > [A, B, C, D, E, F, G, H, I]
--
-- We split it in two, giving us the prefix and the rest:
--
-- > prefix: [A, B]
-- > rest:   [C, D, E, F, G, H, I]
--
-- We advance the model with the prefix.
--
-- __Make a suffix__: we take commands from @rest@ as long as these are
-- parallel safe (see 'parallelSafe'). This means that the pre-conditions
-- (using the \'advanced\' model) of each of those commands will hold no
-- matter in which order they are executed.
--
-- Say this is true for @[C, D, E]@, but not anymore for @F@, maybe because
-- @F@ depends on one of @[C, D, E]@. Then we divide this \'chunk\' in two by
-- splitting it in the middle, obtaining @[C]@ and @[D, E]@. These two halves
-- of the chunk (stored as a 'Pair') will later be executed in parallel.
-- Together they form one suffix.
--
-- Then the model is advanced using the whole chunk @[C, D, E]@. Think of it
-- as a barrier after executing the two halves of the chunk in parallel. Then
-- this process of building a chunk/suffix repeats itself, starting from
-- __Make a suffix__ using the \'advanced\' model.
--
-- In the end we might end up with something like this:
--
-- >         ┌─ [C] ──┐  ┌ [F, G] ┐
-- > [A, B] ─┤        ├──┤        │
-- >         └ [D, E] ┘  └ [H, I] ┘
--
generateParallelCommands :: forall model cmd m resp. Rank2.Foldable resp
                         => Show (model Symbolic)
                         => (Show (cmd Symbolic), Show (resp Symbolic))
                         => StateMachine model cmd m resp
                         -> Gen (ParallelCommands cmd resp)
generateParallelCommands sm@StateMachine { initModel } = do
  Commands cmds      <- generateCommands sm Nothing
  prefixLength       <- sized (\k -> choose (0, k `div` 3))
  let (prefix, rest) =  bimap Commands Commands (splitAt prefixLength cmds)
  return (ParallelCommands prefix
            (makeSuffixes (advanceModel sm initModel prefix) rest))
  where
    makeSuffixes :: model Symbolic -> Commands cmd resp -> [Pair (Commands cmd resp)]
    makeSuffixes model0 = go model0 [] . unCommands
      where
        go _     acc []   = reverse acc
        go model acc cmds = go (advanceModel sm model (Commands safe))
                               (Pair (Commands safe1) (Commands safe2) : acc)
                               rest
          where
            (safe, rest)   = spanSafe model [] cmds
            (safe1, safe2) = splitAt (length safe `div` 2) safe

        suffixLength = 5

        -- Split the list of commands in two such that the first half is a
        -- list of commands for which the preconditions of all commands hold
        -- for permutation of the list, i.e. it is parallel safe. The other
        -- half is the remainder of the input list.
        spanSafe :: model Symbolic -> [Command cmd resp] -> [Command cmd resp]
                 -> ([Command cmd resp], [Command cmd resp])
        spanSafe _     safe []           = (reverse safe, [])
        spanSafe model safe (cmd : cmds)
          | length safe <= suffixLength
          , parallelSafe sm model (Commands (cmd : safe))
          = spanSafe model (cmd : safe) cmds
          | otherwise
          = (reverse safe, cmd : cmds)

-- | A list of commands is parallel safe if the pre-conditions for all commands
--   hold in all permutations of the list.
parallelSafe :: StateMachine model cmd m resp -> model Symbolic
             -> Commands cmd resp -> Bool
parallelSafe StateMachine { precondition, transition } model0
  = and
  . map (preconditionsHold model0)
  . permutations
  . unCommands
  where
    preconditionsHold _     []                              = True
    preconditionsHold model (Command cmd resp _vars : cmds) =
        boolean (precondition model cmd) &&
          preconditionsHold (transition model cmd resp) cmds

-- | Apply the transition of some commands to a model.
advanceModel :: StateMachine model cmd m resp
             -> model Symbolic      -- ^ The model.
             -> Commands cmd resp   -- ^ The commands.
             -> model Symbolic
advanceModel StateMachine { transition } model0 =
  go model0 . unCommands
  where
    go model []                              = model
    go model (Command cmd resp _vars : cmds) =
        go (transition model cmd resp) cmds

------------------------------------------------------------------------

-- | Shrink a parallel program in a pre-condition and scope respecting
--   way.
shrinkParallelCommands
  :: forall cmd model m resp. Rank2.Traversable cmd
  => Rank2.Foldable resp
  => StateMachine model cmd m resp
  -> (ParallelCommands cmd resp -> [ParallelCommands cmd resp])
shrinkParallelCommands sm (ParallelCommands prefix suffixes)
  = concatMap go
      [ Shrunk s (ParallelCommands prefix' (map toPair suffixes'))
      | Shrunk s (prefix', suffixes') <- shrinkPairS shrinkCommands' shrinkSuffixes
                                                     (prefix, map fromPair suffixes)
      ]
      ++
      shrinkMoveSuffixToPrefix
  where
    go :: Shrunk (ParallelCommands cmd resp) -> [ParallelCommands cmd resp]
    go (Shrunk shrunk cmds) =
        shrinkAndValidateParallel sm
                                  (if shrunk then DontShrink else MustShrink)
                                  cmds

    shrinkCommands' :: Commands cmd resp -> [Shrunk (Commands cmd resp)]
    shrinkCommands' = map (fmap Commands) . shrinkListS' . unCommands

    shrinkSuffixes :: [(Commands cmd resp, Commands cmd resp)]
                   -> [Shrunk [(Commands cmd resp, Commands cmd resp)]]
    shrinkSuffixes = shrinkListS (shrinkPairS' shrinkCommands')

    -- Moving a command from a suffix to the prefix preserves validity
    shrinkMoveSuffixToPrefix :: [ParallelCommands cmd resp]
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

shrinkAndValidateParallel :: forall model cmd m resp. (Rank2.Traversable cmd, Rank2.Foldable resp)
                          => StateMachine model cmd m resp
                          -> ShouldShrink
                          -> ParallelCommands cmd resp
                          -> [ParallelCommands cmd resp]
shrinkAndValidateParallel sm@StateMachine { initModel } = \shouldShrink (ParallelCommands prefix suffixes) ->
    let env = initValidateEnv initModel
        curryGo shouldShrink' (env', prefix') = go prefix' env' shouldShrink' suffixes in
    case shouldShrink of
      DontShrink -> concatMap (curryGo DontShrink) (shrinkAndValidate sm DontShrink env prefix)
      MustShrink -> concatMap (curryGo DontShrink) (shrinkAndValidate sm MustShrink env prefix)
                 ++ concatMap (curryGo MustShrink) (shrinkAndValidate sm DontShrink env prefix)
  where
    withCounterFrom :: ValidateEnv model -> ValidateEnv model -> ValidateEnv model
    e `withCounterFrom` e' = e { veCounter = veCounter e' }

    go :: Commands cmd resp          -- validated prefix
       -> ValidateEnv model          -- environment after the prefix
       -> ShouldShrink               -- should we /still/ shrink something?
       -> [Pair (Commands cmd resp)] -- suffixes to validate
       -> [ParallelCommands cmd resp]
    go prefix' envAfterPrefix = go' [] envAfterPrefix
      where
        go' :: [Pair (Commands cmd resp)] -- accumulated validated suffixes (in reverse order)
            -> ValidateEnv model          -- environment after the validated suffixes
            -> ShouldShrink               -- should we /still/ shrink something?
            -> [Pair (Commands cmd resp)] -- suffixes to validate
            -> [ParallelCommands cmd resp]
        go' _   _   MustShrink [] = [] -- Failed to shrink something
        go' acc _   DontShrink [] = [ParallelCommands prefix' (reverse acc)]
        go' acc env shouldShrink (Pair l r : suffixes) = do
            ((shrinkL, shrinkR), shrinkRest) <- shrinkOpts
            (envL, l') <- shrinkAndValidate sm shrinkL  env                         l
            (envR, r') <- shrinkAndValidate sm shrinkR (env `withCounterFrom` envL) r
            go' (Pair l' r' : acc) (combineEnv envL envR r') shrinkRest suffixes
          where
            combineEnv :: ValidateEnv model -> ValidateEnv model -> Commands cmd resp -> ValidateEnv model
            combineEnv envL envR cmds = ValidateEnv {
                  veModel   = advanceModel sm (veModel envL) cmds
                , veScope   = Map.union (veScope envL) (veScope envR)
                , veCounter = veCounter envR
                }

            shrinkOpts :: [((ShouldShrink, ShouldShrink), ShouldShrink)]
            shrinkOpts =
                case shouldShrink of
                  DontShrink -> [ ((DontShrink, DontShrink), DontShrink) ]
                  MustShrink -> [ ((MustShrink, DontShrink), DontShrink)
                                , ((DontShrink, MustShrink), DontShrink)
                                , ((DontShrink, DontShrink), MustShrink) ]

------------------------------------------------------------------------

runParallelCommands :: (Show (cmd Concrete), Show (resp Concrete))
                    => (Rank2.Traversable cmd, Rank2.Foldable resp)
                    => (MonadCatch m, MonadUnliftIO m)
                    => StateMachine model cmd m resp
                    -> ParallelCommands cmd resp
                    -> PropertyM m [(History cmd resp, Logic)]
runParallelCommands sm = runParallelCommandsNTimes 10 sm

runParallelCommandsNTimes :: (Show (cmd Concrete), Show (resp Concrete))
                          => (Rank2.Traversable cmd, Rank2.Foldable resp)
                          => (MonadCatch m, MonadUnliftIO m)
                          => Int -- ^ How many times to execute the parallel program.
                          -> StateMachine model cmd m resp
                          -> ParallelCommands cmd resp
                          -> PropertyM m [(History cmd resp, Logic)]
runParallelCommandsNTimes n sm cmds =
  replicateM n $ do
    (hist, _reason) <- run (executeParallelCommands sm cmds)
    return (hist, linearise sm hist)

executeParallelCommands :: (Show (cmd Concrete), Show (resp Concrete))
                        => (Rank2.Traversable cmd, Rank2.Foldable resp)
                        => (MonadCatch m, MonadUnliftIO m)
                        => StateMachine model cmd m resp
                        -> ParallelCommands cmd resp
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
                       => ParallelCommands cmd resp
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
      simplify (ExistsC [] [])            = BotC
      simplify (ExistsC _ [Fst ce])       = ce
      simplify (ExistsC x (Fst ce : ces)) = ce `EitherC` simplify (ExistsC x ces)
      simplify (ExistsC _ (Snd ce : _))   = simplify ce
      simplify _                          = error "simplify: impossible,\
                                                  \ because of the structure of linearise."

-- | Draw an ASCII diagram of the history of a parallel program. Useful for
--   seeing how a race condition might have occured.
toBoxDrawings :: forall cmd resp. Rank2.Foldable cmd
              => (Show (cmd Concrete), Show (resp Concrete))
              => ParallelCommands cmd resp -> History cmd resp -> Doc
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

getAllUsedVars :: Rank2.Foldable cmd => Commands cmd resp -> Set Var
getAllUsedVars = S.fromList . foldMap (\(Command cmd _ _) -> getUsedVars cmd) . unCommands
