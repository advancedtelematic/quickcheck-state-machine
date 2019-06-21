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
  ( forAllNParallelCommands
  , forAllParallelCommands
  , generateNParallelCommands
  , generateParallelCommands
  , shrinkNParallelCommands
  , shrinkParallelCommands
  , shrinkAndValidateNParallel
  , shrinkAndValidateParallel
  , shrinkCommands'
  , runNParallelCommands
  , runParallelCommands
  , runParallelCommands'
  , runNParallelCommandsNTimes
  , runParallelCommandsNTimes
  , runParallelCommandsNTimes'
  , executeParallelCommands
  , linearise
  , toBoxDrawings
  , prettyNParallelCommands
  , prettyParallelCommands
  , prettyParallelCommandsWithOpts
  , prettyNParallelCommandsWithOpts
  , advanceModel
  ) where

import           Control.Monad
                   (foldM, replicateM)
import           Control.Monad.Catch
                   (MonadCatch)
import           Control.Monad.State.Strict
                   (runStateT)
import           Data.Bifunctor
                   (bimap)
import           Data.List
                   (find, partition, permutations)
import qualified Data.Map.Strict               as Map
import           Data.Maybe
                   (fromMaybe)
import           Data.Monoid
                   ((<>))
import           Data.Set
                   (Set)
import qualified Data.Set                      as S
import           Data.Tree
                   (Tree(Node))
import           Prelude
import           Test.QuickCheck
                   (Gen, Property, Testable, choose, forAllShrinkShow,
                   property, sized)
import           Test.QuickCheck.Monadic
                   (PropertyM, run)
import           Text.PrettyPrint.ANSI.Leijen
                   (Doc)
import           Text.Show.Pretty
                   (ppShow)
import           UnliftIO
                   (MonadIO, MonadUnliftIO, concurrently,
                   forConcurrently, newTChanIO)

import           Test.StateMachine.BoxDrawer
import           Test.StateMachine.DotDrawing
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


forAllNParallelCommands :: Testable prop
                        => (Show (cmd Symbolic), Show (resp Symbolic), Show (model Symbolic))
                        => (Rank2.Traversable cmd, Rank2.Foldable resp)
                        => StateMachine model cmd m resp
                        -> Int                                      -- ^ Number of threads
                        -> (NParallelCommands cmd resp -> prop)     -- ^ Predicate.
                        -> Property
forAllNParallelCommands sm np =
  forAllShrinkShow (generateNParallelCommands sm np) (shrinkNParallelCommands sm) ppShow


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
            (safe, rest)   = spanSafe sm model [] cmds
            (safe1, safe2) = splitAt (length safe `div` 2) safe

-- Split the list of commands in two such that the first half is a
-- list of commands for which the preconditions of all commands hold
-- for permutation of the list, i.e. it is parallel safe. The other
-- half is the remainder of the input list.
spanSafe :: StateMachine model cmd m resp
         -> model Symbolic -> [Command cmd resp] -> [Command cmd resp]
         -> ([Command cmd resp], [Command cmd resp])
spanSafe _ _     safe []           = (reverse safe, [])
spanSafe sm model safe (cmd : cmds)
    | length safe <= 5
  , parallelSafe sm model (Commands (cmd : safe))
  = spanSafe sm model (cmd : safe) cmds
  | otherwise
  = (reverse safe, cmd : cmds)

-- Generate Parallel commands. The length of each suffix, indicates how many thread can
-- concurrently execute the commands safely.
generateNParallelCommands :: forall model cmd m resp. Rank2.Foldable resp
                          => Show (model Symbolic)
                          => (Show (cmd Symbolic), Show (resp Symbolic))
                          => StateMachine model cmd m resp
                          -> Int
                          -> Gen (NParallelCommands cmd resp)
generateNParallelCommands sm@StateMachine { initModel } np =
  if np <= 0 then error "number of threads must be positive" else do
  Commands cmds      <- generateCommands sm Nothing
  prefixLength       <- sized (\k -> choose (0, k `div` 3))
  let (prefix, rest) =  bimap Commands Commands (splitAt prefixLength cmds)
  return (ParallelCommands prefix
            (makeSuffixes (advanceModel sm initModel prefix) rest))
  where
    makeSuffixes :: model Symbolic -> Commands cmd resp -> [[(Commands cmd resp)]]
    makeSuffixes model0 = go model0 [] . unCommands
      where
        go :: model Symbolic
           -> [[(Commands cmd resp)]]
           -> [(Command cmd resp)]
           -> [[(Commands cmd resp)]]
        go _     acc []   = reverse acc
        go model acc cmds = go (advanceModel sm model (Commands safe))
                               (safes : acc)
                               rest
          where
            (safe, rest)   = spanSafe sm model [] cmds
            safes = Commands <$> chunksOf np (length safe `div` np) safe

        -- Split the list in n sublists, whose concat is the initial list.
        -- We try to keep the length of each sublist len.
        --
        -- It is important that we miss no elements here or else executeCommands may fail, because
        -- of missing references. It is also important that the final list has the correct length
        -- n, or else there will be different number of threads than the user specified.
        chunksOf :: Int -> Int -> [a] -> [[a]]
        chunksOf 1 _ xs = [xs]
        chunksOf n len xs = as : chunksOf (n-1) len bs
            where (as, bs) = splitAt len xs


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

-- | Shrink a parallel program in a pre-condition and scope respecting
--   way.
shrinkNParallelCommands
  :: forall cmd model m resp. Rank2.Traversable cmd
  => Rank2.Foldable resp
  => StateMachine model cmd m resp
  -> (NParallelCommands cmd resp -> [NParallelCommands cmd resp])
shrinkNParallelCommands sm (ParallelCommands prefix suffixes)
  = concatMap go
      [ Shrunk s (ParallelCommands prefix' suffixes')
      | Shrunk s (prefix', suffixes') <- shrinkPairS shrinkCommands' shrinkSuffixes
                                                     (prefix, suffixes)
      ]
      ++
      shrinkMoveSuffixToPrefix
  where
    go :: Shrunk (NParallelCommands cmd resp) -> [NParallelCommands cmd resp]
    go (Shrunk shrunk cmds) =
      shrinkAndValidateNParallel sm
                                       (if shrunk then DontShrink else MustShrink)
                                       cmds

    shrinkSuffixes :: [[Commands cmd resp]]
                   -> [Shrunk [[Commands cmd resp]]]
    shrinkSuffixes = shrinkListS (shrinkListS'' shrinkCommands')

    -- Moving a command from a suffix to the prefix preserves validity
    shrinkMoveSuffixToPrefix :: [NParallelCommands cmd resp]
    shrinkMoveSuffixToPrefix = case suffixes of
      []                   -> []
      (suffix : suffixes') ->
        [ ParallelCommands (prefix <> Commands [prefix'])
                           (fmap Commands suffix' : suffixes')
        | (prefix', suffix') <- pickOneReturnRestL (unCommands <$> suffix)
        ]

-- | Shrinks Commands in a way that it has strictly less number of commands.
shrinkCommands' :: Commands cmd resp -> [Shrunk (Commands cmd resp)]
shrinkCommands' = map (fmap Commands) . shrinkListS' . unCommands

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
            go' (Pair l' r' : acc) (combineEnv sm envL envR r') shrinkRest suffixes
          where

            shrinkOpts :: [((ShouldShrink, ShouldShrink), ShouldShrink)]
            shrinkOpts =
                case shouldShrink of
                  DontShrink -> [ ((DontShrink, DontShrink), DontShrink) ]
                  MustShrink -> [ ((MustShrink, DontShrink), DontShrink)
                                , ((DontShrink, MustShrink), DontShrink)
                                , ((DontShrink, DontShrink), MustShrink) ]

combineEnv :: StateMachine model cmd m resp
           -> ValidateEnv model
           -> ValidateEnv model
           -> Commands cmd resp
           -> ValidateEnv model
combineEnv sm envL envR cmds = ValidateEnv {
      veModel   = advanceModel sm (veModel envL) cmds
    , veScope   = Map.union (veScope envL) (veScope envR)
    , veCounter = veCounter envR
    }

withCounterFrom :: ValidateEnv model -> ValidateEnv model -> ValidateEnv model
withCounterFrom e e' = e { veCounter = veCounter e' }

shrinkAndValidateNParallel :: forall model cmd m resp. (Rank2.Traversable cmd, Rank2.Foldable resp)
                           => StateMachine model cmd m resp
                           -> ShouldShrink
                           -> NParallelCommands cmd resp
                           -> [NParallelCommands cmd resp]
shrinkAndValidateNParallel sm = \shouldShrink  (ParallelCommands prefix suffixes) ->
    let env = initValidateEnv $ initModel sm
        curryGo shouldShrink' (env', prefix') = go prefix' env' shouldShrink' suffixes in
    case shouldShrink of
      DontShrink -> concatMap (curryGo DontShrink) (shrinkAndValidate sm DontShrink env prefix)
      MustShrink -> concatMap (curryGo DontShrink) (shrinkAndValidate sm MustShrink env prefix)
                 ++ concatMap (curryGo MustShrink) (shrinkAndValidate sm DontShrink env prefix)
  where

    go :: Commands cmd resp         -- validated prefix
       -> ValidateEnv model         -- environment after the prefix
       -> ShouldShrink              -- should we /still/ shrink something?
       -> [[Commands cmd resp]]     -- suffixes to validate
       -> [NParallelCommands cmd resp]
    go prefix' envAfterPrefix = go' [] envAfterPrefix
      where
        go' :: [[Commands cmd resp]] -- accumulated validated suffixes (in reverse order)
            -> ValidateEnv model     -- environment after the validated suffixes
            -> ShouldShrink          -- should we /still/ shrink something?
            -> [[Commands cmd resp]] -- suffixes to validate
            -> [NParallelCommands cmd resp]
        go' _   _   MustShrink [] = [] -- Failed to shrink something
        go' acc _   DontShrink [] = [ParallelCommands prefix' (reverse acc)]
        go' acc env shouldShrink (suffix : suffixes) = do
            (suffixWithShrinks, shrinkRest) <- shrinkOpts suffix
            (envFinal, suffix') <- snd $ foldl f (True, [(env,[])]) suffixWithShrinks
            go' ((reverse suffix') : acc) envFinal shrinkRest suffixes
          where

            f :: (Bool, [(ValidateEnv model, [Commands cmd resp])])
              -> (ShouldShrink, Commands cmd resp)
              -> (Bool, [(ValidateEnv model, [Commands cmd resp])])
            f (firstCall, acc') (shrink, cmds) = (False, acc'')
              where
                    acc'' = do
                      (envPrev, cmdsPrev) <- acc'
                      let envUsed = if firstCall then env else env `withCounterFrom` envPrev
                      (env', cmd') <- shrinkAndValidate sm shrink envUsed cmds
                      let env'' = if firstCall then env' else
                            combineEnv sm envPrev env' cmd'
                      return (env'', cmd' : cmdsPrev)

            shrinkOpts :: [a] -> [([(ShouldShrink, a)], ShouldShrink)]
            shrinkOpts ls =
              let len = length ls
                  dontShrink = replicate len DontShrink
                  shrinks = if len == 0
                    then error "Invariant violation! A suffix should never be an empty list"
                    else flip map [1..len] $ \n ->
                        (replicate (n - 1) DontShrink) ++ [MustShrink] ++ (replicate (len - n) DontShrink)
              in case shouldShrink of
                  DontShrink -> [(zip dontShrink ls, DontShrink)]
                  MustShrink -> fmap (\shrinkLs -> (zip shrinkLs ls, DontShrink)) shrinks
                             ++ [(zip dontShrink ls, MustShrink)]

------------------------------------------------------------------------

runParallelCommands :: (Show (cmd Concrete), Show (resp Concrete))
                    => (Rank2.Traversable cmd, Rank2.Foldable resp)
                    => (MonadCatch m, MonadUnliftIO m)
                    => StateMachine model cmd m resp
                    -> ParallelCommands cmd resp
                    -> PropertyM m [(History cmd resp, Logic)]
runParallelCommands sm = runParallelCommandsNTimes 10 sm

runParallelCommands' :: (Show (cmd Concrete), Show (resp Concrete))
                     => (Rank2.Traversable cmd, Rank2.Foldable resp)
                     => (MonadCatch m, MonadUnliftIO m)
                     => StateMachine model cmd m resp
                     -> (cmd Concrete -> resp Concrete)
                     -> ParallelCommands cmd resp
                     -> PropertyM m [(History cmd resp, Logic)]
runParallelCommands' sm = runParallelCommandsNTimes' 10 sm

runNParallelCommands :: (Show (cmd Concrete), Show (resp Concrete))
                     => (Rank2.Traversable cmd, Rank2.Foldable resp)
                     => (MonadCatch m, MonadUnliftIO m)
                     => StateMachine model cmd m resp
                     -> NParallelCommands cmd resp
                     -> PropertyM m [(History cmd resp, Logic)]
runNParallelCommands sm = runNParallelCommandsNTimes 10 sm

runParallelCommandsNTimes :: (Show (cmd Concrete), Show (resp Concrete))
                          => (Rank2.Traversable cmd, Rank2.Foldable resp)
                          => (MonadCatch m, MonadUnliftIO m)
                          => Int -- ^ How many times to execute the parallel program.
                          -> StateMachine model cmd m resp
                          -> ParallelCommands cmd resp
                          -> PropertyM m [(History cmd resp, Logic)]
runParallelCommandsNTimes n sm cmds =
  replicateM n $ do
    (hist, _reason1, _reason2) <- run (executeParallelCommands sm cmds)
    return (hist, linearise sm hist)

runParallelCommandsNTimes' :: (Show (cmd Concrete), Show (resp Concrete))
                           => (Rank2.Traversable cmd, Rank2.Foldable resp)
                           => (MonadCatch m, MonadUnliftIO m)
                           => Int -- ^ How many times to execute the parallel program.
                           -> StateMachine model cmd m resp
                           -> (cmd Concrete -> resp Concrete)
                           -> ParallelCommands cmd resp
                           -> PropertyM m [(History cmd resp, Logic)]
runParallelCommandsNTimes' n sm complete cmds =
  replicateM n $ do
    (hist, _reason1, _reason2) <- run (executeParallelCommands sm cmds)
    let hist' = completeHistory complete hist
    return (hist', linearise sm hist')

runNParallelCommandsNTimes :: (Show (cmd Concrete), Show (resp Concrete))
                           => (Rank2.Traversable cmd, Rank2.Foldable resp)
                           => (MonadCatch m, MonadUnliftIO m)
                           => Int -- ^ How many times to execute the parallel program.
                           -> StateMachine model cmd m resp
                           -> NParallelCommands cmd resp
                           -> PropertyM m [(History cmd resp, Logic)]
runNParallelCommandsNTimes n sm cmds =
  replicateM n $ do
    (hist, _reason) <- run (execueNParallelCommands sm cmds)
    return (hist, linearise sm hist)

executeParallelCommands :: (Show (cmd Concrete), Show (resp Concrete))
                        => (Rank2.Traversable cmd, Rank2.Foldable resp)
                        => (MonadCatch m, MonadUnliftIO m)
                        => StateMachine model cmd m resp
                        -> ParallelCommands cmd resp
                        -> m (History cmd resp, Reason, Reason)
executeParallelCommands sm@StateMachine{ initModel } (ParallelCommands prefix suffixes) = do

  hchan <- newTChanIO

  (reason0, (env0, _smodel, _counter, _cmodel)) <- runStateT
    (executeCommands sm hchan (Pid 0) CheckEverything prefix)
    (emptyEnvironment, initModel, newCounter, initModel)

  if reason0 /= Ok
  then do
    hist <- getChanContents hchan
    return (History hist, reason0, reason0)
  else do
    (reason1, reason2, _) <- go hchan (Ok, Ok, env0) suffixes
    hist <- getChanContents hchan
    return (History hist, reason1, reason2)
  where
    go _hchan (res1, res2, env) []                         = return (res1, res2, env)
    go hchan  (Ok,   Ok,   env) (Pair cmds1 cmds2 : pairs) = do

      ((reason1, (env1, _, _, _)), (reason2, (env2, _, _, _))) <- concurrently

        -- XXX: Post-conditions not checked, so we can pass in initModel here...
        -- It would be better if we made executeCommands take a Maybe Environment
        -- instead of the Check...

        (runStateT (executeCommands sm hchan (Pid 1) CheckNothing cmds1) (env, initModel, newCounter, initModel))
        (runStateT (executeCommands sm hchan (Pid 2) CheckNothing cmds2) (env, initModel, newCounter, initModel))
      go hchan ( reason1
               , reason2
               , env1 <> env2
               ) pairs
    go hchan (Ok, ExceptionThrown, env) (Pair cmds1 _cmds2 : pairs) = do

      -- XXX: It's possible that pre-conditions fail at this point, because
      -- commands may depend on references that never got created in the crashed
      -- process. For example, consider:
      --
      --          x <- Create
      --    ------------+----------
      --    Write 1 x   | Write 2 x
      --    y <- Create |
      --    ------------+----------
      --    Write 3 x   | Write 4 y
      --                | Read x
      --
      -- If the @Write 1 x@ fails, @y@ will never be created and the
      -- pre-condition for @Write 4 y@ will fail. This also means that @Read x@
      -- will never get executed, and so there could be a bug in @Write@ that
      -- never gets discovered. Not sure if we can do something better here?
      --
      (reason1, (env1, _, _, _)) <- runStateT (executeCommands sm hchan (Pid 1) CheckPrecondition cmds1)
                                              (env, initModel, newCounter, initModel)
      go hchan ( reason1
               , ExceptionThrown
               , env1
               ) pairs
    go hchan (ExceptionThrown, Ok, env) (Pair _cmds1 cmds2 : pairs) = do

      (reason2, (env2, _, _, _)) <- runStateT (executeCommands sm hchan (Pid 2) CheckPrecondition cmds2)
                                              (env, initModel, newCounter, initModel)
      go hchan ( ExceptionThrown
               , reason2
               , env2
               ) pairs
    go _hchan out@(ExceptionThrown,       ExceptionThrown,       _env) (_ : _) = return out
    go _hchan out@(PreconditionFailed {}, ExceptionThrown,       _env) (_ : _) = return out
    go _hchan out@(ExceptionThrown,       PreconditionFailed {}, _env) (_ : _) = return out
    go _hchan (res1, res2, _env) (Pair _cmds1 _cmds2 : _pairs) =
      error ("executeParallelCommands, unexpected result: " ++ show (res1, res2))

execueNParallelCommands :: (Rank2.Traversable cmd, Show (cmd Concrete), Rank2.Foldable resp)
                        => Show (resp Concrete)
                        => (MonadCatch m, MonadUnliftIO m)
                        => StateMachine model cmd m resp
                        -> NParallelCommands cmd resp
                        -> m (History cmd resp, Reason)
execueNParallelCommands sm@StateMachine{ initModel } (ParallelCommands prefix suffixes) = do

  hchan <- newTChanIO

  (reason0, (env0, _smodel, _counter, _cmodel)) <- runStateT
    (executeCommands sm hchan (Pid 0) CheckNothing prefix)
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
    go _ (_, env) [] = return (Ok, env)
    go hchan (_, env) suffix = do
      reasons <- forConcurrently (zip [1..] suffix) $ \(i, cmds) ->

        -- XXX: Post-conditions not checked, so we can pass in initModel here...
        -- It would be better if we made executeCommands take a Maybe model
        -- instead of the boolean...

        (runStateT (executeCommands sm hchan (Pid i) CheckNothing cmds) (env, initModel, newCounter, initModel))
      return ( combineReasons (fst <$> reasons)
             , mconcat ((\(_, (env', _, _, _)) -> env') <$> reasons)
             )
      where
        combineReasons :: [Reason] -> Reason
        combineReasons ls = fromMaybe Ok (find (/= Ok) ls)


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
prettyParallelCommandsWithOpts :: (MonadIO m, Rank2.Foldable cmd)
                              => (Show (cmd Concrete), Show (resp Concrete))
                              => ParallelCommands cmd resp
                              -> Maybe GraphOptions
                              -> [(History cmd resp, Logic)] -- ^ Output of 'runParallelCommands'.
                              -> PropertyM m ()
prettyParallelCommandsWithOpts cmds mGraphOptions hist =
  mapM_ (\(h, l) -> printCounterexample h (logic l) `whenFailM` property (boolean l)) hist
    where
      printCounterexample hist' (VFalse ce) = do
        print (toBoxDrawings cmds hist')
        putStrLn ""
        print (simplify ce)
        putStrLn ""
        case mGraphOptions of
          Nothing -> return ()
          Just gOptions -> createAndPrintDot cmds gOptions hist'
      printCounterexample _hist _
        = error "prettyParallelCommands: impossible, because `boolean l` was False."

simplify :: Counterexample -> Counterexample
simplify (ExistsC [] [])            = BotC
simplify (ExistsC _ [Fst ce])       = ce
simplify (ExistsC x (Fst ce : ces)) = ce `EitherC` simplify (ExistsC x ces)
simplify (ExistsC _ (Snd ce : _))   = simplify ce
simplify _                          = error "simplify: impossible,\
                                            \ because of the structure of linearise."

prettyParallelCommands :: (Show (cmd Concrete), Show (resp Concrete))
                       => MonadIO m
                       => Rank2.Foldable cmd
                       => ParallelCommands cmd resp
                       -> [(History cmd resp, Logic)] -- ^ Output of 'runNParallelCommands'.
                       -> PropertyM m ()
prettyParallelCommands cmds = prettyParallelCommandsWithOpts cmds Nothing

-- | Takes the output of parallel program runs and pretty prints a
--   counterexample if any of the runs fail.
prettyNParallelCommandsWithOpts :: (Show (cmd Concrete), Show (resp Concrete))
                                => MonadIO m
                                => Rank2.Foldable cmd
                                => NParallelCommands cmd resp
                                -> Maybe GraphOptions
                                -> [(History cmd resp, Logic)] -- ^ Output of 'runNParallelCommands'.
                                -> PropertyM m ()
prettyNParallelCommandsWithOpts cmds mGraphOptions hist = do
  mapM_ (\(h, l) -> printCounterexample h (logic l) `whenFailM` property (boolean l)) hist
    where
      printCounterexample hist' (VFalse ce) = do
        putStrLn ""
        print (simplify ce)
        putStrLn ""
        case mGraphOptions of
          Nothing -> return ()
          Just gOptions -> createAndPrintDot cmds gOptions hist'
      printCounterexample _hist _
        = error "prettyNParallelCommands: impossible, because `boolean l` was False."

prettyNParallelCommands :: (Show (cmd Concrete), Show (resp Concrete))
                        => MonadIO m
                        => Rank2.Foldable cmd
                        => NParallelCommands cmd resp
                        -> [(History cmd resp, Logic)] -- ^ Output of 'runNParallelCommands'.
                        -> PropertyM m ()
prettyNParallelCommands cmds = prettyNParallelCommandsWithOpts cmds Nothing

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

createAndPrintDot :: forall cmd resp t. Foldable t => Rank2.Foldable cmd
                  => (Show (cmd Concrete), Show (resp Concrete))
                  => ParallelCommandsF t cmd resp
                  -> GraphOptions
                  -> History cmd resp
                  -> IO ()
createAndPrintDot (ParallelCommands prefix suffixes) gOptions = toDotGraph allVars
  where
    allVars = getAllUsedVars prefix `S.union`
                foldMap (foldMap getAllUsedVars) suffixes

    toDotGraph :: Set Var -> History cmd resp -> IO ()
    toDotGraph knownVars (History h) = printDotGraph gOptions $ (fmap out) <$> (Rose (snd <$> prefixMessages) groupByPid)
      where
        (prefixMessages, h') = partition (\e -> fst e == Pid 0) h
        alterF a Nothing = Just [a]
        alterF a (Just ls) = Just $ a : ls
        groupByPid = foldr (\(p,e) m -> Map.alter (alterF e) p m) Map.empty h'

        out :: HistoryEvent cmd resp -> String
        out (Invocation cmd vars)
          | vars `S.isSubsetOf` knownVars = show (S.toList vars) ++ " ← " ++ show cmd
          | otherwise                     = show cmd
        out (Response resp) = " → " ++ show resp
        out (Exception err) = " → " ++ err


getAllUsedVars :: Rank2.Foldable cmd => Commands cmd resp -> Set Var
getAllUsedVars = S.fromList . foldMap (\(Command cmd _ _) -> getUsedVars cmd) . unCommands
