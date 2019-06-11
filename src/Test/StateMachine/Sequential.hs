{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Sequential
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan.andjelkovic@here.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains helpers for generating, shrinking, and checking
-- sequential programs.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Sequential
  ( forAllCommands
  , existsCommands
  , generateCommands
  , generateCommandsState
  , deadlockError
  , getUsedVars
  , shrinkCommands
  , shrinkAndValidate
  , ValidateEnv(..)
  , ShouldShrink(..)
  , initValidateEnv
  , runCommands
  , getChanContents
  , Check(..)
  , executeCommands
  , prettyPrintHistory
  , prettyPrintHistory'
  , prettyCommands
  , prettyCommands'
  , saveCommands
  , runSavedCommands
  , commandNames
  , commandNamesInOrder
  , checkCommandNames
  , showLabelledExamples
  , showLabelledExamples'
  )
  where

import           Control.Exception
                   (SomeException, SomeAsyncException (..), displayException,
                   fromException)
import           Control.Monad (when)
import           Control.Monad.Catch
                   (MonadCatch, catch)
import           Control.Monad.State.Strict
                   (StateT, evalStateT, get, lift, put, runStateT)
import           Data.Bifunctor
                   (second)
import           Data.Dynamic
                   (Dynamic, toDyn)
import           Data.Either
                   (fromRight)
import           Data.List
                   (inits)
import qualified Data.Map                          as M
import           Data.Map.Strict
                   (Map)
import           Data.Maybe
                   (fromMaybe)
import           Data.Monoid
                   ((<>))
import           Data.Proxy
                   (Proxy(..))
import qualified Data.Set                          as S
import           Data.Time
                   (defaultTimeLocale, formatTime, getZonedTime)
import           Data.TreeDiff
                   (ToExpr, ansiWlBgEditExprCompact, ediff)
import           Prelude
import           System.Directory
                   (createDirectoryIfMissing)
import           System.FilePath
                   ((</>))
import           System.Random
                   (getStdRandom, randomR)
import           Test.QuickCheck
                   (Gen, Property, Testable, choose, collect, cover,
                   forAllShrinkShow, labelledExamplesWith, maxSuccess,
                   once, property, replay, sized, stdArgs, whenFail)
import           Test.QuickCheck.Monadic
                   (PropertyM, run)
import           Test.QuickCheck.Random
                   (mkQCGen)
import           Text.PrettyPrint.ANSI.Leijen
                   (Doc)
import qualified Text.PrettyPrint.ANSI.Leijen      as PP
import           Text.Show.Pretty
                   (ppShow)
import           UnliftIO
                   (MonadIO, TChan, atomically, liftIO, newTChanIO,
                   tryReadTChan, writeTChan)
import           UnliftIO.Exception (throwIO)

import           Test.StateMachine.ConstructorName
import           Test.StateMachine.Labelling
                   (Event(..), execCmds)
import           Test.StateMachine.Logic
import           Test.StateMachine.Types
import qualified Test.StateMachine.Types.Rank2     as Rank2
import           Test.StateMachine.Utils

------------------------------------------------------------------------

forAllCommands :: Testable prop
               => (Show (cmd Symbolic), Show (resp Symbolic), Show (model Symbolic))
               => (Rank2.Traversable cmd, Rank2.Foldable resp)
               => StateMachine model cmd m resp
               -> Maybe Int -- ^ Minimum number of commands.
               -> (Commands cmd resp -> prop)     -- ^ Predicate.
               -> Property
forAllCommands sm mminSize =
  forAllShrinkShow (generateCommands sm mminSize) (shrinkCommands sm) ppShow

-- | Generate commands from a list of generators.
existsCommands :: forall model cmd m resp prop. (Testable prop, Rank2.Foldable resp)
               => (Show (model Symbolic), Show (cmd Symbolic), Show (resp Symbolic))
               => StateMachine model cmd m resp
               -> [model Symbolic -> Gen (cmd Symbolic)]  -- ^ Generators.
               -> (Commands cmd resp -> prop)             -- ^ Predicate.
               -> Property
existsCommands StateMachine { initModel, precondition, transition, mock } gens0 =
  once . forAllShrinkShow (go gens0 initModel newCounter []) (const []) ppShow
  where
    go :: [model Symbolic -> Gen (cmd Symbolic)] -> model Symbolic -> Counter
       -> [Command cmd resp] -> Gen (Commands cmd resp)
    go []           _model _counter acc = return (Commands (reverse acc))
    go (gen : gens) model  counter  acc = do
      cmd <- either (deadlockError model acc . ppShow) id <$>
               gen model `suchThatEither` (boolean . precondition model)
      let (resp, counter') = runGenSym (mock model cmd) counter
      go gens (transition model cmd resp) counter'
         (Command cmd resp (getUsedVars resp) : acc)

deadlockError :: (Show (model Symbolic), Show (cmd Symbolic), Show (resp Symbolic))
              => model Symbolic -> [Command cmd resp] -> String -> b
deadlockError model generated counterexamples = error $ concat
  [ "\n"
  , "A deadlock occured while generating commands.\n"
  , "No pre-condition holds in the following model:\n\n"
  , "    " ++ ppShow model
  , "\n\nThe following commands have been generated so far:\n\n"
  , "    " ++ ppShow generated
  , "\n\n"
  , "Example commands generated whose pre-condition doesn't hold:\n\n"
  , "    " ++ counterexamples
  , "\n"
  ]

generateCommands :: (Rank2.Foldable resp, Show (model Symbolic))
                 => (Show (cmd Symbolic), Show (resp Symbolic))
                 => StateMachine model cmd m resp
                 -> Maybe Int -- ^ Minimum number of commands.
                 -> Gen (Commands cmd resp)
generateCommands sm@StateMachine { initModel } mminSize =
  evalStateT (generateCommandsState sm newCounter mminSize) initModel

generateCommandsState :: forall model cmd m resp. Rank2.Foldable resp
                      => (Show (model Symbolic), Show (cmd Symbolic), Show (resp Symbolic))
                      => StateMachine model cmd m resp
                      -> Counter
                      -> Maybe Int -- ^ Minimum number of commands.
                      -> StateT (model Symbolic) Gen (Commands cmd resp)
generateCommandsState StateMachine { precondition, generator, transition, mock } counter0 mminSize = do
  let minSize = fromMaybe 0 mminSize
  size0 <- lift (sized (\k -> choose (minSize, k + minSize)))
  go size0 counter0 []
  where
    go :: Int -> Counter -> [Command cmd resp]
       -> StateT (model Symbolic) Gen (Commands cmd resp)
    go 0    _       cmds = return (Commands (reverse cmds))
    go size counter cmds = do
      model <- get
      case generator model of
        Nothing  -> return (Commands (reverse cmds))
        Just gen -> do
          enext <- lift $ gen `suchThatEither` (boolean . precondition model)
          case enext of
            Left  ces  -> deadlockError model (reverse cmds) (ppShow ces)
            Right next -> do
              let (resp, counter') = runGenSym (mock model next) counter
              put (transition model next resp)
              go (size - 1) counter' (Command next resp (getUsedVars resp) : cmds)

getUsedVars :: Rank2.Foldable f => f Symbolic -> [Var]
getUsedVars = Rank2.foldMap (\(Symbolic v) -> [v])

-- | Shrink commands in a pre-condition and scope respecting way.
shrinkCommands ::  forall model cmd m resp. (Rank2.Traversable cmd, Rank2.Foldable resp)
               => StateMachine model cmd m resp -> Commands cmd resp
               -> [Commands cmd resp]
shrinkCommands sm@StateMachine { initModel } =
    concatMap go . shrinkListS' . unCommands
  where
    go :: Shrunk [Command cmd resp] -> [Commands cmd resp]
    go (Shrunk shrunk cmds) = map snd $
        shrinkAndValidate sm
                          (if shrunk then DontShrink else MustShrink)
                          (initValidateEnv initModel)
                          (Commands cmds)

-- | Environment required during 'shrinkAndValidate'
data ValidateEnv model = ValidateEnv {
      -- | The model we're starting validation from
      veModel   :: model Symbolic

      -- | Reference renumbering
      --
      -- When a command
      --
      -- > Command .. [Var i, ..]
      --
      -- is changed during validation to
      --
      -- > Command .. [Var j, ..]
      --
      -- then any subsequent uses of @Var i@ should be replaced by @Var j@. This
      -- is recorded in 'veScope'. When we /remove/ the first command
      -- altogether (during shrinking), then @Var i@ won't appear in the
      -- 'veScope' and shrank candidates that contain commands referring to @Var
      -- i@ should be considered as invalid.
    , veScope   :: Map Var Var

      -- | Counter (for generating new references)
    , veCounter :: Counter
    }

initValidateEnv :: model Symbolic -> ValidateEnv model
initValidateEnv initModel = ValidateEnv {
      veModel   = initModel
    , veScope   = M.empty
    , veCounter = newCounter
    }

data ShouldShrink = MustShrink | DontShrink

-- | Validate list of commands, optionally shrinking one of the commands
--
-- The input to this function is a list of commands ('Commands'), for example
--
-- > [A, B, C, D, E, F, G, H]
--
-- The /result/ is a /list/ of 'Commands', i.e. a list of lists. The
-- outermost list is used for all the shrinking possibilities. For example,
-- let's assume we haven't shrunk something yet, and therefore need to shrink
-- one of the commands. Let's further assume that only commands B and E can be
-- shrunk, to B1, B2 and E1, E2, E3 respectively. Then the result will look
-- something like
--
-- > [    -- outermost list recording all the shrink possibilities
-- >     [A', B1', C', D', E' , F', G', H']   -- B shrunk to B1
-- >   , [A', B2', C', D', E' , F', G', H']   -- B shrunk to B2
-- >   , [A', B' , C', D', E1', F', G', H']   -- E shrunk to E1
-- >   , [A', B' , C', D', E2', F', G', H']   -- E shrunk to E2
-- >   , [A', B' , C', D', E3', F', G', H']   -- E shrunk to E3
-- > ]
--
-- where one of the commands has been shrunk and all commands have been
-- validated and renumbered (references updated). So, in this example, the
-- result will contain at most 5 lists; it may contain fewer, since some of
-- these lists may not be valid.
--
-- If we _did_ already shrink something, then no commands will be shrunk, and
-- the resulting list will either be empty (if the list of commands was invalid)
-- or contain a /single/ element with the validated and renumbered commands.
shrinkAndValidate :: forall model cmd m resp. (Rank2.Traversable cmd, Rank2.Foldable resp)
                  => StateMachine model cmd m resp
                  -> ShouldShrink
                  -> ValidateEnv model
                  -> Commands cmd resp
                  -> [(ValidateEnv model, Commands cmd resp)]
shrinkAndValidate StateMachine { precondition, transition, mock, shrinker } =
    \env shouldShrink cmds -> map (second Commands) $ go env shouldShrink (unCommands cmds)
  where
    go :: ShouldShrink -> ValidateEnv model -> [Command cmd resp] -> [(ValidateEnv model, [Command cmd resp])]
    go MustShrink   _   [] = []          -- we failed to shrink anything
    go DontShrink   env [] = [(env, [])] -- successful termination
    go shouldShrink (ValidateEnv model scope counter) (Command cmd' _resp vars' : cmds) =
      case Rank2.traverse (remapVars scope) cmd' of
        Just remapped ->
          -- shrink at most one command
          let candidates :: [(ShouldShrink, cmd Symbolic)]
              candidates =
                case shouldShrink of
                  DontShrink -> [(DontShrink, remapped)]
                  MustShrink -> map (DontShrink,) (shrinker model remapped)
                             ++ [(MustShrink, remapped)]
          in flip concatMap candidates $ \(shouldShrink', cmd) ->
               if boolean (precondition model cmd)
                 then let (resp, counter') = runGenSym (mock model cmd) counter
                          vars = getUsedVars resp
                          env' = ValidateEnv {
                                     veModel   = transition model cmd resp
                                   , veScope   = M.fromList (zip vars' vars) `M.union` scope
                                   , veCounter = counter'
                                   }
                      in map (second (Command cmd resp vars:)) $ go shouldShrink' env' cmds
                 else []
        Nothing ->
          []

    remapVars :: Map Var Var -> Symbolic a -> Maybe (Symbolic a)
    remapVars scope (Symbolic v) = Symbolic <$> M.lookup v scope

runCommands :: (Show (cmd Concrete), Show (resp Concrete))
            => (Rank2.Traversable cmd, Rank2.Foldable resp)
            => (MonadCatch m, MonadIO m)
            => StateMachine model cmd m resp
            -> Commands cmd resp
            -> PropertyM m (History cmd resp, model Concrete, Reason)
runCommands sm@StateMachine { initModel } = run . go
  where
    go cmds = do
      hchan <- newTChanIO
      (reason, (_, _, _, model)) <- runStateT
        (executeCommands sm hchan (Pid 0) CheckEverything cmds)
        (emptyEnvironment, initModel, newCounter, initModel)
      hist <- getChanContents hchan
      return (History hist, model, reason)

getChanContents :: MonadIO m => TChan a -> m [a]
getChanContents chan = reverse <$> atomically (go' [])
  where
    go' acc = do
      mx <- tryReadTChan chan
      case mx of
        Just x  -> go' (x : acc)
        Nothing -> return acc

data Check
  = CheckPrecondition
  | CheckEverything
  | CheckNothing

executeCommands :: (Show (cmd Concrete), Show (resp Concrete))
                => (Rank2.Traversable cmd, Rank2.Foldable resp)
                => (MonadCatch m, MonadIO m)
                => StateMachine model cmd m resp
                -> TChan (Pid, HistoryEvent cmd resp)
                -> Pid
                -> Check
                -> Commands cmd resp
                -> StateT (Environment, model Symbolic, Counter, model Concrete) m Reason
executeCommands StateMachine {..} hchan pid check =
  go . unCommands
  where
    go []                           = return Ok
    go (Command scmd _ vars : cmds) = do
      (env, smodel, counter, cmodel) <- get
      case (check, logic (precondition smodel scmd)) of
        (CheckPrecondition, VFalse ce) -> return (PreconditionFailed (show ce))
        (CheckEverything,   VFalse ce) -> return (PreconditionFailed (show ce))
        _otherwise                    -> do
          let ccmd = fromRight (error "executeCommands: impossible") (reify env scmd)
          atomically (writeTChan hchan (pid, Invocation ccmd (S.fromList vars)))
          !ecresp <- lift $ (fmap Right (semantics ccmd)) `catch`
                            \(err :: SomeException) -> do
                              when (isSomeAsyncException err) (liftIO (putStrLn $ displayException err) >> throwIO err)
                              return (Left (displayException err))
          case ecresp of
            Left err    -> do
              atomically (writeTChan hchan (pid, Exception err))
              return ExceptionThrown
            Right cresp -> do
              let cvars = getUsedConcrete cresp
              if length vars /= length cvars
              then do
                let err = mockSemanticsMismatchError (ppShow ccmd) (ppShow vars) (ppShow cresp) (ppShow cvars)
                atomically (writeTChan hchan (pid, Exception err))
                return MockSemanticsMismatch
              else do
                atomically (writeTChan hchan (pid, Response cresp))
                case (check, logic (postcondition cmodel ccmd cresp)) of
                  (CheckEverything, VFalse ce) -> return (PostconditionFailed (show ce))
                  _otherwise ->
                    case (check, logic (fromMaybe (const Top) invariant cmodel)) of
                      (CheckEverything, VFalse ce') -> return (InvariantBroken (show ce'))
                      _otherwise                    -> do
                        let (sresp, counter') = runGenSym (mock smodel scmd) counter
                        put ( insertConcretes vars cvars env
                            , transition smodel scmd sresp
                            , counter'
                            , transition cmodel ccmd cresp
                            )
                        go cmds

    isSomeAsyncException :: SomeException -> Bool
    isSomeAsyncException se = case fromException se of
      Just (SomeAsyncException _) -> True
      _                           -> False

    mockSemanticsMismatchError :: String -> String -> String -> String -> String
    mockSemanticsMismatchError cmd svars cresp cvars = unlines
      [ ""
      , "Mismatch between `mock` and `semantics`."
      , ""
      , "The definition of `mock` for the command:"
      , ""
      , "    ", cmd
      , ""
      , "returns the following references:"
      , ""
      , "    ", svars
      , ""
      , "while the response from `semantics`:"
      , ""
      , "    ", cresp
      , ""
      , "returns the following references:"
      , ""
      , "    ", cvars
      , ""
      , "Continuing to execute commands at this point could result in scope"
      , "errors, because we might have commands that use references (returned"
      , "by `mock`) that are not available (returned by `semantics`), to avoid"
      , "this please fix the mismatch."
      , ""
      ]

getUsedConcrete :: Rank2.Foldable f => f Concrete -> [Dynamic]
getUsedConcrete = Rank2.foldMap (\(Concrete x) -> [toDyn x])

modelDiff :: ToExpr (model r) => model r -> Maybe (model r) -> Doc
modelDiff model = ansiWlBgEditExprCompact . flip ediff model . fromMaybe model

prettyPrintHistory :: forall model cmd m resp. ToExpr (model Concrete)
                   => (Show (cmd Concrete), Show (resp Concrete))
                   => StateMachine model cmd m resp
                   -> History cmd resp
                   -> IO ()
prettyPrintHistory StateMachine { initModel, transition }
  = PP.putDoc
  . go initModel Nothing
  . makeOperations
  . unHistory
  where
    go :: model Concrete -> Maybe (model Concrete) -> [Operation cmd resp] -> Doc
    go current previous [] =
      PP.line <> modelDiff current previous <> PP.line <> PP.line
    go current previous [Crash cmd err pid] =
      mconcat
        [ PP.line
        , modelDiff current previous
        , PP.line, PP.line
        , PP.string "   == "
        , PP.string (ppShow cmd)
        , PP.string " ==> "
        , PP.string err
        , PP.string " [ "
        , PP.int (unPid pid)
        , PP.string " ]"
        , PP.line
        ]
    go current previous (Operation cmd resp pid : ops) =
      mconcat
        [ PP.line
        , modelDiff current previous
        , PP.line, PP.line
        , PP.string "   == "
        , PP.string (ppShow cmd)
        , PP.string " ==> "
        , PP.string (ppShow resp)
        , PP.string " [ "
        , PP.int (unPid pid)
        , PP.string " ]"
        , PP.line
        , go (transition current cmd resp) (Just current) ops
        ]
    go _ _ _ = error "prettyPrintHistory: impossible."

prettyCommands :: (MonadIO m, ToExpr (model Concrete))
               => (Show (cmd Concrete), Show (resp Concrete))
               => StateMachine model cmd m resp
               -> History cmd resp
               -> Property
               -> PropertyM m ()
prettyCommands sm hist prop = prettyPrintHistory sm hist `whenFailM` prop

prettyPrintHistory' :: forall model cmd m resp tag. ToExpr (model Concrete)
                    => (Show (cmd Concrete), Show (resp Concrete), ToExpr tag)
                    => StateMachine model cmd m resp
                    -> ([Event model cmd resp Symbolic] -> [tag])
                    -> Commands cmd resp
                    -> History cmd resp
                    -> IO ()
prettyPrintHistory' sm@StateMachine { initModel, transition } tag cmds
  = PP.putDoc
  . go initModel Nothing [] (map tag (drop 1 (inits (execCmds sm cmds))))
  . makeOperations
  . unHistory
  where
    tagsDiff :: [tag] -> [tag] -> Doc
    tagsDiff old new = ansiWlBgEditExprCompact (ediff old new)

    go :: model Concrete -> Maybe (model Concrete) -> [tag] -> [[tag]]
       -> [Operation cmd resp] -> Doc
    go current previous _seen _tags [] =
      PP.line <> modelDiff current previous <> PP.line <> PP.line
    go current previous seen (tags : _) [Crash cmd err pid] =
      mconcat
        [ PP.line
        , modelDiff current previous
        , PP.line, PP.line
        , PP.string "   == "
        , PP.string (ppShow cmd)
        , PP.string " ==> "
        , PP.string err
        , PP.string " [ "
        , PP.int (unPid pid)
        , PP.string " ]"
        , PP.line
        , if not (null tags)
          then PP.line <> PP.string "   " <> tagsDiff seen tags <> PP.line
          else PP.empty
        ]
    go current previous seen (tags : tagss) (Operation cmd resp pid : ops) =
      mconcat
        [ PP.line
        , modelDiff current previous
        , PP.line, PP.line
        , PP.string "   == "
        , PP.string (ppShow cmd)
        , PP.string " ==> "
        , PP.string (ppShow resp)
        , PP.string " [ "
        , PP.int (unPid pid)
        , PP.string " ]"
        , PP.line
        , if not (null tags)
          then PP.line <> PP.string "   " <> tagsDiff seen tags <> PP.line
          else PP.empty
        , go (transition current cmd resp) (Just current) tags tagss ops
        ]
    go _ _ _ _ _ = error "prettyPrintHistory': impossible."

-- | Variant of 'prettyCommands' that also prints the @tag@s covered by each
-- command.
prettyCommands' :: (MonadIO m, ToExpr (model Concrete), ToExpr tag)
                => (Show (cmd Concrete), Show (resp Concrete))
                => StateMachine model cmd m resp
                -> ([Event model cmd resp Symbolic] -> [tag])
                -> Commands cmd resp
                -> History cmd resp
                -> Property
                -> PropertyM m ()
prettyCommands' sm tag cmds hist prop =
  prettyPrintHistory' sm tag cmds hist `whenFailM` prop

saveCommands :: (Show (cmd Symbolic), Show (resp Symbolic))
             => FilePath -> Commands cmd resp -> Property -> Property
saveCommands dir cmds prop = go `whenFail` prop
  where
    go :: IO ()
    go = do
      createDirectoryIfMissing True dir
      file <- formatTime defaultTimeLocale "%F_%T" <$> getZonedTime
      let fp = dir </> file
      writeFile fp (ppShow cmds)
      putStrLn ("Saved counterexample in: " ++ fp)
      putStrLn ""

runSavedCommands :: (Show (cmd Concrete), Show (resp Concrete))
                 => (Rank2.Traversable cmd, Rank2.Foldable resp)
                 => (MonadCatch m, MonadIO m)
                 => (Read (cmd Symbolic), Read (resp Symbolic))
                 => StateMachine model cmd m resp
                 -> FilePath
                 -> PropertyM m (Commands cmd resp, History cmd resp, model Concrete, Reason)
runSavedCommands sm fp = do
  cmds <- read <$> liftIO (readFile fp)
  (hist, model, res) <- runCommands sm cmds
  return (cmds, hist, model, res)

------------------------------------------------------------------------


-- | Print distribution of commands and fail if some commands have not
--   been executed.
checkCommandNames :: forall cmd resp. CommandNames cmd
                  => Commands cmd resp -> Property -> Property
checkCommandNames cmds
  = collect names
  . cover 1 (length names == numOfConstructors) "coverage"
  where
    names             = commandNames cmds
    numOfConstructors = length (cmdNames (Proxy :: Proxy (cmd Symbolic)))

commandNames :: forall cmd resp. CommandNames cmd
             => Commands cmd resp -> [(String, Int)]
commandNames = M.toList . foldl go M.empty . unCommands
  where
    go :: Map String Int -> Command cmd resp -> Map String Int
    go ih cmd = M.insertWith (+) (commandName cmd) 1 ih

commandNamesInOrder :: forall cmd resp. CommandNames cmd
                    => Commands cmd resp -> [String]
commandNamesInOrder = reverse . foldl go [] . unCommands
  where
    go :: [String] -> Command cmd resp -> [String]
    go ih cmd = commandName cmd : ih

------------------------------------------------------------------------

-- | Show minimal examples for each of the generated tags.
showLabelledExamples' :: (Show tag, Show (model Symbolic))
                      => (Show (cmd Symbolic), Show (resp Symbolic))
                      => (Rank2.Traversable cmd, Rank2.Foldable resp)
                      => StateMachine model cmd m resp
                      -> Maybe Int
                      -- ^ Seed
                      -> Int
                      -- ^ Number of tests to run to find examples
                      -> ([Event model cmd resp Symbolic] -> [tag])
                      -> (tag -> Bool)
                      -- ^ Tag filter (can be @const True@)
                      -> IO ()
showLabelledExamples' sm mReplay numTests tag focus = do
    replaySeed <- case mReplay of
      Nothing   -> getStdRandom (randomR (1, 999999))
      Just seed -> return seed

    labelledExamplesWith (stdArgs { replay     = Just (mkQCGen replaySeed, 0)
                                  , maxSuccess = numTests
                                  }) $
      forAllShrinkShow (generateCommands sm Nothing)
                       (shrinkCommands   sm)
                       ppShow $ \cmds ->
        collects (filter focus . tag . execCmds sm $ cmds) $
          property True

    putStrLn $ "Used replaySeed " ++ show replaySeed

showLabelledExamples :: (Show tag, Show (model Symbolic))
                     => (Show (cmd Symbolic), Show (resp Symbolic))
                     => (Rank2.Traversable cmd, Rank2.Foldable resp)
                     => StateMachine model cmd m resp
                     -> ([Event model cmd resp Symbolic] -> [tag])
                     -> IO ()
showLabelledExamples sm tag = showLabelledExamples' sm Nothing 1000 tag (const True)
