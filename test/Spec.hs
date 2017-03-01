{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}

module Main where

import           Control.Concurrent                (threadDelay)
import           Control.Monad.State
import           Data.Char
import           Data.IORef
import           Data.List
import           Data.Maybe
import           System.Random
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck
import           Test.QuickCheck.Monadic

import           Test.QuickCheck.StateMachineModel

------------------------------------------------------------------------

newtype Ref = Ref Int
  deriving (Eq, Read, Ord, Show, Enum)

unRef :: Ref -> Int
unRef (Ref i) = i

data MemStepF ref
  = New
  | Read ref
  | Write ref Int
  | Inc ref
  deriving (Show, Eq, Read, Functor, Foldable, Ord)

type MemStep = MemStepF Ref

------------------------------------------------------------------------

type Model = [Int]

initModel :: Model
initModel = []

preconditions :: Model -> MemStep -> Bool
preconditions m cmd = case cmd of
  New             -> True
  Read  (Ref i)   -> i < length m
  Write (Ref i) _ -> i < length m
  Inc   (Ref i)   -> i < length m

transitions :: Model -> MemStep -> Response -> Model
transitions m cmd resp = case cmd of
  New         -> m ++ [0]
  Read  _     -> m
  Write ref i -> update m (unRef ref) i
  Inc   ref   -> update m (unRef ref) ((m ! ref) + 1)

postconditions :: Model -> MemStep -> Response -> Bool
postconditions m cmd resp = case cmd of
  New         -> True
  Read  ref   -> let ReadR i = resp in m ! ref == i && m' == m
  Write ref i -> m' ! ref == i
  Inc   ref   -> m' ! ref == m ! ref + 1
  where
  m' = transitions m cmd resp

------------------------------------------------------------------------

(!) :: [a] -> Ref -> a
xs0 ! (Ref i0) = case go xs0 i0 of
  Nothing -> error $ "!: " ++ show (length xs0, i0)
  Just x  -> x
  where
  go :: [a] -> Int -> Maybe a
  go []       _ = Nothing
  go (x : _)  0 = Just x
  go (_ : xs) i = go xs (i - 1)

update :: [a] -> Int -> a -> [a]
update []       _ _ = []
update (_ : xs) 0 y = y : xs
update (x : xs) i y = x : update xs (i - 1) y


------------------------------------------------------------------------

data Response
  = NewR (IORef Int)
  | ReadR Int
  | WriteR
  | IncR
  deriving Eq

instance Show Response where
  show (NewR _)  = "$"
  show (ReadR i) = show i
  show WriteR    = "()"
  show IncR      = "()"

------------------------------------------------------------------------

data Problem = None | Bug | RaceCondition
  deriving Eq

semStep :: MonadIO m => Problem -> MemStepF (IORef Int) -> m Response
semStep _   New           = NewR   <$> liftIO (newIORef 0)
semStep _   (Read ref)    = ReadR  <$> liftIO (readIORef ref)
semStep prb (Write ref i) = WriteR <$  liftIO (writeIORef ref i')
  where
  -- Introduce bug:
  i' | i `elem` [5..10] = if prb == Bug then i + 1 else i
     | otherwise        = i
semStep prb (Inc ref)     = liftIO $ do

  -- Possible race condition:
  if prb == RaceCondition
  then do
    i <- readIORef ref
    threadDelay =<< randomRIO (0, 200)
    writeIORef ref (i + 1)
  else
    atomicModifyIORef' ref (\i -> (i + 1, ()))

  return IncR

isRef :: Response -> Maybe (IORef Int)
isRef (NewR ref) = Just ref
isRef _          = Nothing

debugMem :: MonadIO io => [MemStep] -> io ()
debugMem ms = do
  liftIO $ putStrLn ""
  env <- semSteps ms
  liftIO $ putStrLn ""
  forM_ (zip [(0 :: Integer)..] env) $ \(i, ref) -> liftIO $ do
    v <- readIORef ref
    putStrLn $ "$" ++ show i ++ ": " ++ show v
  where
  semSteps :: MonadIO io => [MemStep] -> io [IORef Int]
  semSteps = flip execStateT [] . go
    where
    go :: MonadIO io => [MemStep] -> StateT [IORef Int] io ()
    go = flip foldM () $ \ih ms -> do
      liftIO (print ms)
      semStep' ms
      return ih
      where
      semStep' :: MonadIO io => MemStep -> StateT [IORef Int] io Response
      semStep' = liftSem (semStep None) isRef

------------------------------------------------------------------------

gens :: [(Int, Gen (MemStepF ()))]
gens =
  [ (1, return New)
  , (5, return $ Read ())
  , (5, Write <$> pure () <*> arbitrary)
  , (5, return $ Inc ())
  ]

------------------------------------------------------------------------

shrink1 :: MemStepF ref -> [MemStepF ref]
shrink1 (Write ref i) = [ Write ref i' | i' <- shrink i ]
shrink1 _             = []

------------------------------------------------------------------------

instance (Enum ref, Ord ref) => RefKit MemStepF ref where
  returnsRef New = True
  returnsRef _   = False

------------------------------------------------------------------------

smm :: StateMachineModel Model MemStep Response
smm = StateMachineModel
  { precondition  = preconditions
  , postcondition = postconditions
  , transition    = transitions
  , initialModel  = initModel
  }

prop_safety :: Problem -> Property
prop_safety prb = sequentialProperty
  smm
  gens
  shrink1
  show
  (semStep prb)
  ioProperty
  isRef

prop_parallel :: Problem -> Property
prop_parallel prb = parallelProperty
  smm
  gens
  shrink1
  (semStep prb)
  isRef

------------------------------------------------------------------------

scopeCheck :: RefKit cmd ref => [cmd ref] -> Bool
scopeCheck = go 0
  where
  go _ []       = True
  go s (c : cs) = all (\r -> r < toEnum s) (usesRefs c) &&
    go (if returnsRef c then s + 1 else s) cs

prop_genScope :: Property
prop_genScope = forAll (liftGenFork gens) $ \(Fork l p r) ->
  scopeCheck (p ++ l) &&
  scopeCheck (p ++ (r :: [MemStep]))

shrinkPropertyHelper :: Property -> (String -> Bool) -> Property
shrinkPropertyHelper prop p = monadicIO $ do
  result <- run $ quickCheckWithResult (stdArgs {chatty = False}) prop
  case result of
    Failure { output = outputLines } -> do
      assert' outputLines $ p outputLines
    _                                -> return ()

prop_sequentialShrink :: Property
prop_sequentialShrink = shrinkPropertyHelper (prop_safety Bug)
  ((== "[New,Write (Ref 0) 5,Read (Ref 0)]") . last . lines)

cheat :: Fork [MemStep] -> Fork [MemStep]
cheat = fmap (map (\ms -> case ms of
                      Write ref _ -> Write ref 0
                      _           -> ms))

prop_shrinkForkSubseq :: Property
prop_shrinkForkSubseq = forAll (liftGenFork gens) $ \f@(Fork l p r) ->
  all (\(Fork l' p' r') -> noRefs l' `isSubsequenceOf` noRefs l &&
                           noRefs p' `isSubsequenceOf` noRefs p &&
                           noRefs r' `isSubsequenceOf` noRefs r)
      (liftShrinkFork shrink1 (cheat f))

  where
  noRefs = fmap (const ())

prop_shrinkForkScope :: Property
prop_shrinkForkScope = forAll (liftGenFork gens) $ \f ->
  all (\(Fork l' p' r') -> scopeCheck (p' ++ l') &&
                           scopeCheck (p' ++ (r' :: [MemStep])))
      (liftShrinkFork shrink1 f)

------------------------------------------------------------------------

prop_shrinkForkMinimal :: Property
prop_shrinkForkMinimal = shrinkPropertyHelper (prop_parallel RaceCondition) $ \out ->
  let f = read $ dropWhile isSpace (lines out !! 1)
  in hasMinimalShrink f || f `elem` minimal
  where
  hasMinimalShrink :: Fork [MemStep] -> Bool
  hasMinimalShrink
    = anyRose (`elem` minimal)
    . rose (liftShrinkFork shrink1)
    where
    anyRose :: (a -> Bool) -> Rose a -> Bool
    anyRose p (Rose x xs) = p x || any (anyRose p) xs

    rose :: (a -> [a]) -> a -> Rose a
    rose more = go
      where
      go x = Rose x $ map go $ more x

  minimal :: [Fork [MemStep]]
  minimal  = minimal' ++ map mirrored minimal'
    where
    minimal' = [m0, m1, m2, m3]

    mirrored :: Fork a -> Fork a
    mirrored (Fork l p r) = Fork r p l

    m0 = Fork [Write (Ref 0) 0, Read (Ref 0)]
              [New]
              [Inc (Ref 0)]

    m1 = Fork [Write (Ref 0) 0]
              [New]
              [Inc (Ref 0), Read (Ref 0)]

    m2 = Fork [Inc (Ref 0),Read (Ref 0)]
              [New]
              [Inc (Ref 0)]

    m3 = Fork [Inc (Ref 0)]
              [New]
              [Inc (Ref 0), Read (Ref 0)]

------------------------------------------------------------------------

main :: IO ()
main = hspec $ do

  describe "liftGenFork" $
    it "generates well-scoped programs"
      prop_genScope

  describe "sequentialProperty" $ do

    it "returns a property that passes when there are no bugs" $
      prop_safety None

    it "always shrinks to the minimal counterexample when there's a bug"
      prop_sequentialShrink

  describe "liftShrinkFork" $ do

    it "shrinks into subsequences"
      prop_shrinkForkSubseq

    it "shrinks into well-scoped programs"
      prop_shrinkForkScope

  describe "parallelProperty" $

    modifyMaxSuccess (const 30) $ do

      it "returns a property that passes when there are no race conditions" $
        prop_parallel None

      it "always shrinks to one of the minimal counter examples when there's a race condition"
        prop_shrinkForkMinimal
