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
import           System.Random
import           Test.Hspec
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

newtype Mem = Mem { unMem :: [MemStep] }
  deriving (Show, Eq, Monoid, Read)

------------------------------------------------------------------------

type Model = [Int]

initModel :: Model
initModel = []

new_pre :: Model -> Bool
new_pre _ = True

new_next :: Model -> () -> IORef Int -> Model
new_next m _ _ = m ++ [0]

new_post :: Model -> () -> IORef Int -> Bool
new_post _ _ _ = True


read_pre :: Model -> Ref -> Bool
read_pre m (Ref i) = i < length m

read_next :: Model -> Ref -> Int -> Model
read_next m _ _ = m

(!) :: [a] -> Ref -> a
xs0 ! (Ref i0) = case go xs0 i0 of
  Nothing -> error $ "!: " ++ show (length xs0, i0)
  Just x  -> x
  where
  go :: [a] -> Int -> Maybe a
  go []       _ = Nothing
  go (x : _)  0 = Just x
  go (_ : xs) i = go xs (i - 1)


read_post :: Model -> Ref -> Int -> Bool
read_post m ref r = m ! ref == r && m' == m
  where
  m' = read_next m ref r

write_pre :: Model -> Ref -> Bool
write_pre m (Ref i) = i < length m

update :: [a] -> Int -> a -> [a]
update []       _ _ = []
update (_ : xs) 0 y = y : xs
update (x : xs) i y = x : update xs (i - 1) y

write_next :: Model -> (Ref, Int) -> () -> Model
write_next m (ref, i) _ = update m (unRef ref) i

write_post :: Model -> (Ref, Int) -> () -> Bool
write_post m (ref, i) _ = m' ! ref == i
  where
  m' = write_next m (ref, i) ()

inc_pre :: Model -> Ref -> Bool
inc_pre m (Ref i) = i < length m

inc_next :: Model -> Ref -> () -> Model
inc_next m ref _ = update m (unRef ref) ((m ! ref) + 1)

inc_post :: Model -> Ref -> () -> Bool
inc_post m ref _ = m' ! ref == m ! ref + 1
  where
  m' = inc_next m ref ()

------------------------------------------------------------------------

data Response
  = NewR Int (IORef Int)
  | ReadR Int
  | WriteR
  | IncR
  deriving Eq

instance Show Response where
  show (NewR i _) = '$' : show i
  show (ReadR i)  = show i
  show WriteR     = "()"
  show IncR       = "()"

------------------------------------------------------------------------

type OurMonad m = (MonadIO m, MonadState Env m)

type Env = [IORef Int]

defaultEnv :: Env
defaultEnv = []

data Problem = None | Bug | RaceCondition
  deriving Eq

semStep
  :: (MonadIO m, MonadState Env m)
  => Problem
  -> MemStepF (IORef Int)
  -> m Response
semStep _   New           = do
  i   <- length <$> get
  ref <- liftIO (newIORef 0)
  return $ NewR i ref
semStep _   (Read ref)    = ReadR  <$> liftIO (readIORef ref)
semStep prb (Write ref i) = WriteR <$  liftIO (writeIORef ref i')
  where
  -- Introduce bug:
  i' | i `elem` [5..10] = if prb == Bug then i + 1 else i
     | otherwise        = i
semStep prb (Inc ref)     = do
  liftIO $ do

    -- Possible race condition:
    if prb == RaceCondition
    then do
      i <- readIORef ref
      threadDelay =<< randomRIO (0, 200)
      writeIORef ref (i + 1)
    else
      modifyIORef' ref (+ 1)

  return IncR

isRef :: Response -> Maybe (IORef Int)
isRef (NewR _ ref) = Just ref
isRef _            = Nothing

debugMem :: Mem -> IO ()
debugMem m = do
  putStrLn ""
  (_, env) <- flip runStateT defaultEnv $ sem m
  putStrLn ""
  forM_ (zip [(0 :: Integer)..] env) $ \(i, ref) -> do
    v <- readIORef ref
    putStrLn $ "$" ++ show i ++ ": " ++ show v
  where
  sem :: OurMonad m => Mem -> m ()
  sem = foldM (\ih ms -> semStep' ms >> return ih) () . unMem
    where
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

preConds :: Model -> MemStep -> Bool
preConds m New           = new_pre   m
preConds m (Read ref)    = read_pre  m ref
preConds m (Write ref _) = write_pre m ref
preConds m (Inc ref)     = inc_pre   m ref

postNext :: Model -> MemStepF Ref -> Response -> Maybe Model
postNext m New           (NewR _ ref)
  | new_post m () ref = Just $ new_next m () ref
  | otherwise         = Nothing
postNext m (Read ref)    (ReadR i)
  | read_post m ref i = Just $ read_next m ref i
  | otherwise         = Nothing
postNext m (Write ref i) WriteR
  | write_post m (ref, i) () = Just $ write_next m (ref, i) ()
  | otherwise         = Nothing
postNext m (Inc ref)     IncR
  | inc_post m ref () = Just $ inc_next m ref ()
  | otherwise         = Nothing
postNext _ _ _ = error "postNext: Impossible"

------------------------------------------------------------------------

prop_safety :: Problem -> Property
prop_safety prb = sequentialProperty
  preConds
  postNext
  initModel
  gens
  shrink1
  show
  (semStep prb)
  isRef
  defaultEnv

prop_parallel :: Problem -> Property
prop_parallel prb = parallelProperty
  postNext
  initModel
  gens
  shrink1
  (semStep prb)
  isRef
  defaultEnv

------------------------------------------------------------------------

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

  describe "parallelProperty" $ do

    xit "returns a property that passes when there are no race conditions" $ do
      prop_parallel None

    it "always shrinks to one of the minimal counter examples when there's a race condition"
      prop_shrinkForkMinimal
