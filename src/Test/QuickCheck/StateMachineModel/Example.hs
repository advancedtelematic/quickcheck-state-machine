{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE StandaloneDeriving         #-}

module Test.QuickCheck.StateMachineModel.Example where

import           Control.Applicative
import           Control.Concurrent                (threadDelay)
import           Control.Monad.State
import           Data.Char
import           Data.Dynamic
import           Data.IORef
import           Data.List
import           System.Random
import           Test.QuickCheck
import           Test.QuickCheck.Monadic
import           Text.Read
import           Unsafe.Coerce

import           Test.QuickCheck.StateMachineModel
import           Test.QuickCheck.StateMachineModel.Utils

------------------------------------------------------------------------

newtype Ref = Ref Int
  deriving (Eq, Read, Ord, Show, Enum)

unRef :: Ref -> Int
unRef (Ref i) = i

data MemStepF :: * -> * -> * where
  New   ::               MemStepF ref ref
  Read  :: ref ->        MemStepF Int ref
  Write :: ref -> Int -> MemStepF ()  ref
  Inc   :: ref ->        MemStepF ()  ref

deriving instance Show ref => Show (MemStepF resp ref)
deriving instance Eq   ref => Eq   (MemStepF resp ref)
deriving instance Ord  ref => Ord  (MemStepF resp ref)
deriving instance Foldable (MemStepF resp)

type MemStep resp = MemStepF resp Ref

------------------------------------------------------------------------

type Model = [Int]

initModel :: Model
initModel = []

preconditions :: Model -> MemStep resp -> Bool
preconditions m cmd = case cmd of
  New             -> True
  Read  (Ref i)   -> i < length m
  Write (Ref i) _ -> i < length m
  Inc   (Ref i)   -> i < length m

transitions :: Model -> MemStep resp -> resp -> Model
transitions m cmd _ = case cmd of
  New         -> m ++ [0]
  Read  _     -> m
  Write ref i -> update m (unRef ref) i
  Inc   ref   -> update m (unRef ref) ((m ! ref) + 1)

postconditions :: Model -> MemStep resp  -> resp -> Property
postconditions m cmd resp = case cmd of
  New         -> property $ True
  Read ref    -> m  ! ref === resp .&&. m' == m
  Write ref i -> property $ m' ! ref == i
  Inc   ref   -> property $ m' ! ref == m ! ref + 1
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

data Problem = None | Bug | RaceCondition
  deriving Eq

semStep :: MonadIO m => Problem -> MemStepF resp (IORef Int) -> m resp
semStep _   New           = liftIO (newIORef 0)
semStep _   (Read  ref)   = liftIO (readIORef ref)
semStep prb (Write ref i) = liftIO (writeIORef ref i')
  where
  -- Introduce bug:
  i' | i `elem` [5..10] = if prb == Bug then i + 1 else i
     | otherwise        = i
semStep prb (Inc ref)     = liftIO $ do

  -- Possible race condition:
  if prb == RaceCondition
  then do
    i <- readIORef ref
    threadDelay =<< randomRIO (0, 5000)
    writeIORef ref (i + 1)
  else
    atomicModifyIORef' ref (\i -> (i + 1, ()))

------------------------------------------------------------------------

debugMem :: MonadIO io => [Untyped MemStepF Ref] -> io ()
debugMem ms0 = do
  liftIO $ putStrLn ""
  env <- semSteps ms0
  liftIO $ putStrLn ""
  forM_ (zip [(0 :: Integer)..] env) $ \(i, ref) -> liftIO $ do
    v <- readIORef ref
    putStrLn $ "$" ++ show i ++ ": " ++ show v
  where
  semSteps :: MonadIO io => [Untyped MemStepF Ref] -> io [IORef Int]
  semSteps = flip execStateT [] . go
    where
    go :: MonadIO io => [Untyped MemStepF Ref] -> StateT [IORef Int] io ()
    go = flip foldM () $ \_ (Untyped ms) -> do
      liftIO (print ms)
      _ <- semStep' ms
      return ()
      where
      semStep'
        :: (MonadIO io, Typeable resp, Show resp)
        => MemStep resp -> StateT [IORef Int] io resp
      semStep' = liftSem (semStep None)

------------------------------------------------------------------------

gens :: [(Int, Gen (Untyped MemStepF ()))]
gens =
  [ (1, return . Untyped $ New)
  , (5, return . Untyped $ Read ())
  , (5, Untyped . Write () <$> arbitrary)
  , (5, return . Untyped $ Inc ())
  ]

------------------------------------------------------------------------

shrink1 :: Untyped MemStepF ref -> [Untyped MemStepF ref ]
shrink1 (Untyped (Write ref i)) = [ Untyped (Write ref i') | i' <- shrink i ]
shrink1 _                       = []

------------------------------------------------------------------------

instance Show ref => Show (Untyped MemStepF ref) where
  show (Untyped c) = show c

-- https://ghc.haskell.org/trac/ghc/ticket/8128
instance (Read ref, Typeable ref, Show ref) => Read (Untyped MemStepF ref) where

  readPrec = parens $ do
    Ident ident <- parens lexP
    case ident of
      "New"   -> return $ Untyped New
      "Read"  -> Untyped . Read  <$> readPrec
      "Write" -> Untyped <$> (Write <$> readPrec <*> readPrec)
      "Inc"   -> Untyped . Inc   <$> readPrec
      _       -> empty

  readListPrec = readListPrecDefault

instance (Eq ref, Typeable ref) => Eq (Untyped MemStepF ref) where
  Untyped c1 == Untyped c2 = Just c1 == cast c2

instance (Ord ref, Typeable ref) => Ord (Untyped MemStepF ref) where
  Untyped c1 <= Untyped c2 = Just c1 <= cast c2

instance Functor (MemStepF resp) where
  fmap _ New           = unsafeCoerce New -- XXX: Hmm?
  fmap f (Read  ref)   = Read  (f ref)
  fmap f (Write ref i) = Write (f ref) i
  fmap f (Inc   ref)   = Inc   (f ref)

deriving instance Functor  (Untyped MemStepF)
deriving instance Foldable (Untyped MemStepF)

instance (Enum ref, Ord ref) => RefKit MemStepF ref where
  returnsRef (Untyped New) = True
  returnsRef _             = False

  returnsRef' New = Just Refl
  returnsRef' _   = Nothing

------------------------------------------------------------------------

smm :: StateMachineModel Model MemStepF Ref
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
  (semStep prb)
  ioProperty

prop_parallel :: Problem -> Property
prop_parallel prb = parallelProperty
  smm
  gens
  shrink1
  (semStep prb)

------------------------------------------------------------------------

scopeCheck :: RefKit cmd ref => [Untyped cmd ref] -> Bool
scopeCheck = go 0
  where
  go _ []       = True
  go s (c : cs) = all (\r -> r < toEnum s) (usesRefs c) &&
    go (if returnsRef c then s + 1 else s) cs

prop_genScope :: Property
prop_genScope = forAll (liftGenFork gens) $ \(Fork l p r) ->
  scopeCheck (p ++ l) &&
  scopeCheck (p ++ (r :: [Untyped MemStepF Ref]))

shrinkPropertyHelper :: Property -> (String -> Bool) -> Property
shrinkPropertyHelper prop p = monadicIO $ do
  result <- run $ quickCheckWithResult (stdArgs {chatty = False}) prop
  case result of
    Failure { output = outputLines } -> liftProperty $
      counterexample ("failed: " ++ outputLines) $ p outputLines
    _                                -> return ()

prop_sequentialShrink :: Property
prop_sequentialShrink = shrinkPropertyHelper (prop_safety Bug)
  ((== "[New,Write (Ref 0) 5,Read (Ref 0)]") . (!! 1) . lines)

cheat :: Fork [Untyped MemStepF Ref] -> Fork [Untyped MemStepF Ref]
cheat = fmap (map (\ms -> case ms of
                      Untyped (Write ref _) -> Untyped (Write ref 0)
                      _                     -> ms))

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
                           scopeCheck (p' ++ (r' :: [Untyped MemStepF Ref])))
      (liftShrinkFork shrink1 f)

------------------------------------------------------------------------

prop_shrinkForkMinimal :: Property
prop_shrinkForkMinimal = shrinkPropertyHelper (prop_parallel RaceCondition) $ \out ->
  let f = read $ dropWhile isSpace (lines out !! 1)
  in hasMinimalShrink f || f `elem` minimal
  where
  hasMinimalShrink :: Fork [Untyped MemStepF Ref] -> Bool
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

  minimal :: [Fork [Untyped MemStepF Ref]]
  minimal  = minimal' ++ map mirrored minimal'
    where
    minimal' = [m0, m1, m2, m3]

    mirrored :: Fork a -> Fork a
    mirrored (Fork l p r) = Fork r p l

    m0 = Fork [Untyped (Write (Ref 0) 0), Untyped (Read (Ref 0))]
              [Untyped New]
              [Untyped (Inc (Ref 0))]

    m1 = Fork [Untyped (Write (Ref 0) 0)]
              [Untyped New]
              [Untyped (Inc (Ref 0)), Untyped (Read (Ref 0))]

    m2 = Fork [Untyped (Inc (Ref 0)), Untyped (Read (Ref 0))]
              [Untyped New]
              [Untyped (Inc (Ref 0))]

    m3 = Fork [Untyped (Inc (Ref 0))]
              [Untyped New]
              [Untyped (Inc (Ref 0)), Untyped (Read (Ref 0))]
