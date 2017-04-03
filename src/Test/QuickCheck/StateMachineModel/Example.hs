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
import           Control.Concurrent                      (threadDelay)
import           Control.Monad.State
import           Data.Char
import           Data.Dynamic
import           Data.IORef
import           Data.List
import           Data.Map                                (Map)
import qualified Data.Map                                as M
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

data MemStep :: * -> * -> * where
  New   ::               MemStep ref ref
  Read  :: ref ->        MemStep Int ref
  Write :: ref -> Int -> MemStep ()  ref
  Inc   :: ref ->        MemStep ()  ref

deriving instance Show ref => Show (MemStep resp ref)
deriving instance Eq   ref => Eq   (MemStep resp ref)
deriving instance Ord  ref => Ord  (MemStep resp ref)
deriving instance Foldable (MemStep resp)

------------------------------------------------------------------------

newtype Model ref = Model (Map ref Int)
  deriving Show

initModel :: Model ref
initModel = Model M.empty

preconditions :: Ord ref => Model ref -> MemStep resp ref -> Bool
preconditions (Model m) cmd = case cmd of
  New         -> True
  Read  ref   -> M.member ref m
  Write ref _ -> M.member ref m
  Inc   ref   -> M.member ref m

transitions :: (Enum ref, Ord ref) => Model ref -> MemStep resp ref -> resp -> Model ref
transitions (Model m) cmd ix = case cmd of
  New         -> Model (M.insert ix 0 m)
  Read  _     -> Model m
  Write ref i -> Model (M.insert ref i m)
  Inc   ref   -> Model (M.insert ref (m M.! ref + 1) m)

postconditions :: (Enum ref, Ord ref) => Model ref -> MemStep resp ref -> resp -> Property
postconditions (Model m) cmd resp = case cmd of
  New         -> property $ True
  Read  ref   -> property $ m  M.! ref == resp
  Write ref i -> property $ m' M.! ref == i
  Inc   ref   -> property $ m' M.! ref == m M.! ref + 1
  where
  Model m' = transitions (Model m) cmd resp

------------------------------------------------------------------------

data Problem = None | Bug | RaceCondition
  deriving Eq

semStep :: MonadIO m => Problem -> MemStep resp (IORef Int) -> m resp
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

debugMem :: MonadIO io => [Untyped MemStep (Ref, Int)] -> io ()
debugMem ms0 = do
  liftIO $ putStrLn ""
  env <- semSteps ms0
  liftIO $ putStrLn ""
  forM_ (zip [(0 :: Integer)..] env) $ \(i, ref) -> liftIO $ do
    v <- readIORef ref
    putStrLn $ "$" ++ show i ++ ": " ++ show v
  where
  semSteps :: MonadIO io => [Untyped MemStep (Ref, Int)] -> io [IORef Int]
  semSteps = fmap M.elems . flip execStateT M.empty . go
    where
    go :: MonadIO io => [Untyped MemStep (Ref, Int)]
       -> StateT (Map (Ref, Int) (IORef Int)) io ()
    go = flip foldM () $ \_ (Untyped ms) -> do
      liftIO (print ms)
      _ <- semStep' ms
      return ()
      where
      semStep'
        :: (MonadIO io, Typeable resp, Show resp)
        => MemStep resp (Ref, Int) -> StateT (Map (Ref, Int) (IORef Int)) io resp
      semStep' = liftSem (semStep None) 0

------------------------------------------------------------------------

gens :: [(Int, Gen (Untyped MemStep ()))]
gens =
  [ (1, return . Untyped $ New)
  , (5, return . Untyped $ Read ())
  , (5, Untyped . Write () <$> arbitrary)
  , (5, return . Untyped $ Inc ())
  ]

------------------------------------------------------------------------

shrink1 :: Untyped MemStep ref -> [Untyped MemStep ref ]
shrink1 (Untyped (Write ref i)) = [ Untyped (Write ref i') | i' <- shrink i ]
shrink1 _                       = []

shrink1Mono :: Untyped MemStep (Ref, Int) -> [Untyped MemStep (Ref, Int) ]
shrink1Mono = shrink1

------------------------------------------------------------------------

instance Show ref => Show (Untyped MemStep ref) where
  show (Untyped c) = show c

-- https://ghc.haskell.org/trac/ghc/ticket/8128
instance (Read ref, Typeable ref, Show ref) => Read (Untyped MemStep ref) where

  readPrec = parens $ do
    Ident ident <- parens lexP
    case ident of
      "New"   -> return $ Untyped New
      "Read"  -> Untyped . Read  <$> readPrec
      "Write" -> Untyped <$> (Write <$> readPrec <*> readPrec)
      "Inc"   -> Untyped . Inc   <$> readPrec
      _       -> empty

  readListPrec = readListPrecDefault

instance (Eq ref, Typeable ref) => Eq (Untyped MemStep ref) where
  Untyped c1 == Untyped c2 = Just c1 == cast c2

instance (Ord ref, Typeable ref) => Ord (Untyped MemStep ref) where
  Untyped c1 <= Untyped c2 = Just c1 <= cast c2

instance Functor (MemStep resp) where
  fmap _ New           = unsafeCoerce New -- XXX: Hmm?
  fmap f (Read  ref)   = Read  (f ref)
  fmap f (Write ref i) = Write (f ref) i
  fmap f (Inc   ref)   = Inc   (f ref)

deriving instance Functor  (Untyped MemStep)
deriving instance Foldable (Untyped MemStep)

instance RefKit MemStep where
  returnsRef (Untyped New) = True
  returnsRef _             = False

  returnsRef' New = Just Refl
  returnsRef' _   = Nothing

------------------------------------------------------------------------

smm :: StateMachineModel Model MemStep
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
  shrink1Mono
  (semStep prb)
  ioProperty

prop_parallel :: Problem -> Property
prop_parallel prb = parallelProperty
  smm
  gens
  shrink1Mono
  (semStep prb)

------------------------------------------------------------------------

scopeCheck
  :: (Enum ix, Ord ix, RefKit cmd)
  => [(Int, Untyped cmd (ix, Int))] -> Bool
scopeCheck = go 0 0 []
  where
  go _ _      _    []              = True
  go s oldPid refs ((pid, c) : cs) = all (\r -> r `elem` refs) (usesRefs c) &&
    go s' oldPid' refs' cs
    where
    (s', oldPid', refs')
      | returnsRef c && pid == oldPid = (s + 1, oldPid, (toEnum s, pid) : refs)
      | returnsRef c && pid /= oldPid = (1,     pid,    (toEnum 0, pid) : refs)
      | otherwise                     = (s,     oldPid,           refs)

prop_genScope :: Property
prop_genScope = forAll (liftGenFork gens) $ \(Fork l p r) ->
  let p' = zip (repeat 0) p in
  scopeCheck (p' ++ zip (repeat 1) l) &&
  scopeCheck (p' ++ zip (repeat 2) (r :: [Untyped MemStep (Ref, Int)]))

shrinkPropertyHelper :: Property -> (String -> Bool) -> Property
shrinkPropertyHelper prop p = monadicIO $ do
  result <- run $ quickCheckWithResult (stdArgs {chatty = False}) prop
  case result of
    Failure { output = outputLines } -> liftProperty $
      counterexample ("failed: " ++ outputLines) $ p outputLines
    _                                -> return ()

prop_sequentialShrink :: Property
prop_sequentialShrink = shrinkPropertyHelper (prop_safety Bug)
  ((== "[New,Write (Ref 0,0) 5,Read (Ref 0,0)]") . (!! 1) . lines)

cheat :: Fork [Untyped MemStep ref] -> Fork [Untyped MemStep ref]
cheat = fmap (map (\ms -> case ms of
                      Untyped (Write ref _) -> Untyped (Write ref 0)
                      _                     -> ms))

prop_shrinkForkSubseq :: Property
prop_shrinkForkSubseq = forAll (liftGenFork gens) $ \f@(Fork l p r) ->
  all (\(Fork l' p' r') -> noRefs l' `isSubsequenceOf` noRefs l &&
                           noRefs p' `isSubsequenceOf` noRefs p &&
                           noRefs r' `isSubsequenceOf` noRefs r)
      (liftShrinkFork shrink1Mono (cheat f))

  where
  noRefs = fmap (const ())

prop_shrinkForkScope :: Property
prop_shrinkForkScope = forAll (liftGenFork gens) $ \f ->
  all (\(Fork l p r) ->
         let p' = zip (repeat 0) p
             l' = zip (repeat 1) l
             r' = zip (repeat 2) r
         in scopeCheck (p' ++ l') &&
            scopeCheck (p' ++ r'))
      (liftShrinkFork shrink1Mono f)

------------------------------------------------------------------------

prop_shrinkForkMinimal :: Property
prop_shrinkForkMinimal = shrinkPropertyHelper (prop_parallel RaceCondition) $ \out ->
  let f = read $ dropWhile isSpace (lines out !! 1)
  in hasMinimalShrink f || f `elem` minimal
  where
  hasMinimalShrink :: Fork [Untyped MemStep (Ref, Int)] -> Bool
  hasMinimalShrink
    = anyRose (`elem` minimal)
    . rose (liftShrinkFork shrink1Mono)
    where
    anyRose :: (a -> Bool) -> Rose a -> Bool
    anyRose p (Rose x xs) = p x || any (anyRose p) xs

    rose :: (a -> [a]) -> a -> Rose a
    rose more = go
      where
      go x = Rose x $ map go $ more x

  minimal :: [Fork [Untyped MemStep (Ref, Int)]]
  minimal  = minimal' ++ map mirrored minimal'
    where
    minimal' = [m0, m1, m2, m3]

    mirrored :: Fork a -> Fork a
    mirrored (Fork l p r) = Fork r p l

    m0 = Fork [Untyped (Write (Ref 0, 0) 0), Untyped (Read (Ref 0, 0))]
              [Untyped New]
              [Untyped (Inc (Ref 0, 0))]

    m1 = Fork [Untyped (Write (Ref 0, 0) 0)]
              [Untyped New]
              [Untyped (Inc (Ref 0, 0)), Untyped (Read (Ref 0, 0))]

    m2 = Fork [Untyped (Inc (Ref 0, 0)), Untyped (Read (Ref 0, 0))]
              [Untyped New]
              [Untyped (Inc (Ref 0, 0))]

    m3 = Fork [Untyped (Inc (Ref 0, 0))]
              [Untyped New]
              [Untyped (Inc (Ref 0, 0)), Untyped (Read (Ref 0, 0))]
