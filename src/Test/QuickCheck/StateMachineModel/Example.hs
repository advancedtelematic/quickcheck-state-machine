{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module Test.QuickCheck.StateMachineModel.Example where

import           Control.Concurrent                      (threadDelay)
import           Control.Monad.State
import           Data.Char
import           Data.Constraint
import           Data.Dynamic
import           Data.IORef
import           Data.Kind
import           Data.List                               hiding ((\\))
import           Data.Map                                (Map)
import qualified Data.Map                                as M
import           Data.Singletons.Prelude                 hiding ((:-), Map)
import           System.Random
import           Test.QuickCheck
import           Test.QuickCheck.Monadic
import           Text.ParserCombinators.ReadP            (string)
import           Text.Read

import           Test.QuickCheck.StateMachineModel
import           Test.QuickCheck.StateMachineModel.Utils

------------------------------------------------------------------------

data MemStep :: Response () -> (TyFun () * -> *) -> * where
  New   ::                       MemStep ('Reference '()) refs
  Read  :: refs @@ '() ->        MemStep ('Response Int)  refs
  Write :: refs @@ '() -> Int -> MemStep ('Response   ()) refs
  Inc   :: refs @@ '() ->        MemStep ('Response   ()) refs
  Copy  :: refs @@ '() ->        MemStep ('Reference '()) refs

deriving instance Eq   (MemStep resp (ConstSym1 IntRef))
deriving instance Show (MemStep resp (ConstSym1 IntRef))

instance IxFunctor (MemStep resp) where
  ifmap _ New           = New
  ifmap f (Read  ref)   = Read  (f STuple0 ref)
  ifmap f (Write ref i) = Write (f STuple0 ref) i
  ifmap f (Inc   ref)   = Inc   (f STuple0 ref)
  ifmap f (Copy  ref)   = Copy  (f STuple0 ref)

------------------------------------------------------------------------

newtype Model refs = Model (Map (refs @@ '()) Int)

initModel :: Model ref
initModel = Model M.empty

type Ords refs = IxForallF Ord refs :- Ord (refs @@ '())

preconditions :: forall refs resp. IxForallF Ord refs => Model refs -> MemStep resp refs -> Bool
preconditions (Model m) cmd = case cmd of
  New         -> True
  Read  ref   -> M.member ref m \\ (iinstF @'() Proxy :: Ords refs)
  Write ref _ -> M.member ref m \\ (iinstF @'() Proxy :: Ords refs)
  Inc   ref   -> M.member ref m \\ (iinstF @'() Proxy :: Ords refs)
  Copy  ref   -> M.member ref m \\ (iinstF @'() Proxy :: Ords refs)

transitions :: forall refs resp. IxForallF Ord refs => Model refs -> MemStep resp refs
  -> Response_ refs resp -> Model refs
transitions (Model m) cmd resp = case cmd of
  New          -> Model (M.insert resp 0 m)              \\ (iinstF @'() Proxy :: Ords refs)
  Read  _      -> Model m                                \\ (iinstF @'() Proxy :: Ords refs)
  Write ref i  -> Model (M.insert ref i m)               \\ (iinstF @'() Proxy :: Ords refs)
  Inc   ref    -> Model (M.insert ref (m M.! ref + 1) m) \\ (iinstF @'() Proxy :: Ords refs)
  Copy  ref    -> Model (M.insert resp (m M.! ref) m)    \\ (iinstF @'() Proxy :: Ords refs)

postconditions :: forall refs resp. IxForallF Ord refs => Model refs -> MemStep resp refs
  -> Response_ refs resp -> Property
postconditions (Model m) cmd resp = case cmd of
  New         -> property $ True
  Read  ref   -> property $ m  M.! ref == resp          \\ (iinstF @'() Proxy :: Ords refs)
  Write ref i -> property $ m' M.! ref == i             \\ (iinstF @'() Proxy :: Ords refs)
  Inc   ref   -> property $ m' M.! ref == m M.! ref + 1 \\ (iinstF @'() Proxy :: Ords refs)
  Copy  ref   -> property $ m' M.! resp == m M.! ref    \\ (iinstF @'() Proxy :: Ords refs)
  where
  Model m' = transitions (Model m) cmd resp

------------------------------------------------------------------------

data Problem = None | Bug | RaceCondition
  deriving Eq

semStep
  :: MonadIO m
  => Problem -> MemStep resp (ConstSym1 (IORef Int))
  -> m (Response_ (ConstSym1 (IORef Int)) resp)
semStep _   New           = liftIO (newIORef 0)
semStep _   (Read  ref)   = liftIO (readIORef  ref)
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
semStep _   (Copy ref)    = do
  old <- liftIO (readIORef ref)
  liftIO (newIORef old)

------------------------------------------------------------------------

gens :: [(Int, Gen (Untyped MemStep (IxRefs ())))]
gens =
  [ (1, return . Untyped $ New)
  , (5, return . Untyped $ Read STuple0)
  , (5, Untyped . Write STuple0 <$> arbitrary)
  , (5, return . Untyped $ Inc STuple0)
  -- , (5, return . Untyped $ Copy STuple0)
  ]

returns :: MemStep resp refs -> SResponse () resp
returns New         = SReference STuple0
returns (Read  _)   = SResponse
returns (Write _ _) = SResponse
returns (Inc   _)   = SResponse
returns (Copy _)    = SReference STuple0

ixfor :: Applicative f => Proxy q -> MemStep resp p
  -> (forall x. Sing x -> p @@ x -> f (q @@ x))
  -> f (MemStep resp q)
ixfor _ New             _ = pure New
ixfor _ (Read  ref)     f = Read  <$> f STuple0 ref
ixfor _ (Write ref val) f = Write <$> f STuple0 ref <*> pure val
ixfor _ (Inc   ref)     f = Inc   <$> f STuple0 ref
ixfor _ (Copy  ref)     f = Copy  <$> f STuple0 ref

------------------------------------------------------------------------

shrink1 :: Untyped' MemStep refs -> [Untyped' MemStep refs ]
shrink1 (Untyped' (Write ref i) iref) = [ Untyped' (Write ref i') iref | i' <- shrink i ]
shrink1 _                               = []

------------------------------------------------------------------------

instance Read (Untyped' MemStep (ConstSym1 IntRef)) where
  readPrec = parens $ choice
    [ Untyped' <$ key "Untyped'" <*> parens (New <$ key " New") <*> readPrec
    , Untyped' <$ key "Untyped'" <*> parens (Read <$ key "Read" <*> readPrec) <*> readPrec
    , Untyped' <$ key "Untyped'" <*> parens (Write <$ key "Write" <*> readPrec <*> readPrec) <*> readPrec
    , Untyped' <$ key "Untyped'" <*> parens (Inc <$ key "Inc" <*> readPrec) <*> readPrec
    ]
    where
      key s = Text.Read.lift (string s)

  readListPrec = readListPrecDefault

instance IxFunctor1 MemStep where
  ifmap1 _ New           = New
  ifmap1 f (Read  ref)   = Read  (f STuple0 ref)
  ifmap1 f (Write ref i) = Write (f STuple0 ref) i
  ifmap1 f (Inc   ref)   = Inc   (f STuple0 ref)
  ifmap1 f (Copy  ref)   = Copy  (f STuple0 ref)

instance IxFoldable (Untyped' MemStep) where
  ifoldMap _ (Untyped' New           _) = mempty
  ifoldMap f (Untyped' (Read  ref)   _) = f STuple0 ref
  ifoldMap f (Untyped' (Write ref _) _) = f STuple0 ref
  ifoldMap f (Untyped' (Inc   ref)   _) = f STuple0 ref
  ifoldMap f (Untyped' (Copy  ref)   _) = f STuple0 ref

instance Show a => Show (Untyped MemStep (ConstSym1 a)) where
  show (Untyped New          ) =  "New"
  show (Untyped (Read  ref)  ) =  "Read ("  ++ show ref ++ ")"
  show (Untyped (Write ref i)) =  "Write (" ++ show ref ++ ") " ++ show i
  show (Untyped (Inc   ref)  ) =  "Inc ("   ++ show ref ++ ")"
  show (Untyped (Copy  ref)  ) =  "Copy ("   ++ show ref ++ ")"

instance Show a => Show (Untyped' MemStep (ConstSym1 a)) where
  show (Untyped' New           miref) = "Untyped' New (" ++ show miref ++ ")"
  show (Untyped' (Read  ref)   miref) =
    "Untyped' (Read ("  ++ show ref ++ ")) " ++ show miref
  show (Untyped' (Write ref i) miref) =
    "Untyped' (Write (" ++ show ref ++ ") (" ++ show i ++ ")) " ++ show miref
  show (Untyped' (Inc   ref)   miref) =
    "Untyped' (Inc ("   ++ show ref ++ ")) "  ++ show miref
  show (Untyped' (Copy  ref)   miref) =
    "Untyped' (Copy ("   ++ show ref ++ ")) (" ++ show miref ++ ")"

instance ShowCmd MemStep (ConstSym1 IntRef) where
  showCmd New           =  "New"
  showCmd (Read  ref)   =  "Read ("  ++ show ref ++ ")"
  showCmd (Write ref i) =  "Write (" ++ show ref ++ ") " ++ show i
  showCmd (Inc   ref)   =  "Inc ("   ++ show ref ++ ")"
  showCmd (Copy  ref)   =  "Copy ("   ++ show ref ++ ")"

instance Eq (Untyped' MemStep (ConstSym1 IntRef)) where
  Untyped' c1 _ == Untyped' c2 _ = Just c1 == cast c2

instance Ord (Untyped' MemStep (ConstSym1 IntRef)) where
  Untyped' c1 _ <= Untyped' c2 _ = Just c1 <= cast c2

data RawMemStep refs
  = NewR
  | ReadR  (refs @@ '())
  | WriteR (refs @@ '()) Int
  | IncR   (refs @@ '())
  | CopyR  (refs @@ '())

deriving instance Eq  (RawMemStep (ConstSym1 IntRef))
deriving instance Ord (RawMemStep (ConstSym1 IntRef))

raw :: MemStep resp refs -> RawMemStep refs
raw New           = NewR
raw (Read  ref)   = ReadR  ref
raw (Write ref i) = WriteR ref i
raw (Inc   ref)   = IncR   ref
raw (Copy  ref)   = CopyR  ref

instance Ord (MemStep resp (ConstSym1 IntRef)) where
  c1 <= c2 = raw c1 <= raw c2

instance IxForallF Show p => Show (Model p) where
  show (Model m) = show m \\ (iinstF @'() Proxy :: IxForallF Show p :- Show (p @@ '()))

------------------------------------------------------------------------

smm :: StateMachineModel Model MemStep
smm = StateMachineModel preconditions postconditions transitions initModel

prop_safety :: Problem -> Property
prop_safety prb = sequentialProperty
  smm
  gens
  shrink1
  returns
  (semStep prb)
  ixfor
  ioProperty

prop_parallel :: Problem -> Property
prop_parallel prb = parallelProperty
  smm
  gens
  shrink1
  returns
  (semStep prb)
  ixfor

------------------------------------------------------------------------

usesRefs :: MemStep resp refs -> [Ex refs]
usesRefs New           = []
usesRefs (Read  ref)   = [Ex STuple0 ref]
usesRefs (Write ref _) = [Ex STuple0 ref]
usesRefs (Inc   ref)   = [Ex STuple0 ref]
usesRefs (Copy  ref)   = [Ex STuple0 ref]

scopeCheck
  :: forall
     (ix   :: *)
     (cmd  :: Response ix -> (TyFun ix * -> *) -> *)
  .  (forall resp. cmd resp (ConstSym1 IntRef) -> SResponse ix resp)
  -> (forall resp. cmd resp (ConstSym1 IntRef) -> [Ex (ConstSym1 IntRef)])
  -> [(Pid, Untyped' cmd (ConstSym1 IntRef))]
  -> Bool
scopeCheck returns' uses' = go []
  where
  go :: [IntRef] -> [(Pid, Untyped' cmd (ConstSym1 IntRef))] -> Bool
  go _    []                           = True
  go refs ((_, Untyped' c miref) : cs) = case returns' c of
    SReference _  ->
      let refs' = miref : refs in
      all (\(Ex _ ref) -> ref `elem` refs) (uses' c) &&
      go refs' cs
    SResponse     ->
      all (\(Ex _ ref) -> ref `elem` refs) (uses' c) &&
      go refs cs

scopeCheckFork'
  :: forall
     (ix   :: *)
     (cmd  :: Response ix -> (TyFun ix * -> *) -> *)
  .  (forall resp. cmd resp (ConstSym1 IntRef) -> SResponse ix resp)
  -> (forall resp. cmd resp (ConstSym1 IntRef) -> [Ex (ConstSym1 IntRef)])
  -> Fork [Untyped' cmd (ConstSym1 IntRef)] -> Bool
scopeCheckFork' returns' uses' (Fork l p r) =
  let p' = zip (repeat 0) p in
  scopeCheck returns' uses' (p' ++ zip (repeat 1) l) &&
  scopeCheck returns' uses' (p' ++ zip (repeat 2) r)

scopeCheckFork :: Fork [Untyped' MemStep (ConstSym1 IntRef)] -> Bool
scopeCheckFork = scopeCheckFork' returns usesRefs

prop_genScope :: Property
prop_genScope = forAll (fst <$> liftGen gens (Pid 0) M.empty returns ixfor) $ \p ->
  let p' = zip (repeat 0) p in
  scopeCheck returns usesRefs p'

prop_genForkScope :: Property
prop_genForkScope = forAll
  (liftGenFork gens returns ixfor)
  scopeCheckFork

shrinkPropertyHelper :: Property -> (String -> Bool) -> Property
shrinkPropertyHelper prop p = monadicIO $ do
  result <- run $ quickCheckWithResult (stdArgs {chatty = False}) prop
  case result of
    Failure { output = outputLines } -> liftProperty $
      counterexample ("failed: " ++ outputLines) $ p outputLines
    _                                -> return ()

prop_sequentialShrink :: Property
prop_sequentialShrink = shrinkPropertyHelper (prop_safety Bug) $ alphaEq returns ixfor
  [ Untyped' New    (IntRef (Ref 0) (Pid 0))
  , Untyped' (Write (IntRef (Ref 0) (Pid 0)) (5)) ()
  , Untyped' (Read  (IntRef (Ref 0) (Pid 0))) ()
  ]
  . read . (!! 1) . lines

cheat :: Fork [Untyped' MemStep (ConstSym1 refs)] -> Fork [Untyped' MemStep (ConstSym1 refs)]
cheat = fmap (map (\ms -> case ms of
  Untyped' (Write ref _) () -> Untyped' (Write ref 0) ()
  _                         -> ms))

prop_shrinkForkSubseq :: Property
prop_shrinkForkSubseq = forAll (liftGenFork gens returns ixfor) $ \f@(Fork l p r) ->
  all (\(Fork l' p' r') -> noRefs l' `isSubsequenceOf` noRefs l &&
                           noRefs p' `isSubsequenceOf` noRefs p &&
                           noRefs r' `isSubsequenceOf` noRefs r)
      (liftShrinkFork returns shrink1 (cheat f))

  where
  noRefs = fmap (const ())

prop_shrinkForkScope :: Property
prop_shrinkForkScope = forAll (liftGenFork gens returns ixfor) $ \f ->
  all scopeCheckFork (liftShrinkFork returns shrink1 f)

debugShrinkFork :: Fork [Untyped' MemStep (ConstSym1 IntRef)]
  -> [Fork [Untyped' MemStep (ConstSym1 IntRef)]]
debugShrinkFork = take 1 . map snd . dropWhile fst . map (\f -> (scopeCheckFork f, f))
  . liftShrinkFork returns shrink1

------------------------------------------------------------------------

prop_shrinkForkMinimal :: Property
prop_shrinkForkMinimal = shrinkPropertyHelper (prop_parallel RaceCondition) $ \out ->
  let f = read $ dropWhile isSpace (lines out !! 1)
  in hasMinimalShrink f ||  isMinimal f
  where
  hasMinimalShrink :: Fork [Untyped' MemStep (ConstSym1 IntRef)] -> Bool
  hasMinimalShrink
    = anyRose isMinimal
    . rose (liftShrinkFork returns shrink1)
    where
    anyRose :: (a -> Bool) -> Rose a -> Bool
    anyRose p (Rose x xs) = p x || any (anyRose p) xs

    rose :: (a -> [a]) -> a -> Rose a
    rose more = go
      where
      go x = Rose x $ map go $ more x

  isMinimal :: Fork [Untyped' MemStep (ConstSym1 IntRef)] -> Bool
  isMinimal xs = any (alphaEqFork returns ixfor xs) minimal

  minimal :: [Fork [Untyped' MemStep (ConstSym1 IntRef)]]
  minimal  = minimal' ++ map mirrored minimal'
    where
    minimal' = [ Fork [w0, Untyped' (Read var) ()]
                      [Untyped' New var]
                      [w1]
               | w0 <- writes
               , w1 <- writes
               ]

    mirrored :: Fork a -> Fork a
    mirrored (Fork l p r) = Fork r p l

    var = IntRef 0 0
    writes = [Untyped' (Write var 0) (), Untyped' (Inc var) ()]
