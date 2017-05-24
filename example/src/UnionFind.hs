{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE ExplicitNamespaces    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module UnionFind where

import           Control.Monad.State
                   (StateT, evalStateT, get, lift, liftIO, modify)
import           Data.IORef
                   (IORef, newIORef, readIORef, writeIORef)
import           Data.Singletons.Prelude
                   (ConstSym1)
import           Test.QuickCheck
                   (Gen, Property, arbitrary, choose, frequency,
                   ioProperty, property, shrink)

import           Test.StateMachine
import           Test.StateMachine.Types

------------------------------------------------------------------------

type Ref = Int

data Action :: Signature () where
  New   :: Int        -> Action refs ('Response (Element Int))
  Find  :: Ref        -> Action refs ('Response (Element Int))
  Union :: Ref -> Ref -> Action refs ('Response (Element Int))

------------------------------------------------------------------------

newtype Model refs = Model [Element Int]

initModel :: Model refs
initModel = Model []

------------------------------------------------------------------------

preconditions
  :: forall refs resp. IxForallF Ord refs
  => Model refs -> Action refs resp -> Bool
preconditions (Model m) cmd = case cmd of
  New   _         -> True
  Find  ref       -> ref  < length m
  Union ref1 ref2 -> ref1 < length m && ref2 < length m

transitions
  :: forall refs resp. IxForallF Ord refs
  => Model refs -> Action refs resp -> Response_ refs resp -> Model refs
transitions (Model m) cmd resp = case cmd of
  New   _         -> Model (m ++ [resp])
  Find  _         -> Model m
  Union ref1 ref2 ->
    let z  = resp -- which will be the same as `m' !! ref1`.
        m' = [ if z' == m !! ref1 || z' == m !! ref2
               then z else z'
             | z' <- m
             ]
    in Model m'

postconditions
  :: forall refs resp. IxForallF Ord refs
  => Model refs -> Action refs resp -> Response_ refs resp -> Property
postconditions (Model m) cmd resp = case cmd of
  New   _         -> property True
  Find  ref       -> property (resp == m !! ref)
  Union ref1 ref2 ->
    let z = m' !! ref1
    in property $ (z == m !! ref1 || z == m !! ref2) && z == m' !! ref2
  where
  Model m' = transitions (Model m) cmd resp

smm :: StateMachineModel Model Action
smm = StateMachineModel preconditions postconditions transitions initModel

------------------------------------------------------------------------

gen :: StateT Int Gen (Untyped Action (RefPlaceholder ()))
gen = do
  n <- get
  if n == 0
  then do
    modify succ
    lift $ Untyped . New <$> arbitrary
  else do
    cmd <- lift $ frequency
      [ (1, Untyped . New  <$> arbitrary)
      , (5, Untyped . Find <$> choose (0, n - 1))
      , (5, Untyped <$> (Union <$> choose (0, n - 1) <*> choose (0, n - 1)))
      ]
    case cmd of
      Untyped (New _) -> modify succ
      _               -> return ()
    return cmd

shrink1 :: Action refs resp -> [Action refs resp]
shrink1 (New x) = [ New x' | x' <- shrink x ]
shrink1 _       = []

------------------------------------------------------------------------

data Element a = Element a (IORef (Link a))

data Link a
  = Weight Int
  | Next (Element a)

newElement :: a -> IO (Element a)
newElement x = do
  ref <- newIORef (Weight 1)
  return (Element x ref)

findElement :: Element a -> IO (Element a)
findElement (Element x ref) = do
  e <- readIORef ref
  case e of
    Weight _  -> return (Element x ref)
    Next next -> do
      last' <- findElement next
      writeIORef ref (Next last')
      return last'

unionElements :: Element a -> Element a -> IO (Element a)
unionElements e1 e2 = do

  Element x1 ref1 <- findElement e1
  Element x2 ref2 <- findElement e2
  Weight w1       <- readIORef ref1
  Weight w2       <- readIORef ref2

  if w1 <= w2
  then do
    writeIORef ref1 (Next (Element x2 ref2))
    writeIORef ref2 (Weight (w1 + w2))
    return (Element x2 ref2)
  else do
    writeIORef ref2 (Next (Element x1 ref1))
    writeIORef ref1 (Weight (w1 + w2))
    return (Element x1 ref1)

instance Eq (Element a) where
  Element _ ref1 == Element _ ref2 = ref1 == ref2

instance Show a => Show (Element a) where
  show (Element x _) = "Element " ++ show x

------------------------------------------------------------------------

semantics
  :: Action (ConstSym1 (Element Int)) resp
  -> StateT [Element Int] IO (Response_ (ConstSym1 (Element Int)) resp)
semantics (New   x)     = do
  e <- liftIO (newElement x)
  modify (++ [e])
  return e
semantics (Find  r)     = do
  env <- get
  liftIO (findElement (env !! r))
semantics (Union r1 r2) = do
  env <- get
  liftIO (unionElements (env !! r1) (env !! r2))

------------------------------------------------------------------------

instance HasResponse Action where
  response New   {} = SResponse
  response Find  {} = SResponse
  response Union {} = SResponse

instance IxFunctor Action where
  ifmap _ (New   x)         = New   x
  ifmap _ (Find  ref)       = Find  ref
  ifmap _ (Union ref1 ref2) = Union ref1 ref2

instance IxFoldable Action where
  ifoldMap _ (New   _)   = mempty
  ifoldMap _ (Find  _)   = mempty
  ifoldMap _ (Union _ _) = mempty

instance IxTraversable Action where
  ifor _ (New   x)         _ = pure (New x)
  ifor _ (Find  ref)       _ = pure (Find  ref)
  ifor _ (Union ref1 ref2) _ = pure (Union ref1 ref2)

instance ShowCmd Action where
  showCmd (New   x)         = "New "    ++ show x
  showCmd (Find  ref)       = "Find ("  ++ show ref ++ ")"
  showCmd (Union ref1 ref2) = "Union (" ++ show ref1 ++ ") (" ++ show ref2 ++ ")"

------------------------------------------------------------------------

prop_sequential :: Property
prop_sequential = sequentialProperty'
  smm
  gen
  0
  shrink1
  semantics
  (ioProperty . flip evalStateT [])
