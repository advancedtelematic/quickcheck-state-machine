{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE PolyKinds          #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  CircularBuffer
-- Copyright   :  (C) 2017, Xia Li-yao
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Xia Li-yao
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains a specification of a circular buffer. Adapted
-- from John Hughes' /Experiences with QuickCheck: Testing the hard
-- stuff and staying sane/.
--
------------------------------------------------------------------------

module CircularBuffer
  ( unpropNoSizeCheck
  , unpropFullIsEmpty
  , unpropBadRem
  , unpropStillBadRem
  , prop_circularBuffer
  )
  where

import           Control.Applicative
                   (liftA2)
import           Control.Monad
                   (guard)
import           Data.Function
                   (on)
import           Data.Functor.Classes
                   (Eq1)
import           Data.IORef
                   (IORef, newIORef, readIORef, writeIORef)
import           Data.Kind
                   (Type)
import           Data.Maybe
                   (isJust)
import           Data.Vector.Unboxed.Mutable
                   (IOVector)
import qualified Data.Vector.Unboxed.Mutable   as V
import           GHC.Generics
                   (Generic, Generic1)
import           Prelude
import           Test.QuickCheck
                   (Gen, Positive(..), Property, arbitrary, elements,
                   frequency, shrink, (===))
import           Test.QuickCheck.Monadic
                   (monadicIO)

import           Test.StateMachine
import qualified Test.StateMachine.Types.Rank2 as Rank2

------------------------------------------------------------------------

-- | Sets of bugs in the implementation and specification.
type Bugs = [Bug]

-- | Possible bugs.
--
-- See 'unpropNoSizeCheck', 'unpropFullIsEmpty', 'unpropBadRem',
-- and 'unpropStillBadRem'.
data Bug = NoSizeCheck | FullIsEmpty | BadRem | StillBadRem
  deriving (Eq, Enum)

-- | Switch to disable or enable testing of the 'lenBuffer' function.
data Version = NoLen | YesLen
  deriving Eq

------------------------------------------------------------------------

-- | An efficient mutable circular buffer.
data Buffer = Buffer
  { top :: IORef Int     -- ^ Index to the top: where to 'Put' the next element
  , bot :: IORef Int     -- ^ Index to the bottom: where to 'Get' the next element
  , arr :: IOVector Int  -- ^ Array of elements of fixed capacity
  }

-- | Different buffers are assumed to have disjoint memories,
-- so we can use 'V.overlaps' to check equality.
instance Eq Buffer where
  (==) =
    ((==) `on` top) `also`
    ((==) `on` bot) `also`
    (V.overlaps `on` arr)
    where
      also = (liftA2 . liftA2) (&&)

-- | See 'New'.
newBuffer :: Bugs -> Int -> IO Buffer
newBuffer bugs n = Buffer
  <$> newIORef 0
  <*> newIORef 0
  <*> V.new (if FullIsEmpty `elem` bugs then n else n + 1)

-- | See 'Put'.
putBuffer :: Int -> Buffer -> IO ()
putBuffer x Buffer{top, arr} = do
  i <- readIORef top
  V.write arr i x
  writeIORef top $! (i + 1) `mod` V.length arr

-- | See 'Get'.
getBuffer :: Buffer -> IO Int
getBuffer Buffer{bot, arr} = do
  j <- readIORef bot
  y <- V.read arr j
  writeIORef bot $! (j + 1) `mod` V.length arr
  return y

-- | See 'Len'.
lenBuffer :: Bugs -> Buffer -> IO Int
lenBuffer bugs Buffer{top, bot, arr} = do
  i <- readIORef top
  j <- readIORef bot
  return $
    if BadRem `elem` bugs then
      (i - j) `rem` V.length arr
    else if StillBadRem `elem` bugs then
      abs ((i - j) `rem` V.length arr)
    else
      (i - j) `mod` V.length arr

------------------------------------------------------------------------

-- | Buffer actions.
data Action (r :: Type -> Type)
    -- | Create a new buffer of bounded capacity.
  = New Int

    -- | Put an element at the top of the buffer.
  | Put Int (Reference (Opaque Buffer) r)

    -- | Get an element out of the bottom of the buffer.
  | Get (Reference (Opaque Buffer) r)

    -- | Get the number of elements in the buffer.
  | Len (Reference (Opaque Buffer) r)
  deriving (Show, Generic1, Rank2.Functor, Rank2.Foldable, Rank2.Traversable, CommandNames)

data Response (r :: Type -> Type)
  = NewR (Reference (Opaque Buffer) r)
  | PutR
  | GetR Int
  | LenR Int
  deriving (Show, Generic1, Rank2.Foldable)

------------------------------------------------------------------------

-- | A simple, persistent, inefficient buffer.
--
-- The top of the buffer is the head of the list, the bottom is the last
-- element.
data SpecBuffer = SpecBuffer
  { specSize     :: Int    -- ^ Maximum number of elements
  , specContents :: [Int]  -- ^ Contents of the buffer
  }
  deriving (Generic, Show, ToExpr)

emptySpecBuffer :: Int -> SpecBuffer
emptySpecBuffer n = SpecBuffer n []

insertSpecBuffer :: Int -> SpecBuffer -> SpecBuffer
insertSpecBuffer x (SpecBuffer n xs) = SpecBuffer n (x : xs)

removeSpecBuffer :: SpecBuffer -> (Int, SpecBuffer)
removeSpecBuffer (SpecBuffer n xs) = (last xs, SpecBuffer n (init xs))

------------------------------------------------------------------------

-- | The model is a map from buffer references to their values.
newtype Model r = Model [(Reference (Opaque Buffer) r, SpecBuffer)]
  deriving (Generic, Show)

deriving instance ToExpr (Model Concrete)

-- | Initially, there are no references to buffers.
initModel :: Model v
initModel = Model []

precondition :: Bugs -> Model Symbolic -> Action Symbolic -> Logic
precondition _    _         (New n) = n .> 0
precondition bugs (Model m) (Put _ buffer) | NoSizeCheck `elem` bugs =
  buffer `member` map fst m
precondition _    (Model m) (Put _ buffer) = Boolean $ isJust $ do
  specBuffer <- lookup buffer m
  guard $ length (specContents specBuffer) < specSize specBuffer
precondition _    (Model m) (Get buffer) = Boolean $ isJust $ do
  specBuffer <- lookup buffer m
  guard $ not (null (specContents specBuffer))
precondition _    (Model m) (Len buffer) = buffer `member` map fst m

transition :: Eq1 r => Model r -> Action r -> Response r -> Model r
transition (Model m) (New n)        (NewR ref) =
  Model ((ref, emptySpecBuffer n) : m)
transition (Model m) (Put x buffer) _          =
  case lookup buffer m of
    Just old -> Model (update buffer (insertSpecBuffer x old) m)
    Nothing  -> error "transition: put"
transition (Model m) (Get buffer) _ =
  case lookup buffer m of
    Just old ->
      let (_, new) = removeSpecBuffer old in
      Model (update buffer new m)
    Nothing  -> error "transition: get"
transition m    _ _ = m

update :: Eq a => a -> b -> [(a, b)] -> [(a, b)]
update ref i m = (ref, i) : filter ((/= ref) . fst) m

postcondition :: Model Concrete -> Action Concrete -> Response Concrete -> Logic
postcondition _         (New _)      _        = Top
postcondition _         (Put _ _)    _        = Top
postcondition (Model m) (Get buffer) (GetR y) = case lookup buffer m of
  Nothing         -> Bot
  Just specBuffer ->
    let (y', _) = removeSpecBuffer specBuffer
    in y .== y'
postcondition (Model m) (Len buffer) (LenR k) = case lookup buffer m of
  Nothing         -> Bot
  Just specBuffer -> k .== length (specContents specBuffer)
postcondition _         _            _        = error "postcondition"

------------------------------------------------------------------------

genNew :: Gen (Action Symbolic)
genNew = do
  Positive n <- arbitrary
  return (New n)

generator :: Version -> Model Symbolic -> Maybe (Gen (Action Symbolic))
generator _       (Model m) | null m = Just $ genNew
generator version (Model m)          = Just $ frequency $
  [ (1, genNew)
  , (4, Put <$> arbitrary <*> (fst <$> elements m))
  , (4, Get <$> (fst <$> elements m))
  ] ++
  [ (4, Len <$> (fst <$> elements m)) | version == YesLen ]

shrinker :: Model Symbolic -> Action Symbolic -> [Action Symbolic]
shrinker _ (New n)        = [ New n'        | n' <- shrink n ]
shrinker _ (Put x buffer) = [ Put x' buffer | x' <- shrink x ]
shrinker _ _              = []

------------------------------------------------------------------------

semantics :: Bugs -> Action Concrete -> IO (Response Concrete)
semantics bugs (New n)        = NewR . reference . Opaque <$> newBuffer bugs n
semantics _    (Put x buffer) = PutR <$  putBuffer x (opaque buffer)
semantics _    (Get buffer)   = GetR <$> getBuffer (opaque buffer)
semantics bugs (Len buffer)   = LenR <$> lenBuffer bugs (opaque buffer)

mock :: Model Symbolic -> Action Symbolic -> GenSym (Response Symbolic)
mock _         (New _)      = NewR <$> genSym
mock _         (Put _ _)    = pure PutR
mock (Model m) (Get buffer) = case lookup buffer m of
  Nothing   -> error "mock: get"
  Just spec -> case specContents spec of
    []      -> error "mock: get 2"
    (i : _) -> pure (GetR i)
mock (Model m) (Len buffer) = case lookup buffer m of
  Nothing   -> error "mock: len"
  Just spec -> pure (LenR (specSize spec))

------------------------------------------------------------------------

sm :: Version -> Bugs -> StateMachine Model Action IO Response
sm version bugs = StateMachine
  initModel transition (precondition bugs) postcondition
  Nothing (generator version) shrinker (semantics bugs) mock

-- | Property parameterized by spec version and bugs.
prepropcircularBuffer :: Version -> Bugs -> Property
prepropcircularBuffer version bugs =
  forAllCommands sm' Nothing $ \cmds -> monadicIO $ do
    (hist, _, res) <- runCommands sm' cmds
    prettyCommands sm' hist $
      checkCommandNames cmds (res === Ok)
  where
    sm' = sm version bugs

-- Adapted from John Hughes'
-- /Experiences with QuickCheck: Testing the hard stuff and staying sane/,

-- | The first bug. 'NoSizeCheck'
--
-- Putting more elements than the capacity of the buffer (set when it is
-- constructed using 'New') causes a buffer overflow: new elements overwrite
-- older ones that haven't been removed yet.
-- A minimal counterexample that reveals the bug is simply:
--
-- > buffer <- newBuffer 1
-- > putBuffer 0 buffer
-- > putBuffer 1 buffer
-- > getBuffer buffer
-- >
-- > -- Expected: 0
-- > -- Actual:   1
--
-- The mistake is in the specification: it models an unbounded buffer.
-- For a bounded buffer, that sequence of calls makes no sense.
-- The fix is to add a precondition to forbid 'Put' when the buffer is full.

unpropNoSizeCheck :: Property
unpropNoSizeCheck = prepropcircularBuffer NoLen  [NoSizeCheck ..]

-- | The second bug. 'FullIsEmpty'
--
-- The top and bottom pointers wrap around when they reach the end of the
-- array. We have that @top == bottom@ whenever the buffer is either empty or
-- full.
-- In other words, a full buffer is undistinguishable from an empty one.
-- A minimal counterexample:
--
-- > buffer <- newBuffer 1
-- > putBuffer 0 buffer
-- > lenBuffer buffer
-- >
-- > -- Expected: 1
-- > -- Actual:   0
--
-- In this implementation, the length of a buffer is given by the remainder of
-- a division by its capacity. When the capacity is one, that remainder is
-- always 0.
-- The fix is to allocate one more cell when we allocate a 'New' buffer.
--
-- In a way, the bug is still there. But to observe it, one has to
-- 'Put' one more element than the buffer capacity. Since this violates the
-- specification, it's the user's fault!

unpropFullIsEmpty :: Property
unpropFullIsEmpty = prepropcircularBuffer YesLen [FullIsEmpty ..]

-- | The third bug. 'BadRem'
--
-- The length of a buffer uses 'rem', which is the remainder of a
-- division truncated towards zero (the standard division in many languages,
-- such as C, but not Haskell). When the dividend @(top - bottom)@ is negative,
-- the remainder is non-positive.
-- A minimal counterexample:
--
-- > buffer <- newBuffer 1
-- > putBuffer 0 buffer
-- > getBuffer buffer
-- > putBuffer 0 buffer
-- > lenBuffer buffer
-- >
-- > -- Expected:  1
-- > -- Actual:   -1
--
-- The fix is to ensure the remainder is non-negative...

unpropBadRem :: Property
unpropBadRem = prepropcircularBuffer YesLen [BadRem ..]

-- | The fourth bug. 'StillBadRem'
--
-- ... One way to obtain a non-negative remainder is to make the dividend
-- non-negative. /Clearly/ we should divide by the absolute value instead.
-- QuickCheck provides a minimal counterexample to that "obvious" fix:
--
-- > buffer <- newBuffer 2
-- > putBuffer 0 buffer
-- > getBuffer buffer
-- > putBuffer 0 buffer
-- > putBuffer 0 buffer
-- > lenBuffer len
-- >
-- > -- Expected: 2
-- > -- Actual:   1
--
-- As an aside, for the first time, the buffer /needs/ to be of capacity two.
-- That non-fix fixed buffers of capacity one!
--
-- The actual fix is to use 'mod',
-- which performs division rounding towards -∞.

unpropStillBadRem :: Property
unpropStillBadRem = prepropcircularBuffer YesLen [StillBadRem]

-- | And now tests pass.

prop_circularBuffer :: Property
prop_circularBuffer = prepropcircularBuffer YesLen []
