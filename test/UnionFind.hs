{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE PolyKinds          #-}
{-# LANGUAGE StandaloneDeriving #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  UnionFind
-- Copyright   :  (C) 2017-2019, ATS Advanced Telematic Systems GmbH
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Stevan Andjelkovic <stevan.andjelkovic@here.com>,
--                Momoko Hattori <momohatt10@gmail.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- This module contains a specification for an imperative-style union/find
-- algorithm.
--
-----------------------------------------------------------------------------

module UnionFind
  ( prop_unionFindSequential
  )
  where

import           Data.Functor.Classes
                   (Eq1(..))
import           Data.IORef
                   (IORef, newIORef, readIORef, writeIORef)
import           Data.TreeDiff
                   (ToExpr)
import           GHC.Generics
                   (Generic, Generic1)
import           Prelude
import           Test.QuickCheck
                   (Gen, Property, arbitrary, elements, frequency,
                   shrink, (===))
import           Test.QuickCheck.Monadic
                   (monadicIO)

import           Test.StateMachine
import qualified Test.StateMachine.Types.Rank2      as Rank2
import           Test.StateMachine.Types.References
import           Test.StateMachine.Z
                   (domain, empty)

------------------------------------------------------------------------

-- The union/find algorithm is basically an efficient way of
-- implementing an equivalence relation.
--
-- This example is borrowed from the paper
-- <http://www.cse.chalmers.se/~rjmh/Papers/QuickCheckST.ps *Testing
-- monadic code with QuickCheck*> by Koen Claessen and John Hughes
-- (2002).
--
-- Let's start with the implementation of the algorithm, which we have
-- taken from the paper.

-- Our implementation is slightly different in that we use @IORef@s
-- instead of @STRef@s (see issue #84).
data Element = Element Int (IORef Link)

data Link
  = Weight Int
  | Next Element

instance Eq Element where
  Element _ ref1 == Element _ ref2 = ref1 == ref2

instance Show Element where
  show (Element x _) = "Element " ++ show x

type Ref r = Reference (Opaque Element) r

-- We represent actions in the same way as they do in section 11 of the
-- paper.
data Command r
  = New Int
  | Find (Ref r)
  | Union (Ref r) (Ref r)
  deriving (Eq, Show, Generic1, Rank2.Functor, Rank2.Foldable, Rank2.Traversable, CommandNames)

data Response r
  = -- | New element was created.
    Created (Ref r)
    -- | Command 'Find' was successful with a return value.
  | Found (Ref r)
    -- | Command 'Union' was successful.
  | United
  deriving (Generic1, Rank2.Foldable)

deriving instance Show (Response Symbolic)
deriving instance Show (Response Concrete)

------------------------------------------------------------------------

-- The model corresponds closely to the *relational specification* given
-- in section 12 of the paper.

newtype Model r = Model [(Ref r, Ref r)]
    deriving (Generic, Eq, Show)

instance ToExpr (Model Symbolic)
instance ToExpr (Model Concrete)

initModel :: Model r
initModel = Model empty

-- Find representative of 'ref'
(!) :: Eq1 r => Model r -> Ref r -> Ref r
Model m ! ref = case lookup ref m of
  Just ref' | ref == ref' -> ref
            | otherwise   -> Model m ! ref'
  Nothing                 -> error "(!): couldn't find key"

extend :: Eq1 r => Model r -> (Ref r, Ref r) -> Model r
extend (Model m) p@(ref1, ref2) =
    case lookup ref1 m of
      Just z -> -- case of 'Union' command
          let w = Model m ! ref2 in
          Model $ map (\(x, y) -> if y == z then (x, w) else (x, y)) m
      Nothing -> -- case of 'New' command
          Model $ p : m

------------------------------------------------------------------------

precondition :: Model Symbolic -> Command Symbolic -> Logic
precondition m@(Model model) cmd = case cmd of
  New _           -> Top
  Find ref        -> ref   `member` map fst model
  Union ref1 ref2 -> (ref1 `member` map fst model) .&&
                     (ref2 `member` map fst model) .&&
                     (m ! ref1 ./= m ! ref2)

transition :: Eq1 r => Model r -> Command r -> Response r -> Model r
transition m cmd resp = case (cmd, resp) of
  (New _,           Created ref) -> m `extend` (ref, ref)
  (Find _,          Found _)     ->
      -- The equivalence relation should be the same after 'find' command.
      m
  (Union ref1 ref2, United)      ->
      -- Update the model with a new equivalence relation between ref1 and ref2.
      -- It doesn't matter whether ref1's root is pointed to ref2's root or vice versa.
      m `extend` (ref1, ref2)
  _                              -> error "transition: impossible."

postcondition :: Model Concrete -> Command Concrete -> Response Concrete -> Logic
postcondition m cmd resp = case (cmd, resp) of
  (New _,           Created ref) -> m' ! ref .== ref
  (Find _,          Found _)     -> m .== m'
  (Union ref1 ref2, United)      ->
    let z = m' ! ref1
     in (z .== m ! ref1 .|| z .== m ! ref2) .&& m' ! ref1 .== m' ! ref2
  _                              -> Bot
  where
    m' = transition m cmd resp

------------------------------------------------------------------------

newElement :: Int -> IO Element
newElement x = do
  ref <- newIORef (Weight 1)
  return (Element x ref)

findElement :: Element -> IO Element
findElement (Element x ref) = do
  e <- readIORef ref
  case e of
    Weight _  -> return (Element x ref)
    Next next -> do
      last' <- findElement next
      writeIORef ref (Next last')
      return last'

unionElements :: Element -> Element -> IO ()
unionElements e1 e2 = do
  Element x1 ref1 <- findElement e1
  Element x2 ref2 <- findElement e2
  if ref1 == ref2
     then error "equivalent elements"
     else do
       Weight w1 <- readIORef ref1
       Weight w2 <- readIORef ref2

       if w1 <= w2
       then do
         writeIORef ref1 (Next (Element x2 ref2))
         writeIORef ref2 (Weight (w1 + w2))
       else do
         writeIORef ref2 (Next (Element x1 ref1))
         writeIORef ref1 (Weight (w1 + w2))

semantics :: Command Concrete -> IO (Response Concrete)
semantics (New x)           = Created . Reference . Concrete . Opaque <$> newElement x
semantics (Find ref)        = Found   . Reference . Concrete . Opaque <$> findElement (opaque ref)
semantics (Union ref1 ref2) = United <$ unionElements (opaque ref1) (opaque ref2)

mock :: Model Symbolic -> Command Symbolic -> GenSym (Response Symbolic)
mock _ cmd = case cmd of
  New _     -> Created <$> genSym
  Find _    -> Found <$> genSym
  Union _ _ -> pure United

generator :: Model Symbolic -> Maybe (Gen (Command Symbolic))
generator (Model m)
  | null m    = Just $ New <$> arbitrary
  | otherwise = Just $ frequency
    [ (1, New <$> arbitrary)
    , (8, Find <$> elements (domain m))
    , (8, Union <$> elements (domain m) <*> elements (domain m))
    ]

shrinker :: Model Symbolic -> Command Symbolic -> [Command Symbolic]
shrinker _ (New n) = [ New n' | n' <- shrink n ]
shrinker _ _       = []

sm :: StateMachine Model Command IO Response
sm = StateMachine initModel transition precondition postcondition
         Nothing generator shrinker semantics mock

prop_unionFindSequential :: Property
prop_unionFindSequential =
  forAllCommands sm Nothing $ \cmds -> monadicIO $ do
    (hist, _model, res) <- runCommands sm cmds
    prettyCommands sm hist (checkCommandNames cmds (res === Ok))
