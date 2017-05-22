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

import           Data.IORef
import           Data.Map
                   (Map)
import qualified Data.Map                as M
import           Data.Singletons.Prelude
                   (type (@@), ConstSym1, Proxy(..), Sing(STuple0))
import           Test.QuickCheck
                   (Gen, Property, choose, frequency, ioProperty,
                   property, shrink, (.&&.), (==>))

import           Test.StateMachine
import           Test.StateMachine.Types

------------------------------------------------------------------------

data Action :: Signature () where
  New   :: Int                        -> Action refs ('Reference '())
  Find  :: refs @@ '()                -> Action refs ('Reference '())
  Union :: refs @@ '() -> refs @@ '() -> Action refs ('Response ())

------------------------------------------------------------------------

newtype Model refs = Model (Map (refs @@ '()) (refs @@ '()))

initModel :: Model refs
initModel = Model M.empty

(!!!) :: Ord k => Map k k -> k -> k
m !!! ref =
  let ref' = m M.! ref
  in if ref == ref'
     then ref
     else m !!! ref'

prop_eqRel :: [(Bool, Bool)] -> Property
prop_eqRel xys0 = reflexive .&&. symmetric .&&. transitive
  where
  reflexive  x     = x .~. x
  symmetric  x y   = (x .~. y) <==> (y .~. x)
  transitive x y z = ((x .~. y) && (y .~. z)) ==> (x .~. z)

  (<==>) x y = (x ==> y) .&&. (y ==> x)

  x .~. y = let m = mkRel xys0 in
    x == y ||
    if x `elem` M.keys m &&
       y `elem` M.keys m
    then m !!! x == m !!! y
    else False

  mkRel []             = M.empty
  mkRel ((x, y) : xys) =
    M.insert x x $ M.insert y y $ M.insert x y $ M.insert y x $ mkRel xys

------------------------------------------------------------------------

preconditions
  :: forall refs resp. IxForallF Ord refs
  => Model refs -> Action refs resp -> Bool
preconditions (Model m) cmd = (case cmd of
  New   _         -> True
  Find  ref       -> M.member ref  m
  Union ref1 ref2 -> M.member ref1 m && M.member ref2 m
  ) \\ (iinstF @'() Proxy :: Ords refs)

transitions
  :: forall refs resp. IxForallF Ord refs
  => Model refs -> Action refs resp -> Response_ refs resp -> Model refs
transitions (Model m) cmd resp = (case cmd of
  New   _         -> Model (M.insert resp resp m)
  Find  ref       -> Model (M.insert resp resp $ M.insert ref resp m)
  Union ref1 ref2 -> Model (M.insert ref1 (m !!! ref2) m)
  ) \\ (iinstF @'() Proxy :: Ords refs)

postconditions
  :: forall refs resp. IxForallF Ord refs
  => Model refs -> Action refs resp -> Response_ refs resp -> Property
postconditions (Model m) cmd resp = (case cmd of
  New   _         -> property True
  Find  ref       -> property (resp == m' !!! ref)
  Union ref1 ref2 ->
    let z = m' !!! ref1
    in property $ z == m !!! ref1 || z == m !!! ref2
  ) \\ (iinstF @'() Proxy :: Ords refs)
  where
  Model m' = transitions (Model m) cmd resp

smm :: StateMachineModel Model Action
smm = StateMachineModel preconditions postconditions transitions initModel

------------------------------------------------------------------------

gen :: Gen (Untyped Action (RefPlaceholder ()))
gen = frequency
  [ (1, Untyped . New <$> choose (0, 100))
  , (5, return . Untyped $ Find STuple0)
  , (5, return . Untyped $ Union STuple0 STuple0)
  ]

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

unionElements :: Element a -> Element a -> IO ()
unionElements e1 e2 = do

  Element x1 ref1 <- findElement e1
  Element x2 ref2 <- findElement e2
  Weight w1       <- readIORef ref1
  Weight w2       <- readIORef ref2

  if w1 <= w2
  then do
    writeIORef ref1 (Next (Element x2 ref2))
    writeIORef ref2 (Weight (w1 + w2))
  else do
    writeIORef ref2 (Next (Element x1 ref1))
    writeIORef ref1 (Weight (w1 + w2))

instance Eq (Element a) where
  Element _ ref1 == Element _ ref2 = ref1 == ref2

------------------------------------------------------------------------

semantics
  :: Action (ConstSym1 (Element Int)) resp
  -> IO (Response_ (ConstSym1 (Element Int)) resp)
semantics (New   x)     = newElement x
semantics (Find  e)     = findElement e
semantics (Union e1 e2) = unionElements e1 e2

------------------------------------------------------------------------

instance HasResponse Action where
  response New   {} = SReference STuple0
  response Find  {} = SReference STuple0
  response Union {} = SResponse

instance IxFunctor Action where
  ifmap _ (New   x)         = New  x
  ifmap f (Find  ref)       = Find  (f STuple0 ref)
  ifmap f (Union ref1 ref2) = Union (f STuple0 ref1) (f STuple0 ref2)

instance IxFoldable Action where
  ifoldMap _ (New   _)         = mempty
  ifoldMap f (Find  ref)       = f STuple0 ref
  ifoldMap f (Union ref1 ref2) = f STuple0 ref1  `mappend` f STuple0 ref2

instance IxTraversable Action where
  ifor _ (New   x)         _ = pure (New x)
  ifor _ (Find  ref)       f = Find  <$> f STuple0 ref
  ifor _ (Union ref1 ref2) f = Union <$> f STuple0 ref1 <*> f STuple0 ref2

instance ShowCmd Action where
  showCmd (New   x)         = "New "    ++ show x
  showCmd (Find  ref)       = "Find ("  ++ show ref ++ ")"
  showCmd (Union ref1 ref2) = "Union (" ++ show ref1 ++ ") (" ++ show ref2 ++ ")"

------------------------------------------------------------------------

prop_sequential :: Property
prop_sequential = sequentialProperty
  smm
  gen
  shrink1
  semantics
  ioProperty
