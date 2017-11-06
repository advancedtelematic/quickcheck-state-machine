{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TemplateHaskell       #-}

-- This example is taken from the following presentation:
--
--     https://www.youtube.com/watch?v=fSWZWXx5ixc
--
--

module Bank where

import           Data.Functor.Classes
                   (Show1, liftShowsPrec)
import           Data.Functor.Product
import           Data.List
                   ((\\))
import           Data.Maybe
                   (isJust)
import           Data.Proxy
import           Data.Void
                   (Void)
import           Test.QuickCheck
                   (Arbitrary, Property, arbitrary, elements,
                   frequency, getNonNegative, oneof, shrink, suchThat,
                   (===))

import           Test.StateMachine
import           Test.StateMachine.TH
import           Test.StateMachine.Z

------------------------------------------------------------------------

newtype Account = Account Int
  deriving (Eq, Show)

newtype Person  = Person String
  deriving (Eq, Show)

data Model0 (v :: * -> *) = Model0
  { accounts :: [Account]
  , owner    :: Fun Account Person
  , bal      :: Fun Account Int
  }
  deriving (Eq, Show)

initModel :: Model0 v
initModel = Model0 [] empty empty

invariants0 :: Postcondition' Model0 Action0 Void
invariants0 Model0{..} _ _ =
     isTotalFun owner accounts
  && isTotalFun bal accounts
  && all (\acc -> bal ! acc >= 0) accounts

data Action0 (v :: * -> *) :: * -> * where
  Open     :: Person -> Account -> Action0 v ()
  Close    :: Account -> Action0 v ()
  Deposit  :: Account -> Int -> Action0 v ()
  Withdraw :: Account -> Int -> Action0 v ()

deriveShows       ''Action0
deriveTestClasses ''Action0

precondition0 :: Model0 v -> Action0 v resp -> Bool
precondition0 Model0{..} act = case act of
  Open _   acc   -> acc `notElem` accounts
  Close acc      -> acc `elem` accounts
  Deposit acc q  -> acc `elem` accounts && q >= 0
  Withdraw acc q -> acc `elem` accounts && q >= 0 && q <= bal ! acc

transition0 :: Transition' Model0 Action0 Void
transition0 m@Model0{..} act _ = case act of
  Open prs acc   -> Model0 (accounts `union` [acc])
                           (owner .! acc .= prs)
                           (bal .! acc .= 0)
  Close acc      -> Model0 (accounts \\ [acc])
                           ([acc] <-| owner)
                           ([acc] <-| bal)
  Deposit acc q  -> m { bal = bal .! acc .% (+ q) }
  Withdraw acc q -> m { bal = bal .! acc .% (\i -> i - q) }

------------------------------------------------------------------------

instance Arbitrary Person where
  arbitrary = Person <$> elements ["apa", "bepa", "cepa", "depa", "epa"]

instance Arbitrary Account where
  arbitrary = Account <$> (getNonNegative <$> arbitrary)

generator0 :: Generator Model0 Action0
generator0 (Model0 accs _ _)
  | null accs = Untyped <$> (Open <$> arbitrary <*> arbitrary)
  | otherwise = frequency
      [ (1, Untyped <$> (Open     <$> arbitrary <*> arbitrary))
      , (1, Untyped .    Close    <$> elements accs)
      , (8, Untyped <$> (Deposit  <$> elements accs <*> arbitrary))
      , (8, Untyped <$> (Withdraw <$> elements accs <*> arbitrary))
      ]

shrinker0 :: Shrinker Action0
shrinker0 (Open prs acc)   = [ Open prs' acc   | prs' <- shrink prs ]
shrinker0 (Deposit acc q)  = [ Deposit  acc q' | q'   <- shrink q ]
shrinker0 (Withdraw acc q) = [ Withdraw acc q' | q'   <- shrink q ]
shrinker0 (Close _)        = []

semantics0 :: Action0 v resp -> IO resp
semantics0 act = case act of
  Open     _ _ -> return ()
  Close    _   -> return ()
  Deposit  _ _ -> return ()
  Withdraw _ _ -> return ()

sm :: StateMachine Model0 Action0 IO
sm = StateMachine
  generator0 shrinker0 precondition0 transition0
  invariants0 initModel (okSemantics semantics0) id

------------------------------------------------------------------------

prop_bankSequential :: Property
prop_bankSequential = monadicSequential sm $ \prog -> do
  (hist, _, res) <- runProgram sm prog
  prettyProgram sm hist $
    checkActionNames prog (res === Ok)

------------------------------------------------------------------------

newtype Model1 (v :: * -> *) = Model1
  { inbank :: Rel Account Int }
  deriving (Eq, Show)

initModel1 :: Model1 v
initModel1 = Model1 empty

data Action1 (v :: * -> *) :: * -> * where
  Move1  :: Account -> Account -> Int -> Action1 v ()
  Close1 :: Account -> Action1 v ()

deriveShows       ''Action1
deriveTestClasses ''Action1

precondition1 :: Precondition (Product Model0 Model1) Action1
precondition1 (Pair Model0{..} Model1{..}) act = case act of
  Move1 acc1 acc2 q -> acc1 `elem` accounts && acc2 `elem` accounts &&
                       -- Duplicated...
                       acc1 /= acc2 && q >= 0 && q <= bal ! acc1
  Close1 acc        -> acc `elem` accounts
                       -- Duplicated...
                       -- && acc `notElem` domain inbank

transition1 :: Transition' (Product Model0 Model1) Action1 Void
transition1 (Pair Model0{..} Model1{..}) (Move1 acc1 acc2 q) _ = Pair
  (Model0 accounts owner (bal .! acc1 .% (\i -> i - q)))
  (Model1 (inbank `union` [(acc2, q)]))
transition1 (Pair Model0{..} model1)     (Close1 acc)        _ = Pair
  (Model0 (accounts \\ [acc])
          ([acc] <-| owner)
          ([acc] <-| bal))
  model1

invariants1 :: Postcondition' (Product Model0 Model1) Action1 Void
invariants1 (Pair Model0{..} Model1{..}) _ _ =
  domain inbank `isSubsetOf` accounts

semantics1 :: Action1 Concrete resp -> IO resp
semantics1 act = case act of
  Move1 {}  -> return ()
  Close1 _  -> return ()

generator1 :: Generator (Product Model0 Model1) Action1
generator1 (Pair Model0{..} _) = frequency
  [ (1, Untyped .    Close1 <$> elements accounts)
  , (8, Untyped <$> (Move1  <$> elements accounts <*> elements accounts <*> arbitrary))
  ]

shrinker1 :: Shrinker Action1
shrinker1 (Move1 acc1 acc2 q) = [ Move1 acc1 acc2 q' | q' <- shrink q ]
shrinker1 _                   = []

------------------------------------------------------------------------

-- The following code is from @Danten's PR: "One way of combining models
-- out of smaller ones" (#132).

data Plus act1 act2 (v :: * -> *) :: * -> * where
  Inl :: act1 v resp -> Plus act1 act2 v resp
  Inr :: act2 v resp -> Plus act1 act2 v resp

liftPre
  :: Precondition model0 act0
  -> Precondition (Product model0 model1) act1
  -> Precondition (Product model0 model1) (Plus act0 act1)
liftPre pre0 _   (Pair model0 _)  (Inl act0) = pre0 model0 act0
liftPre _    pre1 model01         (Inr act1) = pre1 model01 act1

liftTrans
  :: Transition' model0 act0 Void
  -> Transition' (Product model0 model1) act1 Void
  -> Transition' (Product model0 model1) (Plus act0 act1) Void
liftTrans trans0 _      (Pair model0 model1) (Inl act0) resp
  = Pair (trans0 model0 act0 resp) model1
liftTrans _      trans1 model01              (Inr act1) resp
  = trans1 model01 act1 resp

liftPost
  :: Postcondition' model0 act0 Void
  -> Postcondition' (Product model0 model1) act1 Void
  -> (forall resp. act0 Concrete resp -> Maybe (act1 Concrete resp))
  -> (forall resp. act1 Concrete resp -> act0 Concrete resp)
  -> Postcondition' (Product model0 model1) (Plus act0 act1) Void
liftPost post0 post1 r0 _ (Pair model0 model1) (Inl act0) resp =
  post0 model0 act0 resp && case r0 act0 of
    Nothing   -> True
    Just act1 -> post1 (Pair model0 model1) act1 resp
liftPost post0 post1 _  r1 (Pair model0 model1) (Inr act1) resp =
  post0 model0 (r1 act1) resp && post1 (Pair model0 model1) act1 resp

liftSem
  :: Semantics' act0 m Void
  -> Semantics' act1 m Void
  -> Semantics' (Plus act0 act1) m Void
liftSem sem0 _    (Inl act0) = sem0 act0
liftSem _    sem1 (Inr act1) = sem1 act1

liftShrinker :: Shrinker act0 -> Shrinker act1 -> Shrinker (Plus act0 act1)
liftShrinker shr0 _    (Inl act) = Inl <$> shr0 act
liftShrinker _    shr1 (Inr act) = Inr <$> shr1 act

liftGen
  :: Generator model0 act0
  -> Generator (Product model0 model1) act1
  -> (forall resp. act0 Symbolic resp -> Bool)
  -> Generator (Product model0 model1) (Plus act0 act1)
liftGen gen0 gen1 r (Pair model0 model1) = oneof [act0, act1]
  where
  act0 = do
    Untyped act <- gen0 model0 `suchThat` (\(Untyped act) -> not (r act))
    return (Untyped (Inl act))

  act1 = do
    Untyped act <- gen1 (Pair model0 model1)
    return (Untyped (Inr act))

instance (Show (Untyped act0), Show (Untyped act1)) =>
    Show (Untyped (Plus act0 act1)) where
  show (Untyped (Inl act)) = show (Untyped act)
  show (Untyped (Inr act)) = show (Untyped act)

instance (Constructors act0, Constructors act1) => Constructors (Plus act0 act1) where
  constructor (Inl act) = constructor act
  constructor (Inr act) = constructor act
  nConstructors _       = nConstructors (Proxy :: Proxy act0) +
                          nConstructors (Proxy :: Proxy act1) -- Minus the ones
                                                              -- we refined...

instance (HFunctor act0, HFunctor act1) => HFunctor (Plus act0 act1) where
  hfmap f (Inl act) = Inl (hfmap f act)
  hfmap f (Inr act) = Inr (hfmap f act)

instance (HFoldable act0, HFoldable act1) => HFoldable (Plus act0 act1) where
  hfoldMap f (Inl act) = hfoldMap f act
  hfoldMap f (Inr act) = hfoldMap f act

instance (HTraversable act0, HTraversable act1) => HTraversable (Plus act0 act1) where
  htraverse f (Inl act) = Inl <$> htraverse f act
  htraverse f (Inr act) = Inr <$> htraverse f act

------------------------------------------------------------------------

instance Show (Product Model0 Model1 Concrete) where
  show (Pair model0 model1) = show model0 ++ "\n" ++ show model1

instance Show1 (Plus Action0 Action1 Symbolic) where
  liftShowsPrec _ _ _ (Inl act) _ = show act
  liftShowsPrec _ _ _ (Inr act) _ = show act

refined :: Action0 v resp -> Maybe (Action1 v resp)
refined (Close acc) = Just (Close1 acc)
refined _           = Nothing

refines :: Action1 v resp -> Action0 v resp
refines (Close1 acc)     = Close acc
refines (Move1 acc1 _ q) = Withdraw acc1 q

------------------------------------------------------------------------

sm01 :: StateMachine (Product Model0 Model1) (Plus Action0 Action1) IO
sm01 = StateMachine
  (liftGen generator0 generator1 (isJust . refined)) (liftShrinker shrinker0 shrinker1)
  (liftPre precondition0 precondition1)
  (liftTrans transition0 transition1)
  (liftPost invariants0 invariants1 refined refines) (Pair initModel initModel1)
  (liftSem (fmap Success . semantics0) (fmap Success . semantics1)) id

prop_refinement :: Property
prop_refinement = monadicSequential sm01 $ \prog -> do
  (hist, _, res) <- runProgram sm01 prog
  prettyProgram sm01 hist $
    checkActionNames prog (res === Ok)
