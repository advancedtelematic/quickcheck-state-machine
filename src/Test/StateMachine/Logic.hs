{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StandaloneDeriving        #-}

module Test.StateMachine.Logic where

infixr 1 :=>
infixr 2 :||
infixr 3 :&&

data Logic
  = Bot
  | Top
  | Logic :&& Logic
  | Logic :|| Logic
  | Logic :=> Logic
  | Not Logic
  | Predicate Predicate
  | Annotate String Logic
  deriving Show

data Predicate
  = forall a. (Eq  a, Show a) => a :== a
  | forall a. (Eq  a, Show a) => a :/= a
  | forall a. (Ord a, Show a) => a :<  a
  | forall a. (Ord a, Show a) => a :<= a
  | forall a. (Ord a, Show a) => a :>  a
  | forall a. (Ord a, Show a) => a :>= a
  | forall a. (Eq  a, Show a) => Elem    a [a]
  | forall a. (Eq  a, Show a) => NotElem a [a]

deriving instance Show Predicate

dual :: Predicate -> Predicate
dual p = case p of
  x :== y        -> x :/= y
  x :/= y        -> x :== y
  x :<  y        -> x :>= y
  x :<= y        -> x :>  y
  x :>  y        -> x :<= y
  x :>= y        -> x :<  y
  x `Elem`    xs -> x `NotElem` xs
  x `NotElem` xs -> x `Elem`    xs

strongNeg :: Logic -> Logic
strongNeg l = case l of
  Bot          -> Top
  Top          -> Bot
  l :&& r      -> strongNeg l :|| strongNeg r
  l :|| r      -> strongNeg l :&& strongNeg r
  l :=> r      ->           l :&& strongNeg r
  Not l        -> l
  Predicate p  -> Predicate (dual p)
  Annotate s l -> Annotate s (strongNeg l)

data Counterexample
  = BotC
  | Fst Counterexample
  | Snd Counterexample
  | EitherC Counterexample Counterexample
  | ImpliesC Counterexample
  | NotC Counterexample
  | PredicateC Predicate
  | AnnotateC String Counterexample
  deriving Show

data Value
  = VFalse Counterexample
  | VTrue
  deriving Show

logic :: Logic -> Value
logic Bot            = VFalse BotC
logic Top            = VTrue
logic (l :&& r)      = case logic l of
  VFalse ce -> VFalse (Fst ce)
  VTrue     -> case logic r of
    VFalse ce' -> VFalse (Snd ce')
    VTrue      -> VTrue
logic (l :|| r)      = case logic l of
  VTrue     -> VTrue
  VFalse ce -> case logic r of
    VTrue      -> VTrue
    VFalse ce' -> VFalse (EitherC ce ce')
logic (l :=> r)      = case logic l of
  VFalse _ -> VTrue
  VTrue    -> case logic r of
    VTrue     -> VTrue
    VFalse ce -> VFalse (ImpliesC ce)
logic (Not l)        = case logic (strongNeg l) of
  VTrue     -> VTrue
  VFalse ce -> VFalse (NotC ce)
logic (Predicate p)  = predicate p
logic (Annotate s l) = case logic l of
  VTrue     -> VTrue
  VFalse ce -> VFalse (AnnotateC s ce)

predicate :: Predicate -> Value
predicate p = let b = boolean p in case p of
  x :== y        -> b (x == y)
  x :/= y        -> b (x /= y)
  x :<  y        -> b (x <  y)
  x :<= y        -> b (x <= y)
  x :>  y        -> b (x >  y)
  x :>= y        -> b (x >= y)
  x `Elem`    xs -> b (x `elem`    xs)
  x `NotElem` xs -> b (x `notElem` xs)
  where
  boolean :: Predicate -> Bool -> Value
  boolean p True  = VTrue
  boolean p False = VFalse (PredicateC (dual p))
