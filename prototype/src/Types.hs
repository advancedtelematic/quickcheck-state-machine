{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE StandaloneDeriving         #-}

module Types where

import           Control.Monad.Reader   (Reader, ask, runReader)
import           Data.Map               (Map)
import qualified Data.Map               as M
import           Data.Typeable          (Typeable)
import           Data.Unique            (Unique, newUnique)
import           Test.QuickCheck        (Gen)

import           Types.HFunctor

------------------------------------------------------------------------

data StateMachine model cmd resp = StateMachine
  { initModel     :: forall r. model r
  , transition    :: forall r. ForallF Ord r => model r -> cmd r -> resp r -> model r
  , precondition  :: model Symbolic -> cmd Symbolic -> Bool
  , postcondition :: forall r. model r -> cmd r -> resp r -> Bool
  , invariant     :: forall r. Maybe (model r -> Bool)
  , generator     :: model Symbolic -> [Gen (cmd Symbolic)]
  , weight        :: Maybe (model Symbolic -> cmd Symbolic -> Int)
  , shrinker      :: cmd Symbolic -> [cmd Symbolic]
  , semantics     :: cmd Concrete -> IO (resp Concrete)
  , mock          :: model Symbolic -> cmd Symbolic -> GenSym (resp Symbolic)
  }

newtype Var = Var Int
  deriving (Eq, Ord, Show)

data Symbolic a where
  Symbolic :: Typeable a => Var -> Symbolic a

deriving instance Show (Symbolic a)
deriving instance Eq   (Symbolic a)
deriving instance Ord  (Symbolic a)

data Concrete a = Concrete a Unique

instance Eq (Concrete a) where
  Concrete _ u1 == Concrete _ u2 = u1 == u2

instance Ord (Concrete a) where
  Concrete _ u1 `compare` Concrete _ u2 = u1 `compare` u2

data Reference r a = Reference (r a)

instance Show (Reference Symbolic a) where
  showsPrec p (Reference v) = showParen (p > appPrec) $
      showString "Reference " .
      showsPrec p v
    where
      appPrec = 10

instance HTraversable Reference where
  htraverse f (Reference r) = fmap Reference (f r)

instance HFoldable Reference
instance HFunctor  Reference

reference :: a -> IO (Reference Concrete a)
reference x = Reference <$> (Concrete x <$> newUnique)

concrete :: Reference Concrete a -> a
concrete (Reference (Concrete x _)) = x

instance Eq (r a) => Eq (Reference r a) where
  Reference r1 == Reference r2 = r1 == r2

instance Ord (r a) => Ord (Reference r a) where
  Reference r1 `compare` Reference r2 = r1 `compare` r2

newtype GenSym a = GenSym (Reader Counter a)
  deriving (Functor, Applicative, Monad)

runGenSym :: GenSym a -> Counter -> a
runGenSym (GenSym m) counter = runReader m counter

genSym :: Typeable a => GenSym (Reference Symbolic a)
genSym  = GenSym $ do
  Counter i <- ask
  return (Reference (Symbolic (Var i)))

newtype Counter = Counter Int
  deriving Num

newCounter :: Counter
newCounter = Counter 0

newtype Env ref = Env (Map Var ref)

lookupEnv :: Var -> Env ref -> ref
lookupEnv sym (Env m) = m M.! sym

data History cmd = History (cmd Symbolic)


data Result = Ok | PostconditionFailed
  deriving (Eq, Show)
