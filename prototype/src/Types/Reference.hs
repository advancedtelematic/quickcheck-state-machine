{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE StandaloneDeriving #-}

module Types.Reference where

import           Data.Typeable
                   (Typeable)
import           Data.Unique
                   (Unique, newUnique)

import qualified Rank2

------------------------------------------------------------------------

newtype Var = Var Int
  deriving (Eq, Ord, Show)

data Symbolic a where
  Symbolic :: Typeable a => Var -> Symbolic a

deriving instance Show (Symbolic a)
deriving instance Eq   (Symbolic a)
deriving instance Ord  (Symbolic a)

data Concrete a where
  Concrete :: Typeable a => a -> Unique -> Concrete a

instance Eq (Concrete a) where
  Concrete _ u1 == Concrete _ u2 = u1 == u2

instance Ord (Concrete a) where
  Concrete _ u1 `compare` Concrete _ u2 = u1 `compare` u2

data Reference a r = Reference (r a)

instance Rank2.Foldable (Reference a) where
  foldMap f (Reference r) = f r

instance Eq (r a) => Eq (Reference a r) where
  Reference r1 == Reference r2 = r1 == r2

instance Ord (r a) => Ord (Reference a r) where
  Reference r1 `compare` Reference r2 = r1 `compare` r2

instance Show (Reference a Symbolic) where
  showsPrec p (Reference v) = showParen (p > appPrec) $
    showString "Reference " .
    showsPrec p v
      where
        appPrec = 10

reference :: Typeable a => a -> IO (Reference a Concrete)
reference x = Reference <$> (Concrete x <$> newUnique)

concrete :: Reference a Concrete -> a
concrete (Reference (Concrete x _)) = x
