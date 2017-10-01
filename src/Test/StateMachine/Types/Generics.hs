{-# LANGUAGE KindSignatures #-}

module Test.StateMachine.Types.Generics where

newtype Constructor = Constructor String
  deriving (Eq, Ord)

instance Show Constructor where
  show (Constructor c) = c

-- | Extracting constructors from actions.
class Constructors (act :: (* -> *) -> * -> *) where

  -- | Constructor of a given action.
  constructor :: act v a -> Constructor

  -- | Total number of constructors in the action type.
  nConstructors :: proxy act -> Int
