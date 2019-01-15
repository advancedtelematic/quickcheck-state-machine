{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DefaultSignatures    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.StateMachine.ConstructorName
  ( CommandNames(..)
  , commandName
  )
  where

import           Data.Kind
                   (Type)
import           Data.Proxy
                   (Proxy(Proxy))
import           GHC.Generics
                   ((:*:)((:*:)), (:+:)(L1, R1), C, Constructor, D,
                   Generic1, K1, M1, Rec1, Rep1, S, U1, conName, from1,
                   unM1, unRec1)
import           Prelude

import           Test.StateMachine.Types
                   (Command(..))

------------------------------------------------------------------------

-- | The names of all possible commands
--
-- This is used for things like tagging, coverage checking, etc.
class CommandNames (cmd :: k -> Type) where
  -- | Name of this particular command
  cmdName  :: cmd r -> String

  -- | Name of all possible commands
  cmdNames :: Proxy (cmd r) -> [String]

  default cmdName :: (Generic1 cmd, CommandNames (Rep1 cmd)) => cmd r -> String
  cmdName = cmdName . from1

  default cmdNames :: forall r. CommandNames (Rep1 cmd) => Proxy (cmd r) -> [String]
  cmdNames _ = cmdNames (Proxy @(Rep1 cmd r))

instance CommandNames U1 where
  cmdName  _ = ""
  cmdNames _ = []

instance CommandNames (K1 i c) where
  cmdName  _ = ""
  cmdNames _ = []

instance Constructor c => CommandNames (M1 C c f) where
  cmdName                            = conName
  cmdNames (_ :: Proxy (M1 C c f p)) = [ conName @c undefined ] -- Can we do
                                                                  -- better
                                                                  -- here?

instance CommandNames f => CommandNames (M1 D c f) where
  cmdName                            = cmdName  . unM1
  cmdNames (_ :: Proxy (M1 D c f p)) = cmdNames (Proxy :: Proxy (f p))

instance CommandNames f => CommandNames (M1 S c f) where
  cmdName                            = cmdName  . unM1
  cmdNames (_ :: Proxy (M1 S c f p)) = cmdNames (Proxy :: Proxy (f p))

instance (CommandNames f, CommandNames g) => CommandNames (f :+: g) where
  cmdName (L1 x) = cmdName x
  cmdName (R1 y) = cmdName y

  cmdNames (_ :: Proxy ((f :+: g) a)) =
    cmdNames (Proxy :: Proxy (f a)) ++
    cmdNames (Proxy :: Proxy (g a))

instance (CommandNames f, CommandNames g) => CommandNames (f :*: g) where
  cmdName  (x :*: y)                  = cmdName x ++ cmdName y
  cmdNames (_ :: Proxy ((f :*: g) a)) =
    cmdNames (Proxy :: Proxy (f a)) ++
    cmdNames (Proxy :: Proxy (g a))

instance CommandNames f => CommandNames (Rec1 f) where
  cmdName                          = cmdName  . unRec1
  cmdNames (_ :: Proxy (Rec1 f p)) = cmdNames (Proxy :: Proxy (f p))

------------------------------------------------------------------------

-- | Convenience wrapper for 'Command'
commandName :: CommandNames cmd => Command cmd resp -> String
commandName (Command cmd _ _) = cmdName cmd
