{-# LANGUAGE DerivingStrategies            #-}
{-# LANGUAGE GADTs                         #-}
{-# LANGUAGE ScopedTypeVariables           #-}
{-# LANGUAGE OverloadedStrings             #-}
{-# LANGUAGE MultiParamTypeClasses         #-}
{-# LANGUAGE TypeFamilies                  #-}
{-# LANGUAGE TypeOperators                 #-}
{-# LANGUAGE TemplateHaskell               #-}
{-# LANGUAGE QuasiQuotes                   #-}
{-# LANGUAGE GeneralizedNewtypeDeriving    #-}
{-# LANGUAGE UndecidableInstances          #-}
{-# LANGUAGE FlexibleInstances             #-}
{-# LANGUAGE DeriveGeneric                 #-}
{-# LANGUAGE RecordWildCards               #-}
{-# LANGUAGE StandaloneDeriving            #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Schema
    ( Person (..)
    , Car (..)
    , Key (..)
    , CarId
    , entityDefs
    ) where

import           Database.Persist.Class
import           Database.Persist.Sqlite
import           Database.Persist.TH
import           Prelude
import           Test.QuickCheck

share [mkPersist sqlSettings, mkSave "entityDefs"] [persistLowerCase|
Person
    name String
    age Int
    Primary name
    deriving Show
    deriving Eq
    deriving Ord

Car
    cid Int
    color String Maybe
    owner PersonId
    deriving Show
    deriving Eq
    deriving Ord
|]

instance Arbitrary Person where
    arbitrary = Person <$> elements names
                       <*> suchThat arbitrary (>0)

instance Arbitrary Car where
    arbitrary = Car <$> arbitrary
                    <*> genColor
                    <*> (PersonKey <$> elements names)

names :: [String]
names = ["John", "Stevan", "Kostas", "Curry", "Robert"]

colors :: [String]
colors = ["black", "blue", "red", "yellow"]

genColor :: Gen (Maybe String)
genColor = elements $ Nothing : (Just <$> colors)
