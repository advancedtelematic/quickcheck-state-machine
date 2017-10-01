{-# LANGUAGE TemplateHaskell #-}

module Test.StateMachine.Types.Generics.TH where

import           Control.Monad
                   ((>=>))
import           Data.Foldable
                   (foldl')
import           Language.Haskell.TH
import           Language.Haskell.TH.Datatype

import           Test.StateMachine.Internal.Utils
                   (dropLast)
import           Test.StateMachine.Types.Generics

deriveConstructors :: Name -> Q [Dec]
deriveConstructors = (fmap . fmap) deriveConstructors' reifyDatatype

deriveConstructors' :: DatatypeInfo -> [Dec]
deriveConstructors' info = pure $
  InstanceD Nothing [] (instanceHead info)
    [ deriveconstructor info
    , derivenConstructors info
    ]

instanceHead :: DatatypeInfo -> Type
instanceHead info =
  ConT ''Constructors `AppT`
    foldl' AppT (ConT (datatypeName info)) (dropLast 2 (datatypeVars info))

-- |
-- > constructor Foo{} = Constructor "Foo"
-- > constructor Bar{} = Constructor "Bar"
deriveconstructor :: DatatypeInfo -> Dec
deriveconstructor info =
  FunD 'constructor (fmap constructorClause (datatypeCons info))

constructorClause :: ConstructorInfo -> Clause
constructorClause info =
  let body = ConE 'Constructor `AppE` LitE (StringL (nameBase (constructorName info)))
  in Clause [RecP (constructorName info) []] (NormalB body) []

derivenConstructors :: DatatypeInfo -> Dec
derivenConstructors info =
  let nCons = fromIntegral (length (datatypeCons info))
  in FunD 'nConstructors [Clause [WildP] (NormalB (LitE (IntegerL nCons))) []]
