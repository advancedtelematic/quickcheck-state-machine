{-# LANGUAGE TemplateHaskell #-}

module Test.StateMachine.Types.Generics.TH where

import           Control.Monad
                   (filterM, (>=>))
import           Data.Foldable
                   (foldl')
import           Language.Haskell.TH
import           Language.Haskell.TH.Datatype
import           Test.QuickCheck
                   (shrink)

import           Test.StateMachine.Internal.Utils
                   (dropLast, nub)
import           Test.StateMachine.Types.Generics
import           Test.StateMachine.Types.References
                   (Reference)

-- * Shrinkers

-- | A generic shrinker which avoids shrinking references.
mkShrinker :: Name -> Q Exp
mkShrinker = reifyDatatype >=> mkShrinker'

mkShrinker' :: DatatypeInfo -> Q Exp
mkShrinker' info = do
  x <- newName "x"
  tms <- traverse shrinkerMatches (datatypeCons info)
  let (_ts, ms) = unzip tms
  lamE [varP x] (caseE (varE x) ms)

shrinkerMatches :: ConstructorInfo -> Q ([Type], Q Match)
shrinkerMatches info = do
  xts <- traverse (\t -> (,) <$> newName "x" <*> pure t) (constructorFields info)
  yts <- filterM (\(_, t) -> shrinkable t) xts
  let (ys, ts) = unzip yts
      fieldPats | [] <- ys = [wildP | _ <- xts]
                 | otherwise = [varP x | (x, _) <- xts]
      m = match (conP (constructorName info) fieldPats) (normalB body) []
      e = foldl' appE (conE (constructorName info)) [varE x | (x, _) <- xts]
      body | [] <- ys = listE []  -- No field is shrinkable
           | otherwise = [|fmap|]
               `appE` lamE [listTupleP ys] e
               `appE` [|shrink $(listTupleE ys)|]
  return (nub ts, m)

listTupleP :: [Name] -> PatQ
listTupleP = listTuple unit cons . fmap varP
  where
    unit = conP (tupleDataName 0) []
    cons a b = tupP [a, b]

listTupleE :: [Name] -> ExpQ
listTupleE = listTuple unit cons . fmap varE
  where
    unit = conE (tupleDataName 0)
    cons a b = tupE [a, b]

listTuple :: a -> (a -> a -> a) -> [a] -> a
listTuple nil cons = go
  where
    go []       = nil
    go [a]      = a
    go (a : as) = cons a (go as)

shrinkable :: Type -> Q Bool
shrinkable =
  fmap (not . isReference) . resolveTypeSynonyms

isReference :: Type -> Bool
isReference (AppT (AppT (ConT r) _) _) = r == ''Reference
isReference _                          = False

-- * Constructor class

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
