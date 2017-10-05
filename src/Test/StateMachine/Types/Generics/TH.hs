{-# LANGUAGE TemplateHaskell #-}

module Test.StateMachine.Types.Generics.TH where

import           Control.Applicative
                   (liftA2)
import           Control.Monad
                   (filterM, (>=>))
import           Data.Foldable
                   (asum, foldl')
import           Data.Functor.Classes
                   (Show1)
import           Data.Maybe
                   (maybeToList)
import           Language.Haskell.TH
import           Language.Haskell.TH.Datatype
import           Test.QuickCheck
                   (shrink)

import           Test.StateMachine.Internal.Utils
                   (dropLast, nub, toLast)
import           Test.StateMachine.Types
                   (Untyped)
import           Test.StateMachine.Types.Generics
import           Test.StateMachine.Types.References
                   (Reference)

-- * Show of actions

-- | Derive @Show (Action v a)@ and @Show (Untyped Action)@.
deriveShows :: Name -> Q [Dec]
deriveShows = (liftA2 . liftA2) (++) deriveShow deriveShowUntyped

-- | Derive @Show (Action v a)@.
deriveShow :: Name -> Q [Dec]
deriveShow = reifyDatatype >=> deriveShow'

deriveShow' :: DatatypeInfo -> Q [Dec]
deriveShow' info = do
  (v_, ts) <- showConstraints info
  let show1v = maybeToList (fmap (AppT (ConT ''Show1)) v_)
      cxt_ = show1v ++ fmap (AppT (ConT ''Show)) ts
      instanceHead_ = AppT
        (ConT ''Show)
        (foldl' AppT (ConT (datatypeName info)) (datatypeVars info))
  return [StandaloneDerivD cxt_ instanceHead_]

-- | Derive @Show (Untyped Action)@.
deriveShowUntyped :: Name -> Q [Dec]
deriveShowUntyped = reifyDatatype >=> deriveShowUntyped'

deriveShowUntyped' :: DatatypeInfo -> Q [Dec]
deriveShowUntyped' info = do
  (_, ts) <- showConstraints info
  let cxt_ = fmap (AppT (ConT ''Show)) ts
      instanceHead_ = AppT
        (ConT ''Show)
        (AppT
          (ConT ''Untyped)
          (foldl' AppT (ConT (datatypeName info)) (dropLast 2 (datatypeVars info))))
  return [StandaloneDerivD cxt_ instanceHead_]

-- | Gather types of fields with parametric types to form @Show@ constraints
-- for a derived instance.
--
-- - @(Show1 v, Show a)@ for fields of type @Reference v a@
-- - @Show a@ for fields of type @a@
--
-- The @Show1 v@ constraint is separated so that we can easily remove
-- it from the list.
showConstraints :: DatatypeInfo -> Q (Maybe Type, [Type])
showConstraints info = do
  let SigT v _ = toLast 1 (datatypeVars info)
  fmap gatherShowConstraints
    (traverse (showConstraintsByCon v) (datatypeCons info))

showConstraintsByCon :: Type -> ConstructorInfo -> Q (Maybe Type, [Type])
showConstraintsByCon v info =
  fmap gatherShowConstraints
    (traverse (showConstraintsByField v) (constructorFields info))

showConstraintsByField :: Type -> Type -> Q (Maybe Type, [Type])
showConstraintsByField v t' = do
  t <- resolveTypeSynonyms t'
  return $ case t of
    AppT (AppT (ConT _ref) v') a
      | _ref == ''Reference && v == v' -> (Just v, singleton a)
    _ -> (Nothing, singleton t)
  where
    singleton t | variableHead t = [t]
                | otherwise = []

gatherShowConstraints :: [(Maybe Type, [Type])] -> (Maybe Type, [Type])
gatherShowConstraints vts =
  let (vs', ts') = unzip vts
      v = asum vs'
      ts = nub (concat ts')
  in (v, ts)

variableHead :: Type -> Bool
variableHead (AppT u _) = variableHead u
variableHead (VarT _)   = True
variableHead _          = False

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
