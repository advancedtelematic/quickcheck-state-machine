{-# LANGUAGE TemplateHaskell #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Test.StateMachine.Types.Generics.TH
-- Copyright   :  (C) 2017, ATS Advanced Telematic Systems GmbH, Li-yao Xia
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Li-yao Xia <lysxia@gmail.com>
-- Stability   :  provisional
-- Portability :  non-portable (GHC extensions)
--
-- Template Haskell functions to derive some general-purpose functionalities.
--
-----------------------------------------------------------------------------

module Test.StateMachine.Types.Generics.TH
  ( deriveShows
  , deriveShow
  , deriveShowUntyped
  , mkShrinker
  , deriveConstructors
  ) where

import           Control.Applicative
                   (liftA3)
import           Control.Monad
                   (filterM, (>=>))
import           Data.Foldable
                   (asum, foldl')
import           Data.Functor.Classes
                   (Show1, liftShowsPrec)
import           Data.Maybe
                   (maybeToList)
import           Language.Haskell.TH
                   (Body(NormalB), Clause(Clause), Cxt,
                   Dec(FunD, InstanceD), Exp(AppE, ConE, LitE, VarE),
                   ExpQ, Lit(IntegerL, StringL), Match, Name,
                   Pat(RecP, VarP, WildP), PatQ, Q,
                   Type(AppT, ConT, SigT, VarT), appE, caseE, conE,
                   conP, lamE, listE, match, mkName, nameBase, newName,
                   normalB, standaloneDerivD, tupE, tupP,
                   tupleDataName, varE, varP, wildP)
import           Language.Haskell.TH.Datatype
                   (ConstructorInfo, DatatypeInfo, constructorFields,
                   constructorName, datatypeCons, datatypeName,
                   datatypeVars, reifyDatatype, resolveTypeSynonyms)
import           Test.QuickCheck
                   (shrink)

import           Test.StateMachine.Internal.Utils
                   (dropLast, nub, toLast)
import           Test.StateMachine.Types
                   (Symbolic, Untyped)
import           Test.StateMachine.Types.Generics
import           Test.StateMachine.Types.References
                   (Reference)

-- * Show of actions

-- | Given a name @''Action@, derive 'Show' for @(Action v a)@ and @('Untyped'
-- Action)@, and 'Show1' @(Action Symbolic)@. See 'deriveShow',
-- 'deriveShowUntyped', and 'deriveShow1'.
deriveShows :: Name -> Q [Dec]
deriveShows = (liftA3 . liftA3)
  (\xs ys zs -> xs ++ ys ++ zs) deriveShow deriveShowUntyped deriveShow1

-- |
--
-- @
-- 'deriveShow' ''Action
-- ===>
-- deriving instance 'Show1' v => 'Show' (Action v a).
-- @
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
  standaloneDerivD' cxt_ instanceHead_

standaloneDerivD' :: Cxt -> Type -> Q [Dec]
standaloneDerivD' cxt ty = (:[]) <$> standaloneDerivD (return cxt) (return ty)

-- |
-- @
-- 'deriveShowUntyped' ''Action
-- ===>
-- deriving instance 'Show' ('Untyped' Action)
-- @
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
  standaloneDerivD' cxt_ instanceHead_

-- |
-- @ 'derivingShow1' ''Action
-- ===>
-- instance Show1 (Action Symbolic) where
--   liftShowsPrec _ _ _ act _ = show act
-- @
deriveShow1 :: Name -> Q [Dec]
deriveShow1 = (fmap . fmap) deriveShow1' reifyDatatype

deriveShow1' :: DatatypeInfo -> [Dec]
deriveShow1' info0 = pure $
  InstanceD Nothing [] (instanceHead' info0)
    [ deriveLiftShows ]
  where
  instanceHead' :: DatatypeInfo -> Type
  instanceHead' info =
    ConT ''Show1 `AppT`
      (ConT (datatypeName info) `AppT` ConT ''Symbolic)

  deriveLiftShows :: Dec
  deriveLiftShows =
    let
      act  = mkName "act"
      body = VarE 'show `AppE` VarE act
    in
      FunD 'liftShowsPrec
        [Clause [WildP, WildP, WildP, VarP act, WildP] (NormalB body) []]

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

-- | @$('mkShrinker' ''Action)@
-- creates a generic shrinker of type @(Action v a -> [Action v a])@
-- which ignores 'Reference' fields.
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

-- |
-- @
-- 'deriveConstructors' ''Action
-- ===>
-- instance 'Constructors' Action where ...
-- @
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
