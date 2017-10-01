{-# LANGUAGE TemplateHaskell #-}

module Test.StateMachine.Types.HFunctor.TH
  ( deriveHClasses
  , deriveHTraversable
  , mkhtraverse
  , deriveHFoldable
  , mkhfoldMap
  , deriveHFunctor
  , mkhfmap
  ) where

import           Control.Applicative
                   (liftA3)
import           Control.Monad
                   (when, (>=>))
import           Data.Foldable
                   (foldl')
import           Data.Monoid
                   (mempty, (<>))
import qualified Data.Set                         as Set
import           Data.Traversable
                   (for)
import           Language.Haskell.TH
import           Language.Haskell.TH.Datatype

import           Test.StateMachine.Internal.Utils
                   (dropLast, nub, toLast)
import           Test.StateMachine.Types.HFunctor

-- | Derive 'HFunctor', 'HFoldable' and 'HTraversable'.
deriveHClasses :: Name -> Q [Dec]
deriveHClasses =
  (liftA3 . liftA3) (\a b c -> a ++ b ++ c)
    deriveHFunctor
    deriveHFoldable
    deriveHTraversable

-- | Derive 'HTraversable'.
deriveHTraversable :: Name -> Q [Dec]
deriveHTraversable = reifying deriveIFor dictHTraversable

-- | Derive the body of 'htraverse'.
mkhtraverse :: Name -> Q Exp
mkhtraverse = reifying mkFFor dictHTraversable

deriveHFoldable :: Name -> Q [Dec]
deriveHFoldable = reifying deriveIFor dictHFoldable

mkhfoldMap :: Name -> Q Exp
mkhfoldMap = reifying mkFFor dictHFoldable

deriveHFunctor :: Name -> Q [Dec]
deriveHFunctor = reifying deriveIFor dictHFunctor

mkhfmap :: Name -> Q Exp
mkhfmap = reifying mkFFor dictHFunctor

data Dictionary = Dictionary
  { className :: Name
  , funName   :: Name
  , pureE     :: Exp -> Exp
  , apE       :: Exp -> Exp -> Exp
  }

dictHFunctor :: Dictionary
dictHFunctor = Dictionary
  { className = ''HFunctor
  , funName = 'hfmap
  , pureE = id
  , apE = AppE
  }

dictHFoldable :: Dictionary
dictHFoldable = Dictionary
  { className = ''HFoldable
  , funName = 'hfoldMap
  , pureE = const (VarE 'mempty)
  , apE = apE'
  } where
    -- mempty <> e = e
    -- e <> mempty = e
    apE' (VarE m) e | m == 'mempty = e
    apE' e (VarE m) | m == 'mempty = e
    apE' e1 e2      = infixE_ e1 '(<>) e2

dictHTraversable :: Dictionary
dictHTraversable = Dictionary
  { className = ''HTraversable
  , funName = 'htraverse
  , pureE = AppE (VarE 'pure)
  , apE = apE'
  } where
    -- pure f <*> v = f <$> v
    apE' (AppE (VarE pure_) f) v | pure_ == 'pure = infixE_ f '(<$>) v
    apE' u v                     = infixE_ u '(<*>) v

reifying :: (Dictionary -> DatatypeInfo -> Q r) -> Dictionary -> Name -> Q r
reifying derive dict = reifyDatatype >=> derive dict

deriveIFor :: Dictionary -> DatatypeInfo -> Q [Dec]
deriveIFor dict info = fmap (: []) $ do
  when (length (datatypeVars info) < 2)
    (fail $ "Type " ++ show (datatypeName info) ++ " should have arity >= 2")
  (cxt_, htraversalDec) <- htraversalWithCxtFor dict info
  let instanceHead = AppT
        (ConT (className dict))
        (foldl' AppT (ConT (datatypeName info)) (dropLast 2 (datatypeVars info)))
  return
    (InstanceD Nothing cxt_ instanceHead [htraversalDec])

mkFFor :: Dictionary -> DatatypeInfo -> Q Exp
mkFFor dict info =
  fmap mkF (htraversalBodyFor dict info)
  where
    mkF (_, pats, body) = LamE pats body

htraversalWithCxtFor :: Dictionary -> DatatypeInfo -> Q (Cxt, Dec)
htraversalWithCxtFor dict info =
  fmap mkFunD (htraversalBodyFor dict info)
  where
    mkFunD (cxt_, pats, body) =
      (cxt_, FunD (funName dict) [Clause pats (NormalB body) []])

htraversalBodyFor :: Dictionary -> DatatypeInfo -> Q (Cxt, [Pat], Exp)
htraversalBodyFor dict info = do
  fN <- newName "f"
  aN <- newName "a"
  let SigT v _ = toLast 1 (datatypeVars info)
  tucs <- traverse (htraversalMatchFor dict v (VarE fN)) (datatypeCons info)
  let (ts, usedF', matches) = unzip3 tucs
      usedF = or usedF'
      fP = if usedF then VarP fN else WildP
      pats = [fP, VarP aN]
      cxt_ = fmap (AppT (ConT (className dict))) (nub (concat ts))
  return (cxt_, pats, CaseE (VarE aN) matches)

htraversalMatchFor :: Dictionary -> Type -> Exp -> ConstructorInfo -> Q ([Type], Bool, Match)
htraversalMatchFor dict v f info = do
  xts <- for (constructorFields info) (\t ->  fmap (\x -> (x, t)) (newName "x"))
  cyfs <- for xts (uncurry (htraversalFieldFor dict v f))
  let conPattern = ConP (constructorName info) [mkVarP x | (x, _) <- xts]
      -- HFoldable instances may have unused fields, replaced with wildcards.
      mkVarP x | className dict == ''HFoldable && x `Set.member` ys = WildP
               | otherwise = VarP x
      c = ConE (constructorName info)
      (cnstrnts', ys', fields) = unzip3 cyfs
      -- f gets used if at least one field did not use pure
      usedF = any null ys'
      cnstrnts = concat cnstrnts'
      ys = Set.fromList (concat ys')
      body = foldl' (apE dict) (pureE dict c) fields
  return
    (cnstrnts, usedF, Match conPattern (NormalB body) [])

infixE_ :: Exp -> Name -> Exp -> Exp
infixE_ x (+.) y = InfixE (Just x) (VarE (+.)) (Just y)

htraversalFieldFor :: Dictionary -> Type -> Exp -> Name -> Type -> Q ([Type], [Name], Exp)
htraversalFieldFor dict v f x' t' = do
  let x = VarE x'
  t <- resolveTypeSynonyms t'
  return $ case t of
    AppT (AppT u v') _ | v == v' ->
      ( [u | variableHead u]
      , []
      , VarE (funName dict) `AppE` f `AppE` x)
    AppT v' _ | v == v' ->
      ([], [], f `AppE` x)
    _ ->
      ([], [x'], pureE dict x)

variableHead :: Type -> Bool
variableHead (AppT u _) = variableHead u
variableHead (VarT _)   = True
variableHead _          = False
