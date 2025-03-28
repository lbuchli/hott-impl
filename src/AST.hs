{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
module AST where

import qualified Data.IntSet as IntSet
import qualified Data.IntMap.Strict as IntMap

import Inference
import DeBrujin (DBIndex(DBIndex))

data Type
  = U Int
  | (:=:) Type Type
  | Σ Type Type
  | Π Type Type
  | Dep Expr
  | TV TyVar
 deriving Show

data Expr
  = App Expr Expr
  | Refl Expr
  | (:&:) Expr Expr
  | Abs Expr
  | Var DBIndex
 deriving Show

instance Holey Type where
  free (U _) = IntSet.empty
  free (t1 :=: t2) = IntSet.union (free t1) (free t2)
  free (Σ t1 t2) = IntSet.union (free t1) (free t2)
  free (Π t1 t2) = IntSet.union (free t1) (free t2)
  free (Dep _) = IntSet.empty
  free (TV v) = IntSet.singleton v

instance Inf Type Type where
  apply _ x@(U _) = x
  apply s (t1 :=: t2) = apply s t1 :=: apply s t2
  apply s (Σ t1 t2) = Σ (apply s t1) (apply s t2)
  apply s (Π t1 t2) = Π (apply s t1) (apply s t2)
  apply _ x@(Dep _) = x
  apply (Subst m) (TV v) = case IntMap.lookup v m of
    Just x -> x -- TODO should we apply subst m x?
    Nothing -> TV v

instance Inferable Type Expr where
  unify :: Type -> Type -> TI (Subst Type)
  unify (U u1) (U u2) | u1 == u2  = return emptySubst
                      | otherwise = err "Different universe levels"
  unify (a1 :=: a2) (b1 :=: b2) = (<>)
    <$> unify @Type @Expr a1 b1
    <*> unify @Type @Expr a2 b2
  unify (Σ a1 a2) (Σ b1 b2) = (<>)
    <$> unify @Type @Expr a1 b1
    <*> unify @Type @Expr a2 b2
  unify (Π a1 a2) (Π b1 b2) = (<>)
    <$> unify @Type @Expr a1 b1
    <*> unify @Type @Expr a2 b2
  unify (Dep _) (Dep _) = return emptySubst -- TODO here we'd need to execute and compare
  unify (TV v) y = return $ singleSubst v y
  unify x (TV v) = return $ singleSubst v x
  unify x y = err $ "Types do not unify: " ++ show x ++ ", " ++ show y

  infer :: TypeEnv Type -> Expr -> TI (Subst Type, Type)
  infer env (App e1 e2) = do
    tv <- TV <$> newTyVar
    (s1, t1) <- infer env e1
    (s2, t2) <- infer (apply s1 env) e2
    s3 <- unify @Type @Expr (apply s2 t1) (Π t2 tv)
    return (s3 <> s2 <> s1, apply s3 tv)
  infer env (Refl e) = do
    (s, t) <- infer env e
    return (s, t :=: t)
  infer env (e1 :&: e2) = do
    (s1, t1) <- infer env e1
    (s2, t2) <- infer (apply s1 env) e2
    return (s2 <> s1, Σ t1 t2)
  infer (TypeEnv i env) (Abs e) = do
    tv <- TV <$> newTyVar
    let env' = TypeEnv (i+1) $ Scheme IntSet.empty tv : env
    (s1, t1) <- infer env' e
    return (s1, Π (apply s1 tv) t1)
  infer (TypeEnv _ env) (Var (DBIndex i)) = do
    t <- instantiate (env !! i) TV
    return (emptySubst, t)

-- TODO impl show by hand
