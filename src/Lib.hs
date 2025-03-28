{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleContexts #-}
module Lib
    ( someFunc
    ) where

import Control.Monad.Trans.State.Strict (StateT (runStateT), get, modify)
import Data.List (findIndex)
import Data.Functor.Identity (Identity (runIdentity))
import Data.Functor (($>))
import Inference (Inf (apply), Holey (free), Inferable (unify, infer), TyVar, Subst (Subst), emptySubst, err, singleSubst, TI, TypeEnv (TypeEnv), runInference, emptyEnv, newTyVar, Scheme (Scheme), instantiate)

import qualified Data.IntSet as IntSet

import qualified Data.IntMap.Strict as IntMap

someFunc :: IO ()
someFunc = putStrLn "someFunc"

newtype DBIndex = DBIndex Int
 deriving Show

newtype DeBrujin_T a m x = DeBrujin_T (StateT (Int, [a]) m x)
 deriving (Functor, Applicative)

bind :: Monad m => a -> DeBrujin_T a m DBIndex
bind x = DeBrujin_T $ do
  (ix, _) <- get
  modify (\(i, ds) -> (i+1, x:ds))
  return $ DBIndex ix

reference :: (Monad m, Eq a) => a -> DeBrujin_T a m (Maybe DBIndex)
reference x = DeBrujin_T $ do
  (_, ds) <- get
  return $ DBIndex <$> findIndex (== x) ds


lookup :: Monad m => DBIndex -> DeBrujin_T a m a
lookup (DBIndex i) = DeBrujin_T $ do
  (_, ds) <- get
  return (ds !! (length ds - i - 1))


runDeBrujin :: Monad m => DeBrujin_T a m x -> m x
runDeBrujin (DeBrujin_T s) = fst <$> runStateT s (0, [])

type Qualifier = String

type DeBrujin a x = DeBrujin_T a Identity x

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

-- TODO impl show by hand

(??) :: Maybe a -> a -> a
Nothing ?? x = x
Just x ?? _ = x

example0 :: Expr
example0 = runIdentity . runDeBrujin $ bind "x" $> Abs <*> (Var . (?? undefined) <$> reference "x")

example1 :: Expr
example1 = runIdentity . runDeBrujin $ App
  <$> (bind "x" $> Abs <*> (Var . (?? undefined) <$> reference "x"))
  <*> (bind "y" $> Abs <*> (Var . (?? undefined) <$> reference "y"))

example2 :: Expr
example2 = runIdentity . runDeBrujin $
  bind "x" $> Abs <*> (bind "y" $> Abs <*> (Var . (?? undefined) <$> reference "x"))

example3 :: Expr
example3 = runIdentity . runDeBrujin $
  bind "x" $> Abs <*> (bind "y" $> Abs <*> (Var . (?? undefined) <$> reference "y"))

-- >>> example3
-- Abs (Abs (Var (DBIndex 0)))


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


-- ti env (EAbs n e) =
-- do tv ← newTyVar
-- let TypeEnv env ′ = remove env n
-- env ′′ = TypeEnv (env ′ ‘Map.union‘ (Map.singleton n (Scheme [ ] tv )))
-- (s1 , t1 ) ← ti env ′′ e
-- return (s1 , TFun (apply s1 tv ) t1 )

-- ti env (EApp e1 e2 ) =
-- do tv ← newTyVar
-- (s1 , t1 ) ← ti env e1
-- (s2 , t2 ) ← ti (apply s1 env ) e2
-- s3 ← mgu (apply s2 t1 ) (TFun t2 tv )
-- return (s3 ‘composeSubst‘ s2 ‘composeSubst‘ s1 , apply s3 tv )

-- >>> runInference @Type @Expr emptyEnv example2
-- Right (Π (TV 0) (Π (TV 1) (TV 1)))
