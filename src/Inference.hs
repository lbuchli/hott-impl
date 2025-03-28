{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Inference where

-- This is heavily inspired/copied from https://github.com/mgrabmueller/AlgorithmW/blob/master/pdf/AlgorithmW.pdf

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap

import Data.IntSet (IntSet, (\\))
import qualified Data.IntSet as IntSet

import Control.Monad.Trans.Except (ExceptT, runExceptT, throwE)
import Control.Monad.Trans.State (State, runState, get, put)
import Control.Monad.Trans.Class (MonadTrans(lift))

type TyVar = Int

newtype Subst a = Subst (IntMap a)

emptySubst :: Subst a
emptySubst = Subst $ IntMap.empty

singleSubst :: TyVar -> a -> Subst a
singleSubst v = Subst . IntMap.singleton v

class Holey a where
  free :: a -> IntSet

class Holey a => Inf t a where
  apply :: Subst t -> a -> a

instance Inf t t => Semigroup (Subst t) where
  (<>) :: Subst t -> Subst t -> Subst t
  (Subst s1) <> (Subst s2) = Subst $ (IntMap.map (apply $ Subst s1) s2) `IntMap.union` s1

instance Inf t t => Monoid (Subst t) where
  mempty :: Subst t
  mempty = Subst $ IntMap.empty

data Scheme a = Scheme IntSet a

instance Holey a => Holey (Scheme a) where
  free (Scheme vs t) = free t \\ vs

instance Inf t t => Inf t (Scheme t) where
  apply (Subst s) (Scheme vs t) = Scheme vs (apply (Subst $ IntMap.withoutKeys s vs) t)

instance Holey a => Holey [a] where
  free xs = IntSet.unions (map free xs)

instance Inf t t => Inf t [t] where
  apply s = map (apply s)

-- De Brujin TypeEnv
data TypeEnv a = TypeEnv Int [Scheme a]

emptyEnv :: TypeEnv a
emptyEnv = TypeEnv 0 []

instance Holey a => Holey (TypeEnv a) where
  free (TypeEnv _ env) = free env

instance Inf t t => Inf t (TypeEnv t) where
  apply s (TypeEnv i env) = TypeEnv i (map (apply s) env)

generalize :: Holey t => TypeEnv t -> t -> Scheme t
generalize env t = Scheme vs t
  where vs = free t \\ free env

-------------------------------------------------------------------------------
--                             Inference context                             --
-------------------------------------------------------------------------------

type TIState = Int
newtype TI a = TI (ExceptT String (State TIState) a)
 deriving (Functor, Applicative, Monad)

runTI :: TI a -> (Either String a, TIState)
runTI (TI t) = runState (runExceptT t) initTIState
  where initTIState = 0

newTyVar :: TI TyVar
newTyVar = TI . lift $ do
  s <- get
  put (s + 1)
  return s

instantiate :: Inf t t => Scheme t -> (TyVar -> t) -> TI t
instantiate (Scheme vs t) varc = do
  s <- Subst <$> sequenceA (IntMap.fromSet (\_ -> varc <$> newTyVar) vs)
  return $ apply s t

err :: String -> TI t
err msg = TI $ throwE msg

-------------------------------------------------------------------------------
--                            Implementation Guide                           --
-------------------------------------------------------------------------------

-- where: t -> type
--        x -> expression
class Inf t t => Inferable t x where
  unify :: t -> t -> TI (Subst t)
  infer :: TypeEnv t -> x -> TI (Subst t, t)

runInference :: Inferable t x => TypeEnv t -> x -> Either String t
runInference env e = fst . runTI $ do
  (s, t) <- infer env e
  return (apply s t)
