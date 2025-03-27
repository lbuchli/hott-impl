{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
module Lib
    ( someFunc
    ) where

import Control.Monad.Trans.State.Strict (StateT (runStateT), get, modify)
import Data.List (findIndex)
import Data.Functor.Identity (Identity (runIdentity))
import Data.Functor (($>))

someFunc :: IO ()
someFunc = putStrLn "someFunc"

newtype DBIndex = DBIndex Int
 deriving Show

newtype TyVar = TyVar Int
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
