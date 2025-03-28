module Lib where

import Data.Functor (($>))
import Data.Functor.Identity (Identity(runIdentity))

import AST
import DeBrujin


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

-- >>> runInference @Type @Expr emptyEnv example2
-- Right (Π (TV 0) (Π (TV 1) (TV 1)))
