{-# LANGUAGE TypeApplications #-}
import Test.Hspec
import Test.QuickCheck

import Data.Functor (($>))
import Data.Functor.Identity (Identity(runIdentity))

import AST
import DeBrujin
import Inference

(??) :: Maybe a -> a -> a
Nothing ?? x = x
Just x ?? _ = x

ex_id :: Expr
ex_id = runIdentity . runDeBrujin $ bind "x" $> Abs <*> (Var . (?? undefined) <$> reference "x")

ex_id_id :: Expr
ex_id_id = runIdentity . runDeBrujin $ App
  <$> (bind "x" $> Abs <*> (Var . (?? undefined) <$> reference "x"))
  <*> (bind "y" $> Abs <*> (Var . (?? undefined) <$> reference "y"))

ex_const :: Expr
ex_const = runIdentity . runDeBrujin $
  bind "x" $> Abs <*> (bind "y" $> Abs <*> (Var . (?? undefined) <$> reference "x"))

ex_seq :: Expr
ex_seq = runIdentity . runDeBrujin $
  bind "x" $> Abs <*> (bind "y" $> Abs <*> (Var . (?? undefined) <$> reference "y"))

main :: IO ()
main = hspec $ do
  describe "DeBrujin" $ do
    it "λx.x => λ0" $ do
      ex_id `shouldBe` Abs (Var $ DBIndex 0)
    it "(λx.x) (λy.y) => (λ0) (λ0)" $ do
      ex_id_id `shouldBe` App (Abs (Var $ DBIndex 0)) (Abs (Var $ DBIndex 0))
    it "(λx.λy.x) => λλ1" $ do
      ex_const `shouldBe` Abs (Abs (Var $ DBIndex 1))
    it "(λx.λy.y) => λλ0" $ do
      ex_seq `shouldBe` Abs (Abs (Var $ DBIndex 0))
  describe "Inference" $ do
    it "λx.x : Πa.a" $ do
      runInference @Type @Expr emptyEnv ex_id `shouldBe` Right (Π (TV 0) (TV 0))
    it "(λx.x) (λy.y) : Πa.a" $ do
      runInference @Type @Expr emptyEnv ex_id_id `shouldBe` Right (Π (TV 0) (TV 0))
    it "(λx.λy.x) : Πa.Πb.a" $ do
      runInference @Type @Expr emptyEnv ex_const `shouldBe` Right (Π (TV 0) (Π (TV 1) (TV 0)))
    it "(λx.λy.y) : Πa.Πb.b" $ do
      runInference @Type @Expr emptyEnv ex_seq `shouldBe` Right (Π (TV 0) (Π (TV 1) (TV 1)))
