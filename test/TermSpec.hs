module TermSpec (spec) where

import Test.Hspec (Spec, describe, it, shouldBe)

import Term (Goal (..), Predicate (..), Struct (..), Term (..))


spec :: Spec
spec = do
  describe "Show Term" $ do
    it "prints variables by name" $
      show (Var "X") `shouldBe` "X"

    it "prints atoms by name" $
      show (Atom "foo") `shouldBe` "foo"

    it "prints the wildcard as _" $
      show Wildcard `shouldBe` "_"

    it "prints compounds as name(arg, ...)" $
      show (Compound Struct{ name = "foo", args = [Atom "a", Var "X"] })
        `shouldBe` "foo(a, X)"

    it "prints nested compounds inside out" $
      show (Compound Struct{ name = "s", args = [Compound Struct{ name = "s", args = [Atom "z"] }] })
        `shouldBe` "s(s(z))"

  describe "Show Struct" $ do
    it "joins arguments with a comma and a space" $
      show Struct{ name = "plus", args = [Atom "z", Var "N", Var "N"] }
        `shouldBe` "plus(z, N, N)"

    it "prints a zero-arity struct as a bare name" $
      show Struct{ name = "raining", args = [] }
        `shouldBe` "raining"

    it "prints a zero-arity fact without parentheses" $
      show (Fact Struct{ name = "raining", args = [] })
        `shouldBe` "raining."

  describe "Show Goal" $ do
    it "prints calls like structs" $
      show (Call Struct{ name = "p", args = [Var "X"] })
        `shouldBe` "p(X)"

    it "prints unification with = between the terms" $
      show (Unify (Var "X") (Compound Struct{ name = "foo", args = [Var "X"] }))
        `shouldBe` "X = foo(X)"

  describe "Show Predicate" $ do
    it "terminates facts with a period" $
      show (Fact Struct{ name = "nat", args = [Atom "z"] })
        `shouldBe` "nat(z)."

    it "prints rules with :- and a comma-separated body" $
      show (Struct{ name = "plus", args = [Compound Struct{ name = "s", args = [Var "N"] }, Var "M", Compound Struct{ name = "s", args = [Var "R"] }] }
              :- [Call Struct{ name = "plus", args = [Var "N", Var "M", Var "R"] }])
        `shouldBe` "plus(s(N), M, s(R)) :- plus(N, M, R)."

  describe "Eq" $ do
    it "distinguishes variables from atoms with the same name" $
      (Var "x" == Atom "x") `shouldBe` False

    it "distinguishes the wildcard from a variable" $
      (Wildcard == Var "_") `shouldBe` False

    it "compares structs structurally" $
      (Struct{ name = "f", args = [Atom "a"] } == Struct{ name = "f", args = [Atom "b"] })
        `shouldBe` False
