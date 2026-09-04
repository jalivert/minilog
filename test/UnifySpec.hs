module UnifySpec (spec) where

import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import Data.Map.Strict qualified as Map
import Data.Maybe (isJust, isNothing)

import Evaluate.Step (occurs, rename'all, rename'both, unify)
import Term (Goal (..), Struct (..), Term (..))


noGoals :: [Goal]
noGoals = []

noVars :: Map.Map String Term
noVars = Map.empty


spec :: Spec
spec = do
  describe "unify: delete" $ do
    it "unifies identical atoms" $
      unify (Atom "a", Atom "a") noGoals noVars
        `shouldBe` Just (noGoals, noVars)

    it "unifies a wildcard with anything" $
      unify (Wildcard, Compound Struct{ name = "foo", args = [Atom "a"] }) noGoals noVars
        `shouldBe` Just (noGoals, noVars)

    it "unifies anything with a wildcard" $
      unify (Var "X", Wildcard) [Call Struct{ name = "p", args = [Var "X"] }] noVars
        `shouldBe` Just ([Call Struct{ name = "p", args = [Var "X"] }], noVars)

    it "unifies a variable with itself" $
      unify (Var "X", Var "X") noGoals noVars
        `shouldBe` Just (noGoals, noVars)

  describe "unify: conflict" $ do
    it "rejects distinct atoms" $
      unify (Atom "a", Atom "b") noGoals noVars
        `shouldSatisfy` isNothing

    it "rejects structs with distinct names" $
      unify ( Compound Struct{ name = "foo", args = [Atom "a"] }
            , Compound Struct{ name = "bar", args = [Atom "a"] })
            noGoals noVars
        `shouldSatisfy` isNothing

    it "rejects structs with distinct arities" $
      unify ( Compound Struct{ name = "foo", args = [Atom "a"] }
            , Compound Struct{ name = "foo", args = [Atom "a", Atom "b"] })
            noGoals noVars
        `shouldSatisfy` isNothing

    it "rejects an atom against a compound" $
      unify (Atom "a", Compound Struct{ name = "a", args = [] }) noGoals noVars
        `shouldSatisfy` isNothing

  describe "unify: decompose" $ do
    it "breaks matching structs into pairwise argument goals" $
      unify ( Compound Struct{ name = "foo", args = [Atom "a", Var "X"] }
            , Compound Struct{ name = "foo", args = [Var "Y", Atom "b"] })
            noGoals noVars
        `shouldBe` Just ( [Unify (Atom "a") (Var "Y"), Unify (Var "X") (Atom "b")]
                        , noVars )

  describe "unify: eliminate and swap" $ do
    it "binds a variable and substitutes it in the remaining goals" $
      unify (Var "X", Atom "a")
            [Call Struct{ name = "p", args = [Var "X", Var "Y"] }]
            (Map.fromList [("X", Var "X"), ("Y", Var "Y")])
        `shouldBe` Just ( [Call Struct{ name = "p", args = [Atom "a", Var "Y"] }]
                        , Map.fromList [("X", Atom "a"), ("Y", Var "Y")] )

    it "handles a variable on the right via swap" $
      unify (Atom "a", Var "X") noGoals (Map.fromList [("X", Var "X")])
        `shouldBe` unify (Var "X", Atom "a") noGoals (Map.fromList [("X", Var "X")])

    it "swap result binds the variable" $
      unify (Atom "a", Var "X") noGoals (Map.fromList [("X", Var "X")])
        `shouldBe` Just (noGoals, Map.fromList [("X", Atom "a")])

  describe "unify: occurs check" $ do
    it "rejects X = foo(X)" $
      unify (Var "X", Compound Struct{ name = "foo", args = [Var "X"] }) noGoals noVars
        `shouldSatisfy` isNothing

    it "rejects a deeply nested occurrence" $
      unify (Var "X", Compound Struct{ name = "foo", args = [Compound Struct{ name = "bar", args = [Var "X"] }] })
            noGoals noVars
        `shouldSatisfy` isNothing

    it "accepts distinct variables" $
      unify (Var "X", Compound Struct{ name = "foo", args = [Var "Y"] }) noGoals noVars
        `shouldSatisfy` isJust

  describe "occurs" $ do
    it "finds the variable itself" $
      occurs "X" (Var "X") `shouldBe` True

    it "ignores other variables" $
      occurs "X" (Var "Y") `shouldBe` False

    it "ignores atoms" $
      occurs "X" (Atom "a") `shouldBe` False

    it "ignores wildcards" $
      occurs "X" Wildcard `shouldBe` False

    it "searches compound arguments recursively" $
      occurs "X" (Compound Struct{ name = "f", args = [Atom "a", Compound Struct{ name = "g", args = [Var "X"] }] })
        `shouldBe` True

    it "reports absence in compounds" $
      occurs "X" (Compound Struct{ name = "f", args = [Atom "a", Var "Y"] })
        `shouldBe` False

  describe "rename'all" $ do
    it "renames every distinct variable to a fresh name" $ do
      let (counter', renamed) = rename'all [Var "X", Atom "a", Wildcard] 0
      counter' `shouldBe` 1
      renamed `shouldBe` [Var "_0", Atom "a", Wildcard]

    it "maps repeated variables to the same fresh name" $ do
      let (counter', renamed) = rename'all [Var "X", Var "X", Var "Y"] 0
      counter' `shouldBe` 2
      renamed `shouldBe` [Var "_0", Var "_0", Var "_1"]

    it "renames inside compounds" $ do
      let (_, renamed) = rename'all [Compound Struct{ name = "f", args = [Var "X", Var "X"] }] 5
      renamed `shouldBe` [Compound Struct{ name = "f", args = [Var "_5", Var "_5"] }]

  describe "rename'both" $ do
    it "shares the renaming between a rule head and its body" $ do
      let patterns = [Compound Struct{ name = "s", args = [Var "N"] }, Var "M"]
          body = [Call Struct{ name = "plus", args = [Var "N", Var "M", Var "R"] }]
          (counter', patterns', body') = rename'both patterns body 0
      counter' `shouldBe` 3
      patterns' `shouldBe` [Compound Struct{ name = "s", args = [Var "_0"] }, Var "_1"]
      body' `shouldBe` [Call Struct{ name = "plus", args = [Var "_0", Var "_1", Var "_2"] }]
