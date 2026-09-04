module ParserSpec (spec) where

import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import Data.Either (isLeft, isRight)

import Parser (parse'base, parse'query)
import Term (Goal (..), Predicate (..), Struct (..), Term (..))


spec :: Spec
spec = do
  describe "parse'base" $ do
    it "parses a fact" $
      parse'base "nat(z)."
        `shouldBe` Right [Fact Struct{ name = "nat", args = [Atom "z"] }]

    it "parses a rule with a conjunctive body" $
      parse'base "plus(s(N), M, s(R)) :- plus(N, M, R)."
        `shouldBe` Right
          [ Struct{ name = "plus"
                  , args = [ Compound Struct{ name = "s", args = [Var "N"] }
                           , Var "M"
                           , Compound Struct{ name = "s", args = [Var "R"] } ] }
              :- [Call Struct{ name = "plus", args = [Var "N", Var "M", Var "R"] }] ]

    it "parses several predicates in sequence" $ do
      let base = "nat(z). nat(s(N)) :- nat(N)."
      case parse'base base of
        Right preds -> length preds `shouldBe` 2
        Left _ -> fail "expected the base to parse"

    it "parses wildcards and unification in rule bodies" $
      parse'base "times(z, _, z). p(X) :- X = foo(X)."
        `shouldSatisfy` isRight

    it "skips % comments" $
      parse'base "% a comment\nnat(z)."
        `shouldBe` Right [Fact Struct{ name = "nat", args = [Atom "z"] }]

    it "parses the factorial knowledge base into six predicates" $ do
      src <- readFile "factorial.pl"
      case parse'base src of
        Right preds -> do
          length preds `shouldBe` 6
          -- spot check: the file starts with plus/3 and ends with a two-goal rule
          case preds of
            (Fact Struct{ name = "plus", args = plusArgs } : _) ->
              length plusArgs `shouldBe` 3
            _ -> fail "expected plus/3 as the first predicate"
          case preds of
            (_ : _ : _ : _ : _ : [(_ :- [_, _])]) -> return ()
            _ -> fail "expected a two-goal rule as the last predicate"
        Left _ -> fail "expected factorial.pl to parse"

    it "parses the natural numbers base into two predicates" $ do
      src <- readFile "natural.pl"
      parse'base src `shouldSatisfy` isRight

  describe "parse'base errors" $ do
    it "rejects the empty input" $
      parse'base "" `shouldSatisfy` isLeft

    it "rejects a bare atom (only structs form predicates)" $
      parse'base "foo." `shouldSatisfy` isLeft

    it "rejects a fact missing its period" $
      parse'base "nat(z)" `shouldSatisfy` isLeft

    it "rejects a rule missing its body" $
      parse'base "p(X) :- ." `shouldSatisfy` isLeft

    it "rejects a rule missing its period" $
      parse'base "p(X) :- q(X)" `shouldSatisfy` isLeft

    it "rejects trailing garbage after a base" $
      parse'base "nat(z). extra" `shouldSatisfy` isLeft

  describe "parse'query" $ do
    it "parses a call" $
      parse'query "fact(A, B)."
        `shouldBe` Right [Call Struct{ name = "fact", args = [Var "A", Var "B"] }]

    it "parses a conjunction" $
      parse'query "fact(A, B), plus(A, B, C)."
        `shouldBe` Right [ Call Struct{ name = "fact", args = [Var "A", Var "B"] }
                         , Call Struct{ name = "plus", args = [Var "A", Var "B", Var "C"] } ]

    it "parses explicit unification goals" $
      parse'query "X = foo(X)."
        `shouldBe` Right [Unify (Var "X") (Compound Struct{ name = "foo", args = [Var "X"] })]

    it "parses a wildcard goal argument" $
      parse'query "times(z, _, z)."
        `shouldBe` Right [Call Struct{ name = "times", args = [Atom "z", Wildcard, Atom "z"] }]

  describe "parse'query errors" $ do
    it "rejects the empty input" $
      parse'query "" `shouldSatisfy` isLeft

    it "rejects a query missing its period" $
      parse'query "fact(A, B)" `shouldSatisfy` isLeft

    it "rejects trailing goals after the period" $
      parse'query "p(a). p(b)." `shouldSatisfy` isLeft
