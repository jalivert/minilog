module EvalSpec (spec) where

import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import Data.Map.Strict qualified as Map

import Evaluate.State (Action (..), State (..))
import Evaluate.Step (step)
import Term (Struct (..), Term (..))

import EvalHelp (collectN, mkState, mustBase, mustQuery, solutionsOf)


isSearching :: Action State -> Bool
isSearching (Searching _) = True
isSearching _ = False


isSucceeded :: Action State -> Bool
isSucceeded (Succeeded _) = True
isSucceeded _ = False


requireSearching :: Action State -> IO State
requireSearching (Searching s) = return s
requireSearching other = fail ("expected Searching, got: " ++ show other)


-- Peano numerals: 0 is z, n+1 is s(n).
num :: Int -> Term
num n | n <= 0 = Atom "z"
      | otherwise = Compound Struct{ name = "s", args = [num (n - 1)] }


factorialBase :: String
factorialBase =
  "plus(z, N, N). \
  \plus(s(N), M, s(R)) :- plus(N, M, R). \
  \times(z, _, z). \
  \times(s(N), M, A) :- times(N, M, R), plus(R, M, A). \
  \fact(z, s(z)). \
  \fact(s(N), R) :- fact(N, PR), times(s(N), PR, R)."


spec :: Spec
spec = do
  describe "single step transitions" $ do
    it "is Done when both stacks are empty" $
      step State{ base = []
                , query'vars = Map.empty
                , backtracking'stack = []
                , goal'stack = []
                , position = 0
                , counter = 0 }
        `shouldBe` Done

    it "is Failed when a goal matches nothing and no backtracking remains" $ do
      let st = mkState [] (mustQuery "p(a).")
      step st `shouldBe` Failed

    it "is Searching after matching a fact" $
      let st = mkState (mustBase "p(a).") (mustQuery "p(a).")
      in step st `shouldSatisfy` isSearching

    it "is Succeeded at once for a zero-arity fact" $
      -- No unification goals remain, so there is nothing to search.
      let st = mkState (mustBase "raining.") (mustQuery "raining.")
      in step st `shouldSatisfy` isSucceeded

  describe "facts" $ do
    it "proves a ground fact" $
      solutionsOf "small(mouse)." "small(mouse)."
        `shouldBe` ([Map.empty], True)

    it "refutes a non-matching ground goal" $
      solutionsOf "small(mouse)." "small(dog)."
        `shouldBe` ([], True)

    it "refutes a goal with an unknown name" $
      solutionsOf "small(mouse)." "big(mouse)."
        `shouldBe` ([], True)

    it "refutes a goal with a wrong arity" $
      solutionsOf "small(mouse)." "small(mouse, mouse)."
        `shouldBe` ([], True)

    it "enumerates every matching fact via backtracking" $
      solutionsOf "p(a). p(b)." "p(X)."
        `shouldBe` ( [ Map.fromList [("X", Atom "a")]
                     , Map.fromList [("X", Atom "b")] ]
                   , True )

    it "restores choicepoints across conjunctions" $
      solutionsOf "p(a). p(b). q(c)." "p(X), q(Y)."
        `shouldBe` ( [ Map.fromList [("X", Atom "a"), ("Y", Atom "c")]
                     , Map.fromList [("X", Atom "b"), ("Y", Atom "c")] ]
                   , True )

  describe "rules" $ do
    it "proves a goal through a rule" $
      solutionsOf "q(a). p(X) :- q(X)." "p(X)."
        `shouldBe` ([Map.fromList [("X", Atom "a")]], True)

    it "joins conjunctions on the shared variable" $
      solutionsOf "p(a). p(b). q(b). q(c)." "p(X), q(X)."
        `shouldBe` ([Map.fromList [("X", Atom "b")]], True)

    it "fails the whole conjunction when one side fails" $
      solutionsOf "p(a). q(b)." "p(X), q(X)."
        `shouldBe` ([], True)

  describe "unification goals" $ do
    it "binds a variable without any base" $
      solutionsOf "" "X = a."
        `shouldBe` ([Map.fromList [("X", Atom "a")]], True)

    it "refutes distinct atoms" $
      solutionsOf "" "a = b."
        `shouldBe` ([], True)

    it "decomposes nested compounds" $
      solutionsOf "" "foo(a, X) = foo(Y, b)."
        `shouldBe` ( [ Map.fromList [("X", Atom "b"), ("Y", Atom "a")] ]
                   , True )

    it "lets a wildcard match anything" $ do
      solutionsOf "p(a, b)." "p(_, b)." `shouldBe` ([Map.empty], True)
      solutionsOf "p(a, b)." "p(_, c)." `shouldBe` ([], True)

    it "rejects infinite terms (occurs check)" $
      -- Prolog succeeds here; Minilog must not.
      solutionsOf "" "X = foo(X)."
        `shouldBe` ([], True)

  describe "backtracking protocol" $ do
    it "offers Redoing while choicepoints remain" $ do
      let st = mkState (mustBase "p(a). p(b).") (mustQuery "p(X).")
          (sols, _done) = collectN 1000 1 st
      sols `shouldBe` [Map.fromList [("X", Atom "a")]]

    it "reports Done after the last solution" $
      solutionsOf "p(a)." "p(X)."
        `shouldBe` ([Map.fromList [("X", Atom "a")]], True)

    it "walks Searching, Succeeded for a one-fact query" $ do
      -- Unifying the last goal empties the goal stack, so the second
      -- step succeeds outright instead of searching further.
      let st = mkState (mustBase "p(a).") (mustQuery "p(X).")
      st1 <- requireSearching (step st)
      step st1 `shouldSatisfy` isSucceeded

  describe "Peano arithmetic (factorial.pl)" $ do
    it "proves a ground addition" $
      solutionsOf factorialBase "plus(s(z), s(z), s(s(z)))."
        `shouldBe` ([Map.empty], True)

    it "computes an addition" $
      solutionsOf factorialBase "plus(z, s(z), X)."
        `shouldBe` ([Map.fromList [("X", num 1)]], True)

    it "computes 2 * 2 = 4" $
      solutionsOf factorialBase "times(s(s(z)), s(s(z)), X)."
        `shouldBe` ([Map.fromList [("X", num 4)]], True)

    it "computes factorial of 2" $
      solutionsOf factorialBase "fact(s(s(z)), X)."
        `shouldBe` ([Map.fromList [("X", num 2)]], True)

    it "proves factorial of 3 is 6" $
      solutionsOf factorialBase "fact(s(s(s(z))), s(s(s(s(s(s(z)))))))."
        `shouldBe` ([Map.empty], True)

    it "finds the README example solution as its first answer" $ do
      -- ?- fact(A, B), plus(A, B, s(s(z))).
      -- The only small solution is A = 1, B = 1; the search space past
      -- it is infinite, so we only take the first solution.
      let st = mkState (mustBase factorialBase)
                       (mustQuery "fact(A, B), plus(A, B, s(s(z))).")
          (sols, _done) = collectN 10000 1 st
      sols `shouldBe` [Map.fromList [("A", num 1), ("B", num 1)]]

    it "binds the first answer of plus(A, B, B) to z" $ do
      -- The full solution stream diverges (see the write-up), but the
      -- first answer is A = z with B still free.
      let st = mkState (mustBase factorialBase) (mustQuery "plus(A, B, B).")
          (sols, _done) = collectN 1000 1 st
      case sols of
        [sol] -> do
          Map.lookup "A" sol `shouldBe` Just (Atom "z")
          case Map.lookup "B" sol of
            Just (Var _) -> return ()
            other -> fail ("expected B to stay free, got: " ++ show other)
        _ -> fail ("expected exactly one solution, got: " ++ show sols)

  describe "zero-arity structs" $ do
    it "proves a bare fact" $
      solutionsOf "raining." "raining."
        `shouldBe` ([Map.empty], True)

    it "refutes an absent bare fact" $
      solutionsOf "raining." "sunny."
        `shouldBe` ([], True)

    it "proves through a rule with bare atoms" $
      solutionsOf "sunny. raining :- sunny." "raining."
        `shouldBe` ([Map.empty], True)

    it "fails a bare rule when its body fails" $
      solutionsOf "raining :- sunny." "raining."
        `shouldBe` ([], True)

    it "conjoins bare atoms" $
      solutionsOf "sunny. warm. nice :- sunny, warm." "nice."
        `shouldBe` ([Map.empty], True)

    it "distinguishes zero arity from other arities" $ do
      solutionsOf "p(a)." "p." `shouldBe` ([], True)
      solutionsOf "p." "p(a)." `shouldBe` ([], True)

    it "queries an empty base and fails" $
      solutionsOf "" "p(a)."
        `shouldBe` ([], True)

  describe "natural numbers (natural.pl)" $ do
    it "proves a ground numeral" $
      solutionsOf "nat(z). nat(s(N)) :- nat(N)." "nat(s(s(z)))."
        `shouldBe` ([Map.empty], True)

    it "answers the first enumeration with z" $ do
      let st = mkState (mustBase "nat(z). nat(s(N)) :- nat(N).") (mustQuery "nat(X).")
          (sols, _done) = collectN 1000 1 st
      sols `shouldBe` [Map.fromList [("X", Atom "z")]]
