-- | Shared driver for end-to-end evaluation tests.
--
-- 'mkState' mirrors @start'query@ from @app/Main.hs@: query variables
-- start unbound (each mapped to itself) and both stacks start empty.
-- 'collectN' pumps 'Evaluate.Step.step'/'resume' the same way
-- @try'to'prove@ in @app/Main.hs@ does, but purely, collecting every
-- solution instead of interacting with the user.
module EvalHelp
  ( mkState
  , mustBase
  , mustQuery
  , collectN
  , solutionsOf
  ) where

import Data.List (foldl')
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

import Evaluate.State (Processing (..), StepResult (..))
import Evaluate.Step (resume, step)
import Parser (parse'base, parse'query)
import Term (Goal (..), Predicate, Struct (..), Term (..))


-- | Build the initial machine state for a base and a query.
mkState :: [Predicate] -> [Goal] -> Processing
mkState base goals =
  case goals of
    -- Unreachable: the query grammar always yields at least one goal.
    [] -> error "mkState: empty goal list"
    (goal : rest) ->
      Processing { base = base
                 , query'vars = Map.fromList q'vars
                 , backtracking'stack = []
                 , goal'stack = goal :| rest
                 , position = 0
                 , counter = 0 }
  where
    free'names :: [String]
    free'names = Set.toList (free'vars'in'query goals)

    q'vars = [(name, Var name) | name <- free'names]


-- | Parse a knowledge base source, crashing on failure (a parse failure
-- here is a bug in the test itself, not in the code under test).
mustBase :: String -> [Predicate]
mustBase src = case parse'base src of
  Left (err, _) -> error ("mustBase: " ++ err)
  Right base -> base


-- | Parse a query source, crashing on failure (see 'mustBase').
mustQuery :: String -> [Goal]
mustQuery src = case parse'query src of
  Left (err, _) -> error ("mustQuery: " ++ err)
  Right goals -> goals


-- | Drive the machine, collecting solutions.
--
-- @collectN fuel maxSols state@ returns the solutions found (bindings of
-- the query variables, oldest first) and whether the search ran to
-- completion ('True') or stopped early ('False', fuel exhausted or the
-- solution cap reached). The cap exists because some queries diverge by
-- design (depth-first search over an infinite proof space); those tests
-- assert on a prefix of the solution stream.
collectN :: Int -> Int -> Processing -> ([Map String Term], Bool)
collectN fuel maxSols proc = go fuel maxSols proc []
  where
    go fuel' _ _ acc | fuel' <= 0 = (reverse acc, False)
    go _ 0 _ acc = (reverse acc, False)
    go fuel' n p acc = case step p of
      Searching p' -> go (fuel' - 1) n p' acc
      DeadEnd stalled ->
        case resume stalled of
          Nothing -> (reverse acc, True)
          Just p' -> go (fuel' - 1) n p' acc
      Solved q'vars stalled ->
        let found = q'vars : acc
        in case resume stalled of
             Nothing -> (reverse found, True)
             Just p' -> go (fuel' - 2) (n - 1) p' found


-- | Parse the base and query sources and collect every solution.
-- Fails the assumption (via 'error') if either source does not parse.
solutionsOf :: String -> String -> ([Map String Term], Bool)
solutionsOf baseSrc querySrc =
  collectN 10000 maxBound (mkState (mustBase baseSrc) (mustQuery querySrc))


-- The free-variable helpers below mirror app/Main.hs.

free'vars'in'query :: [Goal] -> Set.Set String
free'vars'in'query goals =
  foldl' (\set g -> set `Set.union` free'vars'in'goal g) Set.empty goals


free'vars'in'goal :: Goal -> Set.Set String
free'vars'in'goal (Call fun) = free'vars'in'functor fun
free'vars'in'goal (Unify val'l val'r) =
  Set.union (free'vars'in'val val'l) (free'vars'in'val val'r)


free'vars'in'functor :: Struct -> Set.Set String
free'vars'in'functor Struct{ args } =
  foldl' (\set g -> set `Set.union` free'vars'in'val g) Set.empty args


free'vars'in'val :: Term -> Set.Set String
free'vars'in'val (Var name) = Set.singleton name
free'vars'in'val (Atom _) = Set.empty
free'vars'in'val (Compound fun) = free'vars'in'functor fun
free'vars'in'val Wildcard = Set.empty
