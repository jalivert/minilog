-- | Shared driver for end-to-end evaluation tests.
--
-- 'mkState' mirrors @set'goal@/@load'base@ from @app/Main.hs@: query
-- variables start unbound (each mapped to itself) and both stacks start
-- empty. 'collectN' pumps 'Evaluate.Step.step' the same way
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
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

import Evaluate.State (Action (..), State (..))
import Evaluate.Step (step)
import Parser (parse'base, parse'query)
import Term (Goal (..), Predicate, Struct (..), Term (..))


-- | Build the initial machine state for a base and a query.
mkState :: [Predicate] -> [Goal] -> State
mkState base goals =
  State { base = base
        , query'vars = Map.fromList q'vars
        , backtracking'stack = []
        , goal'stack = goals
        , position = 0
        , counter = 0 }
  where
    free'names :: [String]
    free'names = Set.toList (free'vars'in'query goals)

    q'vars = [(name, Var name) | name <- free'names]


-- | Parse a knowledge base source, crashing on failure (a parse failure
-- here is a bug in the test itself, not in the code under test).
-- The empty source denotes the empty base: the grammar itself has no
-- production for it (see the 'rejects the empty input' parser test), so
-- the helper maps it explicitly instead of working around it at every
-- call site.
mustBase :: String -> [Predicate]
mustBase "" = []
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
collectN :: Int -> Int -> State -> ([Map String Term], Bool)
collectN fuel maxSols state = go fuel maxSols state []
  where
    go fuel' _ _ acc | fuel' <= 0 = (reverse acc, False)
    go _ 0 _ acc = (reverse acc, False)
    go fuel' n s acc = case step s of
      Failed -> (reverse acc, True)
      Done -> (reverse acc, True)
      Searching s' -> go (fuel' - 1) n s' acc
      Redoing s' -> go (fuel' - 1) n s' acc
      Succeeded s' ->
        let found = query'vars s' : acc
        in case step s' of
             Done -> (reverse found, True)
             Redoing s'' -> go (fuel' - 2) (n - 1) s'' found
             -- Unreachable: a 'Succeeded' state has an empty goal stack,
             -- so 'step' can only answer 'Done' or 'Redoing'.
             _ -> (reverse found, False)


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
