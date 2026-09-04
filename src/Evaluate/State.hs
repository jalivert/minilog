module Evaluate.State where

import Data.List.NonEmpty ( NonEmpty )
import Data.Map.Strict qualified as Map

import Term ( Goal, Term, Predicate )


{-  The search is either still running (with goals to prove) or stalled
    (with the goal stack empty). The two shapes are distinct types, so
    `step` only ever sees a non-empty goal stack and the "what now?"
    bookkeeping lives in `resume` instead of in the caller's head. -}

-- | The search is still under way: goals remain to be proved.
data Processing = Processing
  { base :: ![Predicate] -- knowledge base
  , query'vars :: !(Map.Map String Term)  -- the variables from the query
  , backtracking'stack :: ![(NonEmpty Goal, Int, Map.Map String Term)]
    -- a stack of things to try when the current
    -- goal fails or succeeds

  , goal'stack :: !(NonEmpty Goal)  -- goals to satisfy
  , position :: !Int -- position in the base

  , counter :: !Int } -- for renaming variables
  deriving (Eq, Show)


-- | The goal stack ran out. Holds everything the search needs to pick
-- up from the backtracking stack, if anything remains to try.
data Stalled = Stalled
  { base'stalled :: ![Predicate]
  , backtracking'stack'stalled :: ![(NonEmpty Goal, Int, Map.Map String Term)]
  , counter'stalled :: !Int }
  deriving (Eq, Show)


-- | The outcome of a single step: more work, a solution, or a dead end.
-- There is deliberately no "done" here: whether a stalled search is
-- over is decided by `resume`, not by `step`.
data StepResult
  = Searching !Processing
  | Solved !(Map.Map String Term) !Stalled
  | DeadEnd !Stalled
  deriving (Eq, Show)


{-  A whole search is just a loop over the two functions in
    `Evaluate.Step`:

      drive proc = case step proc of
        Searching proc' -> drive proc'
        DeadEnd stalled -> case resume stalled of
          Nothing    -> failed (nothing remains to try)
          Just proc' -> drive proc'
        Solved bindings stalled -> report bindings, then resume like above
-}
