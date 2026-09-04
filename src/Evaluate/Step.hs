module Evaluate.Step where

import Data.List ( mapAccumL )
import Data.List.NonEmpty ( NonEmpty(..) )
import Data.Map.Strict qualified as Map


import Evaluate.State ( Processing(..), Stalled(..), StepResult(..) )

import Term ( Predicate(..), Struct(..), Term(..), Goal(..) )


-- | One step of a running search. Only the goal on top of the stack
-- is examined:
--   * a predicate call looks for a matching fact or rule in the base,
--     renames its variables to fresh ones (so separate uses never clash),
--     remembers where to keep looking (the backtracking record), and turns
--     the match into unification goals in front of the remaining goals;
--   * a unification either substitutes a variable everywhere and carries
--     on, or kills the current path (`DeadEnd`).
-- When no goals are left behind, the solution is reported (`Solved`).
step :: Processing -> StepResult
{-  PROVE CALL  -}
step proc@Processing{ base
                    , backtracking'stack
                    , goal'stack = whole@((Call (f@Struct{ name, args })) :| goals)
                    , position
                    , query'vars
                    , counter }
  = case look'for f (drop position base) position of
      Nothing -> DeadEnd (stall proc)

      Just (Fact (Struct{ args = patterns }), the'position) ->
        let (counter', patterns') = rename'all patterns counter
            new'goals = map (uncurry Unify) (zip args patterns') ++ goals

            backtracking'stack' = cause'backtracking f base (the'position + 1) whole query'vars backtracking'stack

            proc' = proc{ backtracking'stack = backtracking'stack'
                        , position = 0  -- the current goal will never ever be tried again (in this goal'stack anyway)
                        , counter = counter' }

        in  settle proc' new'goals

      Just (Struct{ args = patterns } :- body, the'position) ->
        let (counter', patterns', body') = rename'both patterns body counter
            new'goals = map (uncurry Unify) (zip args patterns') ++ body' ++ goals

            backtracking'stack' = cause'backtracking f base (the'position + 1) whole query'vars backtracking'stack

            proc' = proc{ backtracking'stack = backtracking'stack'
                        , position = 0  -- the current goal will never ever be tried again
                        , counter = counter' }

        in  settle proc' new'goals

  where look'for :: Struct -> [Predicate] -> Int -> Maybe (Predicate, Int)
        look'for _ [] _ = Nothing
        -- a fact with the same name and arity
        look'for f@Struct{ name, args } (fact@(Fact (Struct{ name = name', args = args' })) : base) pos
          | name == name' && length args == length args' = Just (fact, pos)
          | otherwise = look'for f base (pos + 1)
        -- | Struct :- Term
        -- a rule with the same name and arity
        look'for f@Struct{ name, args } (rule@(Struct{ name = name', args = args' } :- body) : base) pos
          | name == name' && length args == length args' = Just (rule, pos)
          | otherwise = look'for f base (pos + 1)


        -- Remember the current goal stack in case the match we just took
        -- leads nowhere - but only if another matching predicate exists
        -- further down the base.
        cause'backtracking :: Struct -> [Predicate] -> Int -> NonEmpty Goal -> Map.Map String Term -> [(NonEmpty Goal, Int, Map.Map String Term)] -> [(NonEmpty Goal, Int, Map.Map String Term)]
        cause'backtracking f base position goal'stack q'vars backtracking'stack
          = case look'for f (drop position base) position of
              Nothing -> backtracking'stack
              Just (_, future'position) ->
                let backtracking'record = (goal'stack, future'position, q'vars)
                in  backtracking'record : backtracking'stack

{-  PROVE UNIFICATION -}
step proc@Processing{ goal'stack = (Unify value'l value'r) :| goals
                    , query'vars }
  = case unify (value'l, value'r) goals query'vars of
      Nothing ->
        -- could not unify
        -- this means that this goal fails
        DeadEnd (stall proc)
      Just (goals', query'vars') ->
        -- they can be unified and the new'environment reflects that
        -- just return a new state with stack and env changed
        settle proc{ query'vars = query'vars' } goals'


-- | Keep searching with a new goal list, or report a solution when none
-- remain. This is the only place an emptied goal stack turns into a
-- `Solved`: the stack type guarantees we only get here with something
-- that was just proved.
settle :: Processing -> [Goal] -> StepResult
settle proc [] = Solved (query'vars proc) (stall proc)
settle proc (goal : goals) = Searching proc{ goal'stack = goal :| goals }


-- | The current path cannot continue: package up the resume context so
-- that `resume` can pick the search back up (or conclude it).
-- The counter stays the same (because it only increments).
stall :: Processing -> Stalled
stall Processing{ base, backtracking'stack, counter } =
  Stalled{ base'stalled = base
         , backtracking'stack'stalled = backtracking'stack
         , counter'stalled = counter }


-- | Pick a stalled search back up from its top backtracking record.
-- `Nothing` means nothing remains to try: the search is done.
resume :: Stalled -> Maybe Processing
resume Stalled{ base'stalled = base
              , backtracking'stack'stalled = records
              , counter'stalled = counter } =
  case records of
    [] -> Nothing
    (goals, pos, q'vars) : rest ->
      Just Processing{ base
                     , query'vars = q'vars
                     , backtracking'stack = rest
                     , goal'stack = goals
                     , position = pos
                     , counter }


-- | Give every distinct variable a fresh name; repeats of the same
-- variable share the new name. The counter only moves forward, so names
-- are never reused.
rename'all :: [Term] -> Int -> (Int, [Term])
rename'all patterns counter = (counter', patterns')
  where
    ((counter', mapping), patterns') = mapAccumL rename'val (counter, Map.empty) patterns


rename'val :: (Int, Map.Map String String) -> Term -> ((Int, Map.Map String String), Term)
rename'val (cntr, mapping) (Var name)
  = if Map.member name mapping
    then ((cntr, mapping), Var (mapping Map.! name))
    else  let new'name = "_" ++ show cntr
              new'cntr = cntr + 1
              new'mapping = Map.insert name new'name mapping
          in  ((new'cntr, new'mapping), Var new'name)

rename'val state (Compound (Struct{ name, args }))
  = let (state', args') = mapAccumL rename'val state args
    in  (state', Compound (Struct{ name = name, args = args' }))

rename'val acc val
  = (acc, val)


-- | Rename a rule head and its body together, so that a variable shared
-- between them stays shared after the renaming.
rename'both :: [Term] -> [Goal] -> Int -> (Int, [Term], [Goal])
rename'both patterns goals counter = (counter', patterns', goals')
  where
    (state, patterns') = mapAccumL rename'val (counter, Map.empty) patterns

    (state', goals') = mapAccumL rename'goal state goals

    (counter', _) = state'


rename'goal :: (Int, Map.Map String String) -> Goal -> ((Int, Map.Map String String), Goal)
rename'goal state (Call (Struct{ name, args }))
  = let (state', args') = mapAccumL rename'val state args
    in  (state', Call (Struct{ name, args = args' }))
rename'goal state (Unify val'l val'r)
  = let (state', [val'l', val'r']) = mapAccumL rename'val state [val'l, val'r]
    in  (state', Unify val'l' val'r')


-- | Unification in the style of Martelli and Montanari (see the write-up).
-- Each equation below handles one shape of the pair; a variable facing a
-- term it does not occur in becomes a substitution applied to every goal
-- that is still waiting (and to the recorded query bindings).
unify :: (Term, Term) -> [Goal] -> Map.Map String Term -> Maybe ([Goal], Map.Map String Term)
{-  DELETE  (basically) -}
unify (Wildcard, _) goals query'vars = Just (goals, query'vars)
unify (_, Wildcard) goals query'vars = Just (goals, query'vars)

{-  DELETE  -}
unify (Atom a, Atom b) goals query'vars
  | a == b = Just (goals, query'vars)
  | otherwise = Nothing

{-  DECOMPOSE + CONFLICT  -}
unify ( Compound Struct{ name = name'a, args = args'a }
      , Compound Struct{ name = name'b, args = args'b })
      goals query'vars
  | name'a /= name'b || length args'a /= length args'b = Nothing  -- CONFLICT
  | otherwise = Just (arg'goals ++ goals, query'vars)             -- DECOMPOSE
  where
    arg'goals :: [Goal]
    arg'goals = zipWith Unify args'a args'b

{-  ELIMINATE + OCCURS  -}
unify (Var a, value) goals query'vars
  | (Var a) == value = Just (goals, query'vars) -- DELETE (both are variables)
  | occurs a value = Nothing                    -- OCCURS CHECK (the one on the right is not a variable so I can do the check!)
  | otherwise = Just (substituted'goals, substituted'query'vars)
  where
    substituted'goals = map (subst'goal (a, value)) goals
    substituted'query'vars = Map.map (subst'val (a, value)) query'vars

    subst'goal :: (String, Term) -> Goal -> Goal
    subst'goal substitution (Call fun) = Call substituted'fun
      where substituted'fun = subst'functor substitution fun
    subst'goal substitution (Unify val'a val'b) = Unify substituted'val'a substituted'val'b
      where substituted'val'a = subst'val substitution val'a
            substituted'val'b = subst'val substitution val'b

    subst'val :: (String, Term) -> Term -> Term
    subst'val (from, to) (Var name)
      | name == from = to
      | otherwise = Var name
    subst'val _ (Atom name) = Atom name
    subst'val substitution (Compound fun) = Compound (subst'functor substitution fun)
    subst'val _ Wildcard = Wildcard

    subst'functor :: (String, Term) -> Struct -> Struct
    subst'functor substitution Struct{ name, args } = Struct{ name, args = substituted'args }
      where substituted'args = map (subst'val substitution) args

{-  SWAP  (because of the above equation, we assume the `value` not being a variable) -}
unify (value, Var b) goals query'vars = unify (Var b, value) goals query'vars

unify _ _ _ = Nothing   -- CONFLICT (for atoms and structs)


-- | True when the variable appears anywhere inside the term. Binding a
-- variable to such a term would build an infinite term, so the
-- corresponding unification is rejected instead.
occurs :: String -> Term -> Bool
occurs var'name (Var name) = var'name == name
occurs var'name (Atom _) = False
occurs var'name (Compound Struct{ args }) = any (occurs var'name) args
occurs var'name Wildcard = False
