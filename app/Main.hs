module Main where

import Control.Exception ( IOException, displayException, evaluate, try )
import Data.List ( intercalate )
import Data.List.Extra ( trim )
import Data.List.NonEmpty ( NonEmpty(..) )
import Data.List.NonEmpty qualified as NonEmpty
import Data.Maybe ( fromMaybe )

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

import System.IO ( hFlush, stdout, openFile, IOMode(ReadMode), hGetContents, hClose )


import Term ( Term(..), Struct(..), Predicate(..), Goal(..) )

import Evaluate.Step ( step, resume )
import Evaluate.State ( Processing(..), Stalled(..), StepResult(..) )

import Parser ( parse'base, parse'query )


-- | Build the initial search for a query: its variables start unbound
-- (each mapped to itself) and both stacks start empty.
start'query :: [Predicate] -> NonEmpty Goal -> Processing
start'query base goals = Processing
  { base
  , query'vars = Map.fromList q'vars
  , backtracking'stack = []
  , goal'stack = goals
  , position = 0
  , counter = 0 }
  where
    free'names :: [String]
    free'names = Set.toList (free'vars'in'query (NonEmpty.toList goals))

    q'vars = [(name, Var name) | name <- free'names]


-- | Like `getLine`, but a closed stdin (Ctrl-D) yields `Nothing`
-- instead of throwing.
try'line :: IO (Maybe String)
try'line = either (const Nothing) Just <$> (try getLine :: IO (Either IOException String))


-- | Read a knowledge base file strictly: the content is fully forced
-- before the handle is closed, and any I/O failure is raised to the
-- caller (the REPL reports it instead of crashing).
read'base'file :: FilePath -> IO String
read'base'file path = do
  file'handle <- openFile path ReadMode
  file'content <- hGetContents file'handle
  _ <- evaluate (length file'content)
  hClose file'handle
  return file'content


main :: IO ()
main = do
  putStrLn "Minilog - implementation of simple logic programming language."
  repl []
  putStrLn "Bye!"


-- | The read-eval loop. Only the base is carried over; every query
-- starts a fresh search.
repl :: [Predicate] -> IO ()
repl base = do
  putStr "?- "
  hFlush stdout
  -- Ctrl-D quits, like :q.
  str <- fromMaybe ":q" <$> try'line
  case str of
    ":q" -> return ()
    ":Q" -> return ()
    ':' : 'l' : 'o' : 'a' : 'd' : file'path -> do
      load'result <- try (read'base'file (trim file'path)) :: IO (Either IOException String)
      case load'result of
        Left err -> do
          putStrLn ("Could not load `" ++ trim file'path ++ "': " ++ displayException err)
          repl base
        Right file'content ->
          case parse'base file'content of
            -- No caret here: the error is on some line of a file that was
            -- never echoed, so it would point at nothing. The message
            -- itself carries the line number.
            Left (err, _col) -> do
              putStrLn err
              repl base
            Right new'base -> repl new'base

    ':' : _ -> do
      putStrLn "I don't know this command, sorry."
      repl base

    _ ->
      case parse'query str of
        Left (err, col) -> do
          let padding = replicate (3 + col - 1) ' '
          putStrLn $! padding ++ "^"
          putStrLn err
          repl base
        Right goals ->
          case goals of
            -- Unreachable: the grammar always yields at least one goal.
            [] -> do
              putStrLn "Empty query."
              repl base
            (goal : rest) -> try'to'prove (start'query base (goal :| rest))


-- | Drive one query to all of its solutions: step until the machine
-- stalls, report each solution, and resume on demand (`:next`) or stop
-- (`:done`). A dead end with nothing left to try prints `False.`
try'to'prove :: Processing -> IO ()
try'to'prove proc = case step proc of
  Searching proc' -> try'to'prove proc'

  DeadEnd stalled ->
    case resume stalled of
      Nothing -> do
        putStrLn "False."
        repl (base'stalled stalled)
      Just proc' -> try'to'prove proc'

  Solved q'vars stalled ->
    case resume stalled of
      Nothing -> do
        print'result q'vars
        repl (base'stalled stalled)
      Just proc' -> do
        print'result q'vars
        -- Ctrl-D ends the query like :done (the next prompt quits).
        user'input <- fromMaybe ":done" <$> try'line
        case user'input of
          ":done" -> do
            putStrLn "."
            repl (base proc')
          _ -> do
            putStrLn "  or\n"
            try'to'prove proc'


print'result :: Map.Map String Term -> IO ()
print'result q'vars
  | Map.null q'vars = putStrLn "True"
  | otherwise = putStrLn (intercalate "\n" [k ++ " = " ++ show v | (k, v) <- Map.toList q'vars])


free'vars'in'query :: [Goal] -> Set.Set String
free'vars'in'query goals = foldl' (\ set g -> set `Set.union` free'vars'in'goal g) Set.empty goals


free'vars'in'goal :: Goal -> Set.Set String
free'vars'in'goal (Call fun) = free'vars'in'functor fun
free'vars'in'goal (Unify val'l val'r) = Set.union (free'vars'in'val val'l) (free'vars'in'val val'r)


free'vars'in'functor :: Struct -> Set.Set String
free'vars'in'functor Struct{ args } = foldl' (\ set g -> set `Set.union` free'vars'in'val g) Set.empty args


free'vars'in'val :: Term -> Set.Set String
free'vars'in'val (Var name) = Set.singleton name
free'vars'in'val (Atom _) = Set.empty
free'vars'in'val (Compound fun) = free'vars'in'functor fun
free'vars'in'val Wildcard = Set.empty
