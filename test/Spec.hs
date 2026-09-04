module Main (main) where

import Test.Hspec (describe, hspec)

import qualified EvalSpec
import qualified LexerSpec
import qualified ParserSpec
import qualified TermSpec
import qualified UnifySpec


main :: IO ()
main = hspec $ do
  describe "Term" TermSpec.spec
  describe "Lexer" LexerSpec.spec
  describe "Parser" ParserSpec.spec
  describe "unification" UnifySpec.spec
  describe "evaluation" EvalSpec.spec
