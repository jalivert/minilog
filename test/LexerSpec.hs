module LexerSpec (spec) where

import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import Data.Either (isLeft)

import Lexer (Lexer, eval'parser, read'token)
import Token (Token)
import Token qualified as Token


-- | Tokenize a whole input, keeping the trailing EOF.
lexAll :: String -> Either (String, Int) [Token]
lexAll src = fst <$> eval'parser collectTokens src
  where
    collectTokens :: Lexer [Token]
    collectTokens = do
      t <- read'token
      case t of
        Token.EOF -> return [t]
        _ -> (t :) <$> collectTokens


spec :: Spec
spec = do
  describe "tokens" $ do
    it "lexes lowercase runs as atoms" $
      lexAll "foo" `shouldBe` Right [Token.Atom "foo", Token.EOF]

    it "lexes uppercase runs as variables" $
      lexAll "ABC" `shouldBe` Right [Token.Var "ABC", Token.EOF]

    it "lexes punctuation" $
      lexAll ", . ( ) ="
        `shouldBe` Right [ Token.Comma, Token.Period
                         , Token.Paren'Open, Token.Paren'Close
                         , Token.Equal, Token.EOF ]

    it "lexes :- as If" $
      lexAll ":-" `shouldBe` Right [Token.If, Token.EOF]

    it "lexes _ as Underscore" $
      lexAll "_" `shouldBe` Right [Token.Underscore, Token.EOF]

    it "lexes mixed-case runs as separate tokens" $
      lexAll "fOo"
        `shouldBe` Right [Token.Atom "f", Token.Var "O", Token.Atom "o", Token.EOF]

    it "skips whitespace including newlines" $
      lexAll "  foo\n\tbar "
        `shouldBe` Right [Token.Atom "foo", Token.Atom "bar", Token.EOF]

    it "skips % comments up to the newline" $
      lexAll "% a comment\nfoo"
        `shouldBe` Right [Token.Atom "foo", Token.EOF]

    it "skips a comment at end of input without a newline" $
      lexAll "foo % trailing comment"
        `shouldBe` Right [Token.Atom "foo", Token.EOF]

    it "skips a lone comment without a newline" $
      lexAll "% just a comment"
        `shouldBe` Right [Token.EOF]

  describe "lexical errors" $ do
    it "rejects digits" $
      lexAll "123" `shouldSatisfy` isLeft

    it "rejects semicolons" $
      lexAll "foo;bar" `shouldSatisfy` isLeft

    it "reports a message and a positive column" $ do
      case lexAll "foo 1" of
        Left (msg, col) -> do
          msg `shouldSatisfy` (not . null)
          col `shouldSatisfy` (> 0)
        Right _ -> fail "expected a lexical error"
