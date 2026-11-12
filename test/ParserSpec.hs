{-# LANGUAGE OverloadedStrings #-}

-- | Syntax errors go through the same renderer as type errors, so their shape
--   is checked here: the code, the location and the caret run.
module ParserSpec (pSpec) where

import qualified Data.Text as T
import Test.Hspec

import Parser (chunk, parseFromTextNamed)

-- | Parse a program and return the rendered error, failing the test if the
--   program unexpectedly parses.
parseFailure :: T.Text -> IO [T.Text]
parseFailure src = case parseFromTextNamed "demo.marr" chunk src of
  Left e  -> pure (T.lines (T.pack e))
  Right _ -> expectationFailure "the program parsed, but it should not have" >> pure []

pSpec :: Spec
pSpec = describe "syntax errors" $ do

  it "reports an unexpected token with its code and position" $ do
    ls <- parseFailure $ T.unlines
      [ "funct main () : {Output} ("
      , "  sayn 1"
      ]
    take 5 ls `shouldBe`
      [ "error[E0013]: unexpected `sayn`"
      , " --> demo.marr:2:3"
      , "  |"
      , "2 |   sayn 1"
      , "  |   ^^^^"
      ]

  it "reports an unexpected keyword where a statement cannot start" $ do
    ls <- parseFailure $ T.unlines
      [ "funct main () : {Output} () ="
      , "  val = 3;"
      , "  sayn 1"
      ]
    take 2 ls `shouldBe`
      [ "error[E0013]: unexpected `val`"
      , " --> demo.marr:2:3"
      ]

  it "reports the end of input when a literal is unterminated" $ do
    ls <- parseFailure $ T.unlines
      [ "funct main () : {Output} () ="
      , "  sayn 'unterminated"
      ]
    take 2 ls `shouldBe`
      [ "error[E0013]: unexpected end of input; expected `'`, `\\'`, `\\\\`"
      , " --> demo.marr:3:1"
      ]