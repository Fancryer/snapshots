module Main where

import Test.Hspec
import UnifySpec (uSpec)
import GeneralizeSpec (gSpec)
import FreezeSpec (fSpec)
import ExamplesSpec (eSpec)
import SpanSpec (spanSpec)
import DiagnosticSpec (dSpec)
import ParserSpec (pSpec)
import SuggestSpec (sSpec)

main :: IO ()
main = hspec $ do
  describe "unification" uSpec
  describe "generalisation" gSpec
  describe "freezing" fSpec
  describe "examples" eSpec
  describe "spans" spanSpec
  describe "diagnostics" dSpec
  describe "syntax" pSpec
  describe "suggestions" sSpec
