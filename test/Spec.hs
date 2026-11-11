module Main where

import Test.Hspec
import UnifySpec (uSpec)
import GeneralizeSpec (gSpec)
import FreezeSpec (fSpec)
import ExamplesSpec (eSpec)

main :: IO ()
main = hspec $ do
  describe "unification" uSpec
  describe "generalisation" gSpec
  describe "freezing" fSpec
  describe "examples" eSpec
