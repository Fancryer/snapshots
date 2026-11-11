{-# LANGUAGE OverloadedStrings #-}
module ExamplesSpec (eSpec) where

import Control.Monad (forM_)
import Data.List (isInfixOf)
import System.Environment (setEnv)
import Test.Hspec

import Suite (cases, rejectedProgram, runProgram)

-- | The example programs of the paper, as tests.  The event check of the
--   interpreter is enabled, so a mutation event that the declared row does not
--   license fails the corresponding test.
eSpec :: Spec
eSpec = beforeAll_ (setEnv "MARRAN_CHECK_EVENTS" "1") $ describe "example programs" $ do
  forM_ cases $ \(name, expected) ->
    it (name ++ " prints " ++ show expected) $ do
      r <- runProgram name
      case r of
        Left err -> expectationFailure $ "program failed: " ++ err
        Right out -> do
          let ls = lines out
              violations = filter ("EVENT-VIOLATION" `isInfixOf`) ls
              printed = filter (not . isReport) ls
          violations `shouldBe` []
          printed `shouldBe` expected

  it (rejectedProgram ++ " is rejected with the missing Read effect") $ do
    r <- runProgram rejectedProgram
    case r of
      Left err -> err `shouldSatisfy` ("Read" `isInfixOf`)
      Right out -> expectationFailure $
        "expected a type error, got output: " ++ take 300 out
  where
    isReport l = "EVENTS:" `isInfixOf` l || "EVENT-VIOLATION" `isInfixOf` l
