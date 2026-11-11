{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
module Main (main) where

import System.Environment (getArgs, withArgs)
import System.Exit (exitFailure)
import Benchmark (runBenchmarks, runEdgeSweepBenchmarks)
import Suite (runSuite, runProgram)

main :: IO ()
main = getArgs >>= \case
  []                     -> runSuite >>= \ok -> if ok then pure () else exitFailure
  ("--bench":rest)       -> withArgs (criterionArgs rest) runBenchmarks
  ("--bench-edges":rest) -> withArgs (criterionArgs rest) runEdgeSweepBenchmarks
  ["--run", name] -> runProgram name >>= \case
    Left err -> putStrLn err >> exitFailure
    Right out -> putStr out >> putStrLn "(done)"
  _ -> putStrLn $ unlines
    [ "usage: marran-exe               run the examples of the paper"
    , "       marran-exe --bench [--csv FILE]        the graphs of Table 2"
    , "       marran-exe --bench-edges [--csv FILE]  the wider edge sweep"
    , "       marran-exe --run <name>  run one program"
    ]

-- | Criterion accepts @--csv@ only as its first argument.
criterionArgs :: [String] -> [String]
criterionArgs args = case break (== "--csv") args of
  (before, "--csv" : file : after) -> "--csv" : file : before <> after
  _                                -> args
