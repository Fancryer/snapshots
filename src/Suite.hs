{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The executable part of the test suite: every example program of the paper
--   is elaborated, type-checked and interpreted, and the lines it prints are
--   compared with the expected output.  The mutation-event check of the
--   interpreter is enabled for these runs, so an unlicensed event fails the
--   suite as well.  The module is used both by the executable (@marran-exe@)
--   and by the Hspec driver, so @stack test@ covers the examples too.
module Suite (
    Case
  , cases
  , rejectedProgram
  , runSuite
  , runProgram
  , programPath
  ) where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Control.Exception (bracket, finally, try)
import Control.Monad (filterM)
import Control.Monad.State.Lazy (evalState)
import Control.Monad.Except (runExceptT)
import Data.List (isInfixOf, isPrefixOf, intercalate)
import System.Directory (doesFileExist, getTemporaryDirectory, removeFile)
import System.Environment (setEnv)
import System.IO
import GHC.IO.Handle (hDuplicate, hDuplicateTo)

import Elaborator (elaborate, ElabState(..))
import ErrorContext (toErrorText)
import Infer (inferChunk)
import IntInterpreter (interpret)
import Parser (parseFromText, chunk)
import Unify (TypeCheckState(..), evalTypeCheckM)
import Utils (Pretty(..))

-- | One runnable program and the lines it must print.
type Case = (FilePath, [String])

-- | The programs that must run, with their expected output.
cases :: [Case]
cases =
  [ ("scoping",           ["1"])
  , ("rebind_shared",     ["2"])
  , ("param_reentrancy",  ["3", "4", "3"])
  , ("counter",           ["1", "2"])
  , ("imm_snapshot",      ["6"])
  , ("imm_make",          ["0", "0"])
  , ("imm_recursion",     ["15"])
  , ("row_poly",          ["hello", "42"])
  , ("under",             ["1"])
  ]

-- | The program that the type checker must reject; the error must name @Read@.
rejectedProgram :: FilePath
rejectedProgram = "imm_needs_read"

-- | The directories that may contain the example programs, tried in order.
programPath :: FilePath -> IO (Maybe FilePath)
programPath name = do
  let candidates = [ "app/marr/" <> name <> ".marr"
                   , "../app/marr/" <> name <> ".marr"
                   , "../../app/marr/" <> name <> ".marr"
                   ]
  found <- filterM doesFileExist candidates
  pure $ case found of
    (p:_) -> Just p
    []    -> Nothing

-- | Elaborate, type-check and interpret a program.  Everything it prints is
--   captured and returned; the result is 'Left' on a parse, elaboration or
--   type error.
runProgram :: FilePath -> IO (Either String String)
runProgram name =
  programPath name >>= \case
    Nothing -> pure $ Left $ "program not found: " ++ name ++ ".marr"
    Just path -> do
      src <- T.pack <$> readFile path
      case elaborate <$> parseFromText chunk src of
        Left e -> pure $ Left e
        Right elabAction ->
          case evalState (runExceptT elabAction) (ElabState 0) of
            Left e -> pure $ Left $ "elaboration error: " ++ show e
            Right c' ->
              case evalTypeCheckM (inferChunk [] c') (TypeCheckState (0, 0, 0) 0 []) of
                Left (stack, err) -> pure . Left . T.unpack $ T.concat
                  [ pretty err, "\n", T.unlines (map toErrorText stack) ]
                Right ic -> Right <$> captureStdout (interpret ic [])

-- | Run an action with @stdout@ redirected to a temporary file and return what
--   was written to it.
captureStdout :: IO a -> IO String
captureStdout action = do
  tmp <- getTemporaryDirectory
  (path, h) <- openTempFile tmp "marran-out.txt"
  let cleanup = do
        hClose h
        r <- try (removeFile path) :: IO (Either IOError ())
        either (const (pure ())) pure r
  bracket (hDuplicate stdout) (\saved -> hDuplicateTo saved stdout >> hClose saved) $ \saved ->
    (do hDuplicateTo h stdout
        hSetBuffering stdout LineBuffering
        _ <- action
        hFlush stdout
        hDuplicateTo saved stdout
        hSeek h AbsoluteSeek 0
        T.unpack <$> TIO.hGetContents h)
      `finally` cleanup

-- | Run the whole suite; returns 'True' when every check passes.
runSuite :: IO Bool
runSuite = do
  setEnv "MARRAN_CHECK_EVENTS" "1"
  putStrLn "Programs:"
  results <- mapM check cases
  rejectedOk <- checkRejected
  let failures = [ n | (n, ok) <- results, not ok ]
                 ++ [ rejectedProgram | not rejectedOk ]
      total = length cases + 1
  putStrLn ""
  if null failures
    then putStrLn $ "All " ++ show total ++ " programs behave as expected."
    else putStrLn $ "FAILED: " ++ intercalate ", " failures
  pure (null failures)

check :: Case -> IO (FilePath, Bool)
check (name, expected) = do
  r <- runProgram name
  let (ok, printed, note) = case r of
        Left err  -> (False, [] :: [String], take 300 err)
        Right out ->
          let ls = lines out
              violations = filter ("EVENT-VIOLATION" `isPrefixOf`) ls
              printed' = filter (not . isReportLine) ls
          in (null violations && printed' == expected, printed', intercalate "; " violations)
  putStrLn $ concat
    [ "  ", pad name
    , if ok then "ok  " else "FAILED"
    , " expected " ++ show expected
    , ", got " ++ show printed
    ]
  if null note then pure () else putStrLn $ "    " ++ note
  pure (name, ok)

checkRejected :: IO Bool
checkRejected = do
  r <- runProgram rejectedProgram
  let ok = case r of
        Left err -> "Read" `isInfixOf` err
        Right _  -> False
  putStrLn $ "  " ++ pad rejectedProgram
    ++ (if ok then "rejected, as intended" else "FAILED")
  case r of
    Left err | not ok -> putStrLn $ "    " ++ take 400 err
    Right out         -> putStrLn $ "    output: " ++ take 400 out
    _                 -> pure ()
  pure ok

-- | Lines of the interpreter's own report, not of the program.
isReportLine :: String -> Bool
isReportLine l = "EVENTS:" `isPrefixOf` l || "EVENT-VIOLATION" `isPrefixOf` l

pad :: String -> String
pad s = s ++ replicate (max 1 (18 - length s)) ' '
