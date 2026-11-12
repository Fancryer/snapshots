{-# LANGUAGE OverloadedStrings #-}

-- | The shape of a rendered diagnostic is part of the user interface, so it is
--   checked here rather than only in the end-to-end example tests.
module DiagnosticSpec (dSpec) where

import Data.Text (Text)
import qualified Data.Text as T
import Test.Hspec

import ErrorContext
import Span
import Unify (TypeCheckError (..), errorCode)

-- | A small source file used by every test below.
sources :: SourceMap
sources = insertSource "demo.marr" (T.unlines
  [ "funct main () : {Output} () ="
  , "  val y = 1;"
  , "  sayn (+ true 1)"
  ]) emptySourceMap

-- | The span of @+ true 1@: line 3, columns 9..17.
plusSpan :: Span
plusSpan = Span "demo.marr" 3 9 3 17

irFrame :: Text -> Span -> ErrorFrame
irFrame n s = EFIr (IrFrame n s)

dSpec :: Spec
dSpec = describe "diagnostic rendering" $ do

  it "starts with a severity, an optional code and the message" $ do
    let d = diagnostic SevError (Just "E0003") "cannot unify `Boolean` with `Int`"
    T.lines (renderDiagnostic sources d) `shouldBe`
      ["error[E0003]: cannot unify `Boolean` with `Int`"]

  it "omits the brackets when there is no code" $ do
    let d = diagnostic SevWarning Nothing "unused binding"
    head (T.lines (renderDiagnostic sources d)) `shouldBe` "warning: unused binding"

  it "prints the location of the primary label" $ do
    let d = (diagnostic SevError Nothing "boom") {diagLabels = [primaryLabel plusSpan ""]}
        ls = T.lines (renderDiagnostic sources d)
    ls `shouldBe`
      [ "error: boom"
      , " --> demo.marr:3:9"
      , "  |"
      , "3 |   sayn (+ true 1)"
      , "  |         ^^^^^^^^"
      , "  |"
      ]

  it "keeps the line number gutter aligned for wider line numbers" $ do
    let far = Span "demo.marr" 3 3 3 6
        d = (diagnostic SevError Nothing "boom") {diagLabels = [primaryLabel far ""]}
    T.lines (renderDiagnostic sources d) !! 3
      `shouldBe` "3 |   sayn (+ true 1)"

  it "quotes nothing when the file is not in the source map" $ do
    let other = Span "other.marr" 1 1 1 3
        d = (diagnostic SevError Nothing "boom") {diagLabels = [primaryLabel other ""]}
    -- The location is known but the file is not, so there is nothing to quote
    -- and no caret line: only the header and the location remain.
    T.lines (renderDiagnostic sources d) `shouldBe`
      ["error: boom", " --> other.marr:1:1"]

  it "renders the frames of a stack as notes" $ do
    let stack = [irFrame "sayn (+ true 1)" (Span "demo.marr" 3 3 3 17),
                 irFrame "+ true 1" plusSpan]
        out = renderError sources (irFrame "+ true 1" plusSpan) "cannot unify" stack
    T.lines out `shouldBe`
      [ "error: cannot unify"
      , " --> demo.marr:3:9"
      , "  |"
      , "3 |   sayn (+ true 1)"
      , "  |         ^^^^^^^^"
      , "  |"
      , "  = sayn (+ true 1) at demo.marr:3:3"
      , "  = + true 1"
      ]

  it "does not repeat the primary location in the notes" $ do
    let stack = [irFrame "+ true 1" plusSpan]
        out = renderError sources (irFrame "+ true 1" plusSpan) "cannot unify" stack
    filter ("  = " `T.isPrefixOf`) (T.lines out)
      `shouldSatisfy` all (not . T.isSuffixOf "demo.marr:3:9")

  it "collapses adjacent identical frames" $ do
    let stack = [irFrame "+ true 1" plusSpan, irFrame "+ true 1" plusSpan]
        out = renderError sources (irFrame "boom" plusSpan) "cannot unify" stack
    length (filter ("  = + true 1" `T.isPrefixOf`) (T.lines out)) `shouldBe` 1

  it "caps a long stack and says how many frames it hid" $ do
    let stack = [ irFrame (T.pack ("frame" <> show i)) (Span "demo.marr" 3 3 3 6)
                | i <- [1 .. 10 :: Int] ]
        out = renderError sources (irFrame "boom" noSpan) "cannot unify" stack
        notes = filter ("  = " `T.isPrefixOf`) (T.lines out)
    length notes `shouldBe` 7
    last notes `shouldBe` "  = ... 4 more"

  it "marks a secondary label with dashes instead of carets" $ do
    let d = (diagnostic SevError Nothing "boom") {
              diagLabels = [primaryLabel plusSpan "", secondaryLabel (Span "demo.marr" 2 3 2 8) "bound here"] }
        ls = T.lines (renderDiagnostic sources d)
    ls `shouldSatisfy` any (T.isInfixOf "^^^^")
    ls `shouldSatisfy` any (T.isInfixOf "----- bound here")

  it "reports an error without a position without inventing one" $ do
    T.lines (renderError sources (irFrame "boom" noSpan) "boom" [])
      `shouldBe` ["error: boom"]

  describe "message notes" $ do
    let trace i = irFrame (T.pack ("frame" <> show i)) (Span "demo.marr" 3 3 3 6)
        suggestion = EFMessage "did you mean `counter`?"
        notesOf' out = filter ("  = " `T.isPrefixOf`) (T.lines out)

    it "prints a suggestion after the trace" $ do
      let out = renderError sources (irFrame "+ true 1" plusSpan) "boom"
                  [irFrame "+ true 1" plusSpan, suggestion]
      last (notesOf' out) `shouldBe` "  = did you mean `counter`?"

    it "does not count a suggestion against the frame cap" $ do
      let out = renderError sources (irFrame "boom" noSpan) "boom"
                  (map trace [1 .. 10 :: Int] <> [suggestion])
          ns = notesOf' out
      length ns `shouldBe` 8
      take 6 ns `shouldSatisfy` all (T.isPrefixOf "  = frame" . T.take 10)
      drop 6 ns `shouldBe` ["  = ... 4 more", "  = did you mean `counter`?"]

    it "does not merge a suggestion into an identical note" $ do
      -- A suggestion is written by the checker, not by the stack walk, so it
      -- must survive even when it happens to repeat the text of a frame.
      let out = renderError sources (irFrame "boom" noSpan) "boom"
                  [EFMessage "boom", EFMessage "boom"]
      notesOf' out `shouldBe` ["  = boom", "  = boom"]

    it "reports the error where the innermost positioned frame is" $ do
      -- A suggestion is prepended to the stack, so the location has to come
      -- from the frame below it.
      let stack = [suggestion, irFrame "+ true 1" plusSpan]
          out = renderErrorWith sources (innermost stack) (Just "E0007") "boom" stack
      T.lines out !! 1 `shouldBe` " --> demo.marr:3:9"

  it "gives each kind of type error its own code" $ do
    let codes = map errorCode
          [ TypeError "x"
          , DuplicateDefinition "x"
          , RecordError "x"
          , HandlerError "x"
          , ApplicationError "x"
          , InferenceError "x"
          ]
    codes `shouldBe`
      map Just ["E0001", "E0014", "E0015", "E0016", "E0017", "E0018"]
