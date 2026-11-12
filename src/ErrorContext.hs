{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

-- | Diagnostics with source positions.
--
--   The renderer produces Rust-style output: a header line, an @-->@ location,
--   the offending source line with a caret run under the primary span, and the
--   remaining frames as indented notes:
--
--   > error[E0003]: cannot unify the type `Boolean` with the type `Int`
--   >  --> app/marr/x.marr:3:12
--   >   |
--   > 3 |   val b = + true 3;
--   >   |           ^^^^^^^^
--   >   |
--   >   = + true
--   >   = + true 3 at app/marr/x.marr:3:11
--
--   Positions are 'Span.Span' rather than Megaparsec's @SourcePos@, so that the
--   AST, the IR and the typed IR can carry them without a parser dependency.
module ErrorContext (
  Severity(..),
  severityText,
  Label(..),
  primaryLabel,
  secondaryLabel,
  Diagnostic(..),
  diagnostic,
  withNote,
  ErrorStack,
  ErrorFrame(..),
  AstFrame(..),
  IrFrame(..),
  TypedIrFrame(..),
  ToErrorText(..),
  SourceText(..),
  SourceMap,
  emptySourceMap,
  insertSource,
  insertSourceText,
  sourceOf,
  renderDiagnostic,
  renderDiagnostics,
  renderError,
  renderErrorWith,
  renderErrorStack,
  innermost
) where
import Data.Text (Text)
import qualified Data.Text as T
import Data.Map (Map)
import qualified Data.Map as Map
import Types (Typ)
import Utils (pretty)
import Span (
    Span(..),
    noSpan,
    isNoSpan,
    prettyPoint
  )

-- | How bad a diagnostic is.
data Severity = SevError | SevWarning | SevNote
  deriving (Eq, Ord, Show)

severityText :: Severity -> Text
severityText = \case
  SevError -> "error"
  SevWarning -> "warning"
  SevNote -> "note"

-- | One annotated region of the source.
data Label = Label {
    labelSpan    :: Span
  , labelText    :: Text
  , labelPrimary :: Bool
  } deriving (Eq, Show)

primaryLabel :: Span -> Text -> Label
primaryLabel s t = Label s t True

secondaryLabel :: Span -> Text -> Label
secondaryLabel s t = Label s t False

-- | A single error, warning or note.
data Diagnostic = Diagnostic {
    diagSeverity :: Severity
  , diagCode     :: Maybe Text
  , diagMessage  :: Text
  , diagLabels   :: [Label]
  , diagNotes    :: [Text]
  } deriving (Eq, Show)

diagnostic :: Severity -> Maybe Text -> Text -> Diagnostic
diagnostic sev code msg =
  Diagnostic {diagSeverity = sev, diagCode = code, diagMessage = msg, diagLabels = [], diagNotes = []}

withNote :: Text -> Diagnostic -> Diagnostic
withNote n d = d {diagNotes = diagNotes d <> [n]}

-- | The chain of nodes a diagnostic passed through, outermost first.
type ErrorStack = [ErrorFrame]

data AstFrame = AstFrame {
    afNode   :: Text
  , afSource :: Span
  } deriving (Eq, Show)

data IrFrame = IrFrame {
    ifNode   :: Text
  , ifSource :: Span
  } deriving (Eq, Show)

data TypedIrFrame = TypedIrFrame {
    tifNode   :: Text
  , tifType   :: Typ
  , tifSource :: Span
  } deriving (Eq, Show)

data ErrorFrame =
    EFAst AstFrame
  | EFIr IrFrame
  | EFTypedIr TypedIrFrame
  | EFMessage Text
  deriving (Eq, Show)

class ToErrorText a where
  toErrorText :: a -> Text

instance ToErrorText AstFrame where
  toErrorText (AstFrame n s) =
    if isNoSpan s then n else n <> " at " <> prettyPoint s

instance ToErrorText IrFrame where
  toErrorText (IrFrame n s) =
    if isNoSpan s then n else n <> " at " <> prettyPoint s

instance ToErrorText TypedIrFrame where
  toErrorText (TypedIrFrame n t s) =
    let base = n <> " : " <> pretty t
    in if isNoSpan s then base else base <> " at " <> prettyPoint s

instance ToErrorText ErrorFrame where
  toErrorText = \case
    EFAst a     -> toErrorText a
    EFIr i      -> toErrorText i
    EFTypedIr t -> toErrorText t
    EFMessage m -> m

-- | The contents of one source file, split into lines.
data SourceText = SourceText {
    srcName  :: Text
  , srcLines :: [Text]
  } deriving (Eq, Show)

type SourceMap = Map Text SourceText

emptySourceMap :: SourceMap
emptySourceMap = Map.empty

insertSourceText :: SourceText -> SourceMap -> SourceMap
insertSourceText src = Map.insert (srcName src) src

insertSource :: Text -> Text -> SourceMap -> SourceMap
insertSource name contents = insertSourceText $ SourceText name (T.lines contents)

sourceOf :: SourceMap -> Span -> Maybe SourceText
sourceOf sm s
  | isNoSpan s = Nothing
  | T.null (spanFile s) = Nothing
  | otherwise = Map.lookup (spanFile s) sm

-- | A caret run under one label, or nothing when the file is unknown.
renderLabel :: SourceMap -> Label -> [Text]
renderLabel sm lab =
  case sourceOf sm sp of
    Nothing -> []
    Just src
      | l0 < 1 || l0 > length (srcLines src) -> []
      | otherwise -> [gutterPad <> " |", gutter <> " | " <> lineAt src l0, gutterPad <> " | " <> carets src <> suffix]
    where
      sp = labelSpan lab
      l0 = spanStartLine sp
      c0 = spanStartColumn sp
      l1 = spanEndLine sp
      c1 = spanEndColumn sp
      gutter = T.pack (show l0)
      gutterPad = T.replicate (T.length gutter) " "
      -- A primary label marks the region the error is about; a secondary one
      -- merely relates to it, so it gets dashes instead of carets.
      mark = if labelPrimary lab then "^" else "-"
      carets src
        | min l1 (length (srcLines src)) > l0 =
            T.replicate (max 0 (c0 - 1)) " "
              <> T.replicate (max 1 (T.length (lineAt src l0) - c0 + 1)) mark
        | otherwise =
            T.replicate (max 0 (c0 - 1)) " " <> T.replicate (max 1 (c1 - c0)) mark
      suffix
        | T.null (labelText lab) = ""
        | otherwise = " " <> labelText lab

lineAt :: SourceText -> Int -> Text
lineAt src n
  | n >= 1 && n <= length (srcLines src) = srcLines src !! (n - 1)
  | otherwise = mempty

-- | Render one diagnostic.  The source map is used to quote the offending
--   lines; when the span's file is not in the map only the location is printed.
renderDiagnostic :: SourceMap -> Diagnostic -> Text
renderDiagnostic sm d = T.intercalate "\n" (header : location <> quoted <> notes)
  where
    header =
      severityText (diagSeverity d)
        <> maybe "" (\c -> "[" <> c <> "]") (diagCode d)
        <> ": " <> diagMessage d

    located = filter (not . isNoSpan . labelSpan) (diagLabels d)

    location = case located of
      [] -> []
      (l:_) -> [" --> " <> prettyPoint (labelSpan l)]

    quoted
      | null located = []
      | otherwise = case concatMap (renderLabel sm) located of
          [] -> []
          qs -> qs <> ["  |"]

    notes = map ("  = " <>) (diagNotes d)

-- | Render a list of diagnostics, separated by a blank line.
renderDiagnostics :: SourceMap -> [Diagnostic] -> Text
renderDiagnostics sm ds = T.intercalate "\n\n" (map (renderDiagnostic sm) ds)

-- | The span of a frame, if it has one.
frameSpan :: ErrorFrame -> Span
frameSpan = \case
  EFAst a     -> afSource a
  EFIr i      -> ifSource i
  EFTypedIr t -> tifSource t
  EFMessage _ -> noSpan

-- | The frame a diagnostic is reported at: the innermost one, which is where
--   the checker gave up.  A message frame is a note, not a position, so it is
--   skipped even when it is first in the stack.
innermost :: ErrorStack -> ErrorFrame
innermost stack = case filter (not . isMessage) stack of
  (f:_) -> f
  []    -> EFMessage ""
  where
    isMessage EFMessage{} = True
    isMessage _           = False

-- | How many frames of a stack a diagnostic shows.  A deeply nested expression
--   would otherwise print a note per node of the path, which buries the error
--   itself; the innermost frames (where the checker gave up) are the useful
--   ones, so the outermost are dropped first.
maxNotes :: Int
maxNotes = 6

-- | The notes of a stack: adjacent duplicates removed, capped at 'maxNotes',
--   and with the location omitted when it is the one already shown as the
--   primary label.
--
--   The same span often appears twice, once as the failing expression and once
--   as the frame of the statement that wraps it, and those read as noise.
notesOf :: Span -> ErrorStack -> [Text]
notesOf primarySpan stack =
  let (messages, frames) = partitionFrames stack
      rendered = map renderOne frames
      deduped = dropAdjacentDup rendered
      shown = take maxNotes deduped
      hidden = length deduped - length shown
  in shown <> [ "... " <> T.pack (show hidden) <> " more" | hidden > 0 ] <> messages
  where
    -- A message frame is text the checker wrote on purpose (a suggestion, say),
    -- not a node of the path to the error.  It is never capped and never
    -- merged with its neighbours, and it goes last, so that it reads as a hint
    -- after the trace rather than as part of it.
    partitionFrames = foldr step ([], [])
      where
        step (EFMessage m) (ms, fs) = (m : ms, fs)
        step f (ms, fs) = (ms, f : fs)

    atPrimary f =
      not (isNoSpan primarySpan)
        && not (isNoSpan (frameSpan f))
        && prettyPoint (frameSpan f) == prettyPoint primarySpan

    renderOne f
      | atPrimary f = stripLocation f
      | otherwise = toErrorText f

    -- The frame text always ends in " at file:line:col" when it has a span.
    stripLocation f = case T.breakOnEnd " at " (toErrorText f) of
      (before, _) | not (T.null before) -> T.dropEnd 4 before
      _ -> toErrorText f

    dropAdjacentDup (x:y:rest)
      | x == y = dropAdjacentDup (y:rest)
      | otherwise = x : dropAdjacentDup (y:rest)
    dropAdjacentDup xs = xs

-- | Render the main error together with the frame stack.  The top frame, when
--   it has a position, becomes the primary label; the rest become notes.
renderError :: SourceMap -> ErrorFrame -> Text -> ErrorStack -> Text
renderError sm topFrame message stack = renderErrorWith sm topFrame Nothing message stack

-- | 'renderError' with an explicit diagnostic code, which is what the type
--   checker supplies so that the same class of error always has the same
--   searchable identifier.
renderErrorWith :: SourceMap -> ErrorFrame -> Maybe Text -> Text -> ErrorStack -> Text
renderErrorWith sm topFrame code message stack =
  renderDiagnostic sm d
  where
    d = (diagnostic SevError code message) {
          diagLabels = case frameSpan topFrame of
            s | isNoSpan s -> []
              | otherwise -> [primaryLabel s ""]
        , diagNotes = notesOf (frameSpan topFrame) stack
        }

-- | Render a plain stack as one indented block, for the callers that do not
--   build a 'Diagnostic' of their own.
renderErrorStack :: SourceMap -> Text -> ErrorStack -> Text
renderErrorStack _ message stack = T.intercalate "\n" $
  ["error: " <> message] <> map ("  = " <>) (notesOf noSpan stack)
