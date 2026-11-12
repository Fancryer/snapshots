{-# LANGUAGE OverloadedStrings #-}

-- | Source positions, independent of any parser library.
--
--   The AST, the IR and the typed IR all carry 'Span's, so this module must
--   not depend on Megaparsec: the parser converts its own positions into a
--   'Span' once, at the boundary.
module Span (
  Span(..),
  noSpan,
  isNoSpan,
  spanAt,
  spanTo,
  mergeSpan,
  mergeSpans,
  spanStart,
  spanEnd,
  prettyPoint,
  prettySpan,
  pointInSpan
) where
import Data.Text (Text)
import qualified Data.Text as T

-- | A region of one file.  'noSpan' means \"unknown\", which is what nodes
--   synthesised during elaboration get.
--
--   The end position points /after/ the last character of the region, so a
--   one-character span is @(l, c) .. (l, c + 1)@.
data Span = Span {
    spanFile        :: !Text
  , spanStartLine   :: !Int
  , spanStartColumn :: !Int
  , spanEndLine     :: !Int
  , spanEndColumn   :: !Int
  } deriving (Eq, Ord, Show)

-- | The absence of position information.
noSpan :: Span
noSpan = Span T.empty 0 0 0 0

isNoSpan :: Span -> Bool
isNoSpan (Span _ sl sc el ec) = sl == 0 && sc == 0 && el == 0 && ec == 0

-- | A zero-width span at a point of the given file.
spanAt :: Text -> Int -> Int -> Span
spanAt f l c = Span f l c l c

-- | Extend a span so that it also covers the point @(l, c)@.
spanTo :: Int -> Int -> Span -> Span
spanTo l c s
  | isNoSpan s = Span (spanFile s) l c l c
  | l > spanEndLine s = s {spanEndLine = l, spanEndColumn = c}
  | l == spanEndLine s && c > spanEndColumn s = s {spanEndColumn = c}
  | otherwise = s

-- | The smallest span covering both arguments.  A missing span is ignored.
mergeSpan :: Span -> Span -> Span
mergeSpan a b
  | isNoSpan a = b
  | isNoSpan b = a
  | otherwise =
      Span {
        spanFile        = if T.null (spanFile a) then spanFile b else spanFile a
      , spanStartLine   = startLine
      , spanStartColumn = startColumn
      , spanEndLine     = endLine
      , spanEndColumn   = endColumn
      }
  where
    (startLine, startColumn) = min (spanStart a) (spanStart b)
    (endLine, endColumn) = max (spanEnd a) (spanEnd b)

-- | The smallest span covering a whole list.
mergeSpans :: [Span] -> Span
mergeSpans = foldr mergeSpan noSpan

-- | Start point as @(line, column)@.
spanStart :: Span -> (Int, Int)
spanStart s = (spanStartLine s, spanStartColumn s)

-- | End point as @(line, column)@.
spanEnd :: Span -> (Int, Int)
spanEnd s = (spanEndLine s, spanEndColumn s)

-- | @file:line:column@, or just @line:column@ when the file is unknown.
prettyPoint :: Span -> Text
prettyPoint s
  | isNoSpan s = "?"
  | T.null (spanFile s) = T.pack (show (spanStartLine s) <> ":" <> show (spanStartColumn s))
  | otherwise =
      spanFile s <> ":" <> T.pack (show (spanStartLine s) <> ":" <> show (spanStartColumn s))

-- | @file:line:column@ or @file:line:column-line:column@.
prettySpan :: Span -> Text
prettySpan s
  | isNoSpan s = "?"
  | spanEndLine s == spanStartLine s && spanEndColumn s <= spanStartColumn s + 1 = prettyPoint s
  | spanEndLine s == spanStartLine s =
      prettyPoint s <> "-" <> T.pack (show (spanEndColumn s))
  | otherwise =
      prettyPoint s <> "-" <> T.pack (show (spanEndLine s) <> ":" <> show (spanEndColumn s))

-- | Is the given point inside the span?
pointInSpan :: Int -> Int -> Span -> Bool
pointInSpan l c s
  | isNoSpan s = False
  | otherwise = (l, c) >= spanStart s && (l, c) <= spanEnd s
