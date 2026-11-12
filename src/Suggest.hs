{-# LANGUAGE OverloadedStrings #-}

-- | "Did you mean?" suggestions for a name that is close to one in scope.
--
--   The distance is the optimal string alignment distance (Damerau--Levenshtein
--   with adjacent transpositions, which is the usual sense of a typo): swapping
--   two neighbouring characters counts as one edit, so @lenght@ is one edit
--   from @length@ and not two.  Plain Levenshtein calls that two and, for a
--   short name, misses it.
--
--   A candidate is offered when its distance is within 'threshold', which grows
--   with the length of the name.  A tie at the nearest distance is not broken
--   arbitrarily: an ambiguous suggestion is worse than none, so both are
--   suppressed.
module Suggest (
  distance,
  threshold,
  candidates,
  best,
  suggestionNote,
  typoNote
) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.List (sortOn)

-- | Optimal string alignment distance between two strings: insertions,
--   deletions, substitutions and transpositions of adjacent characters.
--
--   > distance "abc" "abc" == 0
--   > distance "lenght" "length" == 1
--   > distance "" "abc" == 3
--
--   Identifiers are short, so the full table is kept rather than a rolling pair
--   of rows: the transposition rule reaches two rows back, and the clarity is
--   worth more than the few cells of memory.
distance :: Text -> Text -> Int
distance a b = table !! n !! m
  where
    as = T.unpack a
    bs = T.unpack b
    n = length as
    m = length bs

    -- @table !! i !! j@ is the distance from @take i as@ to @take j bs@.
    table = [[entry i j | j <- [0 .. m]] | i <- [0 .. n]]

    entry 0 j = j
    entry i 0 = i
    entry i j
      | as !! (i - 1) == bs !! (j - 1) = table !! (i - 1) !! (j - 1)
      | transposed = 1 + table !! (i - 2) !! (j - 2)
      | otherwise = 1 + minimum [
            table !! (i - 1) !! j
          , table !! i !! (j - 1)
          , table !! (i - 1) !! (j - 1)
          ]
      where
        transposed =
          i > 1 && j > 1
            && as !! (i - 1) == bs !! (j - 2)
            && as !! (i - 2) == bs !! (j - 1)

-- | How far a typo may be from the name it mistypes: one edit for a short name,
--   more for a long one, so that @freezeRowMutiIn@ can still suggest
--   @freezeRowMutIn@.
threshold :: Text -> Int
threshold name = max 1 (T.length name `div` 3)

-- | The names within 'threshold' of the target, nearest first.  At most three
--   are returned, and the target itself is never among them.
candidates :: [Text] -> Text -> [Text]
candidates names target =
  take 3 . map snd . sortOn fst $
    [ (d, n)
    | n <- names
    , n /= target
    , let d = distance target n
    , d <= threshold target
    ]

-- | The single best candidate, or 'Nothing' when there is none or when the
--   nearest distance is shared.
--
--   Silence on a tie is deliberate: @par@ is one edit from both @var@ and
--   @say@, and picking one of them by the order of a map teaches the user the
--   wrong name.
best :: [Text] -> Text -> Maybe Text
best names target =
  case candidates names target of
    [] -> Nothing
    (c:rest)
      | any ((== distance target c) . distance target) rest -> Nothing
      | otherwise -> Just c

-- | The note a diagnostic carries, if a suggestion is worth making.
suggestionNote :: [Text] -> Text -> Maybe Text
suggestionNote names target =
  case best names target of
    Nothing -> Nothing
    Just n  -> Just ("did you mean `" <> n <> "`?")

-- | A stricter variant for the one place where a suggestion is allowed to turn
--   a previously accepted program into an error: an undeclared type name.
--
--   There, an opaque type is legitimate (a program may name a type it does not
--   declare), so a hint must be unambiguous in a stronger sense than usual: the
--   name must be exactly one edit from the declared one, that candidate must be
--   the only one at that distance, and the name must be long enough for a
--   single edit to be a typo rather than a coincidence.  @Foo@ next to @Food@ is
--   therefore left alone, while @Prise@ next to @Price@ is reported.
typoNote :: [Text] -> Text -> Maybe Text
typoNote names target
  | T.length target < 4 = Nothing
  | otherwise = case best names target of
      Just n | distance target n == 1 -> Just ("did you mean `" <> n <> "`?")
      _ -> Nothing
