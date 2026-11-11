{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Lexer (
  Token(..),
  LToken(..),
  Keyword(..),
  tokens,
  token
)
where
import Data.Void
import Data.Text(Text)
import qualified Data.Text as T

import Text.Megaparsec(Parsec, choice, some, MonadParsec (notFollowedBy, try, eof), satisfy, oneOf, between, optional, many, SourcePos, getSourcePos)
import Text.Megaparsec.Char(space1, char, string)
import qualified Text.Megaparsec.Char.Lexer as L
import GHC.Unicode (isAlphaNum, isDigit, isHexDigit)
import Data.Maybe (fromMaybe)
import Data.Scientific (Scientific, scientific)
import Data.Char (digitToInt)
import Data.Functor (($>))
import Utils (Pretty (..))

type Lexer = Parsec Void Text

tokens :: Lexer [LToken]
tokens = between sc eof $ many locatedToken

sc :: Lexer ()
sc = L.space
  space1
  (L.skipLineComment "//|")
  (L.skipBlockComment "/|" "|\\")

lexeme :: Lexer a -> Lexer a
lexeme = L.lexeme sc

sym :: Text -> Token -> Lexer Token
sym s t = t <$ L.symbol sc s

kw :: Text -> Keyword -> Lexer Token
kw s k = lexeme $ TKW k <$ try (string s <* notFollowedBy normalChar)

digit, hexDigit :: Lexer Char

digit = satisfy isDigit
hexDigit = satisfy isHexDigit

stripUnderscore :: String -> String
stripUnderscore = filter (/= '_')

parseDecInt :: String -> Integer
parseDecInt = read . stripUnderscore

parseHexInt :: String -> Integer
parseHexInt =
  foldl (\acc d -> acc * 16 + fromIntegral (digitToInt d)) 0
  . stripUnderscore

intDigitPart :: Lexer String
intDigitPart = do
  prefix <- some digit
  suffix <- many $ char '_' *> some digit
  pure $ prefix <> concat suffix

hexIntDigitPart :: Lexer String
hexIntDigitPart = do
  prefix <- some hexDigit
  suffix <- many $ char '_' *> some hexDigit
  pure $ prefix <> concat suffix

exponentPart :: Lexer String
exponentPart = do
  e <- oneOf ['e', 'E']
  s <- optional $ oneOf ['+', '-']
  ds <- some digit
  pure $ e : maybe "" pure s <> ds

hexExponentPart :: Lexer String
hexExponentPart = do
  p <- oneOf ['p','P']
  s <- optional $ oneOf ['+', '-']
  ds <- some digit
  pure $ p : maybe "" pure s <> ds

parseExponent :: String -> Int
parseExponent [] = 0
parseExponent (_:rest) =
  case rest of
    '-':ds -> negate (read ds)
    '+':ds -> read ds
    ds     -> read ds

intLiteral :: Lexer Integer
intLiteral = lexeme $ parseDecInt <$> intDigitPart

hexIntLiteral :: Lexer Integer
hexIntLiteral = lexeme $ char '0' *> oneOf ['x', 'X'] *> (parseHexInt <$> hexIntDigitPart)

floatLiteral :: Lexer Scientific
floatLiteral = lexeme $ do
  a <- intDigitPart
  _ <- char '.'
  b <- intDigitPart
  e <- optional exponentPart

  let mantissa = parseDecInt $ a <> b
      scale    = negate $ length $ stripUnderscore b
      base     = scientific mantissa scale

  pure $ maybe base (\ex -> base * (10 ^^ parseExponent ex)) e

hexFloatLiteral :: Lexer Scientific
hexFloatLiteral = lexeme $ do
  _ <- char '0'
  _ <- oneOf ['x', 'X']
  (a, b) <- choice [
    do
      a <- optional hexIntDigitPart
      _ <- char '.'
      (,) (fromMaybe "" a) <$> hexIntDigitPart,
    do (, "") <$> hexIntDigitPart
    ]
  e <- hexExponentPart

  let
    mantissa = parseHexInt $ a <> b
    fracLen  = length $ stripUnderscore b
    base     = scientific mantissa $ (-4) * fracLen
    exp2     = parseExponent e

  pure $ base * (2 ^^ exp2)


normalChar :: Lexer Char
normalChar = satisfy (\c -> isAlphaNum c || elem c ("_+/%|&^~<=>.*!?-" :: String))

nameText :: Lexer Text
nameText = T.pack <$> some normalChar

name :: Lexer Token
name = lexeme $ TName <$> nameText

tvar :: Lexer Token
tvar = lexeme $ TTVar <$> (char '`' *> nameText)

infixName :: Lexer Token
infixName = lexeme $ TInfixName <$> between (char '`') (char '`') nameText

locatedToken :: Lexer LToken
locatedToken = LToken <$> getSourcePos <*> token

token :: Lexer Token
token = choice [
    try infixName,
    tvar,
    sym "$" TDollar,
    sym "@" TAt,
    sym "#[" TSharpSquareL, sym "[" TSquareL, sym "]" TSquareR,
    sym "#{" TSharpBraceL,  sym "{" TBraceL,  sym "}" TBraceR,
    sym "(" TParenL,        sym ")" TParenR,
    sym ":=" TRebind,
    sym ":" TColon,
    sym ";" TSemi,
    sym "," TComma,
    sym "..." TEllipsis,
    sym "=>" TMatchArrow,
    sym "==>" THRPArrow,
    sym "=" TAssign,
    sym "|" TPipe,
    sym "_" TUnderscore,
    sym "->" TArrow,
    kw "effect" KWEffect,
    kw "else" KWElse,
    kw "end" KWEnd,
    choice $ map (`kw` KWFalse) ["false", "⊥"],
    choice $ map (`kw` KWForall) ["forall", "∀"],
    kw "funct" KWFunct,
    kw "handle" KWHandle,
    kw "if" KWIf,
    choice $ map (`kw` KWIn) ["in", "∈"],
    kw "imm" KWImm,
    kw "let" KWLet,
    kw "match" KWMatch,
    kw "resume" KWResume,
    kw "row" KWRow,
    kw "then" KWThen,
    kw "to" KWTo,
    choice $ map (`kw` KWTrue) ["true", "⊤"],
    kw "type" KWType,
    kw "under" KWUnder,
    kw "val" KWVal,
    kw "var" KWVar,
    kw "with" KWWith,
    THexFloat <$> try hexFloatLiteral,
    TFloat <$> try floatLiteral,
    THexInt <$> try hexIntLiteral,
    TInt <$> intLiteral,
    charString,
    name
  ]

stringChar :: Lexer Char
stringChar =
  choice [
    string "\\\\" $> '\\',
    string "\\'" $> '\'',
    satisfy (/= '\'')
  ]


charString :: Lexer Token
charString = lexeme $ TString . T.pack <$> between (char '\'') (char '\'') (many stringChar)

data LToken = LToken {ltPos :: SourcePos, ltToken :: Token} deriving (Eq, Show, Ord)

data Token =
  TDollar
  | TAt
  | TColon
  | TComma
  | TSemi
  | TEllipsis

  | TParenL       | TParenR
  | TBraceL       | TBraceR
  | TSquareL      | TSquareR
  | TSharpBraceL  | TSharpSquareL

  | TAssign
  | TRebind
  | TPipe

  | TUnderscore
  | TArrow
  | TMatchArrow
  | THRPArrow

  | TKW Keyword        -- ключевые слова
  | TName Text
  | TInfixName Text
  | TTVar Text

  | TInt Integer
  | TFloat Scientific
  | THexInt Integer
  | THexFloat Scientific

  | TString Text
  | TNil
  deriving (Show, Eq, Ord)

instance Pretty Token where
  pretty = \case
    TDollar   -> "$"
    TAt       -> "@"
    TColon    -> ":"
    TComma    -> ","
    TSemi     -> ";"
    TEllipsis -> "..."

    TParenL       -> "("
    TParenR       -> ")"
    TBraceL       -> "{"
    TBraceR       -> "}"
    TSquareL      -> "["
    TSquareR      -> "]"
    TSharpBraceL  -> "#{"
    TSharpSquareL -> "#["

    TAssign -> "="
    TRebind -> ":="
    TPipe   -> "|"

    TUnderscore -> "_"
    TArrow      -> "->"
    TMatchArrow -> "=>"
    THRPArrow   -> "==>"

    TKW k         -> pretty k
    TName n       -> n
    TInfixName n  -> "`" <> n <> "`"
    TTVar v       -> "`" <> v

    TInt i      -> T.pack $ show i
    TFloat f    -> T.pack $ show f
    THexInt i   -> T.pack $ show i
    THexFloat f -> T.pack $ show f

    TString s -> "'" <> s <> "'"
    TNil      -> "()"

data Keyword =
  KWEffect
  | KWElse
  | KWEnd
  | KWFalse
  | KWForall
  | KWFunct
  | KWHandle
  | KWIf
  | KWIn
  | KWImm
  | KWLet
  | KWMatch
  | KWResume
  | KWRow
  | KWThen
  | KWTo
  | KWTrue
  | KWType
  | KWUnder
  | KWVal
  | KWVar
  | KWWith
  deriving (Show, Eq, Ord)

instance Pretty Keyword where
  pretty = \case
    KWEffect  -> "effect"
    KWElse    -> "else"
    KWEnd     -> "end"
    KWFalse   -> "false"
    KWForall  -> "forall"
    KWFunct   -> "funct"
    KWHandle  -> "handle"
    KWIf      -> "if"
    KWIn      -> "in"
    KWImm     -> "imm"
    KWLet     -> "let"
    KWMatch   -> "match"
    KWResume  -> "resume"
    KWRow     -> "row"
    KWThen    -> "then"
    KWTo      -> "to"
    KWTrue    -> "true"
    KWType    -> "type"
    KWUnder   -> "under"
    KWVal     -> "val"
    KWVar     -> "var"
    KWWith    -> "with"