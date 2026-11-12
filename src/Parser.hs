{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Parser(
  Parser,
  chunk,
  parseTokens,
  parseTokensUnposed,
  parseTok,
  parseFromText,
  parseFromTextNamed,
  parseTokensNamed,
  parseTokNamed,
  ParseErrorInfo(..),
  parseDiagnostic,
  parseErrorInfo,
  renderParseError,
  renderParseErrorIn,
  sourceMapFor,
  currentPos,
  Parser.exp,
  letExp,
  number,
  floatLiteral,
  intLiteral,
  stringLiteral,
  bool,
  tupleOrExp,
  block,
  blockStat,
  lambda,
  parens,
  effCons,
  effRow,
  typ,
  typAtom,
  typeDef
)
where
import Data.Void
import Data.Text(Text)

import Text.Megaparsec(
    Parsec,
    runParser,
    many,
    MonadParsec (eof, try, lookAhead, notFollowedBy),
    choice,
    optional,
    some,
    sepBy1,
    sepBy,
    (<|>),
    satisfy,
    between,
    VisualStream (showTokens, tokensLength),
    TraversableStream (reachOffset),
    PosState (pstateInput, pstateSourcePos, pstateOffset),
    getParserState, updateParserState,
    State (stateInput, statePosState), PosState (pstateSourcePos),
    SourcePos(..), mkPos, unPos
  )
import Text.Megaparsec.Error (
    ParseErrorBundle,
    ParseError(..),
    ErrorItem(..),
    ErrorFancy(..),
    ShowErrorComponent(..),
    bundleErrors,
    bundlePosState,
    errorOffset
  )
import qualified Data.List.NonEmpty as NE
import qualified Data.Set as Set
import qualified Text.Megaparsec.Stream as MP
import ErrorContext (
    Diagnostic(..), diagnostic, primaryLabel, renderDiagnostic,
    Severity(SevError), SourceMap, emptySourceMap, insertSource
  )
import Lexer (
    Token (..),
    tokens,
    Keyword (..), LToken (..)
  )
import Data.Scientific (Scientific)
import Data.Maybe (fromMaybe, isJust, fromJust)
import Control.Monad.Combinators.Expr (makeExprParser, Operator (InfixR, Postfix, Prefix, InfixL))
import Data.Functor (($>), void)
import Span (Span(..), mergeSpan)
import Ast
import Control.Monad (MonadPlus)
import qualified Data.Text as T
import Utils (Pretty(pretty))
import Data.Foldable (toList)

type Parser = Parsec Void [LToken]

-- | A parse failure, described the way the renderer wants it: a one-line
--   message, the region of the source it is about, and any extra notes.
data ParseErrorInfo = ParseErrorInfo {
    peMessage :: Text
  , peSpan    :: Span
  , peNotes   :: [Text]
  } deriving (Eq, Show)

-- | How one token of the grammar is shown in a message.  Quotes keep a token
--   from blending into the surrounding prose.
renderLToken :: LToken -> Text
renderLToken = pretty . ltToken

-- | The code every syntax error carries.
syntaxErrorCode :: Text
syntaxErrorCode = "E0013"

-- | Turn a parse failure into a 'Diagnostic'.  The caller supplies the source
--   map, because only it knows the text of the file; without one the renderer
--   still prints the header and the location.
parseDiagnostic :: ParseErrorInfo -> Diagnostic
parseDiagnostic e =
  (diagnostic SevError (Just syntaxErrorCode) (peMessage e)) {
      diagLabels = [primaryLabel (peSpan e) ""]
    , diagNotes  = peNotes e
    }

-- | Render a parse failure with no source to quote.
renderParseError :: ParseErrorInfo -> Text
renderParseError = renderDiagnostic emptySourceMap . parseDiagnostic

-- | Describe the first error of a Megaparsec bundle.
--
--   Megaparsec reports an offset into the stream; 'reachOffset' turns it into
--   a position, which becomes the start of the span.  The width of the
--   offending chunk gives the span its extent, so the caret run covers the
--   token rather than a single character.
--
--   The two stages of the front end have different token types (the lexer
--   reads characters, the grammar reads 'LToken's), so the caller supplies the
--   rendering of a token: that is the only thing the description needs.
fromBundle ::
     forall s e.
     (VisualStream s, TraversableStream s, ShowErrorComponent e)
  => (MP.Token s -> Text) -> FilePath -> ParseErrorBundle s e -> ParseErrorInfo
fromBundle renderToken file bundle =
  ParseErrorInfo {peMessage = message, peSpan = span', peNotes = []}
  where
    err    = NE.head (bundleErrors bundle)
    offset = errorOffset err
    (_, st) = reachOffset offset (bundlePosState bundle)
    pos    = pstateSourcePos st
    line   = unPos (sourceLine pos)
    column = unPos (sourceColumn pos)
    fileName = sourceName pos
    span'  = Span
      { spanFile        = T.pack (if null fileName then file else fileName)
      , spanStartLine   = line
      , spanStartColumn = column
      , spanEndLine     = line
      , spanEndColumn   = column + width
      }

    (message, width) = case err of
      TrivialError _ item expected ->
        let (found, w) = case item of
              Nothing         -> ("the input ends unexpectedly", 1)
              Just (Tokens ts) -> ("unexpected `" <> renderChunk ts <> "`", chunkWidth ts)
              Just (Label l)   -> ("unexpected " <> T.pack (NE.toList l), 1)
              Just EndOfInput  -> ("unexpected end of input", 1)
            -- At end of input Megaparsec says it expected "end of input",
            -- which repeats what was just said.
            expected' = [ described
                        | x <- Set.toList expected
                        , let described = describeItem x
                        , not (isEmpty item && described == "end of input")
                        ]
        in (found <> expectedText expected', w)
      FancyError _ xs ->
        (T.intercalate "; " (map describeFancy (Set.toList xs)), 1)

    renderChunk :: NE.NonEmpty (MP.Token s) -> Text
    renderChunk = T.concat . map renderToken . NE.toList

    chunkWidth :: NE.NonEmpty (MP.Token s) -> Int
    chunkWidth ts = max 1 (sum (map (T.length . renderToken) (NE.toList ts)))

    describeItem = \case
      Tokens ts   -> "`" <> renderChunk ts <> "`"
      Label l     -> T.pack (NE.toList l)
      EndOfInput  -> "end of input"

    isEmpty :: Maybe a -> Bool
    isEmpty Nothing  = True
    isEmpty (Just _) = False

    describeFancy :: ErrorFancy e -> Text
    describeFancy = \case
      ErrorFail m           -> T.pack m
      ErrorCustom custom    -> T.pack (showErrorComponent custom)
      ErrorIndentation {}   -> "the indentation is not a multiple of the tab width"

-- | @; expected a, b, c@, with a cap so that a parser with many alternatives
--   does not produce a wall of text.
expectedText :: [Text] -> Text
expectedText [] = ""
expectedText xs =
  "; expected " <> T.intercalate ", " shown
    <> if hidden == 0 then "" else ", or " <> T.pack (show hidden) <> " more"
  where
    shown  = take 4 xs
    hidden = length xs - length shown

instance VisualStream [LToken] where
  showTokens _ = T.unpack . mconcat . map (pretty . ltToken) . toList
  tokensLength _ = sum . map (T.length . pretty . ltToken) . toList

instance TraversableStream [LToken] where
  reachOffset o posState =
    let input = pstateInput posState
        newPos = case drop o input of
          (LToken pos _:_) -> pos
          [] -> pstateSourcePos posState
        posState' = posState {
          pstateOffset = o,
          pstateInput = drop o input,
          pstateSourcePos = newPos
        }
    in (Nothing, posState')

parseTokens :: Text -> Either String [LToken]
parseTokens input = parseTokensNamed "<test>" input

parseTokensUnposed :: Text -> Either String [Token]
parseTokensUnposed input = map ltToken <$> parseTokensNamed "<test>" input

parseExp :: [LToken] -> Either String Exp
parseExp input = case runParser Parser.exp "<exp>" input of
  Left err -> Left . T.unpack $ renderParseError $ fromBundle renderLToken "<exp>" err
  Right e -> Right e

-- | Parse a stream of tokens that has already been produced.  The tokens carry
--   their own positions, so the error already knows where it is; @file@ is only
--   used when the stream is empty.
parseTok :: Parser a -> [LToken] -> Either String a
parseTok = parseTokNamed ""

parseFromText :: Parser a -> Text -> Either String a
parseFromText = parseFromTextNamed "<test>"

-- | Like 'parseFromText', but records the given name in every 'Span'.
parseFromTextNamed :: FilePath -> Parser a -> Text -> Either String a
parseFromTextNamed file parser txt = do
  let sources = sourceMapFor file txt
  case parseTokensIn sources file txt of
    Left err -> Left err
    Right ts -> parseTokIn sources file parser ts

parseTokensNamed :: FilePath -> Text -> Either String [LToken]
parseTokensNamed file input = parseTokensIn (sourceMapFor file input) file input

-- | The lexer stage, rendered against the source text it is lexing.
parseTokensIn :: SourceMap -> FilePath -> Text -> Either String [LToken]
parseTokensIn sources file input = case runParser tokens file input of
  Left err -> Left . T.unpack $ renderParseErrorIn sources $
    fromBundle T.singleton file err
  Right ts -> Right ts

parseTokNamed :: FilePath -> Parser a -> [LToken] -> Either String a
parseTokNamed = parseTokIn emptySourceMap

-- | The grammar stage.  @sources@ is what lets the error quote the offending
--   line; the spans themselves come from the tokens, which carry positions.
parseTokIn :: SourceMap -> FilePath -> Parser a -> [LToken] -> Either String a
parseTokIn sources file p toks =
  case runParser (p <* eof) file toks of
    Left err -> Left . T.unpack $ renderParseErrorIn sources $
      fromBundle renderLToken file err
    Right e -> Right e

-- | The same failures as 'renderParseError', but with the source text
--   available so that the offending line is quoted under the carets.
renderParseErrorIn :: SourceMap -> ParseErrorInfo -> Text
renderParseErrorIn sources = renderDiagnostic sources . parseDiagnostic

-- | Expose the structured form of a parse failure, for callers that own a
--   source map and want to render it themselves.
parseErrorInfo ::
     (VisualStream s, TraversableStream s, ShowErrorComponent e)
  => (MP.Token s -> Text) -> FilePath -> ParseErrorBundle s e -> ParseErrorInfo
parseErrorInfo = fromBundle

-- | Build a source map with one file in it, which is what a caller needs in
--   order to render a diagnostic that points into that file.
sourceMapFor :: FilePath -> Text -> SourceMap
sourceMapFor file contents = insertSource (T.pack file) contents emptySourceMap

-- | The end of the last consumed token.  Megaparsec does not maintain this,
--   so 'tok' records it: every consumed token sets 'pstateSourcePos' to the
--   position just after itself.
lastConsumedEnd :: Parser SourcePos
lastConsumedEnd = pstateSourcePos . statePosState <$> getParserState

-- | The position of the next token, or the end of the last consumed one at
--   end of input.  Every token carries its own position, so the token stream
--   is the reliable source here.
currentPos :: Parser SourcePos
currentPos = do
  st <- getParserState
  pure $ case stateInput st of
    (LToken p _ : _) -> p
    [] -> pstateSourcePos (statePosState st)

-- | A span from the first position to the second; the two are ordered so that
--   the result is never empty in the wrong direction.
spanFromPositions :: SourcePos -> SourcePos -> Span
spanFromPositions a b =
  Span {
    spanFile        = T.pack (sourceName a)
  , spanStartLine   = min (unPos $ sourceLine a) (unPos $ sourceLine b)
  , spanStartColumn = if la <= lb then ca else cb
  , spanEndLine     = max la lb
  , spanEndColumn   = if la >= lb then ca else cb
  }
  where
    la = unPos $ sourceLine a
    ca = unPos $ sourceColumn a
    lb = unPos $ sourceLine b
    cb = unPos $ sourceColumn b

-- | Extend a span up to the current position.
spanUpToHere :: Span -> Parser Span
spanUpToHere start = do
  end <- currentPos
  pure $ mergeSpan start (spanFromPositions end end)

-- | Run a node parser and attach the span covering exactly what it consumed.
loc :: Parser ExpNode -> Parser Exp
loc p = do
  start <- currentPos
  n <- p
  span' <- spanUpToHere (spanFromPositions start start)
  pure $ Exp span' n

-- | Attach a node to a span that already starts at the right place.
withSpanFrom :: Span -> ExpNode -> Parser Exp
withSpanFrom start n = Exp <$> spanUpToHere start <*> pure n

-- | Run a statement parser and attach the span covering exactly what it
--   consumed.  Statements carry their own position so that errors about the
--   statement as a whole (not about a subexpression) can point at the line.
locStat :: Parser BlockStatNode -> Parser BlockStat
locStat p = do
  start <- currentPos
  n <- p
  span' <- spanUpToHere (spanFromPositions start start)
  pure $ BlockStat span' n

tok :: (Token -> Maybe a) -> Parser a
tok f = do
  LToken p t <- satisfy (isJust . f . ltToken)
  -- Record where this token ends, so that a node ending at end of input still
  -- gets a non-empty span.  Tokens never span lines.
  updateParserState $ \st -> st {
      statePosState = (statePosState st) {
        pstateSourcePos = p {sourceColumn = mkPos (unPos (sourceColumn p) + T.length (pretty t))}
      }
    }
  pure $ fromJust $ f t
  -- satisfyMap
  -- where

    -- satisfyMap :: (Token -> Maybe a) -> Parser a
    -- satisfyMap f = do
    --   t <- satisfy (\p -> isJust (f $ ltToken p))
    --   pure $ fromJust $ f t

keyword :: Keyword -> Parser ()
keyword kw = tok test
  where
    test (TKW k) | k == kw = Just ()
    test _ = Nothing

name, infixName, meta :: Parser Text
name = tok test
  where
    test (TName t) = Just t
    test _ = Nothing

infixName = tok test
  where
    test (TInfixName t) = Just t
    test _ = Nothing

meta = tok test
  where
    test (TTVar t) = Just t
    test _ = Nothing

constantQualifier :: Parser ConstantQualifier
constantQualifier = tok test
  where
    test = \case
      (TKW KWVal) -> Just Val
      (TKW KWVar) -> Just Var
      (TKW KWImm) -> Just Imm
      _ -> Nothing

symbol :: Token -> Parser ()
symbol t = tok test
  where
    test x | x == t = Just ()
    test _ = Nothing

intLiteral :: Parser Integer
intLiteral = tok test
  where
    test (TInt n) = Just n
    test (THexInt n) = Just n
    test _ = Nothing

floatLiteral :: Parser Scientific
floatLiteral = tok test
  where
    test (TFloat n) = Just n
    test (THexFloat n) = Just n
    test _ = Nothing

stringLiteral :: Parser Text
stringLiteral = tok test
  where
    test (TString s) = Just s
    test _ = Nothing

bool :: Parser Bool
bool = tok test
  where
    test (TKW KWTrue) = Just True
    test (TKW KWFalse) = Just False
    test _ = Nothing

betweenSymbols :: Token -> Token -> Parser a -> Parser a
betweenSymbols l = between (symbol l) . symbol

brackets, braces, sharpBraces, parens :: Parser a -> Parser a
brackets = betweenSymbols TSquareL TSquareR
braces = betweenSymbols TBraceL TBraceR
sharpBraces = betweenSymbols TSharpBraceL TBraceR
parens = betweenSymbols TParenL TParenR

semisym, colonsym, pipesym, commasym :: Parser ()
semisym = symbol TSemi
colonsym = symbol TColon
pipesym = symbol TPipe
commasym = symbol TComma

chunk :: Parser Chunk
chunk = Chunk <$> many topLevelStat <* eof

topLevelStat :: Parser TopLevelStat
topLevelStat = locTop $ choice [typeDef, effDef, rowDef, functDef]

-- | Run a declaration parser and give the result the span it covers.  The
--   declaration parsers build their node without a position, so the start is
--   recorded here once instead of in each of them.
locTop :: Parser (Span -> TopLevelStat) -> Parser TopLevelStat
locTop p = do
  start <- currentPos
  mk <- p
  sp <- spanUpToHere (spanFromPositions start start)
  pure $ mk sp

typeDef :: Parser (Span -> TopLevelStat)
typeDef = do
  keyword KWType
  n <- name
  ts <- fromMaybe mempty <$> optional typeParams
  -- es <- fromMaybe mempty <$> optional effParams
  symbol TAssign
  t <- typ
  pure $ \sp -> TypeDef sp n ts t

typeParams :: Parser TypeParams
typeParams = TypeParams <$> brackets (some name)

effParams :: Parser EffParams
effParams = do
  symbol TBraceL
  es <- fromMaybe [] <$> optional (some name)
  rs <- fromMaybe [] <$> optional (pipesym *> some name)
  symbol TBraceR
  pure $ EffParams es rs

typ :: Parser Typ
typ = functType
-- typ = makeExprParser typAtom table
--   where
--     table = [[InfixR $ TPair <$ commasym], [InfixR functionOp]]
--     functionOp = do
--       symbol TArrow
--       eff <- optional effRow
--       pure $ \from to -> TFunct from to eff

functType :: Parser Typ
functType = do
  from <- pairType
  m <- optional $ try $ do
    symbol TArrow
    choice [
        try $ do
          row <- arrowEffRow
          to <- functType
          pure (Just row, to),
        do
          to <- functType
          pure (Nothing, to)
      ]
  pure $ case m of
    Nothing -> from
    Just (fx, to) -> TFunct $ Funct from to (fromMaybe (ERSugar [] Nothing) fx)

pairType :: Parser Typ
pairType = do
  l <- typAtom
  r <- optional (commasym *> pairType)
  pure $ maybe l (TPair l) r

arrowEffRow :: Parser EffRow
arrowEffRow =
  try (braces $ ERSugar <$> sepBy effRowEntry semisym <*> optional (pipesym *> meta))
  <|> try (do
    n <- name
    _ <- lookAhead typeAtomStart
    pure $ ERAlias n)
  <|> try (do
    n <- meta
    _ <- lookAhead typeAtomStart
    pure $ ERVar n)
  where
    typeAtomStart :: Parser ()
    typeAtomStart =
      choice [
        void $ lookAhead name,
        void $ lookAhead meta,
        void $ lookAhead (symbol TParenL),
        void $ lookAhead (symbol TSquareL),
        void $ lookAhead (symbol TSharpBraceL),
        void $ lookAhead (keyword KWForall)
      ]

typAtom :: Parser Typ
typAtom =
  choice [
    try $ TGenericAlias <$> name <*> typeApps,
    TFlat <$> name,
    Ast.TNil <$ nil,
    TArray <$> brackets typ,
    try $ TParen <$> parens typ,
    TVar <$> meta,
    TRecord <$> recordType,
    forallType
  ]

recordType :: Parser RecordTyp
recordType = sharpBraces $
  RecordTyp <$> sepBy1 recordTProp (optional semisym) <* optional semisym

forallType :: Parser Typ
forallType = do
  keyword KWForall
  (ts, es) <- choice [
      -- ts es
      try $ (,) <$> typeParams <*> effParams,
      -- ts
      (, mempty) <$> typeParams,
      -- es
      (mempty, ) <$> effParams
    ]
  symbol THRPArrow
  TForall ts es <$> typ

recordTProp :: Parser RecordTypProp
recordTProp = do
  q <- constantQualifier
  n <- name
  _ <- optional colonsym
  RecordTypProp q n <$> typ

nil :: Parser ()
nil = do
  symbol TParenL
  symbol TParenR
  pure ()

effDef :: Parser (Span -> TopLevelStat)
effDef = do
  keyword KWEffect
  n <- name
  ts <- fromMaybe mempty <$> optional typeParams
  ops <- sepBy effectOp semisym
  keyword KWEnd
  pure $ \sp -> EffectDef sp n ts ops

effectOp :: Parser EffectOp
effectOp = EffectOp <$> name <* colonsym <*> effectOpType

effectOpType :: Parser Funct
effectOpType = do
  from <- pairType
  symbol TArrow
  choice [
      try $ do
        row <- arrowEffRow
        to <- functType
        pure $ Funct from to row,
      do
        to <- functType
        pure $ Funct from to $ ERSugar [] Nothing
    ]

rowDef :: Parser (Span -> TopLevelStat)
rowDef = do
  keyword KWRow
  n <- name
  symbol TAssign
  row <- effRow
  pure $ \sp -> RowDef sp n row

functDef :: Parser (Span -> TopLevelStat)
functDef = do
  keyword KWFunct
  n <- name
  ts <- fromMaybe mempty <$> optional typeParams
  es <- fromMaybe mempty <$> optional effParams
  args <- functArgs
  colonsym
  try $ do
    fx <- optional effRow
    case fx of
      Just (ERAlias a) -> do
        out <- optional typ
        symbol TAssign
        case out of
          Just t -> do
            b <- block
            pure $ \sp -> FunctDef sp n ts es args fx t b
          Nothing -> do
            b <- block
            pure $ \sp -> FunctDef sp n ts es args Nothing (TFlat a) b
      _ -> do
        out <- typ
        symbol TAssign
        b <- block
        pure $ \sp -> FunctDef sp n ts es args fx out b

functArgs :: Parser [FunctArg]
functArgs = some functArg

effRow :: Parser EffRow
effRow =
  choice [
    ERVar <$> meta,
    ERAlias <$> name,
    braces $ ERSugar <$> sepBy effRowEntry semisym <*> optional (pipesym *> meta)
  ]

effRowEntry :: Parser EffRowEntry
effRowEntry =
  choice [
    EREEffCons <$> effCons,
    EREEffRow <$> (symbol TEllipsis *> effRow)
  ]

effCons :: Parser EffCons
effCons = (EVar <$> meta) <|> (EffCons <$> eCons)

eCons :: Parser ECons
eCons = ECons <$> name <*> optional typeApps

block :: Parser Block
block = do
  Block <$> many (try $ blockStat <* semisym) <*> Parser.exp
  -- try (Block [] <$> (Parser.exp <* lookAhead semisym))
  -- <|> try (Block <$> some (blockStat <* semisym) <*> Parser.exp)

blockStat :: Parser BlockStat
blockStat =
  choice [
    try $ locStat $ BBindDefNode <$> bindDef,
    try $ locStat $ BAssignNode <$> assign,
    locStat $ BExpNode <$> Parser.exp
  ]

bindDef :: Parser BindDef
bindDef = do
  cq <- constantQualifier
  lp <- lambdaParam
  symbol TAssign
  BindDef cq lp <$> Parser.exp

lambdaParam :: Parser LambdaParam
lambdaParam = do
  n <- name
  LambdaParam n <$> optional (optional colonsym *> typ)

assign :: Parser Assign
assign = Assign <$> name <* symbol TRebind <*> Parser.exp

letPattern :: Parser LetPattern
--letPattern = choice [LPATom <$> atomLetPattern, LPParam <$> lambdaParam]
letPattern = do
  first <- atom'
  rest <- many $ commasym *> atom'
  pure $ foldr1 pair (first : rest)
  where
    pair l r = LPATom $ ALPPair l r
    atom' = LPATom <$> atomLetPattern <|> LPParam <$> lambdaParam

atomLetPattern :: Parser AtomLetPattern
atomLetPattern = choice [
    ALPNil <$ nil,
    ALPUnderscore <$ symbol TUnderscore,
    ALPParen <$> parens letPattern,
    -- ALPPair <$> letPattern <* commasym <*> letPattern,
    recordLetPattern
  ]

recordLetPattern :: Parser AtomLetPattern
recordLetPattern = sharpBraces $
  ALPRecord <$> sepBy1 atomLetPatternRecordProp semisym <* optional semisym

atomLetPatternRecordProp :: Parser AtomLetPatternRecordProp
atomLetPatternRecordProp = do
  cq <- constantQualifier
  lp <- lambdaParam
  alp <- optional $ do
    symbol TAssign
    atomLetPattern
  pure $ AtomLetPatternRecordProp cq lp alp

functArg :: Parser FunctArg
functArg = parens $ do
  arg <- optional $
    NamedFunctArg <$> name <* optional colonsym <*> typ
  pure $ fromMaybe NilArg arg

typeApps :: Parser TypeApps
typeApps = TypeApps <$> brackets (sepBy typeArg semisym <* optional semisym)

typeArg :: Parser TypeArg
typeArg = makeExprParser typeArgAtom table
  where
    table = [
        [InfixR $ TAPair <$ commasym],
        [InfixR $ TAFunct <$ symbol TArrow]
      ]

typeArgAtom :: Parser TypeArg
typeArgAtom =
  choice [
    try $ TAGenericAlias <$> name <*> typeApps,
    TAFlat <$> name,
    TANil <$ nil,
    try $ TAParen <$> parens typeArg,
    TAArray <$> brackets typeArg,
    TAMeta <$> meta,
    TARecord <$> recordTypeArg
  ]

recordTypeArg :: Parser RecordTypeArg
recordTypeArg = sharpBraces $
  RecordTypeArg <$> sepBy1 recordTypeArgProp (optional semisym) <* optional semisym

recordTypeArgProp :: Parser RecordTypeArgProp
recordTypeArgProp = do
  q <- constantQualifier
  n <- name
  _ <- optional colonsym
  RecordTypeArgProp q n <$> typeArg

effApps :: Parser EffApps
effApps = do
  symbol TBraceL
  es <- sepBy effArg semisym
  rs <- fromMaybe [] <$> optional (pipesym *> some effRow)
  symbol TBraceR
  pure $ EffApps es rs

effArg :: Parser EffArg
effArg = choice [EACons <$> effCons, EARow <$> (symbol TEllipsis *> effRow)]

exp :: Parser Exp
exp = resumeExp --do
  -- e <- applyExp
  -- e' <- parsePostfixOps e
  -- e'' <- parseBackticks e'
  -- parseDollar e''
  -- e <- prefixExp >>= parsePostfix
  -- es <- many $ prefixExp >>= parsePostfix
  -- pure $ foldl EApply e es
resumeExp :: Parser Exp
resumeExp = try (loc $ NResume <$> (keyword KWResume *> resumeExp)) <|> dollarExp


dollarExp :: Parser Exp
dollarExp = do
  e <- backtickExp
  m <- optional (symbol TDollar *> (EDollar e <$> dollarExp))
  pure $ fromMaybe e m

backtickExp :: Parser Exp
backtickExp = do
  e <- withExp
  rest <- many ((,) <$> infixName <*> withExp)
  pure $ foldl (\acc (op, r) -> EBacktick op acc r) e rest

withExp :: Parser Exp
withExp = do
  e <- applyExp
  parseWithOps e

applyExp :: Parser Exp
applyExp = do
  f <- accessExp
  args <- many accessExp
  pure $ foldl EApply f args

accessExp :: Parser Exp
accessExp = do
  e <- prefixExp
  parseAccessOps e

parseAccessOps :: Exp -> Parser Exp
parseAccessOps e = do
  m <- optional $ symbol TAt *> name
  case m of
    Just n -> withSpanFrom (expSpan e) (NPropAccess e n) >>= parseAccessOps
    Nothing -> pure e

parseWithOps :: Exp -> Parser Exp
parseWithOps e = do
  m <- optional $ keyword KWWith *> do
    (ts, es) <- choice [
        try $ (,) <$> typeApps <*> effApps,
        (, EffApps [] []) <$> typeApps,
        (TypeApps [], ) <$> effApps
      ]
    withSpanFrom (expSpan e) (NWith e ts es)
  case m of
    Just e' -> parseWithOps e'
    Nothing -> pure e

-- applyExp :: Parser Exp
-- applyExp = foldl1 EApply <$> some prefixExp
  -- do
  -- f <- simpleTerm
  -- args <- many simpleTerm
  -- pure $ foldl EApply f args

-- Начало выражения
prefixExp :: Parser Exp
prefixExp =
      try ifExp
  <|> try letExp
  <|> try under
  <|> try (loc $ NLiteral <$> literal)
  <|> try parensThing
  <|> (loc $ NName <$> name)

-- Постфикс и инфикс операторы
parsePostfix :: Exp -> Parser Exp
parsePostfix e = do
  -- backtick-инфикс
  e' <- parseBackticks e
  -- $-оператор
  e'' <- parseDollar e'
  -- postfixOps: @ и with
  parsePostfixOps e'' <|> pure e''

-- backtick инфикс
parseBackticks :: Exp -> Parser Exp
parseBackticks e = do
  rest <- many $ (,) <$> infixName <*> prefixExp
  pure $ foldl (\acc (op, r) -> EBacktick op acc r) e rest

-- $-инфикс
parseDollar :: Exp -> Parser Exp
parseDollar e = do
  m <- optional (symbol TDollar *> (EDollar e <$> prefixExp))
  case m of
    Just e' -> parseDollar e'
    Nothing -> pure e

-- postfix опкоды: @Name и with
parsePostfixOps :: Exp -> Parser Exp
parsePostfixOps e = do
  f <- optional (postfixOp e)
  case f of
    Just e' -> parsePostfixOps e'
    Nothing -> pure e

postfixOp :: Exp -> Parser Exp
postfixOp e =
      try $ do
        n <- symbol TAt *> name
        withSpanFrom (expSpan e) (NPropAccess e n)
  <|> (keyword KWWith *> do
        (ts, es) <- choice [
            try $ (,) <$> typeApps <*> effApps,
            (, EffApps [] []) <$> typeApps,
            (TypeApps [], ) <$> effApps
          ]
        withSpanFrom (expSpan e) (NWith e ts es)
      )

-- if-expression
ifExp :: Parser Exp
ifExp = do
  start <- currentPos
  keyword KWIf
  cond <- Parser.exp
  keyword KWThen
  th <- Parser.exp
  keyword KWElse
  e <- Parser.exp
  withSpanFrom (spanFromPositions start start) (NIfThenElse cond th e)

-- let-expression
letExp :: Parser Exp
letExp = do
  start <- currentPos
  keyword KWLet
  lp <- letPattern
  symbol TAssign
  what <- Parser.exp
  keyword KWIn
  e <- Parser.exp
  withSpanFrom (spanFromPositions start start) (NLet lp what e)

-- under-expression
under :: Parser Exp
under = do
  start <- currentPos
  let startSpan = spanFromPositions start start
  keyword KWUnder
  ec <- eCons
  keyword KWTo
  b <- block
  keyword KWHandle
  f <- optional $ try handlerClause
  cs <- many $ try handlerClause
  u <- case f of
        Just f' -> do
          nt <- optional $ do
            _ <- pipesym *> keyword KWThen
            n <- name
            t <- symbol TMatchArrow *> block
            pure (n, t)
          case nt of
            Just (n, t) -> pure $ Under ec b (f' : cs) n t
            -- No 'then' clause: the host handler continues with the identity.
            -- That node has no text of its own, so it borrows the span of the
            -- clause it stands for rather than carrying 'noSpan'.
            Nothing -> do
              end <- currentPos
              let sp = spanFromPositions start end
              pure $ Under ec b (f' : cs) "." (Block [] $ Exp sp (NName "."))
        Nothing -> do
          n <- pipesym *> keyword KWThen *> name
          t <- symbol TMatchArrow *> block
          pure $ Under ec b cs n t
  withSpanFrom startSpan (NUnder u)

parensThing :: Parser Exp
parensThing = do
  start <- currentPos
  symbol TParenL
  e <- try tupleInParens <|> (withSpanFrom (spanFromPositions start start) . NParen =<< block)
  symbol TParenR
  pure $ e {expSpan = mergeSpan (expSpan e) (spanFromPositions start start)}

tupleInParens :: Parser Exp
tupleInParens = do
  first <- Parser.exp
  _ <- commasym
  second <- Parser.exp
  rest <- many (try $ commasym *> Parser.exp)
  _ <- optional commasym
  pure $ foldr1 EPair (first : second : rest)

-- blockInParens :: Parser Exp
-- blockInParens =
--   try (EParen . Block [] <$> (Parser.exp <* lookAhead semisym))
--   <|> try (do
--     sts <- some $ blockStat <* semisym
--     EParen . Block sts <$> Parser.exp)

expNoComma :: Parser Exp
expNoComma = do
  e <- prefixExp >>= parsePostfix
  es <- many $ try $ notFollowedBy (commasym <|> symbol TParenR) *> (prefixExp >>= parsePostfix)
  pure $ foldl EApply e es

tupleOrExp :: Parser Exp
-- tupleOrExp = do
--   first <- expNoComma
--   cs <- optional commasym
--   case cs of
--     Nothing -> pure first
--     Just _ -> do
--       rest <- try $ sepBy1 expNoComma commasym <* optional commasym
--       pure $ foldr1 EPair (first:rest)
tupleOrExp = do
  first <- expNoComma
  rest <- many (commasym *> expNoComma)
  pure $ case rest of
    [] -> first
    xs -> foldr1 EPair (first:xs)

simpleTerm :: Parser Exp
simpleTerm =
    loc (NLiteral <$> literal)
    <|> parensThing
    <|> loc (NName <$> name)

handlerClause :: Parser HandlerClause
handlerClause = do
  pipesym
  n <- name
  args <- many name
  symbol TMatchArrow
  HandlerClause n args <$> block

sepBy2 :: MonadPlus m => m a -> m sep -> m [a]
sepBy2 p sep = do
  a <- p
  _ <- sep
  b <- p
  rest <- many (sep *> p)
  pure $ a : b : rest

resumeOp :: Operator Parser Exp
resumeOp = Prefix $ keyword KWResume $> EResume

postfixProp :: Operator Parser Exp
postfixProp =
  Postfix $
    symbol TAt *> do
      n <- name
      pure $ \e -> EPropAccess e n

postfixWith :: Operator Parser Exp
postfixWith =
  Postfix $
    keyword KWWith *> do
      ts <- typeApps
      es <- effApps
      pure $ \e -> EWith e ts es

backtickOp :: Operator Parser Exp
backtickOp = InfixL $ EBacktick <$> infixName

dollarOp :: Operator Parser Exp
dollarOp = InfixR $ symbol TDollar $> EDollar

literal :: Parser Literal
literal = choice [
    LAtom <$> atom,
    LArray <$> array,
    LLambda <$> lambda,
    LRecord <$> record
  ]

atom :: Parser Atom
atom = choice [
    AString <$> stringLiteral,
    ANumber <$> number,
    ANil <$ nil,
    ABoolean <$> bool
  ]

number :: Parser Number
number = try (NFloat <$> floatLiteral) <|> NInt <$> intLiteral

array :: Parser ArrayLiteral
array = brackets $
  ArrayLiteral <$> sepBy arrayEntry commasym <* optional commasym

arrayEntry :: Parser ArrayEntry
arrayEntry = try (AEBlock <$> block <* semisym) <|> (AEExp <$> Parser.exp)

lambda :: Parser LambdaLiteral
lambda = do
  symbol TBraceL
  ts <- optional typeParams
  es <- optional effParams
  lh <- optional $ try lambdaHead
  b <- block
  symbol TBraceR
  pure $ LambdaLiteral ts es lh b

lambdaHead :: Parser LambdaHead
lambdaHead = do
  lookAhead lambdaHeadStart
  ps <- lambdaParams
  out <- optional $ colonsym *> typ
  symbol TAssign
  pure $ LambdaHead ps out
  where
    lambdaHeadStart :: Parser ()
    lambdaHeadStart = pure ()

lambdaParams :: Parser [LambdaParam]
lambdaParams =
  choice [
    some $ choice [
      parens lambdaParam,
      nil $> LambdaParam "_" Nothing,
      (`LambdaParam` Nothing) <$> name
    ],
    parens $ sepBy1 lambdaParam semisym
  ]

record :: Parser RecordLiteral
record = sharpBraces $
  RecordLiteral <$> optional (Parser.exp <* pipesym) <*> sepBy1 bindDef semisym <* optional semisym