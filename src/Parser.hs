{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Parser(
  Parser,
  chunk,
  parseTokens,
  parseTokensUnposed,
  parseTok,
  parseFromText,
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
    errorBundlePretty,
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
    VisualStream (showTokens),
    TraversableStream (reachOffset),
    manyTill,
    anySingle, PosState (pstateInput, pstateSourcePos, pstateOffset)
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
import Ast
import Control.Monad (MonadPlus)
import Text.Megaparsec.Stream (VisualStream(tokensLength))
import qualified Data.Text as T
import Utils (Pretty(pretty))
import Data.Foldable (toList)

type Parser = Parsec Void [LToken]

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
parseTokens input = case runParser tokens "<test>" input of
  Left err -> Left $ errorBundlePretty err
  Right ts -> Right ts

parseTokensUnposed :: Text -> Either String [Token]
parseTokensUnposed input = case runParser tokens "<test>" input of
  Left err -> Left $ errorBundlePretty err
  Right ts -> Right $ map ltToken ts

parseExp :: [LToken] -> Either String Exp
parseExp input = case runParser Parser.exp "<exp>" input of
  Left err -> Left $ errorBundlePretty err
  Right e -> Right e

parseTok :: Parser a -> [LToken] -> Either String a
parseTok p toks =
  case runParser (p <* eof) "" toks of
    Left err -> Left $ errorBundlePretty err
    Right e -> Right e

parseFromText :: Parser a -> Text -> Either String a
parseFromText parser txt = do
  case parseTokens txt of
    Left err -> Left err
    Right ts -> do parseTok parser ts

tok :: (Token -> Maybe a) -> Parser a
tok f = do
  LToken _ t <- satisfy (isJust . f . ltToken)
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
topLevelStat = choice [typeDef, effDef, rowDef, functDef]

typeDef :: Parser TopLevelStat
typeDef = do
  keyword KWType
  n <- name
  ts <- fromMaybe mempty <$> optional typeParams
  -- es <- fromMaybe mempty <$> optional effParams
  symbol TAssign
  TypeDef n ts <$> typ

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

effDef :: Parser TopLevelStat
effDef = do
  keyword KWEffect
  n <- name
  ts <- fromMaybe mempty <$> optional typeParams
  ops <- sepBy effectOp semisym
  keyword KWEnd
  pure $ EffectDef n ts ops

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

rowDef :: Parser TopLevelStat
rowDef = do
  keyword KWRow
  n <- name
  symbol TAssign
  RowDef n <$> effRow

functDef :: Parser TopLevelStat
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
          Just t -> FunctDef n ts es args fx t <$> block
          Nothing -> FunctDef n ts es args Nothing (TFlat a) <$> block
      _ -> do
        out <- typ
        symbol TAssign
        FunctDef n ts es args fx out <$> block

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
    try $ BBindDef <$> bindDef,
    try $ BAssign <$> assign,
    BExp <$> Parser.exp
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
resumeExp = try (EResume <$> (keyword KWResume *> resumeExp)) <|> dollarExp


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
  m <- optional (symbol TAt *> (EPropAccess e <$> name))
  case m of
    Just e' -> parseAccessOps e'
    Nothing -> pure e

parseWithOps :: Exp -> Parser Exp
parseWithOps e = do
  m <- optional $ keyword KWWith *> do
    (ts, es) <- choice [
        try $ (,) <$> typeApps <*> effApps,
        (, EffApps [] []) <$> typeApps,
        (TypeApps [], ) <$> effApps
      ]
    pure $ EWith e ts es
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
  <|> try (ELiteral <$> literal)
  <|> try parensThing
  <|> (EName <$> name)

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
      try (symbol TAt *> (EPropAccess e <$> name))
  <|> (keyword KWWith *> do
        (ts, es) <- choice [
            try $ (,) <$> typeApps <*> effApps,
            (, EffApps [] []) <$> typeApps,
            (TypeApps [], ) <$> effApps
          ]
        pure $ EWith e ts es
      )

-- if-expression
ifExp :: Parser Exp
ifExp = do
  keyword KWIf
  cond <- Parser.exp
  keyword KWThen
  th <- Parser.exp
  keyword KWElse
  EIfThenElse cond th <$> Parser.exp

-- let-expression
letExp :: Parser Exp
letExp = do
  keyword KWLet
  lp <- letPattern
  symbol TAssign
  what <- Parser.exp
  keyword KWIn
  ELet lp what <$> Parser.exp

-- under-expression
under :: Parser Exp
under = do
  keyword KWUnder
  ec <- eCons
  keyword KWTo
  b <- block
  keyword KWHandle
  f <- optional $ try handlerClause
  cs <- many $ try handlerClause
  EUnder <$> case f of
    Just f' -> do
      nt <- optional $ do
        _ <- pipesym *> keyword KWThen
        n <- name
        t <- symbol TMatchArrow *> block
        pure (n, t)
      let (n, t) = fromMaybe (".", Block [] $ EName ".") nt
      pure $ Under ec b (f' : cs) n t
    Nothing -> do
      n <- pipesym *> keyword KWThen *> name
      t <- symbol TMatchArrow *> block
      pure $ Under ec b cs n t

parensThing :: Parser Exp
parensThing = do
  symbol TParenL
  e <- try tupleInParens <|> (EParen <$> block)
  symbol TParenR
  pure e

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
    ELiteral <$> literal
    <|> parensThing
    <|> EName <$> name

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