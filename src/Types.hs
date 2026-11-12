{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Types (
  Taste(..),
  Typ(..),
  EffRow(..),
  EffCons(..),
  ECons(..),
  EffDef(..),
  Expr(..),
  ExprNode(..),
  pattern Int,
  pattern Float,
  pattern Boolean,
  pattern String,
  pattern Nil,
  pattern XVar,
  pattern Array,
  pattern Pair,
  pattern XLambda,
  pattern NLambda,
  pattern Apply,
  pattern Record,
  pattern With,
  pattern Handle,
  pattern Paren,
  pattern Resume,
  pattern Let,
  pattern PropAccess,
  pattern IfElse,
  atSpan,
  -- Scope(..),
  Block,
  blockSpan,
  -- NativeBlock,
  Stat(..),
  StatNode(..),
  pattern Bind,
  pattern Assign,
  pattern Expr,
  atStatSpan,
  statSpan,
  Lambda(..),
  -- NativeLambda(..),
  TopLevelStat(..),
  topLevelSpan,
  FunctDecl(..),
  Handler(..),
  HandlerSig(..),
  Chunk,
  Mutability(..),
  -- NativeHandlerClause,
  NativeLambdaSign(..),
  AtomLetPattern(..),
  TRecordProp(..),
  ERecordProp(..),
  Scheme(..),
  TypeScheme,
  EffScheme,
  TypeArg(..),
  TARecordProp(..),
  Funct(..),
  RowDef(..),
  LambdaParam(..),
  LetPattern(..),
  LetPatternRecordProp(..),
  HandlerClause,
  TasteMap,
  tasteName,
  metaLevel,
  isSkolem,
  tfunc,
  pureFunct,
  pureTFunc,
  handlerCons,
  effName,
  countArgs,
  monoScheme
) where
import Data.List (intercalate)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Scientific (Scientific)
import Utils (Pretty (..))
import GHC.Generics (Generic)
import Sexp (Sexp (..))
import Text.Printf (PrintfArg (formatArg))
import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Control.Applicative as Set
import qualified Data.Set as Set
import Span (Span, noSpan, mergeSpan, mergeSpans)

-- TODO: replace name-based reachability with binding-identity-based analysis;
-- reduce false positives caused by shadowing.
data Taste =
  Meta Text Int Int     -- name id lvl
  | Skolem Text Int Int -- name id lvl
  | Bound Text Int      -- name id
  deriving (Show, Generic)

instance Sexp Taste

instance Pretty Taste where
  pretty = \case
    Meta m _ _ -> "`" <> m
    Skolem s _ _ -> "`" <> s
    Bound b _ -> "`" <> b

instance Eq Taste where
  Meta _ lid _ == Meta _ rid _ = lid == rid
  Skolem _ lid _ == Skolem _ rid _ = lid == rid
  Bound _ lid == Bound _ rid = lid == rid
  _ == _ = False

instance Ord Taste where
  Meta _ lid _ `compare` Meta _ rid _ = lid `compare` rid
  Skolem _ lid _ `compare` Skolem _ rid _ = lid `compare` rid
  Bound _ lid `compare` Bound _ rid = lid `compare` rid
  Meta {} `compare` _ = GT
  Skolem {} `compare` Meta {} = LT
  Skolem {} `compare` Bound {} = GT
  Bound {} `compare` _ = LT


type TasteMap = Map Taste

data Typ =
  TInt
  | TFloat
  | TBoolean
  | TString
  | TNil
  | TNothing
  | TFlat Text
  | TArray Typ
  | TPair Typ Typ
  | TFunct Funct                -- arg -> row ret
  | TRecord [TRecordProp]
  | TForall
    [Taste] [Taste] [Taste]
    (TasteMap (Set Text))
    (TasteMap (Set Text))
    Typ -- forall [a1 ... an] {e1 ... en | r1 ... rn} to {el1; ...; eln | rl1; ...; rln} ==> type
  | TVar Taste
  deriving (Show, Ord, Eq)

instance Pretty Typ where
  pretty = \case
    TInt -> "Int"
    TFloat -> "Float"
    TBoolean -> "Boolean"
    TString -> "String"
    TNil -> "()"
    TNothing -> "Nothing"
    TFlat n -> n
    TArray t -> "[" <> pretty t <> "]"
    TPair l r -> "(" <> pretty l <> ", " <> pretty r <> ")"
    TFunct f -> pretty f
    TRecord props -> "#{" <> T.intercalate "; " (map pretty props) <>  "}"
    TForall ts es rs els rls t -> T.concat [
        "forall ",
        "[", T.unwords $ map tasteName ts, "]",
        "{", T.unwords $ map tasteName es, if null rs then "" else " | " <> T.unwords (map tasteName rs), "}",
        lacks,
        " ==> ", pretty t
      ]
      where
        lacks = case (Map.elems els, Map.elems rls) of
          ([], []) -> ""
          (els', []) -> T.concat [" to {", T.pack $ show els', "}"]
          ([], rls') -> T.concat [" to {|", T.pack $ show rls', "}"]
          (els', rls') -> T.concat [" to {|", T.pack $ show els', " | ", T.pack $ show rls', "}"]

    TVar n -> "`" <> tasteName n

data Funct = Funct Typ Typ EffRow deriving (Show, Ord, Eq)

instance Pretty Funct where
  pretty (Funct i o fxs) = pretty i <> " -> " <> pretty fxs <> " " <> pretty o

data RowLacks = RowLacks {
  rowVariable :: Taste,
  forbiddenEffects :: Set EffCons
}

data Scheme a = Scheme {
  _ts :: [Taste],
  _es :: [Taste],
  _rs :: [Taste],
  _effLacks :: TasteMap (Set Text),
  _rowLacks :: TasteMap (Set Text),
  _a :: a
} deriving Show

type TypeScheme = Scheme Typ
-- unused, but potentitally could be implemented for row aliases
type EffScheme = Scheme EffRow

monoScheme :: Typ -> TypeScheme
monoScheme = Scheme [] [] [] Map.empty Map.empty

data TRecordProp = TRecordProp {
    tMut :: Mutability,
    tName :: Text,
    tTyp :: Typ
  }
  deriving (Show, Eq, Ord)

instance Pretty TRecordProp where pretty = T.pack . show

data EffRow =
  RClosed [EffCons]       -- Закрытый ряд: {Console; File}
  | ROpen [EffCons] Taste -- Открытый ряд: {console; file | `e}
  | RVar Taste            -- Переменная ряда: `e
  deriving (Show, Ord, Eq, Generic)

instance Sexp EffRow

instance Pretty EffRow where
  pretty = \case
    RClosed cons -> "{" <> T.intercalate "; " (map pretty cons) <> "}"
    ROpen cons t -> "{" <> T.intercalate "; " (map pretty cons) <> " | `" <> tasteName t <> "}"
    RVar n -> "`" <> tasteName n

data EffCons = EffCons ECons | EVar Taste deriving (Ord, Eq, Generic)

data ECons = ECons Text [TypeArg] deriving (Ord, Eq, Generic)

instance Show ECons where
  show (ECons n []) = T.unpack n
  show (ECons n tas) = T.unpack n <> " " <> show tas

instance Pretty ECons where
  pretty (ECons n args) = case args of
    [] -> n
    _ -> n <> "[" <> T.intercalate "; " (map pretty args) <> "]"

instance Sexp ECons
instance Sexp EffCons

instance Show EffCons where
  show = \case
    EffCons (ECons n []) -> "EffCons " <> T.unpack n
    EffCons (ECons n tas) -> "EffCons " <> T.unpack n <> " " <> show tas
    EVar n -> "EVar " <> show n

instance Pretty EffCons where
  pretty = \case
    EffCons e -> pretty e
    EVar n -> "`" <> tasteName n

data EffDef = EffDef Text [Text] [(Text, Funct)] deriving Show

effName :: EffDef -> Text
effName (EffDef n _ _) = n

instance Pretty EffDef where
  pretty (EffDef n ts ops) =
    T.concat [
      "effect ",
      n,
      if null ts then " " else "[" <> T.intercalate "; " ts <> "] ",
      T.intercalate "; " $ map (\(n', f) -> n' <> " : " <> pretty f) ops,
      " end"
    ]

data RowDef = RowDef Text EffRow deriving (Show, Generic)

instance Pretty RowDef where
  pretty (RowDef n row) = "row " <> n <> " = " <> pretty row

-- | An expression together with the region of source it came from.  The
--   elaborator copies the position of the AST node it came from; nodes that
--   have no corresponding source text get 'noSpan'.
data Expr = MkExpr {
    exprSpan :: Span
  , exprNode :: ExprNode
  } deriving (Eq, Ord, Show)

-- | The shape of an expression, without its position.
data ExprNode =
    IntNode Integer
  | FloatNode Scientific
  | BooleanNode Bool
  | StringNode Text
  | NilNode
  | XVarNode Text
  | ArrayNode [Expr]
  | PairNode Expr Expr
  | XLambdaNode Lambda
  | NLambdaNode NativeLambdaSign
  | ApplyNode Expr Expr
  | RecordNode (Maybe Expr) [ERecordProp]
  | WithNode Expr [TypeArg] [EffCons] [EffRow]
  | HandleNode Handler
  | ParenNode Block
  | ResumeNode Expr
  | LetNode LetPattern Expr Expr
  | PropAccessNode Expr Text
  | IfElseNode Expr Expr Expr
  deriving (Eq, Ord, Show)

pattern Int :: Integer -> Expr
pattern Int i <- MkExpr _ (IntNode i) where
  Int i = MkExpr noSpan (IntNode i)

pattern Float :: Scientific -> Expr
pattern Float f <- MkExpr _ (FloatNode f) where
  Float f = MkExpr noSpan (FloatNode f)

pattern Boolean :: Bool -> Expr
pattern Boolean b <- MkExpr _ (BooleanNode b) where
  Boolean b = MkExpr noSpan (BooleanNode b)

pattern String :: Text -> Expr
pattern String s <- MkExpr _ (StringNode s) where
  String s = MkExpr noSpan (StringNode s)

pattern Nil :: Expr
pattern Nil <- MkExpr _ NilNode where
  Nil = MkExpr noSpan NilNode

pattern XVar :: Text -> Expr
pattern XVar n <- MkExpr _ (XVarNode n) where
  XVar n = MkExpr noSpan (XVarNode n)

pattern Array :: [Expr] -> Expr
pattern Array es <- MkExpr _ (ArrayNode es) where
  Array es = MkExpr (mergeSpans (map exprSpan es)) (ArrayNode es)

pattern Pair :: Expr -> Expr -> Expr
pattern Pair l r <- MkExpr _ (PairNode l r) where
  Pair l r = MkExpr (mergeSpan (exprSpan l) (exprSpan r)) (PairNode l r)

pattern XLambda :: Lambda -> Expr
pattern XLambda l <- MkExpr _ (XLambdaNode l) where
  XLambda l = MkExpr noSpan (XLambdaNode l)

pattern NLambda :: NativeLambdaSign -> Expr
pattern NLambda n <- MkExpr _ (NLambdaNode n) where
  NLambda n = MkExpr noSpan (NLambdaNode n)

pattern Apply :: Expr -> Expr -> Expr
pattern Apply f x <- MkExpr _ (ApplyNode f x) where
  Apply f x = MkExpr (mergeSpan (exprSpan f) (exprSpan x)) (ApplyNode f x)

pattern Record :: Maybe Expr -> [ERecordProp] -> Expr
pattern Record a ps <- MkExpr _ (RecordNode a ps) where
  Record a ps =
    MkExpr (mergeSpans (maybe [] (\x -> [exprSpan x]) a <> map (exprSpan . erExpr) ps)) (RecordNode a ps)

pattern With :: Expr -> [TypeArg] -> [EffCons] -> [EffRow] -> Expr
pattern With e ts es rs <- MkExpr _ (WithNode e ts es rs) where
  With e ts es rs = MkExpr (exprSpan e) (WithNode e ts es rs)

pattern Handle :: Handler -> Expr
pattern Handle h <- MkExpr _ (HandleNode h) where
  Handle h = MkExpr noSpan (HandleNode h)

pattern Paren :: Block -> Expr
pattern Paren b <- MkExpr _ (ParenNode b) where
  Paren b = MkExpr noSpan (ParenNode b)

pattern Resume :: Expr -> Expr
pattern Resume e <- MkExpr _ (ResumeNode e) where
  Resume e = MkExpr (exprSpan e) (ResumeNode e)

pattern Let :: LetPattern -> Expr -> Expr -> Expr
pattern Let p w b <- MkExpr _ (LetNode p w b) where
  Let p w b = MkExpr (mergeSpan (exprSpan w) (exprSpan b)) (LetNode p w b)

pattern PropAccess :: Expr -> Text -> Expr
pattern PropAccess e n <- MkExpr _ (PropAccessNode e n) where
  PropAccess e n = MkExpr (exprSpan e) (PropAccessNode e n)

pattern IfElse :: Expr -> Expr -> Expr -> Expr
pattern IfElse p t f <- MkExpr _ (IfElseNode p t f) where
  IfElse p t f =
    MkExpr (mergeSpan (exprSpan p) (mergeSpan (exprSpan t) (exprSpan f))) (IfElseNode p t f)

{-# COMPLETE Int, Float, Boolean, String, Nil, XVar, Array, Pair, XLambda
   , NLambda, Apply, Record, With, Handle, Paren, Resume, Let, PropAccess
   , IfElse #-}

-- | Move an expression to a different span.  Used by the elaborator, which
--   knows the span of the AST node a node came from.
atSpan :: Span -> Expr -> Expr
atSpan s e = e {exprSpan = s}

instance Pretty Expr where
  pretty (MkExpr _ n) = pretty n

instance Pretty ExprNode where
  pretty = \case
    IntNode i -> T.pack $ show i
    FloatNode f -> T.pack $ show f
    BooleanNode b -> if b then "true" else "false"
    StringNode s -> "'" <> s <> "'"
    NilNode -> "()"
    XVarNode n -> n
    ArrayNode es -> "[" <> T.intercalate " " (map pretty es) <> "]"
    PairNode l r -> "(" <> pretty l <> ", " <> pretty r <> ")"
    XLambdaNode l -> pretty l
    NLambdaNode (NativeLambdaSign n t r fxs) ->
      n <> " : " <> pretty t <> " -> " <> prettyFxs fxs <> pretty r
    ApplyNode f e -> pretty f <> " " <> pretty e
    RecordNode ext props ->
      "#{" <> maybe "" ((<> " | ") . pretty) ext
          <> T.intercalate "; " (map prettyERecordProp props) <> "}"
    WithNode e ts es rs ->
      pretty e <> " with [" <> T.intercalate "; " (map pretty ts) <> "]"
        <> (if null es then "" else " {" <> T.intercalate "; " (map pretty es) <> "}")
        <> (if null rs then "" else " " <> T.intercalate " " (map pretty rs))
    HandleNode h -> pretty h
    ParenNode b -> "(" <> pretty b <> ")"
    ResumeNode e -> "resume " <> pretty e
    LetNode p w b -> "let " <> prettyLetPattern p <> " = " <> pretty w <> " in " <> pretty b
    PropAccessNode e n -> pretty e <> "@" <> n
    IfElseNode p t f -> "if " <> pretty p <> " then " <> pretty t <> " else " <> pretty f

prettyERecordProp :: ERecordProp -> Text
prettyERecordProp p = T.concat [
    pretty (erMut p), " ", erName p,
    maybe "" ((" : " <>) . pretty) (erType p),
    " = ", pretty (erExpr p)
  ]

prettyLetPattern :: LetPattern -> Text
prettyLetPattern = \case
  LPATom a -> prettyAtomLetPattern a
  LPParam (LambdaParam n mt) ->
    "(" <> n <> maybe "" ((" : " <>) . pretty) mt <> ")"

prettyAtomLetPattern :: AtomLetPattern -> Text
prettyAtomLetPattern = \case
  ALPNil -> "()"
  ALPUnderscore -> "_"
  ALPPair a b -> "(" <> prettyLetPattern a <> ", " <> prettyLetPattern b <> ")"
  ALPRecord ps ->
    "#{" <> T.intercalate "; " (map prettyLetPatternRecordProp ps) <> "}"

prettyLetPatternRecordProp :: LetPatternRecordProp -> Text
prettyLetPatternRecordProp (LetPatternRecordProp m (LambdaParam n mt) pat) = T.concat [
    pretty m, " ", n,
    maybe "" ((" : " <>) . pretty) mt,
    maybe "" ((" = " <>) . prettyAtomLetPattern) pat
  ]

data TypeArg =
  TAInt
  | TAFloat
  | TABoolean
  | TAString
  | TANil
  | TANothing
  | TAFlat Text
  | TAArray TypeArg
  | TAPair TypeArg TypeArg
  | TAFunct TypeArg TypeArg
  | TARecord [TARecordProp]
  | TAVar Taste
  deriving (Eq, Ord, Show, Generic)

instance Sexp TypeArg

instance Pretty TypeArg where
  pretty = T.pack . show

data TARecordProp = TARecordProp Mutability Text TypeArg deriving (Eq, Ord, Show, Generic)
instance Sexp TARecordProp

data LetPattern = LPATom AtomLetPattern | LPParam LambdaParam deriving (Eq, Ord, Show)

data AtomLetPattern =
  ALPNil
  | ALPUnderscore
  | ALPPair LetPattern LetPattern
  | ALPRecord [LetPatternRecordProp]
  deriving (Eq, Ord, Show)

data LetPatternRecordProp =
  LetPatternRecordProp Mutability LambdaParam (Maybe AtomLetPattern) deriving (Eq, Ord, Show)

data LambdaParam = LambdaParam Text (Maybe Typ) deriving (Eq, Ord, Show)
data ERecordProp = ERecordProp {
  erMut :: Mutability,
  erName :: Text,
  erType :: Maybe Typ,
  erExpr :: Expr
} deriving (Show, Eq, Ord)

data NativeLambdaSign = NativeLambdaSign Text Typ Typ EffRow deriving (Eq, Ord, Show)

prettyTvars :: [Taste] -> Bool -> Text
prettyTvars ts skipBrackets =
  if null ts then
    if skipBrackets then "" else "[]"
  else
    "[" <> T.intercalate "; " (map tasteName ts) <> "] "

data Lambda = Lambda {
  lTvars :: [Taste],
  lEvars :: [Taste],
  lArg   ::  Text,
  lArgT  ::  Maybe Typ,
  lRetT  ::  Maybe Typ,
  lFxs   ::  EffRow,
  lBlock ::  Block
} deriving (Eq, Ord)

instance Pretty Lambda where
  pretty (Lambda ts es n t r fxs b) = T.concat [
      "{",
      prettyTvars ts True,
      if null es then "" else "{" <> T.intercalate "; " (map tasteName es) <> "} ",
      "(", n, maybe "" ((" : " <>) . pretty) t, ")",
      " : ",
      prettyFxs fxs,
      maybe "" pretty r,
      " = ",
      pretty b,
      "}"
    ]

-- | A latent effect row in a function type: compact, and omitted when empty,
--   because @{}Int@ reads as if the type were mangled.
prettyFxs :: EffRow -> Text
prettyFxs = \case
  RClosed [] -> ""
  fxs -> pretty fxs <> " "

instance Show Lambda where
  show (Lambda ts es arg argT retT fxs block) =
    concat [
      "{",
      concat ["[", intercalate "; " $ map show ts, "]"],
      concat ["{", intercalate "; " $ map show es, "}"],
      T.unpack arg,
      maybe "" ((<> " ") . show) argT,
      show fxs,
      maybe "" ((<> " ") . show) retT,
      " = ",
      show block,
      "}"
    ]

-- type NativeBlock  = (Typ, Expr)
type Block        = ([Stat], Expr)

-- | The region a block covers: from its first statement to its result
--   expression.  Blocks are a pair rather than a record, so the span is
--   derived from the parts that have one.
blockSpan :: Block -> Span
blockSpan (stats, e) = mergeSpans (map statSpan stats <> [exprSpan e])

instance Pretty Block where
  pretty (stats, e) = T.concat [
      T.intercalate "; " $ map pretty stats,
      if null stats then "" else "; ",
      pretty e
    ]

-- | A statement of the IR, with the source region it came from.
data Stat = MkStat {
    statSpan :: Span
  , statNode :: StatNode
  } deriving (Eq, Ord)

-- | The shape of a statement, without its position.
data StatNode =
    BindNode Mutability Text (Maybe Typ) Expr
  | AssignNode Text Expr
  | ExprNode Expr
  deriving (Eq, Ord, Show)

pattern Bind :: Mutability -> Text -> Maybe Typ -> Expr -> Stat
pattern Bind m n t e <- MkStat _ (BindNode m n t e) where
  Bind m n t e = MkStat (exprSpan e) (BindNode m n t e)

pattern Assign :: Text -> Expr -> Stat
pattern Assign n e <- MkStat _ (AssignNode n e) where
  Assign n e = MkStat (exprSpan e) (AssignNode n e)

pattern Expr :: Expr -> Stat
pattern Expr e <- MkStat _ (ExprNode e) where
  Expr e = MkStat (exprSpan e) (ExprNode e)

{-# COMPLETE Bind, Assign, Expr #-}

-- | Move a statement to the given span.
atStatSpan :: Span -> Stat -> Stat
atStatSpan s st = st {statSpan = s}

instance Pretty Stat where
  pretty = pretty . statNode

instance Pretty StatNode where
  pretty = \case
    BindNode m n t e -> T.concat [pretty m, " ", n, maybe "" ((" " <>) . pretty) t, " = ", pretty e]
    AssignNode n e -> n <> " := " <> pretty e
    ExprNode e -> pretty e

instance Show Stat where
  show = \case
    Bind m name typ expr ->
      show m <> " " <> T.unpack name <> maybe "" ((" " <>) . show) typ <> " = " <> show expr
    Assign name expr -> T.unpack name <> " := " <> show expr
    Expr expr -> show expr

-- | A top-level declaration with the region of source it came from.  The
--   type checker reports duplicates, which are found after elaboration has
--   thrown the syntax away, so the position has to travel with the node.
data TopLevelStat =
  SFunctDef Span FunctDecl
  | STypeDef Span Text [Text] {-[String]-} Typ
  | SEffDef Span EffDef
  | SRowDef Span RowDef
  deriving (Show, Generic)
instance Sexp TopLevelStat where sexp = show

-- | The position of a declaration, whatever its kind.
topLevelSpan :: TopLevelStat -> Span
topLevelSpan = \case
  SFunctDef s _ -> s
  STypeDef s _ _ _ -> s
  SEffDef s _ -> s
  SRowDef s _ -> s

instance Pretty TopLevelStat where
  pretty = \case
    SFunctDef _ f -> pretty f
    SRowDef _ r -> pretty r
    SEffDef _ e -> pretty e
    s -> T.pack $ show s

data FunctDecl = FunctDecl {
  fName  :: Text,
  fTvars  :: [Text],
  fEvars  :: [Text],
  fRvars  :: [Text],
  fArgs   :: [(Text, Typ)],
  fRet    :: (Maybe EffRow, Typ),
  fBlock :: Block
}  deriving (Show, Generic)

instance Pretty FunctDecl where
  pretty (FunctDecl n ts es rs args (fx, t) b) =
    T.concat [
      "funct ", n,
      "[" <> T.unwords ts <> "]",
      "{" <> T.unwords es <> (if null rs then "" else " | " <> T.unwords rs) <> "}",
      T.unwords $ map (\(n', t') -> "(" <> n' <> " : " <> pretty t' <> ")") args,
      " : ", maybe "" ((<> " ") . pretty) fx, pretty t, " = ", pretty b
    ]

instance Sexp FunctDecl where sexp = show

--eff block clauses then
data Handler = Handler EffCons Block [HandlerClause] Lambda
  deriving (Eq, Ord, Show)

instance Pretty Handler where
  pretty = \case
    -- NativeHandler _eff _block _clauses _then -> ""
    Handler eff block clauses _then -> T.concat [
        "under ", pretty eff, " to ", pretty block,
        " handle ", T.unwords $ map pretty clauses,
        pretty _then
      ]

-- type NativeHandlerClause  = (Text, NativeLambdaSign)
type HandlerClause = (Text, Lambda)

instance Pretty HandlerClause where
  pretty (n, Lambda _ _ n' _ _ _ b) = T.concat [
      " | ", n, " ", n', " => ", pretty b
    ]


-- eff clauses
data HandlerSig = HandlerSig EffCons [(Text, Funct)] deriving Show

type Chunk = [TopLevelStat]

instance Pretty Chunk where pretty = T.intercalate "\n" . map pretty

data Mutability = Val | Var | Imm deriving (Eq, Ord, Generic)

instance Sexp Mutability
instance Pretty Mutability
instance Show Mutability where show = \case Val -> "val"; Var -> "var"; Imm -> "imm"
instance PrintfArg Mutability where formatArg = formatArg . show


tfunc :: Typ -> Typ -> Typ
tfunc i = TFunct . pureFunct i

pureFunct :: Typ -> Typ -> Funct
pureFunct i o = Funct i o $ RClosed []

pureTFunc :: [Typ] -> Maybe Typ
pureTFunc = \case
  [] -> Nothing
  [i, o] -> Just $ tfunc i o
  (i : o) -> tfunc i <$> pureTFunc o

tasteName :: Taste -> Text
tasteName = \case
  Skolem s _ _ -> s
  Meta m _ _ -> m
  Bound b _ -> b

metaLevel :: Taste -> Maybe Int
metaLevel = \case
  Meta _ _ lvl -> Just lvl
  Skolem _ _ lvl -> Just lvl
  _ -> Nothing

isSkolem :: Taste -> Bool
isSkolem Skolem {} = True
isSkolem _ = False

handlerCons :: Handler -> EffCons
-- handlerCons (NativeHandler cons _ _ _) = cons
handlerCons (Handler cons _ _ _) = cons

-- Funct Typ Typ EffRow
countArgs :: Funct -> Int
countArgs (Funct _ tf _) = case tf of
  TFunct f -> 1 + countArgs f
  _ -> 1