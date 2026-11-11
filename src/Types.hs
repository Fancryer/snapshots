{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Types (
  Taste(..),
  Typ(..),
  EffRow(..),
  EffCons(..),
  ECons(..),
  EffDef(..),
  Expr(..),
  -- Scope(..),
  Block,
  -- NativeBlock,
  Stat(..),
  Lambda(..),
  -- NativeLambda(..),
  TopLevelStat(..),
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

data Expr =
  Int Integer
  | Float Scientific
  | Boolean Bool
  | String Text
  | Nil
  | XVar Text
  | Array [Expr]
  | Pair Expr Expr
  | XLambda Lambda
  | NLambda NativeLambdaSign
  | Apply Expr Expr
  | Record (Maybe Expr) [ERecordProp]
  | With Expr [TypeArg] [EffCons] [EffRow]
  | Handle Handler
  | Paren Block
  | Resume Expr
  | Let LetPattern Expr Expr
  | PropAccess Expr Text
  | IfElse Expr Expr Expr
  deriving (Eq, Ord, Show)

instance Pretty Expr where
  pretty = \case
    Int i -> T.pack $ show i
    Float f -> T.pack $ show f
    Boolean b -> T.pack $ show b
    String s -> "'" <> s <> "'"
    Nil -> "()"
    XVar n -> n
    -- Array [ArrayEntry]
    Pair l r -> "(" <> pretty l <> ", " <> pretty r <> ")"
    XLambda l -> pretty l
    -- NLambda NativeLambda
    Apply f e -> pretty f <> " " <> pretty e
    -- Record (Maybe Expr) [ERecordProp]
    -- With Expr [TypeArg] [EffCons] -- expr with [ts] {fxs}
    Handle h -> pretty h
    Paren b -> "(" <> pretty b <> ")"
    Resume e -> "resume " <> pretty e
    -- Let LetPattern Expr Expr
    PropAccess e n -> pretty e <> "@" <> n
    IfElse p t f -> "if " <> pretty p <> " then " <> pretty t <> " else " <> pretty f
    e -> T.pack $ show e

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
      " ",
      if null es then " " else "{" <> T.intercalate "; " (map tasteName es) <> "} ",
      "(", n, maybe "" ((" : " <>) . pretty) t, ")",
      " : ",
      pretty fxs,
      maybe "" pretty r,
      " = ",
      pretty b,
      "}"
    ]

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

instance Pretty Block where
  pretty (stats, e) = T.concat [
      T.intercalate "; " $ map pretty stats,
      if null stats then "" else "; ",
      pretty e
    ]

data Stat =
  Bind Mutability Text (Maybe Typ) Expr
  | Assign Text Expr
  | Expr Expr
  deriving (Eq, Ord)

instance Pretty Stat where
  pretty = \case
    Bind m n t e -> T.concat [pretty m, " ", n, maybe "" ((" " <>) . pretty) t, " = ", pretty e]
    Assign n e -> n <> " := " <> pretty e
    Expr e -> pretty e

instance Show Stat where
  show = \case
    Bind mut name typ expr ->
      show mut <> " " <> T.unpack name <> maybe "" ((" " <>) . show) typ <> " = " <> show expr
    Assign name expr -> T.unpack name <> " := " <> show expr
    Expr expr -> show expr

data TopLevelStat =
  SFunctDef FunctDecl
  | STypeDef Text [Text] {-[String]-} Typ
  | SEffDef EffDef
  | SRowDef RowDef
  deriving (Show, Generic)
instance Sexp TopLevelStat where sexp = show

instance Pretty TopLevelStat where
  pretty = \case
    SFunctDef f -> pretty f
    SRowDef r -> pretty r
    SEffDef e -> pretty e
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