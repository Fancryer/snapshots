{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE OverloadedRecordDot #-}

module TypedIR(
  TypedExpr(..),
  Block,
  Lambda(..),
  Stat(..),
  FunctDecl(..),
  Handler(..),
  Scope(..),
  TERecordProp(..),
  TopLevelStat(..),
  HandlerClause,
  typeOfTypedExpr,
  typeOfTypedBlock,
  Chunk
)
where
import Types (
    Typ(..),
    ECons(..),
    Expr,
    Taste,
    Mutability,
    TypeArg,
    LetPattern,
    EffRow,
    TypeScheme,
    EffDef,
    HandlerSig,
    -- NativeHandlerClause,
    TRecordProp(..),
    Funct(..),
    -- NativeLambdaSign(NativeLambdaSign),
    RowDef,
    EffCons, NativeLambdaSign (..), TasteMap
  )
import Data.Scientific (Scientific)
import qualified Data.Text as T
import Data.Text (Text)
import Utils (Pretty (..), TextMap)
import Data.Map (Map)
import Data.List (find)
import Resume (ResumeInfo)
import Data.Set (Set)

type TypeScope  = TextMap Typ
type ValueScope = TextMap (TypeScheme, Expr, Mutability)
type EffScope   = TextMap EffDef

type TypeSubst    = TasteMap Typ
type TypeArgSubst = TasteMap TypeArg
type EffSubst     = TasteMap EffCons
type RowSubst     = TasteMap EffRow

data Scope = Scope {
  types         :: TypeScope,
  values        :: ValueScope,
  effects       :: EffScope,

  handlerSig    :: Maybe HandlerSig,

  typeSubst     :: TypeSubst,
  typeArgSubst  :: TypeArgSubst,
  effSubst      :: EffSubst,
  rowSubst      :: RowSubst,

  effLacks      :: TasteMap (Set Text),
  rowLacks      :: TasteMap (Set Text),

  parent        :: Maybe Scope
} deriving (Show)

data TypedExpr =
  TEInt Integer
  | TEFloat Scientific
  | TEBoolean Bool
  | TEString Text
  | TENil
  | TEXVar Text Typ
  | TEArray Typ [TypedExpr]
  | TEPair TypedExpr TypedExpr
  | TEXLambda Lambda
  | TENLambda NativeLambdaSign
  | TEApply TypedExpr TypedExpr
  | TERecord (Maybe TypedExpr) [TERecordProp]
  | TEHandle Handler Typ
  | TEParen Block
  | TEResume TypedExpr Typ
  | TELet LetPattern TypedExpr TypedExpr
  | TEPropAccess TypedExpr Text
  | TEIfElse TypedExpr TypedExpr TypedExpr

instance Show TypedExpr where
  show = \case
    TEInt i -> show i
    TEFloat f -> show f
    TEBoolean b -> show b
    TEString s -> show s
    TENil -> "Nil"
    TEXVar v t -> "(XVar " <> show v <> " " <> show t <> ")"
    TEArray t entries -> "(Array " <> show t <> " (" <> unwords (map show entries) <> "))"
    TEPair l r -> "(Pair " <> show l <> " " <> show r <> ")"
    TEXLambda lam -> "(XLambda " <> show lam <> ")"
    TENLambda lam -> "(NLambda " <> show lam <> ")"
    TEApply f x -> "(Apply " <> show f <> " " <> show x <> ")"
    TERecord Nothing props -> "(Record " <> show props <> ")"
    TERecord (Just anchor) props -> "(Record-extend " <> show anchor <> " | " <> show props <> ")"
    TEHandle handler t -> "(Handle " <> show handler <> " " <> show t <> ")"
    TEParen (stats, expr) -> "(Paren " <> unwords (map show stats) <> " " <> show expr <> ")"
    TEResume expr t -> "(Resume " <> show expr <> " " <> show t <> ")"
    TELet pat bound body -> "(Let " <> show pat <> " " <> show bound <> " " <> show body <> ")"
    TEPropAccess expr field -> "(Prop " <> show expr <> " " <> show field <> ")"
    TEIfElse cond thenExpr elseExpr -> "(If " <> show cond <> " " <> show thenExpr <> " " <> show elseExpr <> ")"

instance Pretty TypedExpr where
  pretty = \case
    TEInt i -> T.pack $ show i
    TEFloat f -> T.pack $ show f
    TEBoolean b -> T.pack $ show b
    TEString s -> "'" <> s <> "'"
    TENil -> "()"
    TEXVar n _ -> n
    TEArray _ es -> T.concat ["[", T.concat $ map pretty es ,"]"]
    TEPair l r -> T.concat ["(", pretty l, ", ", pretty r, ")"]
    TEXLambda l -> pretty l
    TENLambda _ -> "!closure!"
    TEApply f e -> pretty f <> " " <> pretty e
    TERecord Nothing ps -> T.concat ["${", T.intercalate "; " $ map pretty ps, "}"]
    TERecord (Just anchor) ps -> T.concat ["${", pretty anchor, " | ", T.intercalate "; " $ map pretty ps, "}"]
    TEHandle h _ -> pretty h
    TEParen b -> "(" <> pretty b <> ")"
    TEResume e t -> "resume " <> pretty e
    -- -- Let LetPattern TypedExpr TypedExpr
    -- PropAccess e n -> pretty e <> "@" <> n
    TEIfElse p t f -> "if " <> pretty p <> " then " <> pretty t <> " else " <> pretty f
    e -> T.pack $ show e

data TERecordProp = TERecordProp {
    terMut :: Mutability,
    terName :: Text,
    terType :: Typ,
    terExpr :: TypedExpr
  } deriving Show

instance Pretty TERecordProp

data Lambda = Lambda {
    lTvars :: [Taste],
    lEvars :: [Taste],
    lArg   ::  Text,
    lArgT  ::  Typ,
    lRetT  ::  Typ,
    lFxs   ::  EffRow,
    lBlock ::  Block
  }

instance Show Lambda where
  show (Lambda ts es arg argT retT fxs block) =
    concat [
      "(Lambda",
      if null ts then "" else " [" <> unwords (map show ts) <> "]",
      if null es then "" else " {" <> unwords (map show es) <> "}",
      " (", show arg, " : ", show argT, ") : ",
      show fxs, " ", show retT,
      " ", show block,
      ")"
    ]

instance Pretty Lambda where
  pretty (Lambda ts es arg argT retT fxs block) =
    T.concat [
      "{",
      if null ts then "" else " [" <> T.unwords (map pretty ts) <> "]",
      if null es then "" else " {" <> T.unwords (map pretty es) <> "}",
      " (", pretty arg, " : ", pretty argT, ") : ",
      pretty fxs, " ", pretty retT,
      " = ", pretty block, "}"
    ]

type Block = ([Stat], TypedExpr)

instance Pretty Block where
  pretty (stats, e) = T.concat [
      T.intercalate "; " $ map pretty stats,
      if null stats then "" else "; ",
      pretty e
    ]

data Stat =
  Bind Mutability Text TypedExpr
  | Rebind Text TypedExpr
  | Expr TypedExpr
  deriving (Show)

instance Pretty Stat where
  pretty = \case
    Bind m n e -> T.concat [pretty m, " ", n, " = ", pretty e]
    Rebind n e -> n <> " := " <> pretty e
    Expr e -> pretty e

data FunctDecl = FunctDecl {
    fName  :: Text,
    fTvars  :: [Text],
    fEvars  :: [Text],
    fArgs  :: [(Text, Typ)],
    fRet    :: (Maybe EffRow, Typ),
    fBlock :: Block
  }

instance Show FunctDecl where
  show (FunctDecl n ts es args (retR, retT) block) =
    concat [
      "(FunctDecl ", show n,
      if null ts then "" else " [" <> unwords (map show ts) <> "]",
      if null es then "" else " {" <> unwords (map show es) <> "}",
      if null args then "()" else unwords (map show args),
      maybe "" ((" " <>) . show) retR,
      show retT,
      show block,
      ")"
    ]

instance Pretty FunctDecl where
  pretty (FunctDecl n ts es args (retR, retT) block) =
    T.concat [
      "funct ", n,
      if null ts then "" else " [" <> T.unwords ts <> "]",
      if null es then "" else " {" <> T.unwords es <> "}",
      if null args then "()" else T.unwords $
        flip map args $ \(n', t) ->
          T.concat ["(", n', " : ", pretty t,")"],
      " : ",
      maybe "" ((<> " ") . pretty) retR,
      pretty retT, " = ", pretty block
    ]

--eff block clauses then
data Handler =
  -- NativeHandler ECons TypedExpr [NativeHandlerClause] (Maybe NativeLambdaSign)
  -- |
  Handler ECons Block [HandlerClause] Lambda

instance Show Handler where
  show (Handler eff block clauses mThen) =
    concat [
      "(handler (effect ",
      show eff,
      ") (block ",
      show block,
      ") (clauses ", unwords (map show clauses), ")",
      " (then " <> show mThen <> ")",
      ")"
    ]

instance Pretty Handler where
  pretty (Handler eff block clauses _then) =
    T.concat [
      "under ", pretty eff, " to ", pretty block,
      "handle ",
        if null clauses then "" else T.unwords $ map pretty clauses,
      " | then ", pretty _then
    ]

-- op name, lambda, resume amount, args amount
type HandlerClause = (Text, Lambda, ResumeInfo, Int)

instance Pretty HandlerClause where
  pretty (n, lam, _, _) =
    T.concat [
      "| ", n, "(", lam.lArg, " : ", pretty lam.lArgT,
      ") => ", pretty lam.lBlock
    ]

data TopLevelStat =
  SFunctDef FunctDecl
  | STypeDef Text [Text] {-[String]-} Typ
  | SEffDef EffDef
  | SRowDef RowDef
  deriving (Show)

instance Pretty TopLevelStat where
  pretty = \case
    SFunctDef f -> pretty f
    STypeDef n ts t ->
      let ts' = if null ts then "" else T.concat ["[", T.concat ts, "]"] in
      T.concat ["type ", n, ts', " = ", pretty t]
    SEffDef e -> pretty e
    SRowDef r -> pretty r

type Chunk = [TopLevelStat]

instance Pretty Chunk where pretty sts = T.intercalate "\n" $ map pretty sts

typeOfTypedExpr :: TypedExpr -> Either Text Typ
typeOfTypedExpr = \case
  TEInt _ -> Right TInt
  TEFloat _ -> Right TFloat
  TEBoolean _ -> Right TBoolean
  TEString _ -> Right TString
  TENil -> Right TNil
  TEXVar _ t -> Right t
  TEArray t _ -> Right t
  TEPair l r -> TPair <$> typeOfTypedExpr l <*> typeOfTypedExpr r
  TEXLambda (TypedIR.Lambda _ _ _ argT retT fxs _) -> Right . TFunct $ Funct argT retT fxs
  TENLambda (NativeLambdaSign _ argT retT fxs) -> Right . TFunct $ Funct argT retT fxs
  TEApply f _ ->
    typeOfTypedExpr f >>= \case
      TFunct (Funct _ ret' _) -> pure ret'
      r -> Left $ "typeOfTypedExpr [TEApply]| Apply of non-function: " <> T.pack (show r)
  TERecord _ props -> Right $ TRecord [TRecordProp mut name t | TERecordProp mut name t _ <- props]
  -- TEWith _ _ _ t -> t
  TEHandle _ t -> Right t
  TEParen block -> typeOfTypedBlock block
  TEResume _ t -> Right t
  TELet _ _ body -> typeOfTypedExpr body
  TEPropAccess expr field ->
    typeOfTypedExpr expr >>= \case
      TRecord props ->
        case find ((field ==) . tName) props of
          Just (TRecordProp _ _ t) -> Right t
          Nothing -> Left $ "Field " <> field <> " not found"
      r -> Left $ "PropAccess on non-record: " <> T.pack (show r)
  TEIfElse _ thenExpr _ -> typeOfTypedExpr thenExpr

typeOfTypedBlock :: TypedIR.Block -> Either Text Typ
typeOfTypedBlock = typeOfTypedExpr . snd