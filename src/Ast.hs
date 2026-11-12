{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Ast (
  Chunk(..),
  TopLevelStat(..),
  topLevelSpan,
  EffectOp(..),
  FunctArg(..),
  Typ(..),
  RecordTyp(..),
  RecordTypProp(..),
  EffRow(..),
  EffRowEntry(..),
  EffCons(..),
  Block(..),
  BindDef(..),
  ConstantQualifier(..),
  BlockStat(..),
  BlockStatNode(..),
  pattern BExp,
  pattern BBindDef,
  pattern BAssign,
  atBlockStatSpan,
  Assign(..),
  PathExp(..),
  LetPattern(..),
  AtomLetPattern(..),
  TypeApps(..),
  EffApps(..),
  EffArg(..),
  ECons(..),
  TypeArg(..),
  RecordTypeArg(..),
  RecordTypeArgProp(..),
  Exp(..),
  ExpNode(..),
  -- Read-only views of 'ExpNode', for destructuring.
  pattern EName,
  pattern EApply,
  pattern EDollar,
  pattern ELiteral,
  pattern EPair,
  pattern ELet,
  pattern EBacktick,
  pattern EPropAccess,
  pattern EIfThenElse,
  pattern EUnder,
  pattern EResume,
  pattern EParen,
  pattern EWith,
  binExp,
  HandlerClause(..),
  Literal(..),
  Atom(..),
  Number(..),
  ArrayLiteral(..),
  ArrayEntry(..),
  LambdaLiteral(..),
  LambdaHead(..),
  LambdaParam(..),
  RecordLiteral(..),
  TypeParams(..),
  EffParams(..),
  AtomLetPatternRecordProp(..),
  Under(..),
  Funct(..)
) where
import Data.Text (Text)
import Data.Scientific (Scientific)
import qualified Data.Set as Set
import Utils (Pretty (pretty))
import qualified Data.Text as T
import qualified Data.List as String
import GHC.Generics (Generic)
import Sexp (Sexp(..))
import Span (Span, noSpan, mergeSpan)

newtype Chunk = Chunk [TopLevelStat] deriving (Eq, Show, Generic)
instance Sexp Chunk
instance Pretty Chunk where pretty (Chunk stats) = T.intercalate "\n" $ map pretty stats

newtype TypeParams = TypeParams [Text] deriving (Eq, Show, Generic)
instance Sexp TypeParams

instance Semigroup TypeParams where
  TypeParams l <> TypeParams r = TypeParams $ Set.toList (Set.fromList $ l <> r)
instance Monoid TypeParams where mempty = TypeParams mempty

instance Pretty TypeParams where
  pretty (TypeParams ts) = T.concat ["[", T.unwords ts, "]"]


data EffParams = EffParams [Text] [Text] deriving (Eq, Show, Generic)
instance Sexp EffParams

instance Semigroup EffParams where
  EffParams le lr <> EffParams re rr =
    EffParams (Set.toList $ Set.fromList $ le <> re) (Set.toList $ Set.fromList $ lr <> rr)
instance Monoid EffParams where mempty = EffParams mempty mempty

instance Pretty EffParams where
  pretty (EffParams es rs) = T.concat ["{", T.unwords es, if null rs then "" else " | " <> T.unwords rs, "}"]

-- | A top-level declaration together with the region it occupies.  Duplicates
--   are reported by the type checker, which never sees the parser's positions
--   otherwise, so the span travels with the declaration.
data TopLevelStat =
  TypeDef Span Text TypeParams {-EffParams-} Typ
  | EffectDef Span Text TypeParams [EffectOp]
  | RowDef Span Text EffRow
  | FunctDef Span Text TypeParams EffParams [FunctArg] (Maybe EffRow) Typ Block
  deriving (Eq, Show, Generic)
instance Sexp TopLevelStat where sexp = show

-- | The position of a declaration, whatever its kind.
topLevelSpan :: TopLevelStat -> Span
topLevelSpan = \case
  TypeDef s _ _ _ -> s
  EffectDef s _ _ _ -> s
  RowDef s _ _ -> s
  FunctDef s _ _ _ _ _ _ _ -> s

instance Pretty TopLevelStat where
  pretty = \case
    TypeDef _ n ts {-es-} t ->
      T.concat ["type ", n, prettyTs ts, {-, prettyEs es-} " = ", pretty t]
    EffectDef _ n ts ops ->
      T.concat ["effect ", n, prettyTs ts, " ", T.unwords $ map pretty ops, " end"]
    RowDef _ n row ->
      T.concat ["row ", n, " = ", pretty row]
    FunctDef _ n ts es args fxs t b ->
      T.concat [
        "funct ",
        n,
        prettyTs ts,
        prettyEs es,
        T.unwords $ map pretty args,
        " : ",
        maybe "" ((<> " ") . pretty) fxs,
        pretty t,
        " = ",
        pretty b
      ]
    where
      prettyTs = \case
        TypeParams [] -> ""
        ts -> " " <> pretty ts
      prettyEs = \case
        EffParams [] [] -> ""
        es -> " " <> pretty es

data EffectOp = EffectOp Text Funct deriving (Eq, Show, Generic)
instance Sexp EffectOp

instance Pretty EffectOp where
  pretty (EffectOp n t) = T.concat [n, " : ", pretty t]

data FunctArg = NamedFunctArg Text Typ | NilArg deriving (Eq, Show, Generic)
instance Sexp FunctArg

instance Pretty FunctArg where
  pretty = \case
    NamedFunctArg n t -> T.concat ["(", n, " : ", pretty t, ")"]
    NilArg -> "()"

data Typ =
  TFlat Text
  | TNil
  | TArray Typ
  | TParen Typ
  | TPair Typ Typ
  | TFunct Funct
  | TRecord RecordTyp
  | TForall TypeParams EffParams Typ
  | TVar Text
  | TGenericAlias Text TypeApps
  deriving (Eq, Show, Generic)
instance Sexp Typ

data Funct = Funct Typ Typ EffRow deriving (Eq, Show, Generic)
instance Sexp Funct

instance Pretty Funct where
  pretty (Funct i o r) = T.concat [pretty i, " -> ", pretty r, pretty o]

instance Pretty Typ where
  pretty = \case
    TFlat t -> t
    TNil -> "()"
    TParen t -> T.concat ["(", pretty t, ")"]
    TArray t -> T.concat ["[", pretty t, "]"]
    TPair l r -> T.concat [pretty l, ", ", pretty r]
    TFunct f -> pretty f
    TRecord r -> pretty r
    TForall ts es t -> T.concat ["forall ", pretty ts, pretty es, " ==> ", pretty t]
    TVar v -> T.append "`" v
    TGenericAlias t tas -> T.append t $ pretty tas

newtype RecordTyp = RecordTyp [RecordTypProp] deriving (Eq, Show, Generic)
instance Sexp RecordTyp

instance Pretty RecordTyp where
  pretty (RecordTyp ps) = T.concat ["#{", T.intercalate "; " $ map pretty ps, "}"]

data RecordTypProp = RecordTypProp ConstantQualifier Text Typ deriving (Eq, Show, Generic)
instance Sexp RecordTypProp

instance Pretty RecordTypProp where
  pretty (RecordTypProp cq n t) = T.concat [pretty cq, " ", n, " : ", pretty t]

data EffRow =
  ERVar Text
  | ERAlias Text
  | ERSugar [EffRowEntry] (Maybe Text)
  deriving (Eq, Show, Generic)
instance Sexp EffRow

instance Pretty EffRow where
  pretty = \case
    ERVar r -> "`" <> r
    ERAlias a -> a
    ERSugar res t -> T.concat [T.intercalate "; " $ map pretty res, maybe T.empty (T.append " | ") t]

data EffRowEntry = EREEffCons EffCons | EREEffRow EffRow deriving (Eq, Show, Generic)
instance Sexp EffRowEntry

instance Pretty EffRowEntry where
  pretty (EREEffCons ec) = pretty ec
  pretty (EREEffRow er) = T.append "..." $ pretty er

data EffCons = EffCons ECons | EVar Text deriving (Eq, Show, Generic)

data ECons = ECons Text (Maybe TypeApps) deriving (Eq, Show, Generic)

instance Sexp ECons
instance Sexp EffCons

instance Pretty ECons where
  pretty (ECons n tps) = T.append n $ pretty tps

instance Pretty EffCons where
  pretty (EffCons e) = pretty e
  pretty (EVar n) = "`" <> n

data Block = Block [BlockStat] Exp deriving (Eq, Generic)
instance Sexp Block

instance Pretty Block where
  pretty (Block sts e) = T.intercalate "; " $ map pretty sts <> [pretty e]

instance Show Block where
  show (Block sts e) =
    concat ["(Block [", String.intercalate "; " (map show sts), "] ", show e, ")"]

data BindDef = BindDef ConstantQualifier LambdaParam Exp deriving (Eq, Show, Generic)
instance Sexp BindDef

instance Pretty BindDef where
  pretty (BindDef cq lp e) =
    T.concat [pretty cq, " ", pretty lp, " = ", pretty e]

data ConstantQualifier = Var | Val | Imm deriving (Eq, Show, Generic)
instance Sexp ConstantQualifier

instance Pretty ConstantQualifier where
  pretty = \case
    Var -> "var"
    Val -> "val"
    Imm -> "imm"

-- | A statement of a block, with the source region it came from.  Statements
--   need their own position because the errors they raise (assigning to an
--   immutable variable, shadowing a binding in the same scope) are about the
--   statement, not about any subexpression.
data BlockStat = BlockStat {
    bsSpan :: Span
  , bsNode :: BlockStatNode
  } deriving (Eq, Generic)

-- | The shape of a block statement, without its position.
data BlockStatNode =
  BExpNode Exp
  | BBindDefNode BindDef
  | BAssignNode Assign
  deriving (Eq, Show, Generic)

instance Sexp BlockStat where sexp = sexp . bsNode
instance Sexp BlockStatNode

pattern BExp :: Exp -> BlockStat
pattern BExp e <- BlockStat _ (BExpNode e) where
  BExp e = BlockStat (expSpan e) (BExpNode e)

pattern BBindDef :: BindDef -> BlockStat
pattern BBindDef b <- BlockStat _ (BBindDefNode b) where
  BBindDef b@(BindDef _ _ e) = BlockStat (expSpan e) (BBindDefNode b)

pattern BAssign :: Assign -> BlockStat
pattern BAssign a <- BlockStat _ (BAssignNode a) where
  BAssign a@(Assign _ e) = BlockStat (expSpan e) (BAssignNode a)

{-# COMPLETE BExp, BBindDef, BAssign #-}

instance Show BlockStat where
  show (BlockStat _ n) = show n

-- | Move a statement to the given span.
atBlockStatSpan :: Span -> BlockStat -> BlockStat
atBlockStatSpan s st = st {bsSpan = s}

instance Pretty BlockStat where
  pretty = pretty . bsNode

instance Pretty BlockStatNode where
  pretty = \case
    BExpNode e -> pretty e
    BBindDefNode b -> pretty b
    BAssignNode a -> pretty a

data Assign = Assign Text Exp deriving (Eq, Show, Generic)
instance Sexp Assign

instance Pretty Assign where
  pretty (Assign anchor e) = T.append anchor $ pretty e

data PathExp = PathExp Exp [Text] deriving (Eq, Show)

instance Pretty PathExp where
  pretty (PathExp e ns) =
    T.concat [
      pretty e,
      "@",
      case ns of [n] -> n; _ -> T.concat ["(", T.unwords ns, ")"]
    ]

data LetPattern = LPATom AtomLetPattern | LPParam LambdaParam deriving (Eq, Show, Generic)
instance Sexp LetPattern


instance Pretty LetPattern where
  pretty (LPATom a) = pretty a
  pretty (LPParam lp) = pretty lp

data AtomLetPattern =
  ALPNil
  | ALPUnderscore
  | ALPPair LetPattern LetPattern
  | ALPParen LetPattern
  | ALPRecord [AtomLetPatternRecordProp]
  deriving (Eq, Show, Generic)
instance Sexp AtomLetPattern

instance Pretty AtomLetPattern where
  pretty = \case
    ALPNil -> "()"
    ALPUnderscore -> "_"
    ALPPair l r -> T.concat [pretty l, ", ", pretty r]
    ALPParen lp -> T.concat ["(", pretty lp, ")"]
    ALPRecord ps -> T.concat ["#{", T.intercalate "; " $ map pretty ps, "}"]

data AtomLetPatternRecordProp =
  AtomLetPatternRecordProp ConstantQualifier LambdaParam (Maybe AtomLetPattern)
  deriving (Eq, Show, Generic)
instance Sexp AtomLetPatternRecordProp

instance Pretty AtomLetPatternRecordProp where
  pretty (AtomLetPatternRecordProp cq lp alp) = T.unwords [pretty cq, pretty lp, maybe "" pretty alp]

newtype TypeApps = TypeApps [TypeArg] deriving (Eq, Show, Generic)
instance Sexp TypeApps

instance Pretty TypeApps where
  pretty (TypeApps tas) = T.concat ["[", T.intercalate "; " $ map pretty tas, "]"]

data EffApps = EffApps [EffArg] [EffRow] deriving (Eq, Show, Generic)
instance Sexp EffApps
instance Pretty EffApps where
  pretty (EffApps es rs) = T.concat [
      "{",
      T.intercalate "; " $ map pretty es,
      if null rs then "" else " | " <> T.intercalate "; " (map pretty rs),
      "}"
    ]

data EffArg = EACons EffCons | EARow EffRow deriving (Eq, Show, Generic)
instance Sexp EffArg

instance Pretty EffArg where
  pretty = \case EACons c -> pretty c; EARow r -> T.append "..." $ pretty r

data TypeArg =
  TAFlat Text
  | TANil
  | TAArray TypeArg
  | TAParen TypeArg
  | TAPair TypeArg TypeArg
  | TAFunct TypeArg TypeArg
  | TARecord RecordTypeArg
  | TAMeta Text
  | TAGenericAlias Text TypeApps
  deriving (Eq, Show, Generic)
instance Sexp TypeArg

instance Pretty TypeArg where
  pretty = \case
    TAFlat t -> t
    TANil -> "()"
    TAArray t -> T.concat ["[", pretty t, "]"]
    TAParen t -> T.concat ["(", pretty t, ")"]
    TAPair l r -> T.concat [pretty l, ", ", pretty r]
    TAFunct i o -> T.concat [pretty i, " -> ", pretty o]
    TARecord r -> pretty r
    TAMeta v -> "`" <> v
    TAGenericAlias t tas -> t <> pretty tas

newtype RecordTypeArg = RecordTypeArg [RecordTypeArgProp] deriving (Eq, Show, Generic)
instance Sexp RecordTypeArg

instance Pretty RecordTypeArg where
  pretty (RecordTypeArg ps) = T.concat ["#{", T.intercalate "; " $ map pretty ps, "}"]

data RecordTypeArgProp = RecordTypeArgProp ConstantQualifier Text TypeArg deriving (Eq, Show, Generic)
instance Sexp RecordTypeArgProp
instance Pretty RecordTypeArgProp where
  pretty (RecordTypeArgProp cq n t) = T.concat [pretty cq, " ", n, " : ", pretty t]

-- | An expression together with the region of source it came from.
--
--   Constructed by the parser with a real 'Span'; the elaborator only ever
--   matches on it.  'noSpan' means \"unknown\" and every consumer must
--   tolerate it.
data Exp = Exp {
    expSpan :: Span
  , expNode :: ExpNode
  } deriving (Eq, Show, Generic)

-- | The shape of an expression, without its position.
data ExpNode =
    NName Text
  | NApply Exp Exp
  | NDollar Exp Exp
  | NLiteral Literal
  | NPair Exp Exp
  | NLet LetPattern Exp Exp
  | NBacktick Text Exp Exp
  | NPropAccess Exp Text
  | NIfThenElse Exp Exp Exp
  | NUnder Under
  | NResume Exp
  | NParen Block
  | NWith Exp TypeApps EffApps
  deriving (Eq, Show, Generic)

instance Sexp Exp where sexp = sexp . expNode
instance Sexp ExpNode

-- | The public constructors of 'ExpNode' as matchable patterns.
--
--   They are bidirectional, but the builder form attaches 'noSpan': only the
--   parser has a position to give, and it overwrites the span of the finished
--   node (see 'Parser.located').  'tests/SpanSpec.hs' checks that every node of
--   every example program ends up with a real span, so a forgotten 'located'
--   fails the suite instead of silently losing the position.
pattern EName :: Text -> Exp
pattern EName n <- Exp _ (NName n) where
  EName n = Exp noSpan (NName n)

pattern EApply :: Exp -> Exp -> Exp
pattern EApply f x <- Exp _ (NApply f x) where
  EApply f x = Exp (mergeSpan (expSpan f) (expSpan x)) (NApply f x)

pattern EDollar :: Exp -> Exp -> Exp
pattern EDollar f x <- Exp _ (NDollar f x) where
  EDollar f x = Exp (mergeSpan (expSpan f) (expSpan x)) (NDollar f x)

pattern ELiteral :: Literal -> Exp
pattern ELiteral l <- Exp _ (NLiteral l) where
  ELiteral l = Exp noSpan (NLiteral l)

pattern EPair :: Exp -> Exp -> Exp
pattern EPair l r <- Exp _ (NPair l r) where
  EPair l r = Exp (mergeSpan (expSpan l) (expSpan r)) (NPair l r)

pattern ELet :: LetPattern -> Exp -> Exp -> Exp
pattern ELet p w b <- Exp _ (NLet p w b) where
  ELet p w b = Exp (mergeSpan (expSpan w) (expSpan b)) (NLet p w b)

pattern EBacktick :: Text -> Exp -> Exp -> Exp
pattern EBacktick op l r <- Exp _ (NBacktick op l r) where
  EBacktick op l r = Exp (mergeSpan (expSpan l) (expSpan r)) (NBacktick op l r)

pattern EPropAccess :: Exp -> Text -> Exp
pattern EPropAccess e n <- Exp _ (NPropAccess e n) where
  EPropAccess e n = Exp (expSpan e) (NPropAccess e n)

pattern EIfThenElse :: Exp -> Exp -> Exp -> Exp
pattern EIfThenElse p t f <- Exp _ (NIfThenElse p t f) where
  EIfThenElse p t f =
    Exp (mergeSpan (expSpan p) (mergeSpan (expSpan t) (expSpan f))) (NIfThenElse p t f)

pattern EUnder :: Under -> Exp
pattern EUnder u <- Exp _ (NUnder u) where
  EUnder u = Exp noSpan (NUnder u)

pattern EResume :: Exp -> Exp
pattern EResume e <- Exp _ (NResume e) where
  EResume e = Exp (expSpan e) (NResume e)

pattern EParen :: Block -> Exp
pattern EParen b <- Exp _ (NParen b) where
  EParen b = Exp noSpan (NParen b)

pattern EWith :: Exp -> TypeApps -> EffApps -> Exp
pattern EWith e ts es <- Exp _ (NWith e ts es) where
  EWith e ts es = Exp (expSpan e) (NWith e ts es)

{-# COMPLETE EName, EApply, EDollar, ELiteral, EPair, ELet, EBacktick
   , EPropAccess, EIfThenElse, EUnder, EResume, EParen, EWith #-}

-- | A node covering both children.
binExp :: (Exp -> Exp -> ExpNode) -> Exp -> Exp -> Exp
binExp f l r = Exp (mergeSpan (expSpan l) (expSpan r)) (f l r)

instance Pretty Exp where
  pretty (Exp _ n) = pretty n

instance Pretty ExpNode where
  pretty = \case
    NName n -> n
    NApply c e -> T.concat [pretty c, " ", pretty e]
    NDollar c e -> T.concat [pretty c, " $ ", pretty e]
    NLiteral l -> pretty l
    NPair l r -> T.concat ["(", pretty l, ", ", pretty r, ")"]
    NLet p w e -> T.concat ["let ", pretty p, " = ", pretty w, " in ", pretty e]
    NBacktick op l r -> T.concat [pretty l, "`", op, "`", pretty r]
    NPropAccess e n -> T.concat [pretty e, "@", n]
    NIfThenElse p t f -> T.concat ["if ", pretty p, " then ", pretty t, " else ", pretty f]
    NUnder u -> pretty u
    NResume e -> T.append "resume " $ pretty e
    NParen b -> T.concat ["(", pretty b, ")"]
    NWith e tas eas -> T.concat [pretty e, " with ", pretty tas, pretty eas]

data ExpPrecedence =
  PrecResume
  | PrecDollar
  | PrecBacktick
  | PrecPostfix      -- @, with
  | PrecApply
  | PrecAtom
  deriving (Eq, Ord, Show, Enum, Bounded)

-- precExp :: Exp -> ExpPrecedence
-- precExp = \case
--   -- атомы
--   EPair {}        -> PrecAtom
--   ELiteral _      -> PrecAtom
--   EName _         -> PrecAtom
--   EParen _        -> PrecAtom  -- если есть

--   -- apply
--   EApply {}       -> PrecApply

--   -- постфиксы
--   EPropAccess {}  -> PrecPostfix
--   EWith {}        -> PrecPostfix

--   -- инфиксы
--   EBacktick {}    -> PrecBacktick
--   EDollar {}      -> PrecDollar

--   -- слабый префикс
--   EResume _       -> PrecResume

--   -- структурные формы считаем самыми слабыми
--   EIfThenElse {}  -> PrecResume
--   ELet {}         -> PrecResume
--   EUnder {}       -> PrecResume

data Under =
  Under ECons Block [HandlerClause] Text Block
  -- | UThen EffCons Block [HandlerClause] Text Block
  deriving (Eq, Show, Generic)
instance Sexp Under

instance Pretty Under where
  pretty (Under ec b hcs n t) =
    T.concat [
      "under ",
      pretty ec,
      " to ",
      pretty b,
      " handle ",
      T.unwords $ map pretty hcs,
      T.concat [" | then ", n, " => ", pretty t]
    ]
  -- pretty (UThen ec b hcs n t) =
  --   T.concat [
  --     "under ", pretty ec, " to ",
  --     pretty b,
  --     " handle ",
  --     T.unwords $ map pretty hcs,
  --     " | then ", n, " => ", pretty t
  --   ]


data HandlerClause = HandlerClause Text [Text] Block deriving (Eq, Show, Generic)
instance Sexp HandlerClause

instance Pretty HandlerClause where
  pretty (HandlerClause op ns b) =
    T.concat [
      " | ",
      op,
      " ",
      T.unwords ns,
      " => ",
      pretty b
    ]

data Literal =
  LAtom Atom
  | LArray ArrayLiteral
  | LLambda LambdaLiteral
  | LRecord RecordLiteral
  deriving (Eq, Show, Generic)

instance Sexp Literal

instance Pretty Literal where
  pretty = \case
    LAtom a -> pretty a
    LArray ar -> pretty ar
    LLambda l -> pretty l
    LRecord r -> pretty r

data Atom =
  AString Text
  | ANumber Number
  | ANil
  | ABoolean Bool
  deriving (Eq, Show, Generic)

instance Sexp Atom

instance Pretty Atom where
  pretty = \case
    AString s -> T.concat ["'", s, "'"]
    ANumber n -> pretty n
    ANil -> "()"
    ABoolean b -> if b then "true" else "false"

data Number = NInt Integer | NFloat Scientific deriving (Eq, Show, Generic)

instance Sexp Number

instance Pretty Number where
  pretty = \case
    NInt n -> T.pack $ show n
    NFloat f -> T.pack $ show f

newtype ArrayLiteral = ArrayLiteral [ArrayEntry] deriving (Eq, Show, Generic)
instance Sexp ArrayLiteral

instance Pretty ArrayLiteral where
  pretty (ArrayLiteral ar) = T.concat ["[", T.intercalate ", " (map pretty ar), "]"]

data ArrayEntry = AEExp Exp | AEBlock Block deriving (Eq, Show, Generic)
instance Sexp ArrayEntry

instance Pretty ArrayEntry where
  pretty = \case AEExp e -> pretty e; AEBlock b -> pretty b

data LambdaLiteral =
  LambdaLiteral (Maybe TypeParams) (Maybe EffParams) (Maybe LambdaHead) Block
  deriving (Eq, Show, Generic)
instance Sexp LambdaLiteral

{-
data LambdaLiteral =
  LambdaLiteral (Maybe TypeParams) (Maybe EffParams) (Maybe LambdaHead) Block
  deriving (Eq, Show)
-}

instance Pretty LambdaLiteral where
  pretty (LambdaLiteral tps eps lh b) =
    T.concat ["{", pretty tps, pretty eps, pretty lh, pretty b, "}"]

data LambdaHead = LambdaHead [LambdaParam] (Maybe Typ) deriving (Eq, Show, Generic)
instance Sexp LambdaHead

instance Pretty LambdaHead where
  pretty (LambdaHead lps t) =
    T.concat [
      "(",
      T.intercalate "; " $ map pretty lps,
      ")",
      maybe "" (T.append " : " . pretty) t,
      " = "
    ]

data LambdaParam = LambdaParam Text (Maybe Typ) deriving (Eq, Show, Generic)
instance Sexp LambdaParam

instance Pretty LambdaParam where
  pretty (LambdaParam n t) = T.append n $ maybe "" (T.append " : " . pretty) t

data RecordLiteral = RecordLiteral (Maybe Exp) [BindDef] deriving (Eq, Show, Generic)
instance Sexp RecordLiteral

instance Pretty RecordLiteral where
  pretty (RecordLiteral e bs) =
    T.concat [
      "#{",
      maybe "" ((`T.append` " | ") . pretty) e,
      T.intercalate "; " $ map pretty bs,
      "}"
    ]