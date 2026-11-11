{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE RankNTypes #-}

module Elaborator (
  elaborate,
  elaborateTopLevelStat,
  elaborateEffRow,
  elaborateExpr,
  elaborateBlock,
  ElabState(..),
  ElabM,
  ElaborationError(..),
  ElabEnv(..)
)
where

import qualified Ast
import qualified Types
import qualified Data.Text as T
import Utils (uniqPreserveOrder, TextMap)
import Data.Coerce (coerce)
import Data.Text (Text)
import Text.Printf (printf)
import qualified Data.Map as Map
import Control.Monad.State (State)
import Control.Lens (makeLenses, (%~), (^.), Lens')
import Control.Lens.Lens ((&))
import Control.Monad (foldM, when, forM)
import Control.Monad.Except (ExceptT)
import Control.Lens.Getter (use)
import Control.Lens.Setter ((+=))
import Control.Monad.Error.Class (throwError)
import Types (Mutability, Taste)
import Data.Traversable (for)
import Data.Maybe (fromMaybe)
import Data.Map (Map)

data FlatRow = FlatRow [Types.EffCons] (Maybe Taste)
data TypeAliasDef = TypeAliasDef [Text] Ast.Typ

type RowEnv = [(String, Ast.EffRow)]
type TypEnv = [(String, TypeAliasDef)]
data ElabEnv = ElabEnv {
  _typBounds :: TextMap Taste,
  _effBounds :: TextMap Taste,
  _rowBounds :: TextMap Taste,
  _iTypVars :: TextMap Taste,
  _iEffVars :: TextMap Taste,
  _iRowVars :: TextMap Taste
}

makeLenses ''ElabEnv

emptyEnv :: ElabEnv
emptyEnv = ElabEnv
  mempty
  mempty
  mempty
  mempty
  mempty
  mempty

data ElaborationError =
  ElaborationError Text
  | UnboundVarError Text
  deriving (Show)

newtype ElabState = ElabState {_counter :: Int}

makeLenses ''ElabState

type ElabM a = ExceptT ElaborationError (State ElabState) a

freshBound, freshMeta :: Text -> ElabM Taste
freshBound name = do
  counter += 1
  Types.Bound name <$> use counter

freshMeta name = do
  counter += 1
  Types.Meta name <$> use counter <*> pure (-1)

lookupMap :: Lens' ElabEnv (TextMap Taste) -> ElabEnv -> Text -> Maybe Taste
lookupMap m env x = Map.lookup x $ env ^. m

getBoundOrMakeMeta ::
  Lens' ElabEnv (TextMap Taste)
  -> Lens' ElabEnv (TextMap Taste)
  -> ElabEnv
  -> Text
  -> ElabM Taste
getBoundOrMakeMeta m im env x =
  case lookupMap m env x of
    Just x' -> pure x'
    _ -> case lookupMap im env x of
      Just x' -> pure x'
      _ -> do
        meta <- freshMeta x
        let _ = extendMap im [(x, meta)] env
        pure meta    

extendMap :: Lens' ElabEnv (TextMap Taste) -> [(Text, Taste)] -> ElabEnv -> ElabEnv
extendMap m bs env = env & m %~ Map.union (Map.fromList bs)

lookupTyp, lookupEff, lookupRow, lookupITyp, lookupIEff, lookupIRow ::
  ElabEnv -> Text -> Maybe Taste
lookupTyp  = lookupMap typBounds
lookupEff  = lookupMap effBounds
lookupRow  = lookupMap rowBounds
lookupITyp = lookupMap iTypVars
lookupIEff = lookupMap iEffVars
lookupIRow = lookupMap iRowVars

extendTyp, extendEff, extendRow, extendITyp, extendIEff, extendIRow ::
  [(Text, Taste)] -> ElabEnv -> ElabEnv
extendTyp  = extendMap typBounds
extendEff  = extendMap effBounds
extendRow  = extendMap rowBounds
extendITyp = extendMap iTypVars
extendIEff = extendMap iEffVars
extendIRow = extendMap iRowVars

resolveTypTaste, resolveEffTaste, resolveRowTaste :: ElabEnv -> Text -> ElabM Taste
resolveTypTaste env n =
  case lookupTyp env n of
    Just t -> pure t
    Nothing -> throwError $ UnboundVarError $ "Unbound type variable: " <> n

resolveEffTaste env n =
  case lookupEff env n of
    Just t -> pure t
    Nothing -> throwError $ UnboundVarError $ "Unbound eff variable: " <> n

resolveRowTaste env n =
  case lookupRow env n of
    Just t -> pure t
    Nothing -> throwError $ UnboundVarError $ "Unbound row variable: " <> n

elaborate :: Ast.Chunk -> ElabM Types.Chunk
elaborate (Ast.Chunk stats) = do
  rowEnv <- collectRowEnv stats
  typEnv <- collectTypEnv stats
  mapM (elaborateTopLevelStat rowEnv typEnv) stats

collectRowEnv :: [Ast.TopLevelStat] -> ElabM RowEnv
collectRowEnv = foldM go []
  where
    go :: RowEnv -> Ast.TopLevelStat -> ElabM RowEnv
    go acc stat = case stat of
      Ast.RowDef n row -> do
        let name = T.unpack n
        when (any ((name ==) . fst) acc) $
          throwError $ ElaborationError $ "Duplicate row definition: " <> n
        pure ((name, row) : acc)
      _ -> pure acc

collectTypEnv :: [Ast.TopLevelStat] -> ElabM TypEnv
collectTypEnv = foldM go []
  where
    go :: TypEnv -> Ast.TopLevelStat -> ElabM TypEnv
    go acc stat = case stat of
      Ast.TypeDef n ts body -> do
        let name = T.unpack n
        when (any ((name ==) . fst) acc) $
          throwError $ ElaborationError $ "Duplicate type definition: " <> n
        pure ((name, TypeAliasDef (coerce ts) body) : acc)
      _ -> pure acc

elaborateTopLevelStat :: RowEnv -> TypEnv -> Ast.TopLevelStat -> ElabM Types.TopLevelStat
elaborateTopLevelStat = elaborateTopLevelStat' emptyEnv

elaborateTopLevelStat' :: ElabEnv -> RowEnv -> TypEnv -> Ast.TopLevelStat -> ElabM Types.TopLevelStat
elaborateTopLevelStat' env renv tenv = \case
  Ast.TypeDef n ts t -> do
    ts' <- for (coerce ts) $ \nm -> (nm,) <$> freshBound nm
    let env' = extendTyp ts' env
    Types.STypeDef n (coerce ts) <$> elaborateType' renv tenv env' [] t
  Ast.EffectDef n ts ops -> do
    ts' <- for (coerce ts) $ \nm -> (nm,) <$> freshBound nm
    let env' = extendTyp ts' env
    Types.SEffDef . Types.EffDef n (coerce ts)
      <$> forM ops (\(Ast.EffectOp n' t) -> (n',) <$> elaborateFunct renv tenv env' t)
  Ast.RowDef n fxs ->
    Types.SRowDef . Types.RowDef n <$> elaborateEffRow' renv tenv env fxs
  Ast.FunctDef n ts (Ast.EffParams es rs) args fxs t b -> do
    ts' <- for (coerce ts) $ \nm -> (nm,) <$> freshBound nm
    es' <- for es $ \nm -> (nm,) <$> freshBound nm
    rs' <- for rs $ \nm -> (nm,) <$> freshBound nm
    let env' = extendRow rs' $ extendEff es' $ extendTyp ts' env
    args' <- forM args $ \case
      Ast.NamedFunctArg n' t' -> (n',) <$> elaborateType' renv tenv env' [] t'
      Ast.NilArg -> pure (".", Types.TNil)
    fxs' <- for fxs $ elaborateEffRow' renv tenv env'
    t' <- elaborateType' renv tenv env' [] t
    Types.SFunctDef . Types.FunctDecl
      n
      (coerce ts)
      es
      rs
      args'
      (fxs', t')
      <$> elaborateBlock renv tenv env' b

elaborateBlock :: RowEnv -> TypEnv -> ElabEnv -> Ast.Block -> ElabM Types.Block
elaborateBlock renv tenv env (Ast.Block stats e) = do
  stats' <- forM stats $ elaborateBlockStat renv tenv env
  e' <- elaborateExpr renv tenv env e
  pure (stats', e')

elaborateBlockStat :: RowEnv -> TypEnv -> ElabEnv -> Ast.BlockStat -> ElabM Types.Stat
elaborateBlockStat renv tenv env = \case
  Ast.BExp e -> Types.Expr <$> elaborateExpr renv tenv env e
  Ast.BAssign (Ast.Assign n e) -> Types.Assign n <$> elaborateExpr renv tenv env e
  Ast.BBindDef (Ast.BindDef c (Ast.LambdaParam n t) e) ->
    Types.Bind (elaborateMutability c) n <$> for t (elaborateType' renv tenv env []) <*> elaborateExpr renv tenv env e

elaborateApply :: RowEnv -> TypEnv -> ElabEnv -> Bool -> Ast.Exp -> Ast.Exp -> ElabM Types.Expr
elaborateApply renv tenv env wrapInParens f e = do
  f' <- elaborateExpr renv tenv env f
  e' <- elaborateExpr renv tenv env e
  let e'' = if wrapInParens then Types.Paren ([], e') else e'
  pure $ Types.Apply f' e''

elaborateExpr :: RowEnv -> TypEnv -> ElabEnv -> Ast.Exp -> ElabM Types.Expr
elaborateExpr renv tenv env = \case
  Ast.EName n -> pure $ Types.XVar n
  Ast.EApply f e -> elaborateApply renv tenv env False f e
  Ast.EDollar f e -> elaborateApply renv tenv env True f e
  Ast.ELiteral l -> case l of
    Ast.LAtom a -> case a of
      Ast.AString s -> pure $ Types.String s
      Ast.ANumber (Ast.NInt i) -> pure $ Types.Int i
      Ast.ANumber (Ast.NFloat f) -> pure $ Types.Float f
      Ast.ANil -> pure Types.Nil
      Ast.ABoolean b -> pure $ Types.Boolean b
    Ast.LArray (Ast.ArrayLiteral es) ->
      Types.Array <$> traverse (\case
        Ast.AEExp e -> elaborateExpr renv tenv env e
        Ast.AEBlock b -> Types.Paren <$> elaborateBlock renv tenv env b) es
    Ast.LLambda l' -> elaborateLambdaLiteral renv tenv env l'
    Ast.LRecord (Ast.RecordLiteral e props) -> do
      e' <- mapM (elaborateExpr renv tenv env) e
      Types.Record e' <$> mapM go props
      where
        go :: Ast.BindDef -> ElabM Types.ERecordProp
        go (Ast.BindDef c (Ast.LambdaParam n t) e') =
          Types.ERecordProp (elaborateMutability c) n <$> mapM (elaborateType' renv tenv env []) t <*> elaborateExpr renv tenv env e'
  Ast.EPair l r -> Types.Pair <$> elaborateExpr renv tenv env l <*> elaborateExpr renv tenv env r
  Ast.ELet lp wht whr ->
    Types.Let <$> elaborateLetPattern renv tenv env lp <*> elaborateExpr renv tenv env wht <*> elaborateExpr renv tenv env whr
  Ast.EBacktick op l r ->
    Types.Apply . Types.Apply (Types.XVar op)
      <$> elaborateExpr renv tenv env l
      <*> elaborateExpr renv tenv env r
  Ast.EPropAccess e n -> (`Types.PropAccess` n) <$> elaborateExpr renv tenv env e
  Ast.EIfThenElse p t f ->
    Types.IfElse
      <$> elaborateExpr renv tenv env p
      <*> elaborateExpr renv tenv env t
      <*> elaborateExpr renv tenv env f
  Ast.EResume e -> Types.Resume <$> elaborateExpr renv tenv env e
  Ast.EWith e tas (Ast.EffApps eas ras) -> do
    Types.With
      <$> elaborateExpr renv tenv env e
      <*> mapM (elaborateTypeArg tenv env) (coerce tas)
      <*> (concat <$> mapM (elaborateEffArg renv tenv env) eas)
      <*> forM ras (elaborateEffRow' renv tenv env)
  Ast.EUnder u -> elaborateUnder renv tenv env u
  Ast.EParen b -> Types.Paren <$> elaborateBlock renv tenv env b

elaborateUnder :: RowEnv -> TypEnv -> ElabEnv -> Ast.Under -> ElabM Types.Expr
elaborateUnder renv tenv env = \case
  Ast.Under eff blk clauses thenN thenB ->
    Types.Handle
      <$> (Types.Handler
            <$> elaborateEffCons tenv env (Ast.EffCons eff)
            <*> elaborateBlock renv tenv env blk
            <*> mapM (elaborateHandlerClause renv tenv env) clauses
            <*> elaborateThenClause renv tenv env thenN thenB)

elaborateThenClause :: RowEnv -> TypEnv -> ElabEnv -> Text -> Ast.Block -> ElabM Types.Lambda
elaborateThenClause renv tenv env n = elaboratePlainLambda renv tenv env [n]

elaboratePlainLambda :: RowEnv -> TypEnv -> ElabEnv -> [Text] -> Ast.Block -> ElabM Types.Lambda
elaboratePlainLambda renv tenv env params body =
  case params of
    [] ->
      Types.Lambda [] [] "." Nothing Nothing
        (Types.RClosed [])
        <$> elaborateBlock renv tenv env body
    [n] ->
      Types.Lambda [] [] n Nothing Nothing
        (Types.RClosed [])
        <$> elaborateBlock renv tenv env body
    n : rest ->
      Types.Lambda [] [] n Nothing Nothing
        (Types.RClosed []) . ([] , ) . Types.XLambda <$> elaboratePlainLambda renv tenv env rest body

elaborateHandlerClause :: RowEnv -> TypEnv -> ElabEnv -> Ast.HandlerClause -> ElabM Types.HandlerClause
elaborateHandlerClause renv tenv env (Ast.HandlerClause op ns b) =
  (op, ) <$> elaboratePlainLambda renv tenv env ns b

elaborateEffArg :: RowEnv -> TypEnv -> ElabEnv -> Ast.EffArg -> ElabM [Types.EffCons]
elaborateEffArg renv tenv env = \case
  Ast.EACons c -> do
    c' <- elaborateEffCons tenv env c
    pure [c']
  Ast.EARow row -> do
    row' <- elaborateEffRow' renv tenv env row
    case row' of
      Types.RClosed cs -> pure cs
      Types.ROpen {} -> error "Open effect rows are not allowed in with effect arguments"
      Types.RVar _ -> error "Bare effect row variable is not allowed in with effect arguments"

elaborateLetPatternRecordProp :: RowEnv -> TypEnv -> ElabEnv -> Ast.AtomLetPatternRecordProp -> ElabM Types.LetPatternRecordProp
elaborateLetPatternRecordProp renv tenv env (Ast.AtomLetPatternRecordProp q lp alp) = do
  lp' <- elaborateLambdaParam renv tenv env lp
  alp' <- case alp of
    Just a -> Just <$> elaborateAtomLetPattern renv tenv env a
    _ -> pure Nothing
  pure $ Types.LetPatternRecordProp (elaborateMutability q) lp' alp'

elaborateLambdaParam :: RowEnv -> TypEnv -> ElabEnv -> Ast.LambdaParam -> ElabM Types.LambdaParam
elaborateLambdaParam renv tenv env (Ast.LambdaParam n mt) = do
  Types.LambdaParam n <$> mapM (elaborateType' renv tenv env []) mt

elaborateLetPattern :: RowEnv -> TypEnv -> ElabEnv -> Ast.LetPattern -> ElabM Types.LetPattern
elaborateLetPattern renv tenv env = \case
  Ast.LPATom (Ast.ALPParen lp) -> elaborateLetPattern renv tenv env lp
  Ast.LPATom alp -> Types.LPATom <$> elaborateAtomLetPattern renv tenv env alp
  Ast.LPParam lp -> Types.LPParam <$> elaborateLambdaParam renv tenv env lp

stripParenLetPattern :: Ast.LetPattern -> Ast.LetPattern
stripParenLetPattern = \case
  Ast.LPATom (Ast.ALPParen lp) -> stripParenLetPattern lp
  lp -> lp

elaborateAtomLetPattern :: RowEnv -> TypEnv -> ElabEnv -> Ast.AtomLetPattern -> ElabM Types.AtomLetPattern
elaborateAtomLetPattern renv tenv env = \case
  Ast.ALPNil -> pure Types.ALPNil
  Ast.ALPUnderscore -> pure Types.ALPUnderscore
  Ast.ALPPair l r ->
    Types.ALPPair <$> elaborateLetPattern renv tenv env l <*> elaborateLetPattern renv tenv env r
  Ast.ALPParen lp ->
    case stripParenLetPattern lp of
      Ast.LPATom alp -> elaborateAtomLetPattern renv tenv env alp
      Ast.LPParam _ -> error "Parenthesized lambda parameter is not an atomic let pattern"
  Ast.ALPRecord props ->
    Types.ALPRecord <$> mapM (elaborateLetPatternRecordProp renv tenv env) props

elaborateLambdaLiteral :: RowEnv -> TypEnv -> ElabEnv -> Ast.LambdaLiteral -> ElabM Types.Expr
elaborateLambdaLiteral renv tenv env (Ast.LambdaLiteral mtps mfxs mhead body) =
  case mhead of
    Nothing -> do
      mtps' <- maybe (pure []) (mapM freshBound . coerce) mtps
      (meps, mrps, meps', mrps') <- case mfxs of
        Nothing -> pure (Nothing, Nothing, [], [])
        Just (Ast.EffParams meps mrps) -> (Just meps, Just mrps, ,) <$> mapM freshBound meps <*> mapM freshBound mrps
      let env' =
            extendRow (zip (fromMaybe [] mrps) mrps') $
            extendEff (zip (fromMaybe [] meps) meps') $
            extendTyp (zip (maybe [] coerce mtps) mtps') env
      Types.XLambda . Types.Lambda
        mtps'
        meps'
        "."
        Nothing
        Nothing
        (Types.RClosed [])
        <$> elaborateBlock renv tenv env' body
    Just (Ast.LambdaHead params retT) -> do
      mtps' <- maybe (pure []) (mapM freshBound . coerce) mtps
      (meps, mrps, meps', mrps') <- case mfxs of
        Nothing -> pure (Nothing, Nothing, [], [])
        Just (Ast.EffParams meps mrps) -> (Just meps, Just mrps, ,) <$> mapM freshBound meps <*> mapM freshBound mrps
      let env' =
            extendRow (zip (fromMaybe [] mrps) mrps') $
            extendEff (zip (fromMaybe [] meps) meps') $
            extendTyp (zip (maybe [] coerce mtps) mtps') env
      elaborateCurriedLambda
        renv
        tenv
        env'
        mtps'
        meps'
        params
        retT
        body

elaborateCurriedLambda :: RowEnv
  -> TypEnv
  -> ElabEnv
  -> [Taste]
  -> [Taste]
  -> [Ast.LambdaParam]
  -> Maybe Ast.Typ
  -> Ast.Block
  -> ElabM Types.Expr
elaborateCurriedLambda renv tenv env tps eps params retT body =
  Types.XLambda <$> case params of
    [] -> error "Lambda head must contain at least one parameter"
    [Ast.LambdaParam n argT] ->
      Types.Lambda
        tps
        eps
        n
        <$> mapM (elaborateType' renv tenv env []) argT
        <*> mapM (elaborateType' renv tenv env []) retT
        <*> pure (Types.RClosed [])
        <*> elaborateBlock renv tenv env body
    Ast.LambdaParam n argT : rest -> do
      innerExpr <- elaborateCurriedLambda renv tenv env [] [] rest retT body
      argT' <- mapM (elaborateType' renv tenv env []) argT
      pure $ Types.Lambda
        tps
        eps
        n
        argT'
        Nothing
        (Types.RClosed [])
        ([], innerExpr)

elaborateFunct :: RowEnv -> TypEnv -> ElabEnv -> Ast.Funct -> ElabM Types.Funct
elaborateFunct renv tenv env (Ast.Funct i o fxs) =
  Types.Funct
    <$> elaborateType' renv tenv env [] i
    <*> elaborateType' renv tenv env [] o
    <*> elaborateEffRow' renv tenv env fxs

-- elaborateType :: RowEnv -> TypEnv -> Ast.Typ -> ElabM Types.Typ
-- elaborateType renv tenv = elaborateType' renv tenv emptyEnv []

elaborateType' :: RowEnv -> TypEnv -> ElabEnv -> [Text] -> Ast.Typ -> ElabM Types.Typ
elaborateType' renv tenv env visiting = \case
  Ast.TFlat n -> case n of
    "Int" -> pure Types.TInt
    "Float" -> pure Types.TFloat
    "Boolean" -> pure Types.TBoolean
    "String" -> pure Types.TString
    "Nil" -> pure Types.TNil
    "Nothing" -> pure Types.TNothing
    _ ->
      case lookup (T.unpack n) tenv of
        Just (TypeAliasDef params _)
          | null params -> expandTypeAlias' renv tenv env visiting n (Ast.TypeApps [])
          | otherwise ->
              error $ printf
                "Type alias '%s' expects %d argument(s), but was used without any"
                (T.unpack n)
                (length params)
        Nothing -> pure $ Types.TFlat n
  Ast.TNil -> pure Types.TNil
  Ast.TArray t -> Types.TArray <$> elaborateType' renv tenv env visiting t
  Ast.TParen t -> elaborateType' renv tenv env visiting t
  Ast.TPair l r -> Types.TPair <$> elaborateType' renv tenv env visiting l <*> elaborateType' renv tenv env visiting r
  Ast.TFunct (Ast.Funct i o fxs) -> do
      i' <- elaborateType' renv tenv env visiting i
      o' <- elaborateType' renv tenv env visiting o
      fxs' <- elaborateEffRow' renv tenv env fxs
      pure $ Types.TFunct $ Types.Funct i' o' fxs'
  Ast.TRecord (Ast.RecordTyp props) ->
    Types.TRecord <$>
      mapM (\(Ast.RecordTypProp c n t) ->
        Types.TRecordProp (elaborateMutability c) n <$> elaborateType' renv tenv env visiting t)
      props
  Ast.TForall (Ast.TypeParams ts) (Ast.EffParams es rs) t -> do
    ts' <- traverse (\n -> (n, ) <$> freshBound n) ts
    es' <- traverse (\n -> (n, ) <$> freshBound n) es
    rs' <- traverse (\n -> (n, ) <$> freshBound n) rs
    let env' = extendEff es' $ extendTyp ts' env
    Types.TForall
      (map snd ts') (map snd es') (map snd rs')
      Map.empty
      Map.empty
      <$> elaborateType' renv tenv env' visiting t
  Ast.TVar t -> Types.TVar <$> getBoundOrMakeMeta typBounds iTypVars env t
    -- case lookupTyp env t of
    --   Just t' -> pure $ Types.TVar t'
    --   _ -> case lookupITyp env t of
    --     Just t' -> pure $ Types.TVar t'
    --     _ -> do
    --       meta <- freshMeta t
    --       let _ = extendITyp [(t, meta)] env
    --       pure $ Types.TVar meta
  Ast.TGenericAlias n ts -> expandTypeAlias' renv tenv env visiting n ts

expandTypeAlias' :: RowEnv -> TypEnv -> ElabEnv -> [Text] -> Text -> Ast.TypeApps -> ElabM Types.Typ
expandTypeAlias' renv tenv env visiting n (Ast.TypeApps ts)
  | n `elem` visiting = error $ "Cyclic type alias: " <> T.unpack n
  | otherwise =
    case lookup (T.unpack n) tenv of
      Nothing -> error $ "Unknown type alias: " <> T.unpack n
      Just (TypeAliasDef params body) ->
        if length params /= length ts then
          error $ printf
            "Wrong number of type arguments for alias '%s': expected %d, got %d"
            (T.unpack n)
            (length params)
            (length ts)
        else
          let body' = substTypeInTyp (zip params ts) body
          in elaborateType' renv tenv env (n : visiting) body'

elaborateTypeArg :: TypEnv -> ElabEnv -> Ast.TypeArg -> ElabM Types.TypeArg
elaborateTypeArg tenv env = elaborateTypeArg' tenv env []

elaborateTypeArg' :: TypEnv -> ElabEnv -> [Text] -> Ast.TypeArg -> ElabM Types.TypeArg
elaborateTypeArg' tenv env visiting = \case
  Ast.TAFlat n -> case n of
    "Int" -> pure Types.TAInt
    "Float" -> pure Types.TAFloat
    "Boolean" -> pure Types.TABoolean
    "String" -> pure Types.TAString
    "Nil" -> pure Types.TANil
    "Nothing" -> pure Types.TANothing
    _ ->
      case lookup (T.unpack n) tenv of
        Just (TypeAliasDef params _)
          | null params -> expandTypeArgAlias' tenv env visiting n (Ast.TypeApps [])
          | otherwise ->
              error $ printf
                "Type alias '%s' expects %d argument(s), but was used without any"
                (T.unpack n)
                (length params)
        Nothing -> pure $ Types.TAFlat n
  Ast.TANil -> pure Types.TANil
  Ast.TAArray t -> Types.TAArray <$> elaborateTypeArg' tenv env visiting t
  Ast.TAParen t -> elaborateTypeArg' tenv env visiting t
  Ast.TAPair l r -> Types.TAPair <$> elaborateTypeArg' tenv env visiting l <*> elaborateTypeArg' tenv env visiting r
  Ast.TAFunct i o -> Types.TAFunct <$> elaborateTypeArg' tenv env visiting i <*> elaborateTypeArg' tenv env visiting o
  Ast.TARecord (Ast.RecordTypeArg props) ->
    Types.TARecord <$>
      mapM (\(Ast.RecordTypeArgProp c n t) ->
        Types.TARecordProp (elaborateMutability c) n <$> elaborateTypeArg' tenv env visiting t)
      props
  Ast.TAMeta t -> Types.TAVar <$> getBoundOrMakeMeta typBounds iTypVars env t
  Ast.TAGenericAlias n ts -> expandTypeArgAlias' tenv env visiting n ts

-- expandTypeArgAlias :: TypEnv -> Text -> Ast.TypeApps -> ElabM Types.TypeArg
-- expandTypeArgAlias tenv = expandTypeArgAlias' tenv emptyEnv []

expandTypeArgAlias' :: TypEnv -> ElabEnv -> [Text] -> Text -> Ast.TypeApps -> ElabM Types.TypeArg
expandTypeArgAlias' tenv env visiting n (Ast.TypeApps ts)
  | n `elem` visiting =
      error $ "Cyclic type alias: " <> T.unpack n
  | otherwise =
      case lookup (T.unpack n) tenv of
        Nothing ->
          error $ "Unknown type alias: " <> T.unpack n
        Just (TypeAliasDef params body) ->
          if length params /= length ts then
            error $ printf
              "Wrong number of type arguments for alias '%s': expected %d, got %d"
              (T.unpack n)
              (length params)
              (length ts)
          else
            case typToTypeArg body of
              Left err ->
                error $ printf
                  "Type alias %s is not valid in type-argument position: %s"
                  (T.unpack n)
                  err
              Right bodyArg ->
                elaborateTypeArg' tenv env (n : visiting) $
                  substTypeInTypeArg (zip params ts) bodyArg

substTypeInTyp :: [(Text, Ast.TypeArg)] -> Ast.Typ -> Ast.Typ
substTypeInTyp subst = \case
  Ast.TFlat n -> Ast.TFlat n
  Ast.TNil -> Ast.TNil
  Ast.TArray t -> Ast.TArray $ substTypeInTyp subst t
  Ast.TParen t -> Ast.TParen $ substTypeInTyp subst t
  Ast.TPair l r -> Ast.TPair (substTypeInTyp subst l) (substTypeInTyp subst r)
  Ast.TFunct (Ast.Funct i o fxs) ->
    Ast.TFunct $ Ast.Funct
      (substTypeInTyp subst i)
      (substTypeInTyp subst o)
      (substTypeInEffRow subst fxs)
  Ast.TRecord (Ast.RecordTyp props) ->
    Ast.TRecord $ Ast.RecordTyp $
      map (\(Ast.RecordTypProp q n t) ->
        Ast.RecordTypProp q n (substTypeInTyp subst t)) props
  Ast.TForall (Ast.TypeParams ts) es t ->
    let subst' = filter (\(name, _) -> name `notElem` ts) subst
    in Ast.TForall (Ast.TypeParams ts) es (substTypeInTyp subst' t)
  Ast.TVar v ->
    case lookup v subst of
      Just arg -> typeArgToTyp arg
      Nothing -> Ast.TVar v
  Ast.TGenericAlias n apps ->
    Ast.TGenericAlias n $ substTypeApps subst apps

substTypeInEffRow :: [(Text, Ast.TypeArg)] -> Ast.EffRow -> Ast.EffRow
substTypeInEffRow subst = \case
  Ast.ERSugar entries t -> Ast.ERSugar (substTypeInEffRowEntry subst <$> entries) t
  r -> r

substTypeInEffRowEntry :: [(Text, Ast.TypeArg)] -> Ast.EffRowEntry -> Ast.EffRowEntry
substTypeInEffRowEntry subst = \case
  Ast.EREEffCons eff -> Ast.EREEffCons $ substTypeInEffCons subst eff
  Ast.EREEffRow row -> Ast.EREEffRow $ substTypeInEffRow subst row

substTypeInEffCons :: [(Text, Ast.TypeArg)] -> Ast.EffCons -> Ast.EffCons
substTypeInEffCons subst = \case
  Ast.EffCons (Ast.ECons n mts) -> Ast.EffCons $ Ast.ECons n $ substTypeApps subst <$> mts
  v@(Ast.EVar _) -> v

substTypeApps :: [(Text, Ast.TypeArg)] -> Ast.TypeApps -> Ast.TypeApps
substTypeApps subst (Ast.TypeApps ts) = Ast.TypeApps $ substTypeInTypeArg subst <$> ts

substTypeInTypeArg :: [(Text, Ast.TypeArg)] -> Ast.TypeArg -> Ast.TypeArg
substTypeInTypeArg subst = \case
  Ast.TAFlat n -> Ast.TAFlat n
  Ast.TANil -> Ast.TANil
  Ast.TAArray t -> Ast.TAArray $ substTypeInTypeArg subst t
  Ast.TAParen t -> Ast.TAParen $ substTypeInTypeArg subst t
  Ast.TAPair l r -> Ast.TAPair (substTypeInTypeArg subst l) (substTypeInTypeArg subst r)
  Ast.TAFunct i o -> Ast.TAFunct (substTypeInTypeArg subst i) (substTypeInTypeArg subst o)
  Ast.TARecord (Ast.RecordTypeArg props) ->
    Ast.TARecord $ Ast.RecordTypeArg $
      map (\(Ast.RecordTypeArgProp q n t) ->
        Ast.RecordTypeArgProp q n (substTypeInTypeArg subst t)) props
  Ast.TAMeta v ->
    case lookup v subst of
      Just arg -> arg
      Nothing -> Ast.TAMeta v
  Ast.TAGenericAlias n apps ->
    Ast.TAGenericAlias n $ substTypeApps subst apps

typeArgToTyp :: Ast.TypeArg -> Ast.Typ
typeArgToTyp = \case
  Ast.TAFlat n -> Ast.TFlat n
  Ast.TANil -> Ast.TNil
  Ast.TAArray t -> Ast.TArray $ typeArgToTyp t
  Ast.TAParen t -> Ast.TParen $ typeArgToTyp t
  Ast.TAPair l r -> Ast.TPair (typeArgToTyp l) $ typeArgToTyp r
  Ast.TAFunct i o -> Ast.TFunct $ Ast.Funct (typeArgToTyp i) (typeArgToTyp o) (Ast.ERSugar [] Nothing)
  Ast.TARecord (Ast.RecordTypeArg props) ->
    Ast.TRecord $ Ast.RecordTyp $
      map (\(Ast.RecordTypeArgProp q n t) -> Ast.RecordTypProp q n (typeArgToTyp t)) props
  Ast.TAMeta t -> Ast.TVar t
  Ast.TAGenericAlias n apps -> Ast.TGenericAlias n apps

typToTypeArg :: Ast.Typ -> Either String Ast.TypeArg
typToTypeArg = \case
  Ast.TFlat n -> Right $ Ast.TAFlat n
  Ast.TNil -> Right Ast.TANil
  Ast.TArray t -> Ast.TAArray <$> typToTypeArg t
  Ast.TParen t -> Ast.TAParen <$> typToTypeArg t
  Ast.TPair l r -> Ast.TAPair <$> typToTypeArg l <*> typToTypeArg r
  Ast.TFunct (Ast.Funct i o (Ast.ERSugar [] Nothing)) ->
    Ast.TAFunct <$> typToTypeArg i <*> typToTypeArg o
  Ast.TFunct Ast.Funct{} ->
    Left "Effectful function types are not allowed in type arguments"
  Ast.TRecord (Ast.RecordTyp props) ->
    Ast.TARecord . Ast.RecordTypeArg <$>
      traverse (\(Ast.RecordTypProp q n t) -> Ast.RecordTypeArgProp q n <$> typToTypeArg t) props
  Ast.TForall {} ->
    Left "Forall types are not allowed in type arguments"
  Ast.TVar t -> pure $ Ast.TAMeta t
  Ast.TGenericAlias n ts -> pure $ Ast.TAGenericAlias n ts

elaborateMutability :: Ast.ConstantQualifier -> Types.Mutability
elaborateMutability = \case
  Ast.Val -> Types.Val
  Ast.Var -> Types.Var
  Ast.Imm -> Types.Imm

elaborateEffRow :: RowEnv -> TypEnv -> Ast.EffRow -> ElabM Types.EffRow
elaborateEffRow renv tenv = elaborateEffRow' renv tenv emptyEnv

elaborateEffRow' :: RowEnv -> TypEnv -> ElabEnv -> Ast.EffRow -> ElabM Types.EffRow
elaborateEffRow' renv tenv env row = do
  FlatRow cons t <- flattenEffRow renv tenv env [] row
  pure $ case t of
    Just v -> Types.ROpen (uniqPreserveOrder cons) v
    _ -> Types.RClosed (uniqPreserveOrder cons)

flattenEffRow :: RowEnv -> TypEnv -> ElabEnv -> [String] -> Ast.EffRow -> ElabM FlatRow
flattenEffRow renv tenv env visiting = \case
  Ast.ERAlias n ->
    let name = T.unpack n
    in if name `elem` visiting then
      error $ "Cyclic row alias: " <> name
    else
      case lookup name renv of
        Nothing -> error $ "Unknown row alias: " <> name
        Just row -> flattenEffRow renv tenv env (name : visiting) row
  Ast.ERSugar entries Nothing -> do
    foldM (\acc entry ->
        mergeFlatRows acc =<< flattenEffRowEntry renv tenv env visiting entry
      ) emptyFlatRow entries
  Ast.ERSugar entries (Just t) -> do
    fromEntries <- foldM (\acc entry -> do
        mergeFlatRows acc =<< flattenEffRowEntry renv tenv env visiting entry
      ) emptyFlatRow entries
    mergeFlatRows fromEntries . FlatRow [] . Just =<< getBoundOrMakeMeta rowBounds iRowVars env t
      -- case lookupRow env t of
      --   Just t' -> pure $ FlatRow [] $ Just t'
      --   _ -> case lookupIRow env t of
      --     Just t' -> pure $ FlatRow [] $ Just t'
      --     _ -> do
      --       meta <- freshMeta t
      --       let _ = extendIRow [(t, meta)] env
      --       pure $ FlatRow [] $ Just meta
  Ast.ERVar n -> FlatRow [] . Just <$> getBoundOrMakeMeta rowBounds iRowVars env n --do
    -- case lookupRow env n of
    --   Just n' -> pure $ FlatRow [] $ Just n'
    --   _ -> case lookupIRow env n of
    --     Just n' -> pure $ FlatRow [] $ Just n'
    --     _ -> do
    --       meta <- freshMeta n
    --       let _ = extendIRow [(n, meta)] env
    --       pure $ FlatRow [] $ Just meta

flattenEffRowEntry :: RowEnv -> TypEnv -> ElabEnv -> [String] -> Ast.EffRowEntry -> ElabM FlatRow
flattenEffRowEntry renv tenv env visiting = \case
  Ast.EREEffCons c -> do
    c' <- elaborateEffCons tenv env c
    pure $ FlatRow [c'] Nothing
  Ast.EREEffRow r -> flattenEffRow renv tenv env visiting r

emptyFlatRow :: FlatRow
emptyFlatRow = FlatRow [] Nothing

mergeFlatRows :: FlatRow -> FlatRow -> ElabM FlatRow
mergeFlatRows (FlatRow cons1 t1) (FlatRow cons2 t2) =
  case (t1, t2) of
    (Nothing, Nothing) -> pure $ FlatRow (cons1 <> cons2) Nothing
    (Just t, Nothing) -> pure $ FlatRow (cons1 <> cons2) (Just t)
    (Nothing, Just t) -> pure $ FlatRow (cons1 <> cons2) (Just t)
    (Just _, Just _) -> error "Multiple effect row tails in one row"

elaborateEffCons :: TypEnv -> ElabEnv -> Ast.EffCons -> ElabM Types.EffCons
elaborateEffCons tenv env = \case
  Ast.EffCons (Ast.ECons n apps) ->
    Types.EffCons . Types.ECons n <$> maybe (pure []) (mapM (elaborateTypeArg tenv env) . coerce) apps
  Ast.EVar n -> Types.EVar <$> getBoundOrMakeMeta rowBounds iRowVars env n
    -- case lookupEff env n of
    --   Just n' -> pure $ Types.EVar n'
    --   _ -> case lookupIEff env n of
    --     Just n' -> pure $ Types.EVar n'
    --     _ -> do
    --       meta <- freshMeta n
    --       let _ = extendIEff [(n, meta)] env
    --       pure $ Types.EVar meta