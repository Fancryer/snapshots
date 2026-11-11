{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
module Infer (
  isTypeMonomorphic,
  countResumeInBlock,
  countResumeInStat,
  countResumeInExpr,
  countResumeInLambda,
  inferExpr,
  inferStat,
  inferBlock,
  inferChunk,
  freezeMutability,
  freeze,
  freezeTyp,
  freezeBlock,
  freezeLambda,
  freezeRowMutIn,
  isFrozenExpr,
  isFrozenBlock,
  instantiateTypeScheme,
  generalize,
  typeOfTypedExprUnsafe,
  InferResult(..)
) where
import Types(
    Typ(..),
    Funct(Funct),
    EffRow(..),
    TypeArg(..),
    Block,
    Stat(..),
    Expr(..),
    Handler(..),
    Lambda,
    Lambda(..),
    Taste(..),
    Mutability(..),
    tasteName,
    EffCons(..),
    TypeScheme,
    Scheme(..),
    NativeLambdaSign(..),
    handlerCons,

    HandlerSig(HandlerSig),
    ERecordProp(..),
    TRecordProp(..),
    LetPattern(..),
    TRecordProp(..),
    LetPattern(LPParam),
    LambdaParam(LambdaParam),
    AtomLetPattern(ALPNil, ALPUnderscore, ALPPair, ALPRecord),
    LetPatternRecordProp(LetPatternRecordProp),
    Chunk,
    TopLevelStat(..),
    effName,
    FunctDecl(..),
    pureTFunc, tfunc, ECons (..), countArgs, monoScheme
  )
import qualified Data.Map as Map
import qualified Data.Set as Set
import Record (taTypeArg, eExp)
import Resume (ResumeInfo(..))
import Unify (
    TypeCheckM,
    TypeCheckError(..),
    unifyTypes,
    applyTypeSubst,
    freshMetaTypeM,
    unifyEffRows,
    freshMetaM,
    removeConsFromRow,
    retTypeOf,
    applyEffRowSubst,
    withNewLevel,
    currentLevel, subsumesEffRow, errorStack, throwTypeCheckError, withErrorStack, applyEffConsSubst, addEffLacks, addRowLacks, addRowLacksToRow
  )
import qualified Eff
import qualified Scope
import Control.Monad.Except (MonadError(throwError))
import Control.Monad (foldM, when, forM)
import Scope (enterScope)
import Utils (uniqPreserveOrder, mapFst, Pretty (pretty), mapSnd)
import qualified Data.Text as T
import Data.List (sort, nub, find, nubBy)
import Text.Printf (printf)
import Data.Maybe (isNothing, fromMaybe, catMaybes)
import TypedIR (
    Scope(..),
    TypedExpr(..),
    Block,
    Lambda(..),
    TERecordProp(..),
    Stat(..),
    Handler(..),
    typeOfTypedExpr,
    typeOfTypedBlock,
    Chunk,
    TopLevelStat(..),
    FunctDecl(..), HandlerClause
  )
import Data.Text (Text)
import Control.Lens (use, (^.))
import Eff (rowHasEffect)
import Control.Monad.IO.Class (liftIO)
import Debug.Trace (trace)
import ErrorContext (withFrame, IrFrame (IrFrame), ErrorFrame (..))
import Data.Set (Set)

data InferResult a = InferResult {
    irResult :: a,
    irRow :: EffRow,
    irScope :: Scope
  } deriving Show

type InferM a = TypeCheckM (InferResult a)

isTypeMonomorphic :: Scope -> Typ -> Bool
isTypeMonomorphic scope = \case
  TForall{} -> False
  TVar v -> maybe False (isTypeMonomorphic scope) $ Map.lookup v $ typeSubst scope
  TArray t -> isTypeMonomorphic scope t
  TPair l r -> isTypeMonomorphic scope l && isTypeMonomorphic scope r
  TFunct (Funct i o fxs) -> all (isTypeMonomorphic scope) [i, o] && isEffRowMonomorphic scope fxs
  TRecord props -> all (isTypeMonomorphic scope . tTyp) props
  _ -> True

isTypeArgMonomorphic :: Scope -> TypeArg -> Bool
isTypeArgMonomorphic scope = \case
  TAVar v -> maybe False (isTypeArgMonomorphic scope) $ Map.lookup v $ typeArgSubst scope
  TAArray t -> isTypeArgMonomorphic scope t
  TAPair l r -> isTypeArgMonomorphic scope l && isTypeArgMonomorphic scope r
  TAFunct i o -> isTypeArgMonomorphic scope i && isTypeArgMonomorphic scope o
  TARecord props -> all (isTypeArgMonomorphic scope . taTypeArg) props
  _ -> True

isEffConsMonomorphic :: Scope -> EffCons -> Bool
isEffConsMonomorphic scope = \case
  EVar e -> maybe False (isEffConsMonomorphic scope) $ Map.lookup e $ effSubst scope
  EffCons (ECons _ ts) -> isTypeArgMonomorphic scope `all` ts

isEffRowMonomorphic :: Scope -> EffRow -> Bool
isEffRowMonomorphic scope = \case
  RClosed cons -> isEffConsMonomorphic scope `all` cons
  ROpen cons t -> isEffConsMonomorphic scope `all` cons && isEffRowMonomorphic scope (RVar t)
  RVar _ -> True

substituteTypedExpr :: Scope -> TypedExpr -> TypeCheckM TypedExpr
substituteTypedExpr scope = \case
  TEInt i -> pure $ TEInt i
  TEFloat f -> pure $ TEFloat f
  TEBoolean b -> pure $ TEBoolean b
  TEString s -> pure $ TEString s
  TENil -> pure TENil
  TEXVar v t -> TEXVar v <$> applyTypeSubst scope t
  TEArray t es -> do
    t' <- applyTypeSubst scope t
    es' <- mapM (substituteTypedExpr scope) es
    pure $ TEArray t' es'
  TEPair l r -> TEPair <$> substituteTypedExpr scope l <*> substituteTypedExpr scope r
  TEXLambda lam -> do
    argT' <- applyTypeSubst scope lam.lArgT
    retT' <- applyTypeSubst scope lam.lRetT
    fxs' <- applyEffRowSubst scope lam.lFxs
    block' <- substituteBlock scope lam.lBlock
    pure $ TEXLambda (lam {TypedIR.lArgT = argT', TypedIR.lRetT = retT', TypedIR.lFxs = fxs', TypedIR.lBlock = block'})
  TEApply f x -> TEApply <$> substituteTypedExpr scope f <*> substituteTypedExpr scope x
  TERecord m props -> do
    m' <- mapM (substituteTypedExpr scope) m
    props' <- mapM (substituteRecordProp scope) props
    pure $ TERecord m' props'
  TEParen block -> TEParen <$> substituteBlock scope block
  TEResume e t -> TEResume <$> substituteTypedExpr scope e <*> applyTypeSubst scope t
  TELet pat bound body -> do
    bound' <- substituteTypedExpr scope bound
    body' <- substituteTypedExpr scope body
    pure $ TELet pat bound' body'
  TEPropAccess e f -> TEPropAccess <$> substituteTypedExpr scope e <*> pure f
  TEIfElse p t f -> TEIfElse <$> substituteTypedExpr scope p <*> substituteTypedExpr scope t <*> substituteTypedExpr scope f
  TEHandle handler t -> do
    t' <- applyTypeSubst scope t
    handler' <- substituteHandler scope handler
    pure $ TEHandle handler' t'
  TENLambda (NativeLambdaSign n i o r) ->
    TENLambda <$> (NativeLambdaSign n
      <$> applyTypeSubst scope i
      <*> applyTypeSubst scope o
      <*> applyEffRowSubst scope r)

substituteRecordProp :: Scope -> TERecordProp -> TypeCheckM TERecordProp
substituteRecordProp scope (TERecordProp mut name t e) = do
  t' <- applyTypeSubst scope t
  e' <- substituteTypedExpr scope e
  pure $ TERecordProp mut name t' e'

substituteBlock :: Scope -> TypedIR.Block -> TypeCheckM TypedIR.Block
substituteBlock scope (stats, expr) = do
  stats' <- mapM (substituteStat scope) stats
  expr' <- substituteTypedExpr scope expr
  pure (stats', expr')

substituteStat :: Scope -> TypedIR.Stat -> TypeCheckM TypedIR.Stat
substituteStat scope = \case
  TypedIR.Bind mut n e -> TypedIR.Bind mut n <$> substituteTypedExpr scope e
  TypedIR.Rebind n e -> TypedIR.Rebind n <$> substituteTypedExpr scope e
  TypedIR.Expr e -> TypedIR.Expr <$> substituteTypedExpr scope e

substituteHandler :: Scope -> TypedIR.Handler -> TypeCheckM TypedIR.Handler
substituteHandler scope = \case
  TypedIR.Handler eff block clauses mThen -> do
    eff' <- applyEffConsSubst scope (EffCons eff)
    case eff' of
      EVar e -> throwTypeCheckError $
        EffectError $ "Handler cannot handle effect variable `" <> tasteName e <> "`"
      EffCons e@ECons{} -> do
        block' <- substituteBlock scope block
        clauses' <-
          mapM
            (\(name, lam, r, i) ->
              (name, , r, i) <$> substituteLambda scope lam
            )
            clauses
        then' <- substituteLambda scope mThen
        pure $ TypedIR.Handler e block' clauses' then'

substituteLambda :: Scope -> TypedIR.Lambda -> TypeCheckM TypedIR.Lambda
substituteLambda scope lam = do
  argT' <- applyTypeSubst scope lam.lArgT
  retT' <- applyTypeSubst scope lam.lRetT
  fxs' <- applyEffRowSubst scope lam.lFxs
  block' <- substituteBlock scope lam.lBlock
  pure $ lam {TypedIR.lArgT = argT', TypedIR.lRetT = retT', TypedIR.lFxs = fxs', TypedIR.lBlock = block'}

countResumeInBlock :: Types.Block -> ResumeInfo
countResumeInBlock (stats, e) =
  foldl (\acc stat -> acc <> countResumeInStat stat) NoResume (stats <> [Types.Expr e])

countResumeInStat :: Types.Stat -> ResumeInfo
countResumeInStat = \case
  Types.Expr e -> countResumeInExpr e
  Types.Assign _ e -> countResumeInExpr e
  Types.Bind _ _ _ e -> countResumeInExpr e

countResumeInExpr :: Expr -> ResumeInfo
countResumeInExpr = \case
  Array es -> foldl (<>) NoResume $ map countResumeInExpr es
  Pair l r -> countResumeInExpr l <> countResumeInExpr r
  XLambda l -> countResumeInLambda l
  Apply f x -> countResumeInExpr f <> countResumeInExpr x
  With e _ _ _ -> countResumeInExpr e
  Handle (Types.Handler _ block' cs then_) ->
    countResumeInBlock block'
    <> foldl (<>) NoResume (map (countResumeInBlock . Types.lBlock . snd) cs)
    <> countResumeInLambda then_
  Resume e -> OneResume <> countResumeInExpr e
  Record e props ->
    foldl (<>) (maybe NoResume countResumeInExpr e) $ map (countResumeInExpr . eExp) props
  Paren b -> countResumeInBlock b
  Let _ wht whr -> countResumeInExpr wht <> countResumeInExpr whr
  PropAccess e _ -> countResumeInExpr e
  IfElse p t f -> countResumeInExpr p <> countResumeInExpr t <> countResumeInExpr f
  _ -> NoResume

countResumeInLambda :: Types.Lambda -> ResumeInfo
countResumeInLambda l = countResumeInBlock l.lBlock

substituteType :: Scope -> Taste -> TypeArg -> Scope
substituteType scope taste typ = scope {typeArgSubst = Map.insert taste typ scope.typeArgSubst}

substituteEffRow :: Scope -> Taste -> EffRow -> Scope
substituteEffRow scope taste eff = scope {rowSubst = Map.insert taste eff scope.rowSubst}

substituteEffCons :: Scope -> Taste -> EffCons -> Scope
substituteEffCons scope taste eff = scope {effSubst = Map.insert taste eff scope.effSubst}

buildCurried :: [Typ] -> Maybe EffRow -> Typ -> Typ
buildCurried []     fxs ret = TFunct $ Funct TNil ret $ fromMaybe (RClosed []) fxs
buildCurried [a]    fxs ret = TFunct $ Funct a ret $ fromMaybe (RClosed []) fxs
buildCurried (a:as) fxs ret = tfunc a $ buildCurried as fxs ret

-- | Тип выражения с предварительной подстановкой решений унификации.
--   typeOfTypedExpr чистая и не знает подстановок: без этого вызов функции,
--   результат которой ещё метапеременная (apply + 3 2), даёт "Apply of non-function".
typeOfTypedExprIn :: Scope -> TypedExpr -> TypeCheckM Typ
typeOfTypedExprIn scope e = substituteTypedExpr scope e >>= typeOfTypedExprUnsafe

typeOfTypedBlockIn :: Scope -> TypedIR.Block -> TypeCheckM Typ
typeOfTypedBlockIn scope b = substituteBlock scope b >>= typeOfTypedBlockUnsafe

typeOfTypedExprUnsafe :: TypedExpr -> TypeCheckM Typ
typeOfTypedExprUnsafe e = do
  case typeOfTypedExpr e of
    Left l -> throwTypeCheckError $ TypeError l
    Right r -> pure r

typeOfTypedBlockUnsafe :: TypedIR.Block -> TypeCheckM Typ
typeOfTypedBlockUnsafe b = do
  case typeOfTypedBlock b of
    Left l -> throwTypeCheckError $ TypeError l
    Right r -> pure r

-- most important
inferChunk :: [Text] -> Types.Chunk -> TypeCheckM TypedIR.Chunk
inferChunk args chunk = do
  globalScope <- Scope.globalScope args
  eStack <- use errorStack
  let _ = withFrame (EFIr $ IrFrame "" Nothing) eStack $ \stack ->
        stack
  -- Первый проход: регистрируем только эффекты и функции (с предварительными схемами)
  (scope1, funSigs) <- foldM (\(sc, sigs) stat -> case stat of
      Types.SEffDef effDef -> do
        when (Scope.hasEff False sc (effName effDef)) $
          throwTypeCheckError $ TypeError $ "Duplicate effect definition: " <> effName effDef
        sc' <- Scope.addEffect effDef sc
        pure (sc', sigs)

      Types.SFunctDef functDecl -> do
        let (retFxs, retTyp) = functDecl.fRet
            argTypes = map snd functDecl.fArgs
            -- fullTyp = buildCurried argTypes retFxs retTyp
            -- tvars = map (`Bound` 0) functDecl.fTvars
            -- evars = map (`Bound` 0) functDecl.fEvars
            -- rvars = map (`Bound` 0) functDecl.fRvars
            -- scheme = Scheme tvars evars rvars fullTyp
        let fullTyp = buildCurried argTypes retFxs retTyp
        let allTvars = collectTvarsFromType [] fullTyp
        let allEvars = collectEvarsFromType [] fullTyp
        let allRvars = collectRvarsFromType [] fullTyp

        -- Превращаем все собранные переменные в параметры схемы (Bound)
        -- Но мы должны сохранить явные параметры, если они есть, и объединить с неявными, убрав дубликаты.
        let explicitTvars = map (`Bound` 0) functDecl.fTvars
        let explicitEvars = map (`Bound` 0) functDecl.fEvars
        let explicitRvars = map (`Bound` 0) functDecl.fRvars

        -- Убираем дубликаты по идентификатору
        let tvars = uniqPreserveOrder $ explicitTvars <> allTvars
        let evars = uniqPreserveOrder $ explicitEvars <> allEvars
        let rvars = uniqPreserveOrder $ explicitRvars <> allRvars

        let scheme =
              Scheme tvars evars rvars Map.empty Map.empty fullTyp

        when (Scope.hasBinding False sc functDecl.fName) $
          throwTypeCheckError $ TypeError $ "Duplicate function definition: " <> functDecl.fName

        sc' <- Scope.addBinding functDecl.fName scheme (XVar functDecl.fName) Val sc
        pure (sc', sigs <> [(functDecl, retFxs, retTyp)])

      _ -> pure (sc, sigs)
    ) (globalScope, []) chunk

  -- Второй проход: типизируем тела функций и обновляем схемы
  (scope2, typedFuns) <- foldM (\(sc, acc) (functDecl, retFxs, retTyp) -> do
      let funScope = enterScope sc
      scopeWithArgs <- foldM (\sc' (argName, argTyp) ->
          Scope.addBinding argName (monoScheme argTyp) (XVar argName) Val sc'
        ) funScope functDecl.fArgs

      InferResult typedBlock blockFxs finalScope <- inferBlock scopeWithArgs functDecl.fBlock
      blockTyp <- typeOfTypedBlockIn finalScope typedBlock

      -- Унифицируем тип результата
      scopeUnified <- unifyTypes finalScope blockTyp retTyp

      -- Унифицируем эффекты
      let actualFxs = blockFxs
          expectedFxs = fromMaybe (RClosed []) retFxs
      scopeUnified' <- subsumesEffRow scopeUnified actualFxs expectedFxs

            -- Строим окончательный тип функции.
      -- Сначала применяем все подстановки к аргументам и результату.
      finalArgTypes <-
        mapM (applyTypeSubst scopeUnified' . snd) functDecl.fArgs

      finalRetTyp <-
        applyTypeSubst scopeUnified' retTyp

      finalRetFxs <-
        traverse (applyEffRowSubst scopeUnified') retFxs

      let fullTypFinal =
            buildCurried finalArgTypes finalRetFxs finalRetTyp

      fullTypFinal' <-
        applyTypeSubst scopeUnified' fullTypFinal

      -- Собираем свободные переменные.
      let implicitTvars = collectTvarsFromType (map (`Bound` 0) functDecl.fTvars) fullTypFinal'
          implicitEvars = collectEvarsFromType (map (`Bound` 0) functDecl.fEvars) fullTypFinal'
          implicitRvars = collectRvarsFromType (map (`Bound` 0) functDecl.fRvars) fullTypFinal'

          tvars = uniqPreserveOrder $ map (`Bound` 0) functDecl.fTvars <> implicitTvars
          evars = uniqPreserveOrder $ map (`Bound` 0) functDecl.fEvars <> implicitEvars
          rvars = uniqPreserveOrder $ map (`Bound` 0) functDecl.fRvars <> implicitRvars

          finalRowLacks = Map.filterWithKey (\k _ -> k `elem` rvars) (rowLacks scopeUnified')
          finalEffLacks = Map.filterWithKey (\k _ -> k `elem` evars) (effLacks scopeUnified')

          finalScheme =
            Scheme tvars evars rvars
              finalRowLacks
              finalEffLacks
              fullTypFinal'

          updatedValues = Map.insert functDecl.fName (finalScheme, XVar functDecl.fName, Val) (values sc)

          finalArgs = zip (map fst functDecl.fArgs) finalArgTypes

          typedFunctDecl =
            TypedIR.FunctDecl
              functDecl.fName
              functDecl.fTvars
              functDecl.fEvars
              finalArgs
              (finalRetFxs, finalRetTyp)
              typedBlock

      pure (sc {values = updatedValues}, acc <> [TypedIR.SFunctDef typedFunctDecl])
    ) (scope1, []) funSigs

  -- Собираем остальные топ-левел статы
  otherStats <- forM chunk $ \case
    Types.STypeDef name params typ -> pure $ Just $ TypedIR.STypeDef name params typ
    Types.SEffDef effDef -> pure $ Just $ TypedIR.SEffDef effDef
    Types.SRowDef rowDef -> pure $ Just $ TypedIR.SRowDef rowDef
    Types.SFunctDef _ -> pure Nothing

  pure $ catMaybes (otherStats <> map Just typedFuns)

wrapTypedExprWithCell :: TypedExpr -> EffRow -> EffRow
wrapTypedExprWithCell e r =
  if createsCell e then Eff.appendEff r $ EffCons $ ECons "Cell" [] else r

wrapInferResultWithCell :: InferResult TypedExpr -> InferM TypedExpr
wrapInferResultWithCell (InferResult res fxs scope) =
  pure $ InferResult res (wrapTypedExprWithCell res fxs) scope

inferExpr :: Scope -> Expr -> InferM TypedExpr
inferExpr scope expr = withErrorStack (EFIr $ IrFrame (pretty expr) Nothing) $ case expr of
  Int i -> pure $ InferResult (TEInt i) Eff.empty scope
  Float f -> pure $ InferResult (TEFloat f) Eff.empty scope
  Boolean b -> pure  $ InferResult (TEBoolean b) Eff.empty scope
  String s -> pure  $ InferResult (TEString s) Eff.empty scope
  Nil -> pure  $ InferResult TENil Eff.empty scope
  XVar v -> do
    (bindingT, scope', mut) <- case Scope.findBinding True scope v of
      Nothing -> throwTypeCheckError $ UndefinedVariable v
      Just (scheme, _, mut') -> do
        (t, sc) <- instantiateTypeScheme scope scheme
        pure (t, sc, mut')
    let finalFxs = if mut == Var then Eff.closedOfFlat "Read" else Eff.empty
    pure  $ InferResult (TEXVar v bindingT) finalFxs scope'
  Array [] -> pure $ InferResult (TEArray TNothing []) Eff.empty scope
  Array (x:xs) -> do
    -- Типизируем первый элемент
    InferResult hEntry fxs scope1 <- inferExpr scope x
    hType <- typeOfTypedExprUnsafe hEntry

    -- Типизируем остальные элементы и одновременно унифицируем типы
    (typedEntries, finalFxs, finalScope) <- foldM
      (\(accEntries, accFxs, sc) ae -> do
        InferResult tEntry tFxs sc' <- inferExpr sc ae
        tEntryTyp <- typeOfTypedExprUnsafe tEntry
        sc'' <- unifyTypes sc' hType tEntryTyp
        pure (accEntries <> [tEntry], Eff.unionEffRows accFxs tFxs, sc''))
      ([hEntry], fxs, scope1)
      xs
    wrapInferResultWithCell $ InferResult (TEArray hType typedEntries) finalFxs finalScope
  Pair l r -> do
    InferResult l' lRow scope' <- inferExpr scope l
    InferResult r' rRow scope'' <- inferExpr scope' r
    let pair = TEPair l' r'
    pure $
      InferResult
        pair
        (wrapTypedExprWithCell pair $ Eff.unionEffRows lRow rRow)
        scope''
  XLambda lam -> do
    InferResult lam' fxs scope' <- inferLambda scope lam
    wrapInferResultWithCell $ InferResult (TEXLambda lam') fxs scope'
  Apply callee arg -> do
    InferResult calleeT calleeFxs calleeScope <- inferExpr scope callee
    calleeT' <- typeOfTypedExprIn calleeScope calleeT
    expectedFromT <- freshMetaTypeM
    expectedToT <- freshMetaTypeM
    expectedCalleeT <- TFunct . Funct expectedFromT expectedToT . ROpen [] <$> freshMetaM
    scope' <- unifyTypes calleeScope calleeT' expectedCalleeT
    InferResult argT argFxs argScope <- inferExpr scope' arg
    argT' <- typeOfTypedExprIn argScope argT
    scope'' <- unifyTypes argScope argT' expectedFromT

    -- Эффект вызова (T-App): латентный ряд callee ПОСЛЕ унификации
    -- берётся собственный ряд callee (а не ожидаемый: унификация открытых рядов
    -- привязывает хвост ожидаемого к разности и теряет эффекты)
    calleeResolved <- applyTypeSubst scope'' calleeT'
    resultRow <- case calleeResolved of
      TFunct (Funct _ _ row) -> applyEffRowSubst scope'' row
      _ -> throwTypeCheckError $ TypeError "Apply: callee must be a function"

    -- Объединяем все эффекты: вычисление callee, вычисление arg, и эффект из типа функции
    let finalFxs = Eff.unionEffRowsList [argFxs, resultRow, calleeFxs]

    wrapInferResultWithCell $ InferResult (TEApply calleeT argT) finalFxs scope''
  NLambda n@(NativeLambdaSign{}) -> wrapInferResultWithCell $
    InferResult
      (TENLambda n)
      Eff.empty
      scope
  With expr ts es rs -> do
    InferResult exprExpr exprFxs exprScope <- inferExpr scope expr

    typeOfTypedExprUnsafe exprExpr >>= \case
      TForall tvars evars rvars effLacks rowLacks _ -> do
        let typesLength = length ts
            tvarsLength = length tvars
            fxsLength = length es
            evarsLength = length evars
            rowsLength = length rs
            rvarsLength = length rvars

        when (typesLength /= tvarsLength) $
          throwTypeCheckError $ TypeError $ T.pack $
            printf "Wrong type args amount in with: expected %d, given %d" tvarsLength typesLength

        when (fxsLength /= evarsLength) $
          throwTypeCheckError $ TypeError $ T.pack $
            printf "Wrong effect args amount in with: expected %d, given %d" evarsLength fxsLength

        when (rowsLength /= rvarsLength) $
          throwTypeCheckError $ TypeError $ T.pack $
            printf "Wrong row args amount in with: expected %d, given %d" rvarsLength rowsLength

        let scope1 = enterScope exprScope

        -- Переносим ограничения на аргументы эффектов.
        scope2 <- foldM
          (\sc (evar, fxArg) ->
            maybe (pure sc)
              (addRowLacksToRow sc (RClosed [fxArg]))
              (Map.lookup evar effLacks))
          scope1
          (zip evars es)

        -- Переносим ограничения на аргументы строк эффектов.
        scope3 <- foldM
          (\sc (rvar, rowArg) ->
            maybe (pure sc)
              (addRowLacksToRow sc rowArg)
              (Map.lookup rvar rowLacks))
          scope2
          (zip rvars rs)

        let scope4 = foldl (\sc (tvar, typArg) -> substituteType sc tvar typArg) scope3 (zip tvars ts)
            scope5 = foldl (\sc (evar, fxArg) -> substituteEffCons sc evar fxArg) scope4 (zip evars es)
            scope6 = foldl (\sc (rvar, rowArg) -> substituteEffRow sc rvar rowArg) scope5 (zip rvars rs)

        exprExpr' <- substituteTypedExpr scope6 exprExpr
        row <- applyEffRowSubst scope6 exprFxs

        wrapInferResultWithCell $
          InferResult exprExpr' row scope6

      t -> throwTypeCheckError $ TypeError $ T.concat
        ["with: expression type `", T.pack $ show t, "` is not forall"]
  Handle handler -> inferHandler scope handler
  Record a ps -> inferRecord scope a ps
  Paren b -> do
    InferResult b' fxs scope' <- inferBlock scope b
    wrapInferResultWithCell $ InferResult (TypedIR.TEParen b') fxs scope'
  Resume expr ->
    case Scope.findBinding True scope "resume" of
      Nothing -> throwTypeCheckError $ EffectError "Resume used outside of a handler clause!"
      Just (resumeTypScheme, _, _) -> do
        (resumeTyp, scope') <- instantiateTypeScheme scope resumeTypScheme
        case resumeTyp of
          TFunct (Funct expectedI expectedO expectedFxs) -> do
            InferResult argExpr argFxs argScope <- inferExpr scope' expr
            argT <- typeOfTypedExprUnsafe argExpr
            scope'' <- unifyTypes argScope argT expectedI
            wrapInferResultWithCell $
              InferResult
                (TEResume argExpr expectedO)
                (Eff.unionEffRows argFxs expectedFxs)
                scope''
          _ -> throwTypeCheckError $ EffectError "Invalid resume binding: not a function"
  Let lp wht whr -> do
    -- 1. Сначала типизируем RHS в исходном Scope.
    InferResult whtT whtFxs scope1 <- inferExpr scope wht
    -- 2. Получаем тип вычисленного выражения.
    whT' <- typeOfTypedExprIn scope1 whtT
    -- 3. Создаём bindings из паттерна.
    (lpT, scope2) <- inferLetPattern scope1 lp
    -- 4. Проверяем соответствие типа паттерна типу RHS.
    scope3 <- unifyTypes scope2 lpT whT'
    -- 5. Типизируем тело с уже доступными bindings.
    InferResult whrT whrFxs scope4 <- inferExpr scope3 whr
    wrapInferResultWithCell $
      InferResult
        (TypedIR.TELet lp whtT whrT)
        (Eff.unionEffRows whtFxs whrFxs)
        scope4
  PropAccess e n -> do
    InferResult t fxs scope' <- inferExpr scope e
    -- T-Prop: чтение изменяемого поля (var) даёт Read
    let readIf m = if m == Var then Eff.closedOfFlat "Read" else Eff.empty
    case t of
      TERecord _ props ->
        case find (\(TERecordProp _ n' _ _) -> n == n') props of
          Just (TERecordProp mutP _ _ e') ->
            wrapInferResultWithCell $ InferResult e' (Eff.unionEffRows fxs (readIf mutP)) scope'
          Nothing -> throwTypeCheckError $ TypeError $ "Record doesn't have binding '" <> n <> "'"
      _ -> do
        recT <- typeOfTypedExprUnsafe t
        case recT of
          TRecord rprops ->
            case find ((n ==) . tName) rprops of
              Just rp ->
                wrapInferResultWithCell $
                  InferResult (TEPropAccess t n) (Eff.unionEffRows fxs (readIf (tMut rp))) scope'
              Nothing -> throwTypeCheckError $ TypeError $ "Record doesn't have binding '" <> n <> "'"
          _ ->
            throwTypeCheckError $ TypeError $ T.pack
            $ printf "Cannot access property '%s' of expression: expected record, got: %s" n $ pretty recT
  IfElse p t f -> do
    InferResult typP pFxs pScope <- inferExpr scope p
    typP' <- typeOfTypedExprIn pScope typP
    scope' <- unifyTypes pScope TBoolean typP'
    InferResult typT tFxs tScope <- inferExpr scope' t
    InferResult typF fFxs fScope <- inferExpr tScope f
    typT' <- typeOfTypedExprIn fScope typT
    typF' <- typeOfTypedExprIn fScope typF
    iScope <- unifyTypes fScope typT' typF'
    wrapInferResultWithCell $ InferResult
      (TEIfElse typP typT typF)
      (Eff.unionEffRows pFxs $ Eff.unionEffRows tFxs fFxs)
      iScope

inferLetPattern :: Scope -> LetPattern -> TypeCheckM (Typ, Scope)
inferLetPattern scope = \case
  LPParam (LambdaParam name t) -> do
    t' <- maybe freshMetaTypeM pure t
    scope' <- Scope.addBinding name (monoScheme t') (XVar name) Val scope
    pure (t', scope')

  LPATom a ->
    case a of
      ALPNil -> pure (TNil, scope)
      ALPUnderscore -> (, scope) <$> freshMetaTypeM
      ALPPair l r -> do
        (l', scope') <- inferLetPattern scope l
        (r', scope'') <- inferLetPattern scope' r
        pure (TPair l' r', scope'')
      ALPRecord props -> do
        (recordProps, scope') <- foldM inferProp ([], scope) props
        pure (TRecord recordProps, scope')
        where
          inferProp :: ([TRecordProp], Scope) -> LetPatternRecordProp -> TypeCheckM ([TRecordProp], Scope)
          inferProp (accProps, scope') (LetPatternRecordProp m (LambdaParam name t) alp) = do
            t' <- maybe freshMetaTypeM pure t
            -- Имя свойства становится доступным в текущем Scope.
            scope'' <- Scope.addBinding name (monoScheme t') (XVar name) m scope'
            -- При наличии вложенного паттерна проверяем его
            -- совместимость с типом свойства.
            scope''' <-
              case alp of
                Nothing -> pure scope''
                Just nested -> do
                  (nestedT, nestedScope) <- inferLetPattern scope'' (LPATom nested)
                  unifyTypes nestedScope t' nestedT

            pure (accProps <> [TRecordProp m name t'], scope''')

inferRecord :: Scope -> Maybe Expr -> [ERecordProp] -> InferM TypedExpr
inferRecord scope Nothing props = withNewLevel $ do
  (recProps, finalFxs, finalScope) <- foldM
    (\(accProps, accFxs, sc) (ERecordProp mut name typOpt expr) -> do
      InferResult exprT exprFxs sc' <- inferExpr sc expr
      exprT' <- typeOfTypedExprUnsafe exprT
      (propT, sc'') <- case typOpt of
        Just annot -> (annot, ) <$> unifyTypes sc' exprT' annot
        Nothing -> pure (exprT', sc')
      pure (accProps <> [TERecordProp mut name propT exprT], Eff.unionEffRows accFxs exprFxs, sc'')
    ) ([], Eff.empty, scope) props
  wrapInferResultWithCell $ InferResult (TERecord Nothing recProps) finalFxs finalScope

inferRecord scope (Just anchor) props = withNewLevel $ do
  InferResult anchorExpr anchorFxs scope1 <- inferExpr scope anchor
  anchorTyp <- typeOfTypedExprUnsafe anchorExpr
  case anchorTyp of
    TRecord baseProps -> do
      -- Накапливаем TERecordProp в отдельном аккумуляторе
      (recProps, propFxs, finalScope) <- foldM
        (\(accProps, accFxs, sc) (ERecordProp mut name typOpt expr) -> do
          InferResult exprExpr exprFxs sc' <- inferExpr sc expr
          exprTyp <- typeOfTypedExprUnsafe exprExpr
          (propT, sc'') <- case typOpt of
            Just annot -> (annot,) <$> unifyTypes sc' exprTyp annot
            Nothing -> pure (exprTyp, sc')
          -- Проверяем мутабельность и существование поля в скоупе
          case find ((name ==) . tName) baseProps of
            Just (TRecordProp baseMut _ _) ->
              if baseMut /= mut then
                throwTypeCheckError $ TypeError $ T.pack
                $ printf "Cannot change mutability of field '%s' from %s to %s" name baseMut mut
              else do
                -- Удаляем старое TERecordProp с таким же именем, если есть
                let accProps' = filter (\(TERecordProp _ n _ _) -> n /= name) accProps
                pure (
                    accProps' <> [TERecordProp mut name propT exprExpr],
                    Eff.unionEffRows accFxs exprFxs,
                    sc''
                  )
            Nothing ->
              -- Новое поле
              pure (accProps <> [TERecordProp mut name propT exprExpr], Eff.unionEffRows accFxs exprFxs, sc'')
        ) ([], anchorFxs, scope1) props
      wrapInferResultWithCell $ InferResult (TERecord (Just anchorExpr) recProps) propFxs finalScope
    _ -> throwTypeCheckError $ TypeError "Record anchor must be a record type"

inferHandler :: Scope -> Types.Handler -> InferM TypedExpr
inferHandler scope handler = withNewLevel $
  -- 1. Получаем сигнатуру эффекта
  case handlerCons handler of
    EVar v ->
      throwTypeCheckError $
        TypeError $
          T.concat ["Cannot use effect variable `", tasteName v, "` as handler cons"]
    eff@(EffCons eff'@(ECons n _)) -> do
      ops <- case Scope.findEffOps True scope n of
        Nothing -> throwTypeCheckError $ TypeError $ "Effect '" <> n <> "' is not presented in this scope"
        Just ops -> pure ops
      let opNames = map fst ops
      -- 2. Создаём подскоуп с операциями
      let blockScope = enterScope scope

      scope' <-
        foldM
          (\sc (name, typ) -> do
            opT <- generalize sc $ TFunct typ
            Scope.addBinding name opT (XVar name) Val sc
          )
          blockScope
          ops

      -- 3. Типизируем блок — операции видимы
      (blockStatements, blockExpr, blockFxs, blockScope') <-
        case handler of
          Types.Handler _ block _ _ -> do
            InferResult (stats, expr) fxs sc <- inferBlock scope' block
            pure (stats, expr, fxs, sc)

      blockT' <- typeOfTypedExprUnsafe blockExpr

      -- 4. Проверяем и типизируем handler clauses
      let handlerRow = Unify.removeConsFromRow eff blockFxs

      case handler of
        Types.Handler _ _ clauses _then -> do

          -- Проверяем дубликаты по именам операций,
          -- а не по полному содержимому HandlerClause.
          let clauseNames = map fst clauses
              missing = filter (`notElem` clauseNames) opNames
              extra = filter (`notElem` opNames) clauseNames

          when (length clauseNames /= length (nub clauseNames)) $
            throwTypeCheckError $ TypeError "Duplicate handler clause names"

          when (missing /= []) $
            throwTypeCheckError $
              TypeError $ "Handler missing operations: " <> T.intercalate ", " missing

          when (extra /= []) $
            throwTypeCheckError $
              TypeError $ "Handler defines unknown operations: " <> T.intercalate ", " extra

          -- Обрабатываем операции в порядке их объявления,
          -- но находим соответствующую clause по имени.
          (typedClauses, finalScope) <-
            foldM
              (\(acc, sc) (name, opTyp) ->
                case find ((== name) . fst) clauses of
                  Nothing -> throwTypeCheckError $ TypeError $ "Handler missing operation: " <> name

                  Just (_, lam) -> do

                    -- opTyp = тип операции, например Int -> Int -> Int
                    -- Разворачиваем его до формы TFunct $ Funct args ret fxs
                    let opTyp' = TFunct opTyp

                        replaceRetWithBlockT :: Scope -> Typ -> TypeCheckM (Typ, Scope)
                        replaceRetWithBlockT sc' typ =
                          case typ of
                            TFunct (Funct i o fxs) -> do
                              (o', sc''') <-
                                replaceRetWithBlockT sc' o

                              pure (TFunct $ Funct i o' fxs, sc''')

                            _ ->
                              pure (blockT', sc')

                    (opTypForClause, opScopeForClause) <-
                      replaceRetWithBlockT sc opTyp'

                    case countResumeInLambda lam of

                      MultipleResume m -> throwTypeCheckError $ MultipleResumeError name m

                      OneResume -> do
                        -- Добавляем resume: retT -> blockT
                        let clauseScope = enterScope opScopeForClause
                        sc1 <- Scope.addHandler (HandlerSig eff ops) clauseScope
                        r' <-
                          case retTypeOf opTyp' of
                            Just r -> pure r
                            Nothing -> throwTypeCheckError $ TypeError "Cannot happen"

                        t <- generalize sc1 $ TFunct $ Funct r' blockT' handlerRow
                        sc2 <- Scope.addBinding "resume" t (XVar "resume") Val sc1
                        -- Типизируем lambda, где resume уже известен
                        InferResult typedLambda lamFxs sc3 <- inferLambda sc2 lam

                        let lamFunct = Funct typedLambda.lArgT typedLambda.lRetT typedLambda.lFxs

                            lamTyp = TFunct lamFunct

                        -- Проверяем совместимость с типом операции
                        sc4 <- unifyTypes sc3 lamTyp opTypForClause

                        sc5 <- unifyEffRows sc4 lamFxs handlerRow

                        pure (acc <> [(name, typedLambda, OneResume, countArgs lamFunct)], sc5)

                      NoResume -> do
                        -- Типизируем lambda без resume
                        let clauseScope = enterScope opScopeForClause

                        InferResult typedLam lamFxs sc1 <-
                          inferLambda clauseScope lam

                        let lamFunct = Funct typedLam.lArgT typedLam.lRetT typedLam.lFxs
                            lamTyp = TFunct lamFunct
                        -- Проверяем совместимость с типом операции
                        sc2 <- unifyTypes sc1 lamTyp opTypForClause
                        sc3 <- unifyEffRows sc2 lamFxs handlerRow
                        pure (acc <> [(name, typedLam, NoResume, countArgs lamFunct)], sc3)
              )
              ([], blockScope')
              ops

          -- 5. Типизируем then
          InferResult typedThen thenFxs thenScope <-
            inferLambda finalScope _then

          let finalHandlerRow =
                Eff.unionEffRows handlerRow thenFxs

              typedHandler =
                TypedIR.Handler
                  eff'
                  (blockStatements, blockExpr)
                  typedClauses
                  typedThen

          wrapInferResultWithCell $
            InferResult
              (TypedIR.TEHandle typedHandler blockT')
              finalHandlerRow
              thenScope

inferLambda :: Scope -> Types.Lambda -> InferM TypedIR.Lambda
inferLambda scope lam = withNewLevel $ do
  let scope1 = enterScope scope
  argT' <- maybe freshMetaTypeM pure lam.lArgT
  scope2 <- Scope.addBinding lam.lArg (monoScheme argT') (XVar lam.lArg) Val scope1
  retT' <- maybe freshMetaTypeM pure lam.lRetT
  InferResult blockT blockFxs0 scope3 <- inferBlock scope2 lam.lBlock
  -- модель (T-Lam): упоминание переменной, несущей состояние, попадает в латентный ряд
  men <- mentionRow scope3 (Set.delete lam.lArg (fvTypedBlock blockT))
  let blockFxs = Eff.unionEffRows blockFxs0 men
  blockT' <- typeOfTypedBlockIn scope3 blockT
  scope4 <- unifyTypes scope3 retT' blockT'

  rowFxs <- if lam.lFxs == RClosed [] then ROpen [] <$> freshMetaM else pure lam.lFxs

  -- Затем применяем подстановки
  scope5 <- unifyEffRows scope4 rowFxs blockFxs
  fxs'' <- applyEffRowSubst scope5 rowFxs

  argT'' <- applyTypeSubst scope5 argT'
  retT'' <- applyTypeSubst scope5 retT'

  pure $ InferResult
    (TypedIR.Lambda
      lam.lTvars
      lam.lEvars
      lam.lArg
      argT''
      retT''
      fxs''
      blockT)
    Eff.empty
    -- модель: лямбда открывает область, выход из неё сохраняет только подстановки
    (Scope.keepSubst scope5 scope)

instantiateTypeScheme :: Scope -> TypeScheme -> TypeCheckM (Typ, Scope)
instantiateTypeScheme scope scheme = do
  let tvars = _ts scheme
      evars = _es scheme
      rvars = _rs scheme
      els = _effLacks scheme
      rls = _rowLacks scheme
      typ = _a scheme

  freshTypes <- mapM (const freshMetaM) tvars
  freshEffects <- mapM (const freshMetaM) evars
  freshRows <- mapM (const freshMetaM) rvars

  let typeMapping = Map.fromList [(tv, TVar mv) | (tv, mv) <- zip tvars freshTypes]
      effMapping = Map.fromList [(ev, EVar mv) | (ev, mv) <- zip evars freshEffects]
      rowMapping = Map.fromList [(rv, RVar mv) | (rv, mv) <- zip rvars freshRows]

      scope' = scope {
        typeSubst = Map.union typeMapping scope.typeSubst,
        effSubst = Map.union effMapping scope.effSubst,
        rowSubst = Map.union rowMapping scope.rowSubst
      }

  scope'' <- foldM
    (\sc (old, new) ->
      case Map.lookup old (_rowLacks scheme) of
        Nothing -> pure sc
        Just forbidden -> addRowLacks sc new forbidden)
    scope'
    (zip rvars freshRows)

  scope''' <- foldM
    (\sc (old, new) ->
      case Map.lookup old (_effLacks scheme) of
        Nothing -> pure sc
        Just forbidden -> addEffLacks sc new forbidden)
    scope''
    (zip evars freshEffects)

  typ' <- applyTypeSubst scope''' typ

  pure (typ', scope''')

inferBlock :: Scope -> Types.Block -> InferM TypedIR.Block
inferBlock outer (stats, expr) = withNewLevel $ do
  -- модель (E-Block): блок открывает область видимости;
  -- привязки блока не видны снаружи, подстановки сохраняются
  let scope = enterScope outer
  (scopeAfterStats, statFxs, stats') <- foldM (\(sc, accFxs, accStats) stat -> do
      InferResult stat' fxs sc' <- inferStat sc stat
      pure (sc', Eff.unionEffRows accFxs fxs, accStats <> [stat'])
    ) (scope, Eff.empty, []) stats
  InferResult exprT exprFxs scope' <- inferExpr scopeAfterStats expr
  -- модель (T-Block): Cell, если локальный var достижим из результата блока (состояние
  -- уходит наружу, например в замыкании); иначе Var, если var есть; иначе ничего
  exprTyp <- typeOfTypedExprIn scope' exprT
  let varNames = [n | TypedIR.Bind Var n _ <- stats']
      escapes = canHoldState exprTyp && any (`Set.member` reachNames stats' exprT) varNames
      phi
        | null varNames = Eff.empty
        | escapes = Eff.closedOfFlat "Cell"
        | otherwise = Eff.closedOfFlat "Var"
  pure $ InferResult
    (stats', exprT)
    (Eff.unionEffRows phi $ Eff.unionEffRows statFxs exprFxs)
    (Scope.keepSubst scope' outer)

inferStat :: Scope -> Types.Stat -> InferM TypedIR.Stat
inferStat scope = \case
  Types.Expr e -> do
    InferResult e' fxs scope' <- inferExpr scope e
    pure $ InferResult
      (TypedIR.Expr e')
      fxs
      scope'
  Types.Bind m n typOpt e -> do
    when (Scope.hasBinding False scope n) $
      throwTypeCheckError $ SameScopeBindingShadowing n

    -- 1. Infer expr
    InferResult inferredTypedExpr inferredFxs scope1 <- inferExpr scope e
    inferredTyp <- typeOfTypedExprUnsafe inferredTypedExpr

    -- 2. Prepare binding
    (exprForBinding, typForBinding, fxsForBinding, scope2) <-
      case m of
        Imm -> do
          let frozenExpr = freeze inferredTypedExpr

          -- Freeze the inferred type, including latent function effects.
          inferredTyp' <- applyTypeSubst scope1 inferredTyp
          (scope', frozenTyp) <- freezeTyp scope1 inferredTyp'

          -- Remove explicit mutation effects and constrain the remaining
          -- effect variables and row tails.
          inferredFxs' <- applyEffRowSubst scope' inferredFxs
          (scope'', frozenFxs) <- freezeRowMutIn scope' inferredFxs'

          -- The snapshot itself reads the state of captured variables.
          men <- mentionRow scope'' (fvTyped inferredTypedExpr)
          pure (frozenExpr, frozenTyp, Eff.unionEffRows frozenFxs men, scope'')
        _ -> pure (inferredTypedExpr, inferredTyp, inferredFxs, scope1)

    -- 3. Handle annotation
    (expectedTyp, schemeForScope, scope3) <-
      case typOpt of
        Just anno -> do
          let scheme = monoScheme anno
          (annoInst, scope') <- instantiateTypeScheme scope2 scheme
          scope'' <- unifyTypes scope' typForBinding annoInst
          (annoInst, , scope'') <$> generalize scope'' anno

        Nothing -> do
          typForBinding' <- applyTypeSubst scope2 typForBinding
          pure (typForBinding', monoScheme typForBinding', scope2)

    -- 4. Unification
    scope4 <-
      if isNothing typOpt
        then unifyTypes scope3 typForBinding expectedTyp
        else pure scope3

    -- 5. Generalize (only for val/imm)
    finalScheme <-
      if m /= Var
        then generalize scope4 schemeForScope._a
        else pure schemeForScope

    -- 6. Add binding to Scope
    scope5 <- Scope.addBinding n finalScheme (XVar n) m scope4

    -- 7. Final effects
    let finalFxs = fxsForBinding

    pure $
      InferResult
        (TypedIR.Bind m n exprForBinding)
        finalFxs
        scope5
  Types.Assign n e -> do
    (scheme, _, mut) <- case Scope.findBinding True scope n of
      Nothing -> throwTypeCheckError $ UndefinedVariable n
      Just found -> pure found
    when (mut /= Var) $ throwTypeCheckError $ ImmutableVariableAssignment n
    (varT, scope') <- instantiateTypeScheme scope scheme
    InferResult eT eFxs scope'' <- inferExpr scope' e
    let finalFxs = Eff.unionEffRows eFxs $ Eff.closedOfFlat "Rebind"
    eT' <- typeOfTypedExprUnsafe eT
    InferResult (TypedIR.Rebind n eT) finalFxs <$> unifyTypes scope'' varT eT'

generalize :: Scope -> Typ -> TypeCheckM TypeScheme
generalize scope typ = do
  currentLevel' <- use currentLevel

  -- Сначала полностью разрешаем подстановки.
  typ' <- applyTypeSubst scope typ

  let isGeneralizable (Meta _ _ lvl) = lvl > currentLevel' || lvl == -1
      isGeneralizable _ = False

      allTvars = collectTvarsFromType [] typ'
      allEvars = collectEvarsFromType [] typ'
      allRvars = collectRvarsFromType [] typ'

      tvars = filter isGeneralizable allTvars
      evars = filter isGeneralizable allEvars
      rvars = filter isGeneralizable allRvars

      nonGeneralizableTvars = filter (not . isGeneralizable) allTvars
      nonGeneralizableEvars = filter (not . isGeneralizable) allEvars
      nonGeneralizableRvars = filter (not . isGeneralizable) allRvars

      generalizedRows = Map.filterWithKey (\k _ -> k `elem` rvars) scope.rowLacks
      generalizedEffects = Map.filterWithKey (\k _ -> k `elem` evars) scope.effLacks

  when (any (/= []) [
      nonGeneralizableTvars,
      nonGeneralizableEvars,
      nonGeneralizableRvars
    ]) $
      throwTypeCheckError $ TypeError $
        "Cannot generalize: " <>
        T.pack (show (
          nonGeneralizableTvars,
          nonGeneralizableEvars,
          nonGeneralizableRvars
        ))

  pure Scheme {
    _ts = tvars,
    _es = evars,
    _rs = rvars,
    _rowLacks = generalizedRows,
    _effLacks = generalizedEffects,
    _a = typ'
  }

collectTvarsFromType :: [Taste] -> Typ -> [Taste]
collectTvarsFromType except typ =
  uniqPreserveOrder $ case typ of
    TArray t -> collectTvarsFromType except t
    TPair l r -> collectTvarsFromType except l <> collectTvarsFromType except r
    TFunct (Funct i o fxs) ->
      collectTvarsFromType except i
      <> collectTvarsFromType except o
      <> collectTvarsFromEffRow except fxs
    TForall vars _ _ els rls t -> collectTvarsFromType (uniqPreserveOrder $ vars <> except) t
    TRecord props ->
      concatMap (collectTvarsFromType except . tTyp) props
    TVar v -> ([v | v `notElem` except])
    _ -> []

collectTvarsFromTypeArg :: [Taste] -> TypeArg -> [Taste]
collectTvarsFromTypeArg except typ =
  uniqPreserveOrder $ case typ of
    TAArray t -> collectTvarsFromTypeArg except t
    TAPair l r -> collectTvarsFromTypeArg except l <> collectTvarsFromTypeArg except r
    TAFunct i o -> collectTvarsFromTypeArg except i <> collectTvarsFromTypeArg except o
    TARecord props -> concatMap (collectTvarsFromTypeArg except . taTypeArg) props
    TAVar v -> ([v | v `notElem` except])
    _ -> []

collectTvarsFromEffRow :: [Taste] -> EffRow -> [Taste]
collectTvarsFromEffRow except fx =
  uniqPreserveOrder $ case fx of
    RVar _ -> []
    RClosed cons -> concatMap (collectTvarsFromEffCons except) cons
    ROpen cons _ -> concatMap (collectTvarsFromEffCons except) cons

collectTvarsFromEffCons :: [Taste] -> EffCons -> [Taste]
collectTvarsFromEffCons except e =
  uniqPreserveOrder $ case e of
    EffCons (ECons _ ts) -> concatMap (collectTvarsFromTypeArg except) ts
    EVar _ -> []

collectEvarsFromType :: [Taste] -> Typ -> [Taste]
collectEvarsFromType except typ =
  uniqPreserveOrder $ case typ of
    TArray t -> collectEvarsFromType except t
    TPair l r -> collectEvarsFromType except l <> collectEvarsFromType except r
    TFunct (Funct i o fxs) -> collectEvarsFromType except i <> collectEvarsFromType except o <> collectEvarsFromEffRow except fxs
    TForall _ fxs _ els rls t -> collectEvarsFromType (uniqPreserveOrder $ fxs <> except) t
    TRecord props -> concatMap (collectEvarsFromType except . tTyp) props
    _ -> []

collectEvarsFromEffRow :: [Taste] -> EffRow -> [Taste]
collectEvarsFromEffRow except fx =
  uniqPreserveOrder $ case fx of
    RVar _ -> []
    RClosed cons -> concatMap (collectEvarsFromEffCons except) cons
    ROpen cons _ -> concatMap (collectEvarsFromEffCons except) cons

collectEvarsFromEffCons :: [Taste] -> EffCons -> [Taste]
collectEvarsFromEffCons except e =
  uniqPreserveOrder $ case e of
    EVar t -> [t | t `notElem` except]
    EffCons _ -> []

collectRvarsFromType :: [Taste] -> Typ -> [Taste]
collectRvarsFromType except typ =
  uniqPreserveOrder $ case typ of
    TArray t -> collectRvarsFromType except t
    TPair l r -> collectRvarsFromType except l <> collectRvarsFromType except r
    TFunct (Funct i o fxs) ->
      concatMap (collectRvarsFromType except) [i, o] <>
      collectRvarsFromEffRow except fxs
    TForall _ _ rows els rls t -> collectRvarsFromType (uniqPreserveOrder $ rows <> except) t
    TRecord props -> concatMap (collectRvarsFromType except . tTyp) props
    _ -> []

collectRvarsFromEffRow :: [Taste] -> EffRow -> [Taste]
collectRvarsFromEffRow except fx =
  uniqPreserveOrder $ case fx of
    RVar v -> [v | v `notElem` except]
    ROpen _ v -> [v | v `notElem` except]
    _ -> []

-- | Свободные переменные типизированного выражения (для анализа выхода состояния из блока).
--   Привязки let учитываются консервативно (не вычитаются).
-- | Тип несёт изменяемое состояние (модель: St_T): var-поле записи, латентный ряд стрелки
--   с Read/Rebind или хвост ряда, не обобщённый схемой (неизвестные эффекты).
--   У стрелки учитывается только её собственный ряд, а не тип результата: функция,
--   которая создаёт состояние (make), само состояние не держит.
bearsState :: [Taste] -> Typ -> Bool
bearsState quantified = go
  where
    go = \case
      TArray t -> go t
      TPair l r -> go l || go r
      TFunct (Funct _ _ row) -> rowUses row
      TRecord props -> any (\p -> tMut p == Var || go (tTyp p)) props
      -- переменная типа может быть конкретизирована типом, несущим состояние
      TVar _ -> True
      _ -> False
    rowUses = \case
      RClosed cs -> any isUse cs
      ROpen cs v -> any isUse cs || v `notElem` quantified
      RVar v -> v `notElem` quantified
    isUse = \case
      EffCons (ECons n _) -> n == "Read" || n == "Rebind"
      _ -> False

-- | Несёт ли переменная состояние (модель: St): var-привязка или тип, несущий состояние
varBearsState :: Scope -> Text -> TypeCheckM Bool
varBearsState scope n =
  case Scope.findBinding True scope n of
    Nothing -> pure False
    Just (Scheme _ _ rvs _ _ t, _, m) -> do
      t' <- applyTypeSubst scope t
      pure $ m == Var || bearsState rvs t'

-- | Выражение не создаёт и не меняет состояние: freeze на нём тождествен
--   (нет var-операторов, присваиваний и var-полей)
isFrozenExpr :: TypedExpr -> Bool
isFrozenExpr = \case
  TEArray _ es -> all isFrozenExpr es
  TEPair l r -> isFrozenExpr l && isFrozenExpr r
  TEXLambda lam -> isFrozenBlock lam.lBlock
  TEApply f x -> isFrozenExpr f && isFrozenExpr x
  TERecord me props ->
    maybe True isFrozenExpr me
      && all (\(TERecordProp m _ _ e) -> m /= Var && isFrozenExpr e) props
  TEHandle (TypedIR.Handler _ block clauses mlam) _ ->
    isFrozenBlock block && isFrozenBlock mlam.lBlock
      && all (\(_, l, _, _) -> isFrozenBlock l.lBlock) clauses
  TEParen b -> isFrozenBlock b
  TEResume e _ -> isFrozenExpr e
  TELet _ bound body -> isFrozenExpr bound && isFrozenExpr body
  TEPropAccess e _ -> isFrozenExpr e
  TEIfElse p t f -> isFrozenExpr p && isFrozenExpr t && isFrozenExpr f
  _ -> True

isFrozenBlock :: TypedIR.Block -> Bool
isFrozenBlock (stats, expr) = all stat stats && isFrozenExpr expr
  where
    stat = \case
      TypedIR.Bind m _ e -> m /= Var && isFrozenExpr e
      TypedIR.Rebind _ _ -> False
      TypedIR.Expr e -> isFrozenExpr e

-- | Упоминание (модель: Men): Read, если среди переменных есть несущая состояние.
--   Снимок такой переменной прочитал бы изменяемое состояние, даже если переменная
--   только упомянута и не используется.
mentionRow :: Scope -> Set.Set Text -> TypeCheckM EffRow
mentionRow scope names = do
  flags <- mapM (varBearsState scope) (Set.toList names)
  pure $ if or flags then Eff.closedOfFlat "Read" else Eff.empty

fvTyped :: TypedExpr -> Set.Set Text
fvTyped = \case
  TEXVar n _ -> Set.singleton n
  TEArray _ es -> Set.unions (map fvTyped es)
  TEPair l r -> Set.union (fvTyped l) (fvTyped r)
  TEXLambda lam -> Set.delete lam.lArg (fvTypedBlock lam.lBlock)
  TEApply f x -> Set.union (fvTyped f) (fvTyped x)
  TERecord me props ->
    Set.unions $ maybe [] (pure . fvTyped) me <> [fvTyped e | TERecordProp _ _ _ e <- props]
  TEHandle (TypedIR.Handler _ block clauses mlam) _ ->
    Set.unions $ [fvTypedBlock block, fvTypedBlock mlam.lBlock]
      <> map (\(_, l, _, _) -> fvTypedBlock l.lBlock) clauses
  TEParen b -> fvTypedBlock b
  TEResume e _ -> fvTyped e
  TELet _ bound body -> Set.union (fvTyped bound) (fvTyped body)
  TEPropAccess e _ -> fvTyped e
  TEIfElse p t f -> Set.unions [fvTyped p, fvTyped t, fvTyped f]
  _ -> Set.empty

fvTypedBlock :: TypedIR.Block -> Set.Set Text
fvTypedBlock (stats, expr) = go Set.empty stats
  where
    go bound [] = Set.difference (fvTyped expr) bound
    go bound (s : ss) =
      let (fvS, bound') = stat bound s
      in Set.union fvS (go bound' ss)
    stat bound = \case
      TypedIR.Bind _ n e -> (Set.difference (fvTyped e) bound, Set.insert n bound)
      TypedIR.Rebind n e -> (Set.difference (Set.insert n (fvTyped e)) bound, bound)
      TypedIR.Expr e -> (Set.difference (fvTyped e) bound, bound)

-- | Может ли значение этого типа держать изменяемое состояние (замыкание, запись,
--   структура с такими компонентами). Значения базовых типов состояния не держат,
--   поэтому из блока с результатом Int или () состояние наружу не уходит.
canHoldState :: Typ -> Bool
canHoldState = \case
  TInt -> False
  TFloat -> False
  TBoolean -> False
  TString -> False
  TNil -> False
  TNothing -> False
  TArray t -> canHoldState t
  TPair l r -> canHoldState l || canHoldState r
  _ -> True

-- | Имена, достижимые из результата блока (модель: reach): свободные переменные результата,
--   замкнутые относительно привязок и присваиваний блока.
reachNames :: [TypedIR.Stat] -> TypedExpr -> Set.Set Text
reachNames stats result = grow (fvTyped result)
  where
    grow acc =
      let acc' = foldl step acc stats
      in if acc' == acc then acc else grow acc'
    step acc = \case
      TypedIR.Bind m n e | m /= Imm, Set.member n acc -> Set.union acc (fvTyped e)
      TypedIR.Rebind n e | Set.member n acc -> Set.union acc (fvTyped e)
      _ -> acc

introducesLocalState :: TypedIR.Block -> Bool
introducesLocalState (stats, _) = any (\case TypedIR.Bind Var _ _ -> True; _ -> False) stats

createsCell :: TypedExpr -> Bool
createsCell = \case
  TEParen _ -> False  -- Var/Cell блока учитывает inferBlock (phi)
  TEArray _ es -> any createsCell es
  TEPair l r -> createsCell l || createsCell r
  TEXLambda _ -> False  -- латентный ряд тела несёт Var/Cell
  TERecord me props ->
    maybe False createsCell me ||
    any (\(TERecordProp m _ _ e) -> m == Var || createsCell e) props
  TEHandle _ _ -> False
  TEResume e _ -> createsCell e
  TELet _ wht whr -> any createsCell [wht, whr]
  TEIfElse p t f -> any createsCell [p, t, f]
  TEPropAccess e _ -> createsCell e
  _ -> False

handlerCreatesCell :: TypedIR.Handler -> Bool
handlerCreatesCell = \case
  TypedIR.Handler _ block clauses mlam ->
    introducesLocalState block ||
    any (\(_, l, _, _) -> introducesLocalState l.lBlock) clauses ||
    introducesLocalState mlam.lBlock

freeze :: TypedExpr -> TypedExpr
freeze = \case
  TEArray t es -> TEArray t $ map freeze es
  TEPair l r -> TEPair (freeze l) $ freeze r
  TEXLambda l -> TEXLambda l {TypedIR.lBlock = freezeBlock l.lBlock}
  TEApply c e -> TEApply (freeze c) $ freeze e
  TERecord a ps ->
    let a' = freeze <$> a
        mapTERecordProp :: TERecordProp -> TERecordProp
        mapTERecordProp p = p {terExpr = freeze p.terExpr, terMut = freezeMutability p.terMut}
        ps' = map mapTERecordProp ps
    in
    TERecord a' ps'
  TEHandle h t -> TEHandle (freezeHandler h) t
  TEParen b -> TEParen $ freezeBlock b
  TEResume e t -> TEResume (freeze e) t
  TELet lp wht whr -> TELet lp (freeze wht) (freeze whr)
  TEPropAccess t x -> TEPropAccess (freeze t) x
  TEIfElse p t f -> TEIfElse (freeze p) (freeze t) (freeze f)
  e -> e

-- | Заморозка типа: var-поля записей становятся val, из рядов стрелок убираются
--   Var, Read, Rebind, Cell (модель: freeze на типах)
freezeTyp :: Scope -> Typ -> TypeCheckM (Scope, Typ)
freezeTyp scope = \case
  TArray t -> do mapSnd TArray <$> freezeTyp scope t

  TPair l r -> do
    (scope', l') <- freezeTyp scope l
    mapSnd (TPair l') <$> freezeTyp scope' r

  TFunct (Funct i o fxs) -> do
    (scope', i') <- freezeTyp scope i
    (scope'', o') <- freezeTyp scope' o
    (scope''', fxs') <- freezeRowMutIn scope'' fxs
    pure (scope''', TFunct (Funct i' o' fxs'))

  TRecord props -> mapSnd TRecord <$> foldM freezeProp (scope, []) props

  TForall ts es rs els rls t -> do
    let scope' = scope {
      effLacks = foldr Map.delete scope.effLacks es,
      rowLacks = foldr Map.delete scope.rowLacks rs
    }
    (scope'', t') <- freezeTyp scope' t
    let els' = Map.unionWith Set.union els $ Map.restrictKeys scope''.effLacks (Set.fromList es)
        rls' = Map.unionWith Set.union rls $ Map.restrictKeys scope''.rowLacks (Set.fromList rs)
    pure (scope, TForall ts es rs els' rls' t')

  t -> pure (scope, t)
  where
    freezeProp (sc, acc) p = do
      (sc', typ') <- freezeTyp sc (tTyp p)
      pure (sc', acc <> [p {tMut = freezeMutability (tMut p), tTyp = typ'}])

freezeRowMut :: EffRow -> EffRow
freezeRowMut row = foldl (flip removeConsFromRow) row $ Set.map Eff.label mutationEffects

freezeRowMutIn :: Scope -> EffRow -> TypeCheckM (Scope, EffRow)
freezeRowMutIn scope row = do
  let frozenRow = foldl (flip removeConsFromRow) row $ map Eff.label (Set.toList mutationEffects)
  (, frozenRow) <$> addRowLacksToRow scope frozenRow mutationEffects

mutationEffects :: Set Text
mutationEffects = Set.fromList ["Read", "Var", "Rebind", "Cell"]

freezeMutability :: Mutability -> Mutability
freezeMutability = \case Var -> Val; m -> m

freezeBlock :: TypedIR.Block -> TypedIR.Block
freezeBlock (st, e) = (map freezeStat st, freeze e)

freezeStat :: TypedIR.Stat -> TypedIR.Stat
freezeStat = \case
  TypedIR.Bind m n t -> TypedIR.Bind (freezeMutability m) n $ freeze t
  TypedIR.Rebind _ t -> TypedIR.Expr $ freeze t
  TypedIR.Expr t -> TypedIR.Expr $ freeze t

freezeHandler :: TypedIR.Handler -> TypedIR.Handler
freezeHandler = \case
  TypedIR.Handler e b cs l ->
    TypedIR.Handler
      e
      (freezeBlock b)
      (map freezeHandlerClause cs)
      $ freezeLambda l

freezeHandlerClause :: TypedIR.HandlerClause -> TypedIR.HandlerClause
freezeHandlerClause (n, l, r, i) = (n, freezeLambda l, r, i)

freezeLambda :: TypedIR.Lambda -> TypedIR.Lambda
freezeLambda l = l {TypedIR.lBlock = freezeBlock l.lBlock}