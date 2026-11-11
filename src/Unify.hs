
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveFunctor #-}
module Unify (
  freshMetaM,
  freshSkolemM,
  freshBoundM,
  freshMetaTypeM, freshSkolemTypeM, freshBoundTypeM,
  freshMetaTypeArgM, freshSkolemTypeArgM, freshBoundTypeArgM,
  freshMetaEffM, freshSkolemEffM, freshBoundEffM,
  freshMetaRowM, freshSkolemRowM, freshBoundRowM,
  applyTypeSubst,
  applyTypeArgSubst,
  applyEffRowSubst,
  applyEffConsSubst,
  unifyTypes,
  unifyTypeArgs,
  subsumesEffRow,
  unifyEffCons,
  unifyEffRows,
  addRowLacks,
  addEffLacks,
  addEffLacksForArg,
  addRowLacksToRow,
  TypeCheckM,
  TypeCheckError(..),
  runTypeCheckM,
  evalTypeCheckM,
  execTypeCheckM,
  removeConsFromRow,
  retTypeOf,
  TypeCheckState(..),
  withNewLevel,
  withErrorStack,
  currentLevel,
  errorStack,
  throwTypeCheckError,
  bindRowVar,
  bindEffVar
) where

import Control.Monad.State (State)
import Types (
    Taste(..),
    Typ(..),
    EffRow(..),
    EffCons (..),
    TRecordProp(..),
    Funct(..),
    TypeArg(..),
    TARecordProp(TARecordProp), ECons (..), tasteName
  )
import qualified Data.Map as Map hiding (map)
import qualified Data.IntMap ()
import Data.List (find, nubBy, (\\), isSubsequenceOf)
import GHC.OldList (sort)
import Eff (unionEffRows)
import Occurs (typeOccursInType, typeOccursInTypeArg)
import Control.Monad (foldM, when)
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.State.Lazy (runState)
import Control.Monad.Error.Class (throwError)
import Record (taName, taMut, taTypeArg)
import Data.Bifunctor (bimap)
import Text.Printf (printf)
import qualified Data.Text as T
import Data.Text (Text)
import Control.Lens (makeLenses, use, Field1 (_1), Field2 (_2), Field3 (_3), (-=), (+=), (%=))
import TypedIR (Scope(..))
import Utils (Pretty(..))
import ErrorContext (ErrorStack, ErrorFrame)
import Data.Set (Set)
import qualified Data.Set as Set

data TypeCheckError =
  TypeError Text
  | TypeArgError Text
  | TypeUnificationError Typ Typ
  | TypeArgUnificationError TypeArg TypeArg
  | EffectRowsUnificationError Text EffRow EffRow
  | EffectConsUnificationError EffCons EffCons
  | UndefinedVariable Text
  | ImmutableVariableAssignment Text
  | SameScopeBindingShadowing Text
  | EffectError Text
  | MultipleResumeError Text Int
  | TodoError Text
  deriving (Show, Eq)

data TypeCheckState = TypeCheckState {
  _counter :: (Int, Int, Int),
  _currentLevel :: Int,
  _errorStack :: ErrorStack
}

makeLenses ''TypeCheckState

withNewLevel :: TypeCheckM a -> TypeCheckM a
withNewLevel action = do
  currentLevel += 1
  result <- action
  currentLevel -= 1
  pure result

withErrorStack :: ErrorFrame -> TypeCheckM a -> TypeCheckM a
withErrorStack frame action = do
  errorStack %= (frame :)
  action

type TypeCheckM a = ExceptT (ErrorStack, TypeCheckError) (State TypeCheckState) a

runTypeCheckM :: TypeCheckM a -> TypeCheckState -> (Either (ErrorStack, TypeCheckError) a, TypeCheckState)
runTypeCheckM comp = runState (runExceptT comp)

evalTypeCheckM :: TypeCheckM a -> TypeCheckState -> Either (ErrorStack, TypeCheckError) a
evalTypeCheckM comp = fst . runTypeCheckM comp

execTypeCheckM :: TypeCheckM a -> TypeCheckState -> TypeCheckState
execTypeCheckM comp = snd . runTypeCheckM comp

throwTypeCheckError :: TypeCheckError -> TypeCheckM a
throwTypeCheckError err = throwError . (, err) =<< use errorStack

freshMetaM, freshSkolemM, freshBoundM :: TypeCheckM Taste
freshMetaM = do
  counter . _1 += 1
  m <- use $ counter . _1
  Meta ("m" <> pretty m) m <$> use currentLevel

freshSkolemM = do
  counter . _2 += 1
  s <- use $ counter . _2
  Skolem ("s" <> pretty s) s <$> use currentLevel

freshBoundM = do
  counter . _3 += 1
  b <- use $ counter . _3
  -- Bound vars are rigid; they don't participate in level-lowering like metas do.
  pure $ Bound ("b" <> pretty b) b

freshMetaTypeM, freshSkolemTypeM, freshBoundTypeM :: TypeCheckM Typ
freshMetaTypeM = TVar <$> freshMetaM
freshSkolemTypeM = TVar <$> freshSkolemM
freshBoundTypeM = TVar <$> freshBoundM

freshMetaTypeArgM, freshSkolemTypeArgM, freshBoundTypeArgM :: TypeCheckM TypeArg
freshMetaTypeArgM = TAVar <$> freshMetaM
freshSkolemTypeArgM = TAVar <$> freshSkolemM
freshBoundTypeArgM = TAVar <$> freshBoundM

freshMetaEffM, freshSkolemEffM, freshBoundEffM :: TypeCheckM EffCons
freshMetaEffM = EVar <$> freshMetaM
freshSkolemEffM = EVar <$> freshSkolemM
freshBoundEffM = EVar <$> freshBoundM

freshMetaRowM, freshSkolemRowM, freshBoundRowM :: TypeCheckM EffRow
freshMetaRowM = RVar <$> freshMetaM
freshSkolemRowM = RVar <$> freshSkolemM
freshBoundRowM = RVar <$> freshBoundM

lowerTasteTo :: Int -> Taste -> Taste
lowerTasteTo target = \case
  Meta n i lvl | lvl > target -> Meta n i target
  t -> t

skolemEscapesType :: Int -> Typ -> Bool
skolemEscapesType target = \case
  TVar (Skolem _ _ lvl) -> lvl > target
  TArray t -> skolemEscapesType target t
  TPair l r -> skolemEscapesType target l || skolemEscapesType target r
  TFunct (Funct i o row) ->
    skolemEscapesType target i || skolemEscapesType target o || skolemEscapesRow target row
  TRecord props -> any (\(TRecordProp _ _ t) -> skolemEscapesType target t) props
  TForall _ _ _ _ _ t -> skolemEscapesType target t
  _ -> False

skolemEscapesTypeArg :: Int -> TypeArg -> Bool
skolemEscapesTypeArg target = \case
  TAVar (Skolem _ _ lvl) -> lvl > target
  TAArray t -> skolemEscapesTypeArg target t
  TAPair l r -> skolemEscapesTypeArg target l || skolemEscapesTypeArg target r
  TAFunct i o -> skolemEscapesTypeArg target i || skolemEscapesTypeArg target o
  TARecord props -> any (\(TARecordProp _ _ t) -> skolemEscapesTypeArg target t) props
  _ -> False

skolemEscapesEffCons :: Int -> EffCons -> Bool
skolemEscapesEffCons target = \case
  EffCons (ECons _ args) -> any (skolemEscapesTypeArg target) args
  EVar (Skolem _ _ lvl) -> lvl > target
  _ -> False

skolemEscapesRow :: Int -> EffRow -> Bool
skolemEscapesRow target = \case
  RClosed cs -> any (skolemEscapesEffCons target) cs
  ROpen cs t -> any (skolemEscapesEffCons target) cs || case t of
    Skolem _ _ lvl -> lvl > target
    _ -> False
  RVar t -> case t of
    Skolem _ _ lvl -> lvl > target
    _ -> False

lowerTypeTo :: Int -> Typ -> Typ
lowerTypeTo target = \case
  TVar t -> TVar $ lowerTasteTo target t
  TArray t -> TArray $ lowerTypeTo target t
  TPair l r -> TPair (lowerTypeTo target l) $ lowerTypeTo target r
  TFunct (Funct i o row) ->
    TFunct $ Funct (lowerTypeTo target i) (lowerTypeTo target o) $ lowerRowTo target row
  TRecord props ->
      TRecord [TRecordProp m n $ lowerTypeTo target t | TRecordProp m n t <- props]
  TForall ts es rs els rls t -> TForall ts es rs els rls $ lowerTypeTo target t
  t -> t

lowerTypeArgTo :: Int -> TypeArg -> TypeArg
lowerTypeArgTo target = \case
  TAVar t -> TAVar $ lowerTasteTo target t
  TAArray t -> TAArray $ lowerTypeArgTo target t
  TAPair l r -> TAPair (lowerTypeArgTo target l) $ lowerTypeArgTo target r
  TAFunct i o ->
    TAFunct (lowerTypeArgTo target i) $ lowerTypeArgTo target o
  TARecord props ->
      TARecord [TARecordProp m n $ lowerTypeArgTo target t | TARecordProp m n t <- props]
  t -> t

lowerEffConsTo :: Int -> EffCons -> EffCons
lowerEffConsTo target = \case
  EffCons (ECons n args) -> EffCons . ECons n $ map (lowerTypeArgTo target) args
  EVar t -> EVar $ lowerTasteTo target t

lowerRowTo :: Int -> EffRow -> EffRow
lowerRowTo target = \case
  RClosed cs -> RClosed $ map (lowerEffConsTo target) cs
  ROpen cs t -> ROpen (map (lowerEffConsTo target) cs) $ lowerTasteTo target t
  RVar t -> RVar $ lowerTasteTo target t

bindMetaType :: Scope -> Taste -> Typ -> TypeCheckM Scope
bindMetaType scope m@(Meta _ _ lvlM) t = do
  let t' = lowerTypeTo lvlM t
  if skolemEscapesType lvlM t' then throwTypeCheckError $ TypeError "Skolem escapes type"
  else
    pure scope{typeSubst = Map.insert m t' $ typeSubst scope}
bindMetaType _ s@Skolem{} _ = throwTypeCheckError $ TypeError "Cannot solve a skolem variable"
bindMetaType _ b@Bound{} _ =
  throwTypeCheckError $ TypeError $ "bindMetaType | Cannot solve a bound variable " <> tasteName b

bindMetaTypeArg :: Scope -> Taste -> TypeArg -> TypeCheckM Scope
bindMetaTypeArg scope m@(Meta _ _ lvlM) t = do
  let t' = lowerTypeArgTo lvlM t
  if skolemEscapesTypeArg lvlM t' then
    throwTypeCheckError $ TypeError "Skolem escapes type arg"
  else
    pure scope{typeArgSubst = Map.insert m t' $ typeArgSubst scope}
bindMetaTypeArg _ Skolem{} _ = throwTypeCheckError $ TypeError "Cannot solve a skolem variable"
bindMetaTypeArg _ b@Bound{} _ =
  throwTypeCheckError $ TypeError $ "bindMetaTypeArg | Cannot solve a bound variable " <> tasteName b

bindRowVar :: Scope -> Taste -> EffRow -> TypeCheckM Scope
bindRowVar scope m@(Meta _ _ lvlM) row = do
  let row' = lowerRowTo lvlM row

  resolved <- applyEffRowSubst scope row'

  case resolved of
    RVar n | n == m -> pure scope
    ROpen _ n | n == m ->
      throwTypeCheckError $
        TypeError "Occurs check: a row variable occurs in its own binding"

    _ -> do
      if skolemEscapesRow lvlM row' then
        throwTypeCheckError $ TypeError "Skolem escapes row"
      else do
        let forbidden = Map.findWithDefault Set.empty m scope.rowLacks
        scope' <- addRowLacksToRow scope resolved forbidden
        pure scope' {rowSubst = Map.insert m row' scope'.rowSubst}

bindRowVar _ s@Skolem{} _ =
  throwTypeCheckError $
    TypeError $ "Cannot solve a skolem variable " <> tasteName s

bindRowVar _ b@Bound{} _ =
  throwTypeCheckError $
    TypeError $ "Cannot solve a bound variable " <> tasteName b

bindEffVar :: Scope -> Taste -> EffCons -> TypeCheckM Scope
bindEffVar scope m@(Meta _ _ lvlM) e = do
  e' <- applyEffConsSubst scope e
  case e' of
    EVar n | n == m -> pure scope
    _ -> do
      let lowered = lowerEffConsTo lvlM e'
          forbidden = Map.findWithDefault Set.empty m scope.effLacks
      if skolemEscapesEffCons lvlM lowered then
        throwTypeCheckError $ TypeError "Skolem escapes eff cons"
      else do
        scope' <- case lowered of
          EVar n -> addEffLacks scope n forbidden
          EffCons (ECons name _) -> do
            checkEffectNameLacks forbidden name
            pure scope
        pure scope' {effSubst = Map.insert m lowered scope'.effSubst}

bindEffVar _ s@Skolem{} _ =
  throwTypeCheckError $
    TypeError $ "Cannot solve a skolem variable " <> tasteName s

bindEffVar _ b@Bound{} _ =
  throwTypeCheckError $
    TypeError $ "Cannot solve a bound variable " <> tasteName b

applyTypeSubst :: Scope -> Typ -> TypeCheckM Typ
applyTypeSubst scope = \case
  t@(TVar m) ->
    case Map.lookup m (typeSubst scope) of
      Just t' -> applyTypeSubst scope t'
      Nothing -> pure t
  TArray t -> TArray <$> applyTypeSubst scope t
  TPair l r -> TPair <$> applyTypeSubst scope l <*> applyTypeSubst scope r
  TFunct (Funct i o fxs) ->
    TFunct <$> (Funct <$> applyTypeSubst scope i <*> applyTypeSubst scope o <*> applyEffRowSubst scope fxs)
  TRecord props -> do
    props' <- traverse (\(TRecordProp mut name typ) ->
        TRecordProp mut name <$> applyTypeSubst scope typ
      ) props
    pure $ TRecord props'
  TForall ts es rs els rls t -> do
    let scope' = scope {
        typeSubst = foldr Map.delete scope.typeSubst ts,
        effSubst = foldr Map.delete scope.effSubst es,
        rowSubst = foldr Map.delete scope.rowSubst rs
      }
    TForall ts es rs els rls <$> applyTypeSubst scope' t
  t -> pure t

applyTypeArgSubst :: Scope -> TypeArg -> TypeCheckM TypeArg
applyTypeArgSubst scope = \case
  t@(TAVar m) -> case Map.lookup m (typeArgSubst scope) of
    Just t' -> applyTypeArgSubst scope t'
    Nothing -> pure t
  TAArray t -> TAArray <$> applyTypeArgSubst scope t
  TAPair l r -> TAPair <$> applyTypeArgSubst scope l <*> applyTypeArgSubst scope r
  TAFunct i o -> TAFunct <$> applyTypeArgSubst scope i <*> applyTypeArgSubst scope o
  TARecord props -> do
    props' <- traverse (\(TARecordProp mut name typ) ->
        TARecordProp mut name <$> applyTypeArgSubst scope typ
      ) props
    pure $ TARecord props'
  t -> pure t

unifyTypes :: Scope -> Typ -> Typ -> TypeCheckM Scope
unifyTypes scope t1 t2 = do
  t1' <- applyTypeSubst scope t1
  t2' <- applyTypeSubst scope t2
  case (t1', t2') of
    (TNothing, _); (TInt, TInt); (TFloat, TFloat);
      (TBoolean, TBoolean); (TString, TString); (TNil, TNil) ->
      pure scope
    (TVar x, TVar y) | x == y -> pure scope
    (TVar x@Meta{}, t) -> do
      t' <- applyTypeSubst scope t
      if typeOccursInType x t' then
        throwTypeCheckError $ TypeUnificationError t1' t'
      else
        bindMetaType scope x t'
    (TVar _, _) -> throwTypeCheckError $ TypeUnificationError t1' t2'
    (_, TVar _) -> unifyTypes scope t2' t1'
    (TFlat x, TFlat y) | x == y -> pure scope
    (TArray l1, TArray l2) -> unifyTypes scope l1 l2
    (TPair l1 r1, TPair l2 r2) -> do
      scope' <- unifyTypes scope l1 l2
      unifyTypes scope' r1 r2
    (TFunct (Funct i1 o1 e1), TFunct (Funct i2 o2 e2)) -> do
      scope' <- unifyTypes scope i2 i1
      scope'' <- unifyTypes scope' o1 o2
      unifyEffRows scope'' e1 e2
    (TRecord props1, TRecord props2) -> unifyRecords scope props1 props2
    _ -> throwTypeCheckError $ TypeUnificationError t1' t2'

unifyRecords :: Scope -> [TRecordProp] -> [TRecordProp] -> TypeCheckM Scope
unifyRecords scope props1 props2 = if length props1 /= length props2 then
  throwTypeCheckError $ TypeUnificationError (TRecord props1) (TRecord props2)
else
  let props1' = sort $ nubBy (\p1 p2 -> tName p1 == tName p2) props1 in
  let props2' = sort $ nubBy (\p1 p2 -> tName p1 == tName p2) props2 in
  if length props1 /= length props1' || length props2 /= length props2' then
    throwTypeCheckError $ TypeUnificationError (TRecord props1) (TRecord props2)
  else
    let zipped = zip props1' props2' in
    if any (\(p1, p2) -> tMut p1 /= tMut p2 || tName p1 /= tName p2) zipped then
      throwTypeCheckError $ TypeUnificationError (TRecord props1) (TRecord props2)
    else do
      foldM (
        \sc (typ1, typ2) -> do
          unifyTypes sc typ1 typ2
        ) scope (map (bimap tTyp tTyp) zipped)

applyEffRowSubst :: Scope -> EffRow -> TypeCheckM EffRow
applyEffRowSubst scope = \case
  r@(RVar m) -> case m of
    Meta{} ->
      case Map.lookup m (rowSubst scope) of
        Just r' -> applyEffRowSubst scope r'
        Nothing -> pure r
    Skolem{}; Bound{} -> pure r
  RClosed cs -> RClosed <$> traverse (applyEffConsSubst scope) cs
  ROpen cs t -> do
    cs' <- traverse (applyEffConsSubst scope) cs
    t' <- applyEffRowSubst scope $ RVar t
    pure $ unionEffRows (RClosed cs') t'

applyEffConsSubst :: Scope -> EffCons -> TypeCheckM EffCons
applyEffConsSubst scope = \case
  e@(EVar m) -> case m of
    Meta{} ->
      case Map.lookup m (effSubst scope) of
        Just e' -> applyEffConsSubst scope e'
        Nothing -> pure e
    Skolem{}; Bound{} -> pure e
  EffCons (ECons n args) -> EffCons . ECons n <$> traverse (applyTypeArgSubst scope) args

normalizeEffRow :: EffRow -> EffRow
normalizeEffRow = \case
  RClosed cs -> RClosed $ sort cs
  ROpen cs v -> ROpen (sort cs) v
  r -> r

subsumesEffRow :: Scope -> EffRow -> EffRow -> TypeCheckM Scope
subsumesEffRow scope r1 r2 = do
  r1' <- normalizeEffRow <$> applyEffRowSubst scope r1
  r2' <- normalizeEffRow <$> applyEffRowSubst scope r2
  case (r1', r2') of
    -- Закрытый vs закрытый
    (RClosed cs1, RClosed cs2) ->
      if cs1 `isSubsequenceOf` cs2
        then pure scope
        else throwTypeCheckError $ EffectRowsUnificationError
          (T.concat [
            "Effects of the body are not allowed by the declared row; missing in the declaration: [",
            T.intercalate ", " $ map pretty (cs1 \\ cs2), "]"])
          r1' r2'

    -- Закрытый фактический, открытый ожидаемый: лишние эффекты уходят в хвост
    (RClosed cs1, ROpen cs2 v) -> do
      let extra = cs1 \\ cs2
      if null extra
        then pure scope
        else do
          r <- freshMetaM
          bindRowVar scope v (ROpen extra r)

    -- Открытый фактический, закрытый ожидаемый
    (ROpen cs1 v1, RClosed cs2) -> do
      -- Если открытая часть пуста, хвост связывается со всем закрытым рядом
      if null cs1 then
        bindRowVar scope v1 (RClosed cs2)
      else do
        -- Проверяем, что все эффекты из открытой части есть в закрытом
        let isSubset = cs1 `isSubsequenceOf` cs2
        if not isSubset then
          throwTypeCheckError $ EffectRowsUnificationError
            "Open row has effects not present in closed row"
            (ROpen cs1 v1)
            (RClosed cs2)
        else
          -- Все эффекты уже есть в закрытом, хвост становится пустым
          bindRowVar scope v1 (RClosed [])

    -- Открытый vs открытый
    (ROpen cs1 v1, ROpen cs2 v2) -> unifyOpenOpen scope cs1 v1 cs2 v2

    -- Переменная ряда с чем-то
    (RVar v, row) -> bindRowVar scope v row
    (row, RVar v) -> bindRowVar scope v row

unifyEffRows :: Scope -> EffRow -> EffRow -> TypeCheckM Scope
unifyEffRows scope r1 r2 = do
  r1' <- normalizeEffRow <$> applyEffRowSubst scope r1
  r2' <- normalizeEffRow <$> applyEffRowSubst scope r2
  case (r1', r2') of
    (RClosed c1, RClosed c2) -> unifyClosedEffConsLists scope c1 c2
    (RClosed cl, ROpen op v) -> unifyClosedEffRowWithOpen scope cl op v
    (ROpen op v, RClosed cl) -> unifyOpenEffRowWithClosed scope op v cl
    (ROpen l1 v1, ROpen l2 v2) -> unifyOpenEffConsLists scope l1 v1 l2 v2

    (RVar e1, RVar e2) | e1 == e2 -> pure scope
    (RVar e, row) -> unifyRowVarWithEffRow scope e row
    (row, RVar e) -> unifyRowVarWithEffRow scope e row

unifyClosedEffConsLists :: Scope -> [EffCons] -> [EffCons] -> TypeCheckM Scope
unifyClosedEffConsLists scope l1 l2
  | length l1 /= length l2 =
    throwTypeCheckError $
      EffectRowsUnificationError
        (T.concat ["Closed eff cons lists lengths are unequal: ", pretty $ length l1, " != ", pretty $ length l2])
        (RClosed l1)
        (RClosed l2)
  | otherwise = foldM (\scope' (e1, e2) -> unifyEffCons scope' e1 e2) scope (zip l1 l2)

unifyOpenEffConsLists :: Scope -> [EffCons] -> Taste -> [EffCons] -> Taste -> TypeCheckM Scope
unifyOpenEffConsLists scope l1 v1 l2 v2 = do
  -- Унифицируем общие эффекты
  let commonEffects = filter (`elem` l2) l1
  scope' <- foldM (\sc cons1 ->
          case find (cons1 ==) l2 of
            Nothing -> throwTypeCheckError $ EffectConsUnificationError cons1 (error "Shall not happen")
            Just cons2 -> unifyEffCons sc cons1 cons2
        ) scope commonEffects
  unifyOpenOpen scope' l1 v1 l2 v2

-- | Ряд из явных эффектов и хвоста (пустой список эффектов даёт просто переменную)
mkOpenRow :: [EffCons] -> Taste -> EffRow
mkOpenRow [] t = RVar t
mkOpenRow cs t = ROpen cs t

-- | Унификация двух открытых рядов (по Реми): у обоих рядов общий свежий хвост r,
--   v1 := (l2 \ l1 | r), v2 := (l1 \ l2 | r). Хвост не теряется, поэтому
--   эффектная полиморфность функций высшего порядка сохраняется.
unifyOpenOpen :: Scope -> [EffCons] -> Taste -> [EffCons] -> Taste -> TypeCheckM Scope
unifyOpenOpen scope l1 v1 l2 v2
  | v1 == v2 =
      if null (l1 \\ l2) && null (l2 \\ l1)
        then pure scope
        else throwTypeCheckError $ EffectRowsUnificationError
          "Open rows with the same tail have different effects" (ROpen l1 v1) (ROpen l2 v2)
  | otherwise = do
      r <- freshMetaM
      scope1 <- bindRowVar scope v1 (mkOpenRow (l2 \\ l1) r)
      bindRowVar scope1 v2 (mkOpenRow (l1 \\ l2) r)

unifyRowVarWithEffRow :: Scope -> Taste -> EffRow -> TypeCheckM Scope
unifyRowVarWithEffRow scope v = \case
  RVar n | n == v -> pure scope
  row -> bindRowVar scope v row

unifyClosedEffRowWithOpen :: Scope -> [EffCons] -> [EffCons] -> Taste -> TypeCheckM Scope
unifyClosedEffRowWithOpen scope closed open v = do
  -- явная часть открытого ряда должна содержаться в закрытом ряду
  let missing = open \\ closed
  if not (null missing) then
    throwTypeCheckError $ EffectRowsUnificationError
      (T.concat [
        "Open row has effects not present in closed row: [",
        T.intercalate ", " $ map pretty missing, "]"])
      (RClosed closed)
      (ROpen open v)
  else do
    -- унифицируем общие эффекты (для проверки аргументов)
    scope' <- foldM (\sc cons1 ->
          case find (== cons1) closed of
            Nothing -> throwTypeCheckError $ EffectConsUnificationError cons1 (error "Should not happen")
            Just cons2 -> unifyEffCons sc cons1 cons2
        ) scope open
    -- хвост получает остаток закрытого ряда
    bindRowVar scope' v (RClosed $ closed \\ open)

unifyOpenEffRowWithClosed :: Scope -> [EffCons] -> Taste -> [EffCons] -> TypeCheckM Scope
unifyOpenEffRowWithClosed scope open v closed = unifyClosedEffRowWithOpen scope closed open v

unifyEffCons :: Scope -> EffCons -> EffCons -> TypeCheckM Scope
unifyEffCons scope c1 c2 = do
  c1' <- applyEffConsSubst scope c1
  c2' <- applyEffConsSubst scope c2

  case (c1', c2') of
    (EVar v1, EVar v2)
      | v1 == v2 -> pure scope
      | otherwise -> bindEffVar scope v1 (EVar v2)
    (EffCons (ECons name1 params1), EffCons (ECons name2 params2))
      | name1 /= name2 -> throwTypeCheckError $ EffectConsUnificationError c1' c2'
      | otherwise -> unifyTypeArgLists scope params1 params2
    (EVar t, e@EffCons{}) -> bindEffVar scope t e
    (e@EffCons{}, EVar t) -> bindEffVar scope t e
    -- (EVar _, EVar _) -> throwTypeCheckError $ EffectConsUnificationError c1' c2'

unifyTypeArgLists :: Scope -> [TypeArg] -> [TypeArg] -> TypeCheckM Scope
unifyTypeArgLists scope l1 l2 =
  let s1 = length l1; s2 = length l2
  in if length l1 /= length l2 then
    throwTypeCheckError $ TypeError $ T.pack $ printf "Effect parameter lists length mismatch: %d /= %d" s1 s2
  else
    foldM (\scope' (t1, t2) -> unifyTypeArgs scope' t1 t2) scope (zip l1 l2)

unifyTypeArgs :: Scope -> TypeArg -> TypeArg -> TypeCheckM Scope
unifyTypeArgs scope t1 t2 = do
  t1' <- applyTypeArgSubst scope t1
  t2' <- applyTypeArgSubst scope t2
  case (t1', t2') of
    (TANothing, _) -> pure scope
    (TAVar x, TAVar y) | x == y -> pure scope

    (TAVar x@Meta{}, t) -> do
      t' <- applyTypeArgSubst scope t
      if typeOccursInTypeArg x t' then
        throwTypeCheckError $ TypeArgUnificationError t1' t'
      else
        bindMetaTypeArg scope x t'

    (TAVar _, _) -> throwTypeCheckError $ TypeArgUnificationError t1' t2'
    (_, TAVar _) -> unifyTypeArgs scope t2' t1'
    (TAInt, TAInt) -> pure scope
    (TAFloat, TAFloat) -> pure scope
    (TABoolean, TABoolean) -> pure scope
    (TAString, TAString) -> pure scope
    (TANil, TANil) -> pure scope
    (TAFlat x, TAFlat y) | x == y -> pure scope
    (TAArray l1, TAArray l2) -> unifyTypeArgs scope l1 l2
    (TAPair l1 r1, TAPair l2 r2) -> do
      scope' <- unifyTypeArgs scope l1 l2
      unifyTypeArgs scope' r1 r2
    (TAFunct i1 o1, TAFunct i2 o2) -> do
      scope' <- unifyTypeArgs scope i2 i1
      unifyTypeArgs scope' o1 o2
    (TARecord props1, TARecord props2) -> unifyRecordArgs scope props1 props2
    _ -> throwTypeCheckError $ TypeArgUnificationError t1' t2'

unifyRecordArgs :: Scope -> [TARecordProp] -> [TARecordProp] -> TypeCheckM Scope
unifyRecordArgs scope props1 props2 = if length props1 /= length props2 then
  throwTypeCheckError $ TypeArgUnificationError (TARecord props1) (TARecord props2)
else
  let props1' = sort $ nubBy (\p1 p2 -> taName p1 == taName p2) props1 in
  let props2' = sort $ nubBy (\p1 p2 -> taName p1 == taName p2) props2 in
  if length props1 /= length props1' || length props2 /= length props2' then
    throwTypeCheckError $ TypeArgUnificationError (TARecord props1) (TARecord props2)
  else
    let zipped = zip props1' props2' in
    if any (\(p1, p2) -> taMut p1 /= taMut p2 || taName p1 /= taName p2) zipped then
      throwTypeCheckError $ TypeArgUnificationError (TARecord props1) (TARecord props2)
    else do
      foldM (
        \sc (typ1, typ2) -> do
          unifyTypeArgs sc typ1 typ2
        ) scope (map (bimap taTypeArg taTypeArg) zipped)

removeConsFromRow :: EffCons -> EffRow -> EffRow
removeConsFromRow cons = \case
  RClosed lst -> RClosed $ filter (cons /=) lst
  ROpen lst var -> ROpen (filter (cons /=) lst) var
  r@(RVar _) -> r

retTypeOf :: Typ -> Maybe Typ
retTypeOf (TFunct (Funct _ o _)) = go o
  where
    go (TFunct (Funct _ o' _)) = go o'
    go t = Just t

retTypeOf _ = Nothing

mutationEffects :: Set Text
mutationEffects = Set.fromList ["Read", "Var", "Rebind", "Cell"]

checkEffectNameLacks :: Set Text -> Text -> TypeCheckM ()
checkEffectNameLacks forbidden name =
  when (name `Set.member` forbidden) $
    throwTypeCheckError $
      TypeError $ "Forbidden effect in constrained row: " <> name

addEffLacks :: Scope -> Taste -> Set Text -> TypeCheckM Scope
addEffLacks scope variable forbidden = do
  resolved <- applyEffConsSubst scope (EVar variable)

  case resolved of
    EVar variable' ->
      pure scope {
        effLacks = Map.insertWith Set.union variable' forbidden scope.effLacks
      }

    EffCons (ECons name _) -> do
      checkEffectNameLacks forbidden name
      pure scope

addRowLacks :: Scope -> Taste -> Set Text -> TypeCheckM Scope
addRowLacks scope variable forbidden = do
  resolved <- applyEffRowSubst scope (RVar variable)

  case resolved of
    RVar variable' ->
      pure scope {
        rowLacks = Map.insertWith Set.union
          variable' forbidden scope.rowLacks
      }

    row ->
      addRowLacksToRow scope row forbidden

addEffLacksForArg :: Scope -> EffCons -> Set Text -> TypeCheckM Scope
addEffLacksForArg scope effect = addRowLacksToRow scope $ RClosed [effect]

addRowLacksToRow :: Scope -> EffRow -> Set Text -> TypeCheckM Scope
addRowLacksToRow scope row forbidden =
  case row of
    RClosed effects -> foldM addEffectLacks scope effects
    ROpen effects tailVar -> do
      scope' <- foldM addEffectLacks scope effects
      addRowLacks scope' tailVar forbidden

    RVar variable -> addRowLacks scope variable forbidden
  where
    addEffectLacks sc effect =
      case effect of
        EffCons (ECons name _) -> do
          checkEffectNameLacks forbidden name
          pure sc
        EVar variable -> addEffLacks sc variable forbidden

instance Pretty TypeCheckError where
  pretty = \case
    TypeError e -> "TypeError: " <> e
    TypeArgError e -> "TypeArgError: " <> e
    TypeUnificationError l r ->
      T.pack $ printf "TypeUnificationError: (%s) ~ (%s)" (pretty l) (pretty r)
    TypeArgUnificationError l r ->
      T.pack $ printf "TypeArgUnificationError: (%s) ~ (%s)" (pretty l) (pretty r)
    EffectRowsUnificationError t l r ->
      T.pack $ printf "EffectRowsUnificationError (%s): %s ~ %s" t (pretty l) (pretty r)
    EffectConsUnificationError l r ->
      T.pack $ printf "EffectConsUnificationError: %s ~ %s" (pretty l) (pretty r)
    UndefinedVariable e -> "UndefinedVariable: " <> e
    ImmutableVariableAssignment e -> "ImmutableVariableAssignment: " <> e
    SameScopeBindingShadowing e -> "SameScopeBindingShadowing: " <> e
    EffectError e -> "EffectError: " <> e
    MultipleResumeError e n -> "MultipleResumeError (" <> pretty n <> "): " <> e
    TodoError e -> "TodoError: " <> e