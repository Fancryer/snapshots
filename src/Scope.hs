{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Scope (
  enterScope,
  leaveScope,
  keepSubst,
  isTopLevel,
  findBinding,
  findType,
  findEff,
  findHandler,
  findEffOps,
  hasBinding,
  hasType,
  hasEff,
  hasHandler,
  addBinding,
  addType,
  addEffect,
  addHandler,
  globalScope
)
where

import Types (
    HandlerSig,
    Mutability(..),
    Typ(..),
    EffDef(..),
    Funct(..),
    TypeScheme,

    EffRow(RClosed, RVar, ROpen),
    Scheme(Scheme),
    pureFunct,
    Expr(..), NativeLambdaSign (..), tfunc, monoScheme
  )
import TypedIR (Scope(..))
import qualified Data.Map as Map
import Control.Monad.Except (Except, throwError)
import Unify (TypeCheckM, TypeCheckError (SameScopeBindingShadowing), freshBoundM, freshMetaM, throwTypeCheckError)
import qualified Data.Maybe as Maybe
import Data.Text (Text)
import qualified Eff
import Eff (elabel, label)

enterScope :: Scope -> Scope
enterScope scope = Scope
  Map.empty
  Map.empty
  Map.empty
  Nothing
  scope.typeSubst
  scope.typeArgSubst
  scope.effSubst
  scope.rowSubst
  scope.rowLacks
  scope.effLacks
  (Just scope)

leaveScope :: Scope -> Except String Scope
leaveScope sc = case sc.parent of
  Nothing -> throwError "Cannot leave empty scope"
  Just p -> pure p

-- | Выйти из внутренней области: вернуть внешнюю, сохранив накопленные подстановки.
--   Унификация записывает результат в Scope, поэтому при выходе из области
--   нельзя просто взять родителя: подстановки были бы потеряны.
keepSubst :: Scope -> Scope -> Scope
keepSubst inner outer = outer {
    typeSubst    = inner.typeSubst,
    typeArgSubst = inner.typeArgSubst,
    effSubst     = inner.effSubst,
    rowSubst     = inner.rowSubst
  }

isTopLevel :: Bool -> Scope -> Bool
isTopLevel canBeGlobal sc = case sc.parent of
  Nothing -> canBeGlobal
  Just p -> isTopLevel False p

findBinding :: Bool -> Scope -> Text -> Maybe (TypeScheme, Expr, Mutability)
findBinding uptop sc name =
  case (Map.lookup name sc.values, uptop, sc.parent) of
    (s@(Just _), _, _) -> s
    (Nothing, True, Just p) -> findBinding True p name
    _ -> Nothing

findType :: Bool -> Scope -> Text -> Maybe Typ
findType uptop sc name =
  case (Map.lookup name sc.types, uptop, sc.parent) of
    (s@(Just _), _, _) -> s
    (Nothing, True, Just p) -> findType True p name
    _ -> Nothing

findEff :: Bool -> Scope -> Text -> Maybe EffDef
findEff uptop sc name =
  case (Map.lookup name sc.effects, uptop, sc.parent) of
    (s@(Just _), _, _) -> s
    (Nothing, True, Just p) -> findEff True p name
    _ -> Nothing

findHandler :: Bool -> Scope -> Maybe HandlerSig
findHandler uptop sc =
  case (sc.handlerSig, uptop, sc.parent) of
    (s@(Just _), _, _) -> s
    (Nothing, True, Just p) -> findHandler True p
    _ -> Nothing

findEffOps :: Bool -> Scope -> Text -> Maybe [(Text, Funct)]
findEffOps uptop sc name =
  case findEff uptop sc name of
    Just (EffDef _ _ ops) -> Just ops
    Nothing -> Nothing

hasBinding :: Bool -> Scope -> Text -> Bool
hasBinding uptop scope name = Maybe.isJust $ findBinding uptop scope name

hasType :: Bool -> Scope -> Text -> Bool
hasType uptop scope name = Maybe.isJust $ findType uptop scope name

hasEff :: Bool -> Scope -> Text -> Bool
hasEff uptop scope name = Maybe.isJust $ findEff uptop scope name

hasHandler :: Bool -> Scope -> Bool
hasHandler uptop scope = Maybe.isJust $ findHandler uptop scope

addBinding :: Text -> TypeScheme -> Expr -> Mutability -> Scope -> TypeCheckM Scope
addBinding name typ expr mut scope =
  if hasBinding False scope name then
    throwTypeCheckError $ SameScopeBindingShadowing $ "Cannot shadow a `" <> name <> "` binding in the same scope!"
  else
    pure $ scope {values = Map.insert name (typ, expr, mut) scope.values}

addType :: Text -> Typ -> Scope -> TypeCheckM Scope
addType name typ scope =
  if hasType False scope name then
    throwTypeCheckError $ SameScopeBindingShadowing $ "Cannot shadow a `" <> name <> "` type in the same scope!"
  else
    pure $ scope {types = Map.insert name typ scope.types}

addEffect :: EffDef -> Scope -> TypeCheckM Scope
addEffect effDef@(EffDef name _ _) scope =
  if hasEff False scope name then
    throwTypeCheckError $ SameScopeBindingShadowing $ "Cannot shadow an `" <> name <> "` effect in the same scope!"
  else
    pure $ scope {effects = Map.insert name effDef scope.effects}

addHandler :: HandlerSig -> Scope -> TypeCheckM Scope
addHandler sig scope =
  if hasHandler False scope then
    throwTypeCheckError $ SameScopeBindingShadowing "Cannot shadow an effect handler in the same scope!"
  else
    pure $ scope {handlerSig = Just sig}

globalScope :: [Text] -> TypeCheckM Scope
globalScope args = do
  let scope = Scope
        Map.empty
        Map.empty
        Map.empty
        Nothing
        Map.empty
        Map.empty
        Map.empty
        Map.empty
        Map.empty
        Map.empty
        Nothing
      addPureBinding n t s = addBinding n (monoScheme t) (NLambda s) Val
  scope' <- addPureBinding
    "pred"
    (tfunc TInt TInt)
    (NativeLambdaSign "x" TInt TInt $ RClosed [])
    scope

  scope2 <- do
    boundA <- freshBoundM
    let tBoundA = TVar boundA
    addBinding
      "say"
      (Scheme [boundA] [] [] Map.empty Map.empty (TFunct $ Funct tBoundA TNil Eff.fxOutput))
      (NLambda (NativeLambdaSign "x" tBoundA TNil Eff.fxOutput))
      Val
      scope'

  scope3 <- do
    boundA <- freshBoundM
    let tBoundA = TVar boundA
    addBinding
      "sayn"
      (Scheme [boundA] [] [] Map.empty Map.empty (TFunct $ Funct tBoundA TNil Eff.fxOutput))
      (NLambda (NativeLambdaSign "x" tBoundA TNil Eff.fxOutput))
      Val
      scope2

  scope4 <- addBinding
    "args"
    (monoScheme $ TArray TString)
    (Array $ map String args)
    Val
    scope3

  scope5 <- addPureBinding
    "+"
    (tfunc TInt $ tfunc TInt TInt)
    (NativeLambdaSign "a" TInt (tfunc TInt TInt) Eff.empty)
    scope4

  scope6 <- addPureBinding
    "-"
    (tfunc TInt $ tfunc TInt TInt)
    (NativeLambdaSign "a" TInt (tfunc TInt TInt) Eff.empty)
    scope5

  scope7 <- do
    boundA <- freshBoundM
    let tBoundA = TVar boundA
    boundR <- freshMetaM
    addBinding
      "force"
      (Scheme [boundA] [] [] Map.empty Map.empty $ TFunct $ Funct tBoundA tBoundA $ ROpen [] boundR)
      (NLambda (NativeLambdaSign "a" tBoundA tBoundA $ RVar boundR))
      Val
      scope6
  
  scope8 <- do
    addPureBinding
      "read_int"
      (TFunct $ Funct TNil TInt $ RClosed [label "Input"])
      (NativeLambdaSign "a" TNil TInt $ RClosed [label "Input"])
      scope7
  
  scope9 <- do
    addPureBinding
      "ieq"
      (tfunc TInt $ tfunc TInt TBoolean)
      (NativeLambdaSign "a" TInt (tfunc TInt TBoolean) Eff.empty)
      scope8
  
  scope10 <- do
    addPureBinding
      "and"
      (tfunc TBoolean $ tfunc TBoolean TBoolean)
      (NativeLambdaSign "a" TBoolean (tfunc TBoolean TBoolean) Eff.empty)
      scope9
  
  scope11 <- addPureBinding
    ">"
    (tfunc TInt $ tfunc TInt TBoolean)
    (NativeLambdaSign "a" TInt (tfunc TInt TBoolean) Eff.empty)
    scope10
  
  scope12 <- addPureBinding
    "<"
    (tfunc TInt $ tfunc TInt TBoolean)
    (NativeLambdaSign "a" TInt (tfunc TInt TBoolean) Eff.empty)
    scope11
  
  addBinding
    "random_int"
    (monoScheme $ TFunct $ Funct TInt (TFunct $ Funct TInt TInt Eff.fxRandom) Eff.empty)
    (NLambda $ NativeLambdaSign "a" TInt (TFunct $ Funct TInt TInt Eff.fxRandom) Eff.empty)
    Val
    scope12