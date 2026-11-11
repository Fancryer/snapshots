{-# LANGUAGE LambdaCase #-}

module Occurs (
  typeOccursInType,
  typeOccursInTypeArg,
  typeOccursInEffRow,
  rowOccursInEffRow,
  typeContainsEffects
) where
import Types (Typ(..), EffRow(..), Taste, EffRow, TRecordProp (..), Funct (..), TypeArg (..), TARecordProp (TARecordProp), EffCons (..), ECons (..))

typeOccursInType :: Taste -> Typ -> Bool
typeOccursInType x = \case
  TVar y -> x == y
  TArray t -> typeOccursInType x t
  TPair l r -> any (typeOccursInType x) [l, r]
  TFunct (Funct i o fx) -> any (typeOccursInType x) [i, o] || typeOccursInEffRow x fx
  TForall ts _ _ _ _ typ -> notElem x ts && typeOccursInType x typ
  TRecord props -> any (\(TRecordProp _ _ typ) -> typeOccursInType x typ) props
  _ -> False

typeOccursInTypeArg :: Taste -> TypeArg -> Bool
typeOccursInTypeArg x = \case
  TAVar y -> x == y
  TAArray t -> typeOccursInTypeArg x t
  TAPair l r -> any (typeOccursInTypeArg x) [l, r]
  TAFunct i o -> any (typeOccursInTypeArg x) [i, o]
  TARecord props -> any (\(TARecordProp _ _ typ) -> typeOccursInTypeArg x typ) props
  _ -> False

typeOccursInEffRow :: Taste -> EffRow -> Bool
typeOccursInEffRow x = \case
  ROpen labels _ -> any (\case
    EffCons (ECons _ args) -> any (typeOccursInTypeArg x) args
    EVar _ -> False) labels
  RClosed labels -> any (\case
    EffCons (ECons _ args) -> any (typeOccursInTypeArg x) args
    EVar _ -> False) labels
  RVar _ -> False

rowOccursInEffRow :: Taste -> EffRow -> Bool
rowOccursInEffRow x = \case
  ROpen _ t -> x == t
  _ -> False -- Closed row doesn't contain evar

typeContainsEffects :: Typ -> Bool
typeContainsEffects = \case
  TFunct (Funct i o _) -> any typeContainsEffects [i, o]
  TArray t -> typeContainsEffects t
  TPair l r -> any typeContainsEffects [l, r]
  TForall _ es rs _ _ t -> es /= [] || rs /= [] || typeContainsEffects t
  TRecord props -> any (\(TRecordProp _ _ typ) -> typeContainsEffects typ) props
  _ -> False