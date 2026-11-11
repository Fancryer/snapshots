{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Eff (
  empty,
  label,
  elabel,
  labels,
  closedOfFlat,
  isEmpty,
  extractEffects,
  extractTypeEffects,
  typeHasEffect,
  unionEffRows,
  unionEffRowsList,
  appendEff,
  rowHasEffect,
  pureEffDeclWithOps,
  fxInput,
  fxOutput,
  fxRandom,
  fxTime,
  fxSystem,
  fxVar,
  fxRead,
  fxRebind,
  fxCell
) where
import Types
import Data.List (nub, sort)
import Data.Text (Text)
import qualified Utils

empty :: EffRow
empty = RClosed []

label :: Text -> EffCons
label = EffCons . elabel

elabel :: Text -> ECons
elabel = flip ECons []

labels :: [Text] -> [EffCons]
labels = map label

closedOfFlat :: Text -> EffRow
closedOfFlat l = RClosed [label l]

isEmpty :: EffRow -> Bool
isEmpty = \case RClosed [] -> True; _ -> False

extractEffects :: EffRow -> [EffCons]
extractEffects = \case
  RClosed fxs' -> fxs'
  ROpen fxs' _ -> fxs'
  _ -> []

rowHasEffect :: EffRow -> EffCons -> Bool
rowHasEffect r = (`elem` extractEffects r)

extractTypeEffects :: Typ -> [EffCons]
extractTypeEffects = \case
  TArray t -> extractTypeEffects t
  TPair l r -> extractTypeEffects l <> extractTypeEffects r
  TFunct (Funct i o r) -> extractTypeEffects i <> extractTypeEffects o <> extractEffects r
  TRecord props -> Utils.uniqPreserveOrder $ concatMap (extractTypeEffects . tTyp) props
  TForall _ _ _ _ _ t -> extractTypeEffects t
  _ -> []

typeHasEffect :: Typ -> EffCons -> Bool
typeHasEffect t = (`elem` extractTypeEffects t)

appendEff :: EffRow -> EffCons -> EffRow
appendEff r e = case r of
  ROpen cs t -> ROpen (cs <> [e]) t
  RClosed cs -> RClosed $ cs <> [e]
  _ -> r

unionEffRows :: EffRow -> EffRow -> EffRow
unionEffRows r1 r2 =
  let effects1 = extractEffects r1 in
  let effects2 = extractEffects r2 in

  let combinedEffects = sort $ nub $ effects1 <> effects2 in

  case (r1, r2) of
    -- Если хотя бы один ряд открытый - результат открытый
    (ROpen _ v, _) -> ROpen combinedEffects v
    (_, ROpen _ v) -> ROpen combinedEffects v
    -- Оба закрытые
    (RClosed _, RClosed _) -> RClosed combinedEffects
    (RVar _, RVar _) -> error "Cannot union two abstract row variables"
    (RVar v, r) -> ROpen (extractEffects r) v
    (r, RVar v) -> ROpen (extractEffects r) v

unionEffRowsList :: [EffRow] -> EffRow
unionEffRowsList = foldl unionEffRows $ RClosed []

pureEffDeclWithOps :: Text -> [(Text, Funct)] -> EffDef
pureEffDeclWithOps name = EffDef name []

fxInput, fxOutput, fxRandom, fxTime, fxSystem, fxVar, fxRead, fxRebind, fxCell :: EffRow
fxInput = closedOfFlat "Input"
fxOutput = closedOfFlat "Output"
fxRandom = closedOfFlat "Random"
fxTime = closedOfFlat "Time"
fxSystem = closedOfFlat "System"
fxVar = closedOfFlat "Var"
fxRead = closedOfFlat "Read"
fxRebind = closedOfFlat "Rebind"
fxCell = closedOfFlat "Cell"