
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RequiredTypeArguments #-}

module FreezeSpec (fSpec) where

import Control.Monad (forM_)
import Data.Either (isLeft)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Test.Hspec

import qualified Eff
import qualified Infer
import qualified Scope

import Types
  ( Taste(..)
  , Typ(..)
  , EffRow(..)
  , EffCons(..)
  , ECons(..)
  , Funct(..)
  , TRecordProp(..)
  , Mutability(..)
  , Scheme(..)
  )

import TypedIR (Scope(..))

import Unify
  ( TypeCheckM
  , TypeCheckState(..)
  , runTypeCheckM
  , freshMetaM
  , freshBoundM
  , freshMetaRowM
  , freshMetaEffM
  , unifyEffRows
  , applyEffRowSubst
  , withNewLevel, TypeCheckError
  )
import ErrorContext (ErrorStack)

-- Mutation-related effects forbidden in frozen values.
mutationLabels :: [Text]
mutationLabels = ["Var", "Read", "Rebind", "Cell"]

mutationEffects :: Set.Set Text
mutationEffects = Set.fromList mutationLabels

label :: Text -> EffCons
label = Eff.label

initialState :: TypeCheckState
initialState = TypeCheckState (0, 0, 0) 0 []

emptyScope :: Scope
emptyScope = Scope
  { types = Map.empty
  , values = Map.empty
  , effects = Map.empty
  , handlerSig = Nothing
  , typeSubst = Map.empty
  , typeArgSubst = Map.empty
  , effSubst = Map.empty
  , rowSubst = Map.empty
  , effLacks = Map.empty
  , rowLacks = Map.empty
  , parent = Nothing
  }

runWithScope :: (Scope -> TypeCheckM a) -> Either (ErrorStack, TypeCheckError) a
runWithScope action =
  fst $ runTypeCheckM (action emptyScope) initialState

expectRight :: Show a => Either a t -> (t -> Expectation) -> Expectation
expectRight result check =
  case result of
    Right value -> check value
    Left err -> expectationFailure $ "Unexpected type-check error: " <> show err

expectLeft :: Either err a -> Expectation
expectLeft = \case
  Left _ -> pure ()
  Right _ ->
    expectationFailure "Expected a type-check error"

fSpec :: Spec
fSpec = do
  describe "freezeRowMutIn: explicit effect removal" $ do

    it "removes all four mutation effects and preserves ordinary effects" $
      runWithScope (\scope -> do
        r <- freshMetaM
        e <- freshMetaM

        let row = ROpen [
                label "Read",
                EVar e,
                label "IO",
                label "Var",
                label "Rebind",
                label "Cell"
              ] r

        (scope', frozen) <- Infer.freezeRowMutIn scope row
        pure (r, e, scope', frozen)
      ) `expectRight` \(r, e, scope', frozen) -> do
        frozen `shouldBe` ROpen [EVar e, label "IO"] r
        Map.lookup r (rowLacks scope') `shouldBe` Just mutationEffects
        Map.lookup e (effLacks scope') `shouldBe` Just mutationEffects

    it "produces an empty closed row when all explicit effects are mutations" $
      runWithScope (\scope -> do
        (_, frozen) <- Infer.freezeRowMutIn scope $
          RClosed $ map label mutationLabels
        pure frozen
      ) `expectRight` (`shouldBe` RClosed [])

    it "does not alter an ordinary closed row" $
      runWithScope (\scope -> do
        (_, frozen) <- Infer.freezeRowMutIn scope $
          RClosed [label "IO", label "Output"]
        pure frozen
      ) `expectRight` (`shouldBe` RClosed [label "IO", label "Output"])

  describe "freezeRowMutIn: lacks constraints" $ do

    it "adds mutation constraints to an open row tail" $
      runWithScope (\scope -> do
        r <- freshMetaM
        (scope', frozen) <- Infer.freezeRowMutIn scope $
          ROpen [label "IO"] r
        pure (r, scope', frozen)
      ) `expectRight` \(r, scope', frozen) -> do
        frozen `shouldBe` ROpen [label "IO"] r
        Map.lookup r (rowLacks scope') `shouldBe` Just mutationEffects

    it "adds mutation constraints to effect variables" $
      runWithScope (\scope -> do
        e <- freshMetaM
        (scope', frozen) <- Infer.freezeRowMutIn scope $
          RClosed [EVar e]
        pure (e, scope', frozen)
      ) `expectRight` \(e, scope', frozen) -> do
        frozen `shouldBe` RClosed [EVar e]
        Map.lookup e (effLacks scope') `shouldBe` Just mutationEffects

    it "constrains both effect variables and row tails" $
      runWithScope (\scope -> do
        e <- freshMetaM
        r <- freshMetaM
        (scope', frozen) <- Infer.freezeRowMutIn scope $
          ROpen [EVar e, label "IO"] r
        pure (e, r, scope', frozen)
      ) `expectRight` \(e, r, scope', frozen) -> do
        frozen `shouldBe` ROpen [EVar e, label "IO"] r
        Map.lookup e (effLacks scope') `shouldBe` Just mutationEffects
        Map.lookup r (rowLacks scope') `shouldBe` Just mutationEffects

    it "does not add constraints when no variables remain" $
      runWithScope (\scope -> do
        (scope', _) <- Infer.freezeRowMutIn scope $
          RClosed [label "IO"]
        pure scope'
      ) `expectRight` \scope' -> do
        Map.null (effLacks scope') `shouldBe` True
        Map.null (rowLacks scope') `shouldBe` True

  describe "freezeRowMutIn: forbidden effects" $ do
    forM_ mutationLabels $ \lab -> do
      it ("rejects " <> show lab <> " in a frozen row tail") $
        expectLeft $ runWithScope (\scope -> do
          r <- freshMetaM
          (scope', _) <- Infer.freezeRowMutIn scope (RVar r)
          unifyEffRows scope' (RVar r) (RClosed [label lab])
        )

      it ("rejects " <> show lab <> " in a frozen effect variable") $
        expectLeft $ runWithScope (\scope -> do
          e <- freshMetaM
          (scope', _) <- Infer.freezeRowMutIn scope $
            RClosed [EVar e]
          unifyEffRows scope' (RClosed [EVar e]) $
            RClosed [label lab]
        )

    it "allows an ordinary effect in a constrained row tail" $
      runWithScope (\scope -> do
        r <- freshMetaM
        (scope', _) <- Infer.freezeRowMutIn scope (RVar r)
        scope'' <- unifyEffRows scope' (RVar r) $
          RClosed [label "IO"]
        applyEffRowSubst scope'' (RVar r)
      ) `expectRight` (`shouldBe` RClosed [label "IO"])

    it "allows an ordinary effect in a constrained effect variable" $
      runWithScope (\scope -> do
        e <- freshMetaM
        (scope', _) <- Infer.freezeRowMutIn scope $
          RClosed [EVar e]
        unifyEffRows scope' (RClosed [EVar e]) $
          RClosed [label "IO"]
      ) `expectRight` const (pure ())

  describe "lacks constraints: substitution and aliasing" $ do

    it "rejects a forbidden effect already hidden behind a row substitution" $
      expectLeft $ runWithScope (\scope -> do
        r <- freshMetaM
        let scope' = scope
              { rowSubst = Map.insert r (RClosed [label "Read"]) $
                  rowSubst scope
              }
        Infer.freezeRowMutIn scope' (RVar r)
      )

    it "rejects a forbidden effect already hidden behind an effect substitution" $
      expectLeft $ runWithScope (\scope -> do
        e <- freshMetaM
        let scope' = scope
              { effSubst = Map.insert e (label "Cell") $
                  effSubst scope
              }
        Infer.freezeRowMutIn scope' (RClosed [EVar e])
      )

    it "transfers row constraints when two row variables are unified" $
      expectLeft $ runWithScope (\scope -> do
        r1 <- freshMetaM
        r2 <- freshMetaM
        (scope', _) <- Infer.freezeRowMutIn scope (RVar r1)
        scope'' <- unifyEffRows scope' (RVar r1) (RVar r2)
        unifyEffRows scope'' (RVar r2) $
          RClosed [label "Read"]
      )

    it "transfers effect constraints when two effect variables are unified" $
      expectLeft $ runWithScope (\scope -> do
        e1 <- freshMetaM
        e2 <- freshMetaM
        (scope', _) <- Infer.freezeRowMutIn scope $
          RClosed [EVar e1]
        scope'' <- unifyEffRows scope'
          (RClosed [EVar e1])
          (RClosed [EVar e2])
        unifyEffRows scope'' (RClosed [EVar e2]) $
          RClosed [label "Rebind"]
      )

  describe "freezeTyp: recursive type freezing" $ do

    it "freezes latent effects inside nested function types" $
      runWithScope (\scope -> do
        r <- freshMetaM
        let typ = TArray $
              TFunct $ Funct TInt TInt $
                ROpen [label "Read", label "IO", label "Var"] r
        (scope', frozen) <- Infer.freezeTyp scope typ
        pure (r, scope', frozen)
      ) `expectRight` \(r, scope', frozen) -> do
        frozen `shouldBe`
          TArray (TFunct $ Funct TInt TInt (ROpen [label "IO"] r))
        Map.lookup r (rowLacks scope') `shouldBe` Just mutationEffects

    it "changes var record fields to val and freezes their function types" $
      runWithScope (\scope -> do
        r <- freshMetaM
        let typ = TRecord
              [ TRecordProp Var "callback" $
                  TFunct $ Funct TInt TInt $
                    ROpen [label "Cell", label "IO"] r
              ]
        (scope', frozen) <- Infer.freezeTyp scope typ
        pure (r, scope', frozen)
      ) `expectRight` (\(r, scope', frozen) -> do
        case frozen of
          TRecord [TRecordProp Val "callback"
            (TFunct (Funct TInt TInt (ROpen [io] tailVar)))] -> do
              io `shouldBe` label "IO"
              tailVar `shouldBe` r
          _ -> expectationFailure $
            "Unexpected frozen record type: " <> show frozen

        Map.lookup r (rowLacks scope') `shouldBe` Just mutationEffects
      )

  describe "freezeTyp: forall" $ do

    it "stores constraints for quantified variables inside TForall" $
      runWithScope (\scope -> do
        e <- freshBoundM
        r <- freshBoundM
        let typ = TForall [] [e] [r]
              Map.empty
              Map.empty
              (TFunct $ Funct TInt TInt $
                ROpen [label "Read", EVar e] r)
        (scope', frozen) <- Infer.freezeTyp scope typ
        pure (scope', e, r, frozen)
      ) `expectRight` (\(scope', e, r, frozen) -> do
        Map.null (effLacks scope') `shouldBe` True
        Map.null (rowLacks scope') `shouldBe` True

        case frozen of
          TForall [] [e'] [r'] els rls
            (TFunct (Funct TInt TInt (ROpen [EVar e''] r''))) -> do
              e' `shouldBe` e
              r' `shouldBe` r
              e'' `shouldBe` e
              r'' `shouldBe` r
              Map.lookup e els `shouldBe` Just mutationEffects
              Map.lookup r rls `shouldBe` Just mutationEffects
          _ -> expectationFailure $
            "Unexpected frozen forall type: " <> show frozen
      )

    it "unions new constraints with existing forall constraints" $
      runWithScope (\scope -> do
        e <- freshBoundM
        r <- freshBoundM
        let typ = TForall [] [e] [r]
              (Map.singleton e existingEffects)
              (Map.singleton r existingEffects)
              (TFunct $ Funct TInt TInt $
                ROpen [EVar e] r)
        (_, frozen) <- Infer.freezeTyp scope typ
        pure (e, r, frozen)
      ) `expectRight` (\(e, r, frozen) ->
        case frozen of
          TForall _ _ _ els rls _ -> do
            Map.lookup e els `shouldBe`
              Just (Set.union existingEffects mutationEffects)
            Map.lookup r rls `shouldBe`
              Just (Set.union existingEffects mutationEffects)
          _ -> expectationFailure $
            "Expected a frozen TForall, got: " <> show frozen
      )

existingEffects :: Set.Set Text
existingEffects = Set.singleton "IO"