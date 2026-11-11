{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module UnifySpec (
  uSpec
) where
import Prelude

import Test.Hspec

import Data.Text (Text)

import Types
import Unify
import TypedIR (Scope(..))
import ErrorContext (ErrorStack)
import Utils (Pretty(pretty))
import Scope (globalScope)
import Control.Lens (use)
import Test.QuickCheck (property, (==>))
import Test.Hspec.QuickCheck (prop)
import qualified Data.Map as Map
import qualified Data.Set as Set

testScope :: TypeCheckM Scope
testScope = globalScope []

uSpec :: Spec
uSpec = do
  describe "Type unification" typeUnificationTests
  describe "Type argument unification" typeArgTests
  describe "Effect constructor unification" effectConsTests
  describe "Effect row unification" effectRowTests
  describe "Substitution" substitutionTests
  describe "Level and skolem" levelAndSkolemTests
  describe "Occurs check" $ do
    it "rejects a type variable unified with an array containing itself" $
      runWithScope
        (\sc -> do
          a <- freshMetaTypeM
          unifyTypes sc a (TArray a))
        shouldBeLeft

    it "rejects a type variable unified with a pair containing itself" $
      runWithScope
        (\sc -> do
          a <- freshMetaTypeM
          unifyTypes sc a (TPair a TInt))
        shouldBeLeft

    it "rejects a type variable occurring inside a function type" $
      runWithScope
        (\sc -> do
          a <- freshMetaTypeM
          unifyTypes sc a
            (TFunct (Funct TInt a (RClosed []))))
        shouldBeLeft

    it "rejects a row variable occurring in its own open row" $
      runWithScope
        (\sc -> do
          r <- freshMetaM
          unifyEffRows sc
            (RVar r)
            (ROpen [eff "Output"] r))
        shouldBeLeft

  describe "Effect row subsumption" $ do
    it "accepts identical closed rows" $
      runWithScope
        (\sc ->
          subsumesEffRow sc
            (RClosed [eff "Output"])
            (RClosed [eff "Output"]))
        shouldBeRight

    it "accepts an actual closed row contained in the expected closed row" $
      runWithScope
        (\sc ->
          subsumesEffRow sc
            (RClosed [eff "Output"])
            (RClosed [eff "Output", eff "State"]))
        shouldBeRight

    it "rejects an actual closed row missing from the expected row" $
      runWithScope
        (\sc ->
          subsumesEffRow sc
            (RClosed [eff "Output", eff "State"])
            (RClosed [eff "Output"]))
        shouldBeLeft

    it "allows an expected open row to absorb additional actual effects" $
      runWithScope
        (\sc -> do
          r <- freshMetaM
          subsumesEffRow sc
            (RClosed [eff "Output", eff "State"])
            (ROpen [eff "Output"] r))
        shouldBeRight

    it "accepts an actual open row when its explicit effects fit the expected closed row" $
      runWithScope
        (\sc -> do
          r <- freshMetaM
          subsumesEffRow sc
            (ROpen [eff "Output"] r)
            (RClosed [eff "Output", eff "State"]))
        shouldBeRight

    it "rejects an actual open row with an explicit effect absent from the expected row" $
      runWithScope
        (\sc -> do
          r <- freshMetaM
          subsumesEffRow sc
            (ROpen [eff "State"] r)
            (RClosed [eff "Output"]))
        shouldBeLeft
  
  describe "Effect row subsumption with rigid variables" $ do
    it "allows an open Meta row to be specialized to an empty tail" $
      runWithScope
        (\sc -> do
          r <- freshMetaM
          subsumesEffRow sc
            (ROpen [eff "Output"] r)
            (RClosed [eff "Output"]))
        shouldBeRight

    it "does not specialize a Bound row variable" $
      runWithScope
        (\sc -> do
          r <- freshBoundM
          subsumesEffRow sc
            (ROpen [eff "Output"] r)
            (RClosed [eff "Output"]))
        shouldBeLeft

    it "does not specialize a Skolem row variable" $
      runWithScope
        (\sc -> do
          r <- freshSkolemM
          subsumesEffRow sc
            (ROpen [eff "Output"] r)
            (RClosed [eff "Output"]))
        shouldBeLeft
  
  describe "Forall substitution" $ do
    it "does not substitute a type variable bound by TForall" $
      runWithScope
        (\sc -> do
          let a = bound 1
              typ = TForall [a] [] [] Map.empty Map.empty (TVar a)
          sc' <- unifyTypes sc (TVar (meta 1)) TInt
          applyTypeSubst sc' typ)
        (\case
          Right typ -> typ `shouldBe` TForall [bound 1] [] [] Map.empty Map.empty (TVar (bound 1))
          Left (_, err) ->
            expectationFailure $ "Unexpected error: " <> show err)

    it "still substitutes free type variables under TForall" $
      runWithScope
        (\sc -> do
          let a = bound 1
              b = meta 2
              typ = TForall [a] [] [] Map.empty Map.empty (TPair (TVar a) (TVar b))
          sc' <- unifyTypes sc (TVar b) TInt
          applyTypeSubst sc' typ)
        (\case
          Right typ ->
            typ `shouldBe`
              TForall [bound 1] [] [] Map.empty Map.empty
                (TPair (TVar (bound 1)) TInt)
          Left (_, err) ->
            expectationFailure $ "Unexpected error: " <> show err)
    
    it "removes substitutions for quantified type variables" $
      runWithScope
        (\sc -> do
          a <- freshMetaM
          let typ = TForall [a] [] [] Map.empty Map.empty (TVar a)
          sc' <- unifyTypes sc (TVar a) TInt
          applyTypeSubst sc' typ)
        (\case
          Right typ -> do
            a <- case typ of
              TForall [v] [] [] _ _ _ -> pure v
              _ -> expectationFailure "Unexpected forall structure" >> pure (bound 0)
            typ `shouldBe` TForall [a] [] [] Map.empty Map.empty (TVar a)
          Left (_, err) ->
            expectationFailure $ "Unexpected error: " <> show err)

    it "substitutes free type variables under TForall" $
      runWithScope
        (\sc -> do
          a <- freshBoundM
          b <- freshMetaM
          let typ = TForall [a] [] [] Map.empty Map.empty (TPair (TVar a) (TVar b))
          sc' <- unifyTypes sc (TVar b) TInt
          applyTypeSubst sc' typ)
        (\case
          Right (TForall [a] [] [] _ _ body) ->
            body `shouldBe` TPair (TVar a) TInt
          Right typ ->
            expectationFailure $ "Unexpected type: " <> show typ
          Left (_, err) ->
            expectationFailure $ "Unexpected error: " <> show err)

    -- Effect constructor variables

    it "removes substitutions for quantified effect variables" $
      runWithScope
        (\sc -> do
          e <- freshMetaM
          let typ = TForall [] [e] [] Map.empty Map.empty
                (TFunct (Funct TInt TInt (RClosed [EVar e])))
          sc' <- unifyTypes sc
            (TFunct (Funct TInt TInt (RClosed [EVar e])))
            (TFunct (Funct TInt TInt (RClosed [eff "Output"])))
          applyTypeSubst sc' typ)
        (\case
          Right typ ->
            case typ of
              TForall [] [e] [] _ _ (TFunct (Funct TInt TInt (RClosed [bodyEff]))) ->
                bodyEff `shouldBe` EVar e
              _ ->
                expectationFailure $
                  "Unexpected forall structure: " <> show typ
          Left (_, err) ->
            expectationFailure $ "Unexpected error: " <> show err)

    it "substitutes free effect variables under TForall" $
      runWithScope
        (\sc -> do
          boundEff <- freshBoundM
          freeEff <- freshMetaM
          let typ = TForall [] [boundEff] [] Map.empty Map.empty
                (TFunct (Funct TInt TInt (RClosed [EVar freeEff])))
          sc' <- unifyTypes sc
            (TFunct (Funct TInt TInt (RClosed [EVar freeEff])))
            (TFunct (Funct TInt TInt (RClosed [eff "Output"])))
          applyTypeSubst sc' typ)
        (\case
          Right (TForall [] [_] [] _ _ (TFunct (Funct TInt TInt (RClosed [e])))) ->
            e `shouldBe` eff "Output"
          Right typ ->
            expectationFailure $ "Unexpected type: " <> show typ
          Left (_, err) ->
            expectationFailure $ "Unexpected error: " <> show err)

    -- Effect row variables

    it "removes substitutions for quantified row variables" $
      runWithScope
        (\sc -> do
          r <- freshMetaM
          let typ = TForall [] [] [r] Map.empty Map.empty
                (TFunct (Funct TInt TInt (RVar r)))
          sc' <- unifyEffRows sc
            (RVar r)
            (RClosed [eff "Output"])
          applyTypeSubst sc' typ)
        (\case
          Right (TForall [] [] [r] _ _ (TFunct (Funct TInt TInt (RVar bodyRow)))) ->
            bodyRow `shouldBe` r
          Right typ ->
            expectationFailure $ "Unexpected type: " <> show typ
          Left (_, err) ->
            expectationFailure $ "Unexpected error: " <> show err)

    it "substitutes free row variables under TForall" $
      runWithScope
        (\sc -> do
          boundRow <- freshBoundM
          freeRow <- freshMetaM
          let typ = TForall [] [] [boundRow] Map.empty Map.empty
                (TFunct (Funct TInt TInt (RVar freeRow)))
          sc' <- unifyEffRows sc
            (RVar freeRow)
            (RClosed [eff "Output"])
          applyTypeSubst sc' typ)
        (\case
          Right (TForall [] [] [_] _ _
            (TFunct (Funct TInt TInt (RClosed [e])))) ->
              e `shouldBe` eff "Output"
          Right typ ->
            expectationFailure $ "Unexpected type: " <> show typ
          Left (_, err) ->
            expectationFailure $ "Unexpected error: " <> show err)
    it "preserves effect lacks constraints for quantified variables" $
      runWithScope
        (\sc -> do
          e <- freshMetaM
          let forbidden = Set.singleton "Var"
              typ = TForall [] [e] [] (Map.singleton e forbidden) Map.empty
                (TFunct (Funct TInt TInt (RClosed [EVar e])))
          sc' <- unifyTypes sc
            (TFunct (Funct TInt TInt (RClosed [EVar e])))
            (TFunct (Funct TInt TInt (RClosed [eff "Output"])))
          applyTypeSubst sc' typ)
        (\case
          Right (TForall [] [e] [] els rls
            (TFunct (Funct TInt TInt (RClosed [bodyEff])))) | rls == Map.empty -> do
              els `shouldBe` Map.singleton e (Set.singleton "Var")
              bodyEff `shouldBe` EVar e
          Right typ ->
            expectationFailure $ "Unexpected type: " <> show typ
          Left (_, err) ->
            expectationFailure $ "Unexpected error: " <> show err)
    it "preserves row lacks constraints for quantified variables" $
      runWithScope
        (\sc -> do
          r <- freshMetaM
          let forbidden = Set.singleton "Var"
              typ = TForall [] [] [r] Map.empty (Map.singleton r forbidden)
                (TFunct (Funct TInt TInt (RVar r)))
          sc' <- unifyEffRows sc
            (RVar r)
            (RClosed [eff "Output"])
          applyTypeSubst sc' typ)
        (\case
          Right (TForall [] [] [r] els rls
            (TFunct (Funct TInt TInt (RVar bodyRow)))) | els == Map.empty -> do
              rls `shouldBe` Map.singleton r (Set.singleton "Var")
              bodyRow `shouldBe` r
          Right typ ->
            expectationFailure $ "Unexpected type: " <> show typ
          Left (_, err) ->
            expectationFailure $ "Unexpected error: " <> show err)
    it "preserves quantified effect lacks while substituting free effect variables" $
      runWithScope
        (\sc -> do
          boundEff <- freshBoundM
          freeEff <- freshMetaM
          let forbidden = Set.singleton "Var"
              typ = TForall [] [boundEff] [] 
                (Map.singleton boundEff forbidden) Map.empty
                (TFunct (Funct TInt TInt (RClosed [EVar freeEff])))
          sc' <- unifyTypes sc
            (TFunct (Funct TInt TInt (RClosed [EVar freeEff])))
            (TFunct (Funct TInt TInt (RClosed [eff "Output"])))
          applyTypeSubst sc' typ)
        (\case
          Right (TForall [] [boundEff] [] els rls
            (TFunct (Funct TInt TInt (RClosed [bodyEff])))) | rls == Map.empty -> do
              els `shouldBe`
                Map.singleton boundEff (Set.singleton "Var")
              bodyEff `shouldBe` eff "Output"
          Right typ ->
            expectationFailure $ "Unexpected type: " <> show typ
          Left (_, err) ->
            expectationFailure $ "Unexpected error: " <> show err)
    it "preserves quantified row lacks while substituting free row variables" $
      runWithScope
        (\sc -> do
          boundRow <- freshBoundM
          freeRow <- freshMetaM
          let forbidden = Set.singleton "Var"
              typ = TForall [] [] [boundRow] Map.empty
                (Map.singleton boundRow forbidden)
                (TFunct (Funct TInt TInt (RVar freeRow)))
          sc' <- unifyEffRows sc
            (RVar freeRow)
            (RClosed [eff "Output"])
          applyTypeSubst sc' typ)
        (\case
          Right (TForall [] [] [boundRow] els rls
            (TFunct (Funct TInt TInt (RClosed [bodyEff])))) | els == Map.empty -> do
              rls `shouldBe`
                Map.singleton boundRow (Set.singleton "Var")
              bodyEff `shouldBe` eff "Output"
          Right typ ->
            expectationFailure $ "Unexpected type: " <> show typ
          Left (_, err) ->
            expectationFailure $ "Unexpected error: " <> show err)
  
  prop "type substitution is idempotent" $
    property $ \(n :: Int) ->
      n >= 0 && n < 1000 ==>
        let a = meta n
            sc = initialState
        in case evalTypeCheckM
            (do
              sc' <- testScope
              sc'' <- unifyTypes sc' (TVar a) TInt
              once <- applyTypeSubst sc'' (TArray (TVar a))
              twice <- applyTypeSubst sc'' once
              pure (once, twice))
            sc of
              Right (once, twice) -> once == twice
              Left _ -> False
  describe "Transitive substitution" $ do
    it "resolves a chain of type variable substitutions" $
      runWithScope
        (\sc -> do
          a <- freshMetaTypeM
          b <- freshMetaTypeM
          sc' <- unifyTypes sc a b
          sc'' <- unifyTypes sc' b TInt
          applyTypeSubst sc'' a)
        (\case
          Right typ -> typ `shouldBe` TInt
          Left (_, err) -> expectationFailure $
            "Unexpected type-check error: " <> show err)

    it "resolves a chain of substitutions inside nested types" $
      runWithScope
        (\sc -> do
          a <- freshMetaTypeM
          b <- freshMetaTypeM
          sc' <- unifyTypes sc a b
          sc'' <- unifyTypes sc' b TInt
          applyTypeSubst sc'' (TArray a))
        (\case
          Right typ -> typ `shouldBe` TArray TInt
          Left (_, err) -> expectationFailure $
            "Unexpected type-check error: " <> show err)
  
  describe "Independent substitutions" $ do
    it "resolves independent variables in a pair" $
      runWithScope
        (\sc -> do
          a <- freshMetaTypeM
          b <- freshMetaTypeM
          sc' <- unifyTypes sc a TInt
          sc'' <- unifyTypes sc' b TBoolean
          applyTypeSubst sc'' (TPair a b))
        (\case
          Right typ -> typ `shouldBe` TPair TInt TBoolean
          Left (_, err) -> expectationFailure $
            "Unexpected type-check error: " <> show err)

    it "resolves independent substitution chains in a pair" $
      runWithScope
        (\sc -> do
          a <- freshMetaTypeM
          b <- freshMetaTypeM
          c <- freshMetaTypeM
          d <- freshMetaTypeM
          sc' <- unifyTypes sc a b
          sc'' <- unifyTypes sc' b TInt
          sc''' <- unifyTypes sc'' c d
          sc'''' <- unifyTypes sc''' d TBoolean
          applyTypeSubst sc'''' (TPair a c))
        (\case
          Right typ -> typ `shouldBe` TPair TInt TBoolean
          Left (_, err) -> expectationFailure $
            "Unexpected type-check error: " <> show err)

    it "preserves unresolved variables while resolving other variables" $
      runWithScope
        (\sc -> do
          a <- freshMetaTypeM
          b <- freshMetaTypeM
          sc' <- unifyTypes sc a TInt
          applyTypeSubst sc' (TPair a b))
        (\case
          Right (TPair TInt (TVar b)) ->
            case b of
              Meta{} -> pure ()
              _ -> expectationFailure "Expected an unresolved meta variable"
          Right typ -> expectationFailure $
            "Unexpected result: " <> show typ
          Left (_, err) -> expectationFailure $
            "Unexpected type-check error: " <> show err)
  
  describe "Effect row substitution" $ do
    it "resolves a chain of row variable substitutions" $
      runWithScope
        (\sc -> do
          r1 <- freshMetaM
          r2 <- freshMetaM
          sc' <- unifyEffRows sc (RVar r1) (RVar r2)
          sc'' <- unifyEffRows sc' (RVar r2) (RClosed [])
          applyEffRowSubst sc'' (RVar r1))
        (\case
          Right row -> row `shouldBe` RClosed []
          Left (_, err) -> expectationFailure $
            "Unexpected type-check error: " <> show err)

    it "resolves a row variable inside an open effect row" $
      runWithScope
        (\sc -> do
          r <- freshMetaM
          sc' <- unifyEffRows sc (RVar r) (RClosed [])
          applyEffRowSubst sc' (ROpen [eff "Output"] r))
        (\case
          Right row -> row `shouldBe` RClosed [eff "Output"]
          Left (_, err) -> expectationFailure $
            "Unexpected type-check error: " <> show err)

    it "preserves an unresolved row variable" $
      runWithScope
        (\sc -> do
          r1 <- freshMetaM
          r2 <- freshMetaM
          sc' <- unifyEffRows sc (RVar r1) (RClosed [])
          applyEffRowSubst sc' (ROpen [eff "Output"] r2))
        (\case
          Right row -> row `shouldBe` ROpen [eff "Output"] (case row of
            ROpen _ tailVar -> tailVar
            _ -> error "Expected an open row")
          Left (_, err) -> expectationFailure $
            "Unexpected type-check error: " <> show err)
  describe "Effect row substitution invariants" $ do
    it "is idempotent" $
      runWithScope
        (\sc -> do
          r1 <- freshMetaM
          r2 <- freshMetaM
          sc' <- unifyEffRows sc
            (RVar r1)
            (ROpen [eff "Output"] r2)
          once <- applyEffRowSubst sc' (ROpen [eff "IO"] r1)
          twice <- applyEffRowSubst sc' once
          pure (once, twice))
        (\case
          Right (once, twice) -> once `shouldBe` twice
          Left (_, err) -> expectationFailure $
            "Unexpected type-check error: " <> show err)

    it "preserves effects when resolving a nested open tail" $
      runWithScope
        (\sc -> do
          r1 <- freshMetaM
          r2 <- freshMetaM
          sc' <- unifyEffRows sc
            (RVar r1)
            (ROpen [eff "Output"] r2)
          (r2, ) <$> applyEffRowSubst sc' (ROpen [eff "IO"] r1))
        (\case
          Right (r2, row) ->
            row `shouldBe` ROpen [eff "IO", eff "Output"] r2
          Left (_, err) -> expectationFailure $
            "Unexpected type-check error: " <> show err)

  describe "Effect constructor substitution" $ do
    it "binds an effect variable to a constructor without parameters" $
      runWithScope
        (\sc -> do
          e <- freshMetaM
          let output = EffCons (ECons "Output" [])
          sc' <- unifyEffRows sc
            (RClosed [EVar e])
            (RClosed [output])
          applyEffConsSubst sc' (EVar e))
        (\case
          Right cons -> cons `shouldBe` EffCons (ECons "Output" [])
          Left (_, err) -> expectationFailure $
            "Unexpected type-check error: " <> show err)

    it "preserves type arguments when binding an effect variable" $
      runWithScope
        (\sc -> do
          e <- freshMetaM
          t <- freshMetaM
          let state = EffCons (ECons "State" [TAVar t])
          sc' <- unifyEffRows sc
            (RClosed [EVar e])
            (RClosed [state])
          (t, ) <$> applyEffConsSubst sc' (EVar e))
        (\case
          Right (t, cons) ->
            cons `shouldBe` EffCons (ECons "State" [TAVar t])
          Left (_, err) -> expectationFailure $
            "Unexpected type-check error: " <> show err)

  describe "Effect constructor level lowering" $ do
    it "lowers a type variable inside an effect constructor" $
      runWithScope
        (\sc -> do
          e <- freshMetaM
          withNewLevel $ do
            t <- freshMetaM
            sc' <- unifyEffRows sc
              (RClosed [EVar e])
              (RClosed [EffCons (ECons "State" [TAVar t])])
            pure (t, sc'))
        (\case
          Right (Meta _ _ tLvl, sc') -> do
            tLvl `shouldBe` 1
            case Map.lookup (case Map.keys (effSubst sc') of
              [key] -> key
              _ -> error "Unexpected effect substitution") (effSubst sc') of
              Just (EffCons (ECons "State" [TAVar (Meta _ _ loweredLvl)])) ->
                loweredLvl `shouldBe` 0
              other -> expectationFailure $
                "Unexpected effect substitution: " <> show other
          Right other -> expectationFailure $
            "Unexpected result: " <> show other
          Left (_, err) -> expectationFailure $
            "Unexpected type-check error: " <> show err)
    
    it "lowers a type variable nested inside an effect constructor argument" $
      runWithScope
        (\sc -> do
          e <- freshMetaM
          withNewLevel $ do
            t <- freshMetaM
            sc' <- unifyEffRows sc
              (RClosed [EVar e])
              (RClosed [EffCons (ECons "State" [TAArray (TAVar t)])])
            pure (t, sc'))
        (\case
          Right (Meta _ _ tLvl, sc') -> do
            tLvl `shouldBe` 1
            case Map.elems (effSubst sc') of
              [EffCons (ECons "State" [TAArray (TAVar (Meta _ _ loweredLvl))])] ->
                loweredLvl `shouldBe` 0
              other -> expectationFailure $
                "Unexpected effect substitution: " <> show other
          Right other -> expectationFailure $
            "Unexpected result: " <> show other
          Left (_, err) -> expectationFailure $
            "Unexpected type-check error: " <> show err)

  describe "Skolem escape" $ do
    it "rejects a type metavariable bound to an inner skolem" $
      runWithScope
        (\sc -> do
          m <- freshMetaTypeM
          withNewLevel $ do
            s <- freshSkolemTypeM
            unifyTypes sc m s)
        shouldBeLeft

    it "rejects a type argument metavariable bound to an inner skolem" $
      runWithScope
        (\sc -> do
          m <- freshMetaTypeM
          withNewLevel $ do
            s <- freshSkolemTypeM
            unifyTypes sc
              (TArray m)
              (TArray s))
        shouldBeLeft

  describe "Skolem escape in effect rows and constructors" $ do
    it "rejects an effect row metavariable bound to an inner skolem tail" $
      runWithScope
        (\sc -> do
          r <- freshMetaRowM
          withNewLevel $ do
            s <- freshSkolemRowM
            unifyEffRows sc r s)
        shouldBeLeft

    it "rejects an effect constructor metavariable bound to a constructor containing an inner skolem" $
      runWithScope
        (\sc -> do
          e <- freshMetaEffM
          withNewLevel $ do
            s <- freshSkolemTypeArgM
            let state = EffCons (ECons "State" [s])
            unifyEffRows sc
              (RClosed [e])
              (RClosed [state]))
        shouldBeLeft

  describe "Repeated metavariable resolution" $ do
    it "resolves a dependent chain after several unifications" $
      runWithScope
        (\sc -> do
          a <- freshMetaTypeM
          b <- freshMetaTypeM
          c <- freshMetaTypeM
          sc1 <- unifyTypes sc a (TArray b)
          sc2 <- unifyTypes sc1 b (TPair TInt c)
          sc3 <- unifyTypes sc2 c TBoolean
          applyTypeSubst sc3 a)
        (\case
          Right typ ->
            typ `shouldBe` TArray (TPair TInt TBoolean)
          Left (_, err) -> expectationFailure $
            "Unexpected type-check error: " ++ show err)

    it "resolves shared dependencies consistently across a pair" $
      runWithScope
        (\sc -> do
          a <- freshMetaTypeM
          b <- freshMetaTypeM
          c <- freshMetaTypeM
          sc1 <- unifyTypes sc a c
          sc2 <- unifyTypes sc1 b c
          sc3 <- unifyTypes sc2 c TInt
          applyTypeSubst sc3 (TPair a b))
        (\case
          Right typ -> typ `shouldBe` TPair TInt TInt
          Left (_, err) -> expectationFailure $
            "Unexpected type-check error: " ++ show err)
  
  describe "Open effect row edge cases" $ do
    it "unifies open rows with the same tail and identical effects" $
      runWithScope
        (\sc -> do
          r <- freshMetaM
          unifyEffRows sc
            (ROpen [eff "Output"] r)
            (ROpen [eff "Output"] r))
        shouldBeRight

    it "unifies open rows with the same tail and different effect order" $
      runWithScope
        (\sc -> do
          r <- freshMetaM
          unifyEffRows sc
            (ROpen [eff "Output", eff "State"] r)
            (ROpen [eff "State", eff "Output"] r))
        shouldBeRight

    it "rejects open rows with the same tail but incompatible effects" $
      runWithScope
        (\sc -> do
          r <- freshMetaM
          unifyEffRows sc
            (ROpen [eff "Output"] r)
            (ROpen [eff "State"] r))
        shouldBeLeft

    it "unifies two independent open rows with matching effects" $
      runWithScope
        (\sc -> do
          r1 <- freshMetaM
          r2 <- freshMetaM
          unifyEffRows sc
            (ROpen [eff "Output"] r1)
            (ROpen [eff "Output"] r2))
        shouldBeRight

    it "rejects a closed row when the other open row has an unmatched effect" $
      runWithScope
        (\sc -> do
          r <- freshMetaM
          unifyEffRows sc
            (RClosed [eff "Output"])
            (ROpen [eff "State"] r))
        shouldBeLeft
  
  describe "Effect row lacks constraints" rowLacksTests

rowLacksTests :: Spec
rowLacksTests = do

  let mutationLabels =
        Set.fromList ["Read", "Var", "Rebind", "Cell"]

      addRowConstraint sc r forbidden =
        sc {
          rowLacks =
            Map.insertWith Set.union r forbidden (rowLacks sc)
        }

      addEffConstraint sc e forbidden =
        sc {
          effLacks =
            Map.insertWith Set.union e forbidden (effLacks sc)
        }

  describe "Direct row constraints" $ do

    it "allows a row variable to contain an unrestricted effect" $
      runWithScope
        (\sc -> do
          r <- freshMetaM
          let sc' = addRowConstraint sc r mutationLabels
          unifyEffRows sc' (RVar r) (closed [eff "Output"]))
        shouldBeRight

    it "rejects Read in a constrained row" $
      runWithScope
        (\sc -> do
          r <- freshMetaM
          let sc' = addRowConstraint sc r mutationLabels
          unifyEffRows sc' (RVar r) (closed [eff "Read"]))
        shouldBeLeft

    it "rejects Var in a constrained row" $
      runWithScope
        (\sc -> do
          r <- freshMetaM
          let sc' = addRowConstraint sc r mutationLabels
          unifyEffRows sc' (RVar r) (closed [eff "Var"]))
        shouldBeLeft

    it "rejects Rebind in a constrained row" $
      runWithScope
        (\sc -> do
          r <- freshMetaM
          let sc' = addRowConstraint sc r mutationLabels
          unifyEffRows sc' (RVar r) (closed [eff "Rebind"]))
        shouldBeLeft

    it "rejects Cell in a constrained row" $
      runWithScope
        (\sc -> do
          r <- freshMetaM
          let sc' = addRowConstraint sc r mutationLabels
          unifyEffRows sc' (RVar r) (closed [eff "Cell"]))
        shouldBeLeft

  describe "Constraint propagation to open tails" $ do

    it "propagates row constraints to an open tail" $
      runWithScope
        (\sc -> do
          r <- freshMetaM
          tailVar <- freshMetaM

          let sc' = addRowConstraint sc r mutationLabels

          sc'' <- unifyEffRows sc'
            (RVar r)
            (open [eff "Output"] tailVar)

          pure (Map.lookup tailVar (rowLacks sc'')))
        (\case
          Right result ->
            result `shouldBe` Just mutationLabels
          Left (_, err) ->
            expectationFailure $
              "Unexpected type-check error: " <> show err)

    it "rejects a forbidden effect introduced through an open tail" $
      runWithScope
        (\sc -> do
          r <- freshMetaM
          tailVar <- freshMetaM

          let sc' = addRowConstraint sc r mutationLabels

          sc'' <- unifyEffRows sc'
            (RVar r)
            (open [eff "Output"] tailVar)

          unifyEffRows sc''
            (RVar tailVar)
            (closed [eff "Read"]))
        shouldBeLeft

    it "allows an unrestricted effect introduced through an open tail" $
      runWithScope
        (\sc -> do
          r <- freshMetaM
          tailVar <- freshMetaM

          let sc' = addRowConstraint sc r mutationLabels

          sc'' <- unifyEffRows sc'
            (RVar r)
            (open [eff "Output"] tailVar)

          unifyEffRows sc''
            (RVar tailVar)
            (closed [eff "IO"]))
        shouldBeRight

  describe "Constraint propagation to effect variables" $ do

    it "propagates row constraints to effect variables in the row" $
      runWithScope
        (\sc -> do
          r <- freshMetaM
          e <- freshMetaM

          let sc' = addRowConstraint sc r mutationLabels

          sc'' <- unifyEffRows sc'
            (RVar r)
            (closed [EVar e])

          pure (Map.lookup e (effLacks sc'')))
        (\case
          Right result ->
            result `shouldBe` Just mutationLabels
          Left (_, err) ->
            expectationFailure $
              "Unexpected type-check error: " <> show err)

    it "rejects a forbidden effect introduced through an effect variable" $
      runWithScope
        (\sc -> do
          r <- freshMetaM
          e <- freshMetaM

          let sc' = addRowConstraint sc r mutationLabels

          sc'' <- unifyEffRows sc'
            (RVar r)
            (closed [EVar e])

          unifyEffRows sc''
            (closed [EVar e])
            (closed [eff "Read"]))
        shouldBeLeft

    it "allows an unrestricted effect introduced through an effect variable" $
      runWithScope
        (\sc -> do
          r <- freshMetaM
          e <- freshMetaM

          let sc' = addRowConstraint sc r mutationLabels

          sc'' <- unifyEffRows sc'
            (RVar r)
            (closed [EVar e])

          unifyEffRows sc''
            (closed [EVar e])
            (closed [eff "Output"]))
        shouldBeRight

    it "propagates effect constraints through effect variable aliases" $
      runWithScope
        (\sc -> do
          e1 <- freshMetaM
          e2 <- freshMetaM

          let sc' = addEffConstraint sc e1 (Set.singleton "Read")

          sc'' <- unifyEffRows sc'
            (closed [EVar e1])
            (closed [EVar e2])

          pure (Map.lookup e2 (effLacks sc'')))
        (\case
          Right result ->
            result `shouldBe` Just (Set.singleton "Read")
          Left (_, err) ->
            expectationFailure $
              "Unexpected type-check error: " <> show err)

    it "rejects a forbidden effect after resolving an effect variable alias" $
      runWithScope
        (\sc -> do
          e1 <- freshMetaM
          e2 <- freshMetaM

          let sc' = addEffConstraint sc e1 (Set.singleton "Read")

          sc'' <- unifyEffRows sc'
            (closed [EVar e1])
            (closed [EVar e2])

          unifyEffRows sc''
            (closed [EVar e2])
            (closed [eff "Read"]))
        shouldBeLeft

  describe "Constraint merging during open row unification" $ do

    it "merges constraints from both open row tails" $
      runWithScope
        (\sc -> do
          r1 <- freshMetaM
          r2 <- freshMetaM

          let lacks1 = Set.singleton "Read"
              lacks2 = Set.singleton "Var"

              sc' = addRowConstraint sc r1 lacks1
              sc'' = addRowConstraint sc' r2 lacks2

          sc''' <- unifyEffRows sc''
            (open [eff "Output"] r1)
            (open [eff "Output"] r2)

          resolved <- applyEffRowSubst sc''' (RVar r1)

          case resolved of
              RVar shared ->
                pure (Map.lookup shared (rowLacks sc'''))
              _ ->
                pure Nothing)
        (\case
          Right result ->
            result `shouldBe`
              Just (Set.fromList ["Read", "Var"])
          Left (_, err) ->
            expectationFailure $
              "Unexpected type-check error: " <> show err)

    it "rejects a forbidden effect in the explicit difference of open rows" $
      runWithScope
        (\sc -> do
          r1 <- freshMetaM
          r2 <- freshMetaM

          let sc' =
                addRowConstraint sc r1 (Set.singleton "Read")

          unifyEffRows sc'
            (open [eff "Output"] r1)
            (open [eff "Output", eff "Read"] r2))
        shouldBeLeft

    it "rejects a forbidden effect from the other side's explicit difference" $
      runWithScope
        (\sc -> do
          r1 <- freshMetaM
          r2 <- freshMetaM

          let sc' =
                addRowConstraint sc r2 (Set.singleton "Var")

          unifyEffRows sc'
            (open [eff "Output", eff "Var"] r1)
            (open [eff "Output"] r2))
        shouldBeLeft

    it "allows open rows with compatible constraints and effects" $
      runWithScope
        (\sc -> do
          r1 <- freshMetaM
          r2 <- freshMetaM

          let sc' =
                addRowConstraint sc r1 (Set.singleton "Read")

              sc'' =
                addRowConstraint sc' r2 (Set.singleton "Var")

          unifyEffRows sc''
            (open [eff "Output"] r1)
            (open [eff "Output"] r2))
        shouldBeRight

  describe "Repeated constraints" $ do

    it "accepts repeated identical row constraints" $
      runWithScope
        (\sc -> do
          r <- freshMetaM

          let sc' = addRowConstraint sc r mutationLabels
              sc'' = addRowConstraint sc' r mutationLabels

          unifyEffRows sc'' (RVar r) (closed [eff "Output"]))
        shouldBeRight

    it "unions independently added constraints on the same row variable" $
      runWithScope
        (\sc -> do
          r <- freshMetaM

          let sc' =
                addRowConstraint sc r (Set.singleton "Read")

              sc'' =
                addRowConstraint sc' r (Set.singleton "Var")

          unifyEffRows sc'' (RVar r) (closed [eff "Read"]))
        shouldBeLeft

    it "preserves constraints when unifying a row variable with itself" $
      runWithScope
        (\sc -> do
          r <- freshMetaM

          let sc' = addRowConstraint sc r mutationLabels

          unifyEffRows sc' (RVar r) (RVar r))
        shouldBeRight

  describe "Skolem escape in effect variables" $ do

    it "rejects an effect metavariable bound to an inner effect skolem" $
      runWithScope
        (\sc -> do
          e <- freshMetaM
          withNewLevel $ do
            s <- freshSkolemM
            unifyEffRows sc
              (closed [EVar e])
              (closed [EVar s]))
        shouldBeLeft

-- ---------------------------------------------------------------------------
-- Test infrastructure
-- ---------------------------------------------------------------------------

initialState :: TypeCheckState
initialState = TypeCheckState
  { _counter = (100, 100, 100)
  , _currentLevel = 0
  , _errorStack = []
  }

runWithScope
  :: (Scope -> TypeCheckM a)
  -> (Either (ErrorStack, TypeCheckError) a -> Expectation)
  -> Expectation
runWithScope action assertion =
  assertion $
    evalTypeCheckM (testScope >>= action) initialState

meta :: Int -> Taste
meta n = Meta ("m" <> pretty n) n 0

skolem :: Int -> Taste
skolem n = Skolem ("s" <> pretty n) n 0

bound :: Int -> Taste
bound n = Bound ("b" <> pretty n) n

closed :: [EffCons] -> EffRow
closed = RClosed

open :: [EffCons] -> Taste -> EffRow
open = ROpen

eff :: Text -> EffCons
eff name = EffCons (ECons name [])


shouldBeRight :: Either e a -> Expectation
shouldBeRight result =
  case result of
    Right _ -> pure ()
    Left _ ->
      expectationFailure "Expected Right, got Left"

shouldBeLeft :: Either e a -> Expectation
shouldBeLeft result =
  case result of
    Left _ -> pure ()
    Right _ ->
      expectationFailure "Expected Left, got Right"

shouldReturnType :: (Eq a, Show a) => a -> Either e a -> Expectation
shouldReturnType expected result =
  case result of
    Left _ ->
      expectationFailure "Expected successful substitution, got Left"
    Right actual ->
      actual `shouldBe` expected

-- shouldBeIdempotent :: (Eq a, Show a) => Scope -> Typ -> Expectation
-- shouldBeIdempotent sc typ = do
--   once <- applyTypeSubst sc typ
--   twice <- applyTypeSubst sc once
--   twice `shouldBe` once

-- ---------------------------------------------------------------------------
-- 1. Type unification
-- ---------------------------------------------------------------------------

typeUnificationTests :: Spec
typeUnificationTests = do

  it "unifies identical primitive types" $
    runWithScope
      (\sc -> unifyTypes sc TInt TInt)
      shouldBeRight

  it "unifies identical type variables" $
    runWithScope
      (\sc -> unifyTypes sc (TVar (meta 1)) (TVar (meta 1)))
      shouldBeRight

  it "binds a metavariable to a concrete type" $
    runWithScope
      (\sc -> unifyTypes sc (TVar (meta 1)) TInt)
      shouldBeRight

  it "binds a metavariable to a compound type" $
    runWithScope
      (\sc -> unifyTypes sc (TVar (meta 1)) (TPair TInt TString))
      shouldBeRight

  it "rejects incompatible primitive types" $
    runWithScope
      (\sc -> unifyTypes sc TInt TString)
      shouldBeLeft

  it "rejects binding a skolem variable" $
    runWithScope
      (\sc -> unifyTypes sc (TVar (skolem 1)) TInt)
      shouldBeLeft

  it "rejects binding a rigid bound variable" $
    runWithScope
      (\sc -> unifyTypes sc (TVar (bound 1)) TInt)
      shouldBeLeft

  it "rejects two distinct skolems without diverging" $
    runWithScope
      (\sc ->
        unifyTypes sc
          (TVar (skolem 1))
          (TVar (skolem 2)))
      shouldBeLeft

  it "rejects two distinct bound variables without diverging" $
    runWithScope
      (\sc ->
        unifyTypes sc
          (TVar (bound 1))
          (TVar (bound 2)))
      shouldBeLeft

  it "performs the occurs check" $
    runWithScope
      (\sc ->
        unifyTypes sc
          (TVar (meta 1))
          (TArray (TVar (meta 1))))
      shouldBeLeft

  it "performs the occurs check through function types" $
    runWithScope
      (\sc ->
        unifyTypes sc
          (TVar (meta 1))
          (TFunct (Funct TInt (TVar (meta 1)) (RClosed []))))
      shouldBeLeft

  it "unifies identical function types" $
    runWithScope
      (\sc ->
        unifyTypes sc
          (TFunct (Funct TInt TString (RClosed [])))
          (TFunct (Funct TInt TString (RClosed []))))
      shouldBeRight

-- ---------------------------------------------------------------------------
-- 2. Type argument unification
-- ---------------------------------------------------------------------------

typeArgTests :: Spec
typeArgTests = do

  it "unifies identical type arguments" $
    runWithScope
      (\sc -> unifyTypeArgs sc TAInt TAInt)
      shouldBeRight

  it "binds a type argument metavariable" $
    runWithScope
      (\sc -> unifyTypeArgs sc (TAVar (meta 1)) TAInt)
      shouldBeRight

  it "rejects incompatible type arguments" $
    runWithScope
      (\sc -> unifyTypeArgs sc TAInt TAString)
      shouldBeLeft

  it "rejects distinct rigid type argument variables" $
    runWithScope
      (\sc ->
        unifyTypeArgs sc
          (TAVar (skolem 1))
          (TAVar (skolem 2)))
      shouldBeLeft

  it "performs the occurs check for type arguments" $
    runWithScope
      (\sc ->
        unifyTypeArgs sc
          (TAVar (meta 1))
          (TAArray (TAVar (meta 1))))
      shouldBeLeft

-- ---------------------------------------------------------------------------
-- 3. Effect constructor unification
-- ---------------------------------------------------------------------------

effectConsTests :: Spec
effectConsTests = do

  it "unifies identical effects" $
    runWithScope
      (\sc ->
        unifyEffRows sc
          (closed [eff "Output"])
          (closed [eff "Output"]))
      shouldBeRight

  it "rejects effects with different names" $
    runWithScope
      (\sc ->
        unifyEffRows sc
          (closed [eff "Output"])
          (closed [eff "Input"]))
      shouldBeLeft

  it "unifies identical effect variables" $
    runWithScope
      (\sc ->
        unifyEffRows sc
          (closed [EVar (meta 1)])
          (closed [EVar (meta 1)]))
      shouldBeRight

  it "binds an effect variable to a concrete effect" $
    runWithScope
      (\sc ->
        unifyEffRows sc
          (closed [EVar (meta 1)])
          (closed [eff "Output"]))
      shouldBeRight

  it "rejects binding a rigid effect variable" $
    runWithScope
      (\sc ->
        unifyEffRows sc
          (closed [EVar (skolem 1)])
          (closed [eff "Output"]))
      shouldBeLeft


-- ---------------------------------------------------------------------------
-- 4. Effect row unification
-- ---------------------------------------------------------------------------

effectRowTests :: Spec
effectRowTests = do

  it "unifies equal closed rows" $
    runWithScope
      (\sc ->
        unifyEffRows sc
          (closed [eff "Output", eff "Input"])
          (closed [eff "Output", eff "Input"]))
      shouldBeRight

  it "rejects closed rows with different effects" $
    runWithScope
      (\sc ->
        unifyEffRows sc
          (closed [eff "Output"])
          (closed [eff "Input"]))
      shouldBeLeft

  it "unifies a row variable with a closed row" $
    runWithScope
      (\sc ->
        unifyEffRows sc
          (RVar (meta 1))
          (closed [eff "Output"]))
      shouldBeRight

  it "unifies two identical row variables" $
    runWithScope
      (\sc ->
        unifyEffRows sc
          (RVar (meta 1))
          (RVar (meta 1)))
      shouldBeRight

  it "unifies two open rows with a shared tail" $
    runWithScope
      (\sc ->
        unifyEffRows sc
          (open [eff "Output"] (meta 1))
          (open [eff "Output"] (meta 1)))
      shouldBeRight

  it "rejects incompatible open rows with the same tail" $
    runWithScope
      (\sc ->
        unifyEffRows sc
          (open [eff "Output"] (meta 1))
          (open [eff "Input"] (meta 1)))
      shouldBeLeft

  it "unifies open rows with different explicit effects" $
    runWithScope
      (\sc ->
        unifyEffRows sc
          (open [eff "Output"] (meta 1))
          (open [eff "Input"] (meta 2)))
      shouldBeRight

  it "detects a row variable occurring in its own binding" $
    runWithScope
      (\sc ->
        unifyEffRows sc
          (RVar (meta 1))
          (open [eff "Output"] (meta 1)))
      shouldBeLeft


-- ---------------------------------------------------------------------------
-- 5. Substitution through nested types
-- ---------------------------------------------------------------------------

substitutionTests :: Spec
substitutionTests = do
  it "resolves a chain of type substitutions" $
    runWithScope
      (\sc -> do
        sc1 <- unifyTypes sc (TVar (meta 1)) (TVar (meta 2))
        sc2 <- unifyTypes sc1 (TVar (meta 2)) TInt
        applyTypeSubst sc2 (TVar (meta 1)))
      (shouldReturnType TInt)

  it "resolves substitutions in nested pairs" $
    runWithScope
      (\sc -> do
        sc1 <- unifyTypes sc (TVar (meta 1)) TInt
        sc2 <- unifyTypes sc1 (TVar (meta 2)) TString
        applyTypeSubst sc2
          (TPair (TVar (meta 1)) (TArray (TVar (meta 2)))))
      (shouldReturnType (TPair TInt (TArray TString)))

  it "resolves substitutions in record fields" $
    runWithScope
      (\sc -> do
        sc1 <- unifyTypes sc (TVar (meta 1)) TInt
        applyTypeSubst sc1
          (TRecord [TRecordProp Val "value" (TVar (meta 1))]))
      (shouldReturnType
        (TRecord [TRecordProp Val "value" TInt]))

  it "does not modify unrelated metavariables" $
    runWithScope
      (\sc -> do
        sc1 <- unifyTypes sc (TVar (meta 1)) TInt
        applyTypeSubst sc1 (TVar (meta 2)))
      (shouldReturnType (TVar (meta 2)))

  it "resolves function input and output types" $
    runWithScope
      (\sc -> do
        sc1 <- unifyTypes sc (TVar (meta 1)) TInt
        sc2 <- unifyTypes sc1 (TVar (meta 2)) TString
        applyTypeSubst sc2
          (TFunct (Funct (TVar (meta 1)) (TVar (meta 2)) (RClosed []))))
      (shouldReturnType
        (TFunct (Funct TInt TString (RClosed []))))

  it "resolves function effect row substitutions" $
    runWithScope
      (\sc -> do
        sc1 <- unifyEffRows sc
          (RVar (meta 1))
          (closed [eff "Output"])
        applyTypeSubst sc1
          (TFunct (Funct TInt TInt (RVar (meta 1)))))
      (shouldReturnType
        (TFunct (Funct TInt TInt (closed [eff "Output"]))))

  it "applies a type substitution transitively" $
    runWithScope
      (\sc -> do
        sc1 <- unifyTypes sc (TVar (meta 1)) (TVar (meta 2))
        sc2 <- unifyTypes sc1 (TVar (meta 2)) TInt
        applyTypeSubst sc2 (TVar (meta 1)))
      (shouldReturnType TInt)

  it "applies substitutions inside arrays" $
    runWithScope
      (\sc -> do
        sc1 <- unifyTypes sc (TVar (meta 1)) TInt
        applyTypeSubst sc1 (TArray (TVar (meta 1))))
      (shouldReturnType (TArray TInt))

  it "applies substitutions inside function effect rows" $
    runWithScope
      (\sc -> do
        sc1 <- unifyEffRows sc
          (RVar (meta 1))
          (closed [eff "Output"])
        applyTypeSubst sc1
          (TFunct (Funct TInt TInt (RVar (meta 1)))))
      (shouldReturnType
        (TFunct (Funct TInt TInt (closed [eff "Output"]))))

levelAndSkolemTests :: Spec
levelAndSkolemTests = describe "levels and skolem escape" $ do

  it "allows unifying a metavariable with a skolem at the same level" $
    runWithScope
      (\sc -> withNewLevel $ do
        metaTy <- freshMetaTypeM
        skolemTy <- freshSkolemTypeM
        unifyTypes sc metaTy skolemTy)
      shouldBeRight

  it "rejects a skolem escaping into an outer metavariable" $
    runWithScope
      (\sc -> do
        outerMeta <- freshMetaTypeM
        withNewLevel $ do
          innerSkolem <- freshSkolemTypeM
          unifyTypes sc outerMeta innerSkolem)
      shouldBeLeft

  it "allows an inner metavariable to unify with an outer metavariable" $
    runWithScope
      (\sc -> do
        outerMeta <- freshMetaTypeM
        withNewLevel $ do
          innerMeta <- freshMetaTypeM
          unifyTypes sc innerMeta outerMeta)
      shouldBeRight
  
  it "lowers an inner metavariable when binding an outer metavariable" $
    runWithScope
      (\sc -> do
        outerMeta <- freshMetaTypeM
        withNewLevel $ do
          innerMeta <- freshMetaTypeM
          sc' <- unifyTypes sc outerMeta (TArray innerMeta)
          applyTypeSubst sc' outerMeta)
      (\case
          Right (TArray (TVar (Meta _ _ level))) ->
            level `shouldBe` 0
          Right typ ->
            expectationFailure $
              "Unexpected resolved type: " <> show typ
          Left (_, err) ->
            expectationFailure $
              "Unification failed: " <> show err)