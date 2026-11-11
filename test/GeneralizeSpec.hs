{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
module GeneralizeSpec (
  gSpec
) where
import Test.Hspec (Spec, describe, it, Expectation, expectationFailure, shouldBe, shouldNotBe, shouldContain)
import Types
import Unify (TypeCheckError (..), TypeCheckM, evalTypeCheckM, TypeCheckState (..), freshMetaM, freshMetaRowM, freshMetaEffM, bindRowVar, throwTypeCheckError, addRowLacks, bindEffVar, addEffLacks, currentLevel, applyTypeSubst, unifyTypes, freshBoundM, unifyEffRows)
import ErrorContext (ErrorStack)
import TypedIR (Scope (..))
import Scope (globalScope, addBinding)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set
import Data.Text (Text)
import Infer (instantiateTypeScheme, generalize, InferResult (InferResult), inferExpr, typeOfTypedExprUnsafe)
import Eff (elabel, label, empty)
import Control.Lens (use, (.=))

initialState :: TypeCheckState
initialState = TypeCheckState {
  _counter = (100, 100, 100),
  _currentLevel = 0,
  _errorStack = []
}

testScope :: TypeCheckM Scope
testScope = globalScope []

runWithScope
  :: (Scope -> TypeCheckM a)
  -> (Either (ErrorStack, TypeCheckError) a -> Expectation)
  -> Expectation
runWithScope action assertion =
  assertion $
    evalTypeCheckM (testScope >>= action) initialState

freshMetaAtLevelM :: Int -> TypeCheckM Taste
freshMetaAtLevelM lvl = do
  freshMetaM >>= \case
    Meta name ident _ -> pure (Meta name ident lvl)
    _ -> error "freshMetaM returned a non-Meta value"

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

mutationEffects :: Set Text
mutationEffects = Set.fromList ["Read", "Var", "Rebind", "Cell"]

gSpec :: Spec
gSpec = do
  describe "Scheme lacks constraints" $ do
    describe "Instantiation" $ do
      it "restores row lacks constraints" $
        runWithScope
          (\scope -> do
            t <- freshMetaM
            r <- freshMetaM

            let scheme = Scheme
                  [t] [] [r]
                  Map.empty
                  (Map.singleton r mutationEffects)
                  (TVar t)

            (_, scope') <- instantiateTypeScheme scope scheme

            pure $ case Map.lookup r (rowSubst scope') of
              Just (RVar freshR) ->
                Map.lookup freshR (rowLacks scope')
              _ -> Nothing
          )
          (\case
            Left err -> expectationFailure (show err)
            Right constraints ->
              constraints `shouldBe` Just mutationEffects
          )

      it "restores effect lacks constraints" $
        runWithScope
          (\scope -> do
            t <- freshMetaM
            e <- freshMetaM

            let scheme = Scheme
                  [t] [e] []
                  (Map.singleton e mutationEffects)
                  Map.empty
                  (TVar t)

            (_, scope') <- instantiateTypeScheme scope scheme

            pure $ case Map.lookup e (effSubst scope') of
              Just (EVar freshE) ->
                Map.lookup freshE (effLacks scope')
              _ -> Nothing
          )
          (\case
            Left err -> expectationFailure (show err)
            Right constraints ->
              constraints `shouldBe` Just mutationEffects
          )

      it "rejects a forbidden effect after instantiation" $
        runWithScope
          (\scope -> do
            t <- freshMetaM
            r <- freshMetaM

            let scheme = Scheme
                  [t] [] [r]
                  Map.empty
                  (Map.singleton r mutationEffects)
                  (TVar t)

            (_, scope') <- instantiateTypeScheme scope scheme

            case Map.lookup r (rowSubst scope') of
              Just (RVar freshR) ->
                bindRowVar scope' freshR (RClosed [label "Read"])
              _ -> throwTypeCheckError $
                TypeError "Expected an instantiated row variable"
          )
          shouldBeLeft

      it "allows a non-forbidden effect after instantiation" $
        runWithScope
          (\scope -> do
            t <- freshMetaM
            r <- freshMetaM

            let scheme = Scheme
                  [t] [] [r]
                  Map.empty
                  (Map.singleton r mutationEffects)
                  (TVar t)

            (_, scope') <- instantiateTypeScheme scope scheme

            case Map.lookup r (rowSubst scope') of
              Just (RVar freshR) ->
                bindRowVar scope' freshR (RClosed [label "IO"])
              _ -> throwTypeCheckError $
                TypeError "Expected an instantiated row variable"
          )
          shouldBeRight

      it "creates independent constrained variables for separate instantiations" $
        runWithScope
          (\scope -> do
            t <- freshMetaM
            r <- freshMetaM

            let scheme = Scheme
                  [t] [] [r]
                  Map.empty
                  (Map.singleton r mutationEffects)
                  (TVar t)

            (_, scope1) <- instantiateTypeScheme scope scheme
            (_, scope2) <- instantiateTypeScheme scope1 scheme

            let freshRow scope' =
                  case Map.lookup r (rowSubst scope') of
                    Just (RVar freshR) -> Just freshR
                    _ -> Nothing

            pure (freshRow scope1, freshRow scope2)
          )
          (\case
            Left err -> expectationFailure (show err)
            Right (Just first, Just second) ->
              first `shouldNotBe` second
            Right other ->
              expectationFailure $
                "Expected two fresh row variables, got " <> show other
          )
      it "preserves row lacks constraints after resolving a row alias" $
        runWithScope
          (\scope -> do

            outerLevel <- use currentLevel
            currentLevel .= (outerLevel + 1)

            t <- freshMetaM
            r <- freshMetaM
            s <- freshMetaM

            scope' <- bindRowVar scope r (RVar s)
            scope'' <- addRowLacks scope' s mutationEffects

            let typ = TFunct $ Funct (TVar t) (TVar t) (RVar r)

            currentLevel .= outerLevel

            (s, ) <$> generalize scope'' typ
          )
          (\case
              Left err -> expectationFailure (show err)
              Right (s, scheme) -> do
                _rs scheme `shouldContain` [s]
                Map.lookup s (_rowLacks scheme)
                  `shouldBe` Just mutationEffects
          )
      it "preserves effect lacks constraints after resolving an effect alias" $
        runWithScope
          (\scope -> do
            outerLevel <- use currentLevel
            currentLevel .= (outerLevel + 1)

            t <- freshMetaM
            e <- freshMetaM
            f <- freshMetaM

            scope' <- bindEffVar scope e (EVar f)
            scope'' <- addEffLacks scope' f mutationEffects

            let typ = TFunct $
                  Funct
                    (TVar t)
                    (TVar t)
                    (RClosed [EVar e])

            currentLevel .= outerLevel

            (f, ) <$> generalize scope'' typ
          )
          (\case
              Left err -> expectationFailure (show err)
              Right (f, scheme) -> do
                _es scheme `shouldContain` [f]
                Map.lookup f (_effLacks scheme)
                  `shouldBe` Just mutationEffects
          )
  it "preserves effect lacks constraints for quantified variables" $
    runWithScope
      (\sc -> do
        e <- freshMetaM
        let forbidden = Set.singleton "Var"
            typ = TForall [] [e] [] (Map.singleton e forbidden) Map.empty
              (TFunct (Funct TInt TInt (RClosed [EVar e])))
        sc' <- unifyTypes sc
          (TFunct (Funct TInt TInt (RClosed [EVar e])))
          (TFunct (Funct TInt TInt (RClosed [label "Output"])))
        applyTypeSubst sc' typ)
      (\case
        Right (TForall [] [e] [] els rls
          (TFunct (Funct TInt TInt (RClosed [bodyEff])))) | rls == Map.empty-> do
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
          (RClosed [label "Output"])
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
          (TFunct (Funct TInt TInt (RClosed [label "Output"])))
        applyTypeSubst sc' typ)
      (\case
        Right (TForall [] [boundEff] [] els rls
          (TFunct (Funct TInt TInt (RClosed [bodyEff])))) | rls == Map.empty -> do
            els `shouldBe`
              Map.singleton boundEff (Set.singleton "Var")
            bodyEff `shouldBe` label "Output"
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
          (RClosed [label "Output"])
        applyTypeSubst sc' typ)
      (\case
        Right (TForall [] [] [boundRow] els rls
          (TFunct (Funct TInt TInt (RClosed [bodyEff])))) | els == Map.empty -> do
            rls `shouldBe`
              Map.singleton boundRow (Set.singleton "Var")
            bodyEff `shouldBe` label "Output"
        Right typ ->
          expectationFailure $ "Unexpected type: " <> show typ
        Left (_, err) ->
          expectationFailure $ "Unexpected error: " <> show err)
  describe "Forall instantiation" $ do
    it "rejects a forbidden concrete effect argument" $
      runWithScope
        (\sc -> do
          e <- freshBoundM
          let forbidden = Set.singleton "Var"
              typ = TForall [] [e] [] (Map.singleton e forbidden) Map.empty
                (TFunct (Funct TInt TInt (RClosed [EVar e])))
          sc' <- addBinding
            "f"
            (monoScheme typ)
            (NLambda (NativeLambdaSign "x" TInt TInt Eff.empty))
            Val
            sc
          inferExpr sc' (With (XVar "f") [] [label "Var"] []))
        (\case
          Left _ -> pure ()
          Right result ->
            expectationFailure $
              "Expected forbidden effect error, got: " <> show result)

    -- it "accepts an allowed concrete effect argument" $
    --   runWithScope
    --     (\sc -> do
    --       e <- freshBoundM
    --       let forbidden = Set.singleton "Var"
    --           typ = TForall [] [e] [] (Map.singleton e forbidden) Map.empty
    --             (TFunct (Funct TInt TInt (RClosed [EVar e])))
    --       sc' <- addBinding
    --         "f"
    --         (monoScheme typ)
    --         (NLambda (NativeLambdaSign "x" TInt TInt Eff.empty))
    --         Val
    --         sc
    --       InferResult typed _ scope' <-
    --         inferExpr sc' (With (XVar "f") [] [label "Output"] [])
    --       resultType <- typeOfTypedExprUnsafe typed
    --       pure (resultType, scope'))
    --     (\case
    --       Right (TFunct (Funct TInt TInt (RClosed [e])), _) ->
    --         e `shouldBe` label "Output"
    --       Right result ->
    --         expectationFailure $ "Unexpected result: " <> show result
    --       Left (_, err) ->
    --         expectationFailure $ "Unexpected error: " <> show err)
    -- it "transfers effect lacks constraints to an effect variable argument" $
    --   runWithScope
    --     (\sc -> do
    --       e <- freshBoundM
    --       freeEff <- freshMetaM
    --       let forbidden = Set.singleton "Var"
    --           typ = TForall [] [e] [] (Map.singleton e forbidden) Map.empty
    --             (TFunct (Funct TInt TInt (RClosed [EVar e])))
    --       sc' <- addBinding
    --         "f"
    --         (monoScheme typ)
    --         (NLambda (NativeLambdaSign "x" TInt TInt Eff.empty))
    --         Val
    --         sc
    --       InferResult _ _ scope' <-
    --         inferExpr sc' (With (XVar "f") [] [EVar freeEff] [])
    --       pure (freeEff, scope'))
    --     (\case
    --       Right (freeEff, scope') ->
    --         Map.lookup freeEff (effLacks scope')
    --           `shouldBe` Just (Set.singleton "Var")
    --       Left (_, err) ->
    --         expectationFailure $ "Unexpected error: " <> show err)

    -- it "rejects a forbidden effect inside a row argument" $
    --   runWithScope
    --     (\sc -> do
    --       r <- freshBoundM
    --       let forbidden = Set.singleton "Var"
    --           typ = TForall [] [] [r] Map.empty (Map.singleton r forbidden)
    --             (TFunct (Funct TInt TInt (RVar r)))
    --       sc' <- addBinding
    --         "f"
    --         (monoScheme typ)
    --         (NLambda (NativeLambdaSign "x" TInt TInt Eff.empty))
    --         Val
    --         sc
    --       inferExpr sc' (With (XVar "f") [] [] [RClosed [label "Var"]]))
    --     (\case
    --       Left _ -> pure ()
    --       Right result ->
    --         expectationFailure $
    --           "Expected forbidden effect error, got: " <> show result)

    -- it "transfers row lacks constraints to an open row tail" $
    --   runWithScope
    --     (\sc -> do
    --       r <- freshBoundM
    --       tailVar <- freshMetaM
    --       let forbidden = Set.singleton "Var"
    --           typ = TForall [] [] [r] Map.empty (Map.singleton r forbidden)
    --             (TFunct (Funct TInt TInt (RVar r)))
    --       sc' <- addBinding
    --         "f"
    --         (monoScheme typ)
    --         (NLambda (NativeLambdaSign "x" TInt TInt Eff.empty))
    --         Val
    --         sc
    --       InferResult _ _ scope' <-
    --         inferExpr sc' (With (XVar "f") [] [] [ROpen [] tailVar])
    --       pure (tailVar, scope'))
    --     (\case
    --       Right (tailVar, scope') ->
    --         Map.lookup tailVar (rowLacks scope')
    --           `shouldBe` Just (Set.singleton "Var")
    --       Left (_, err) ->
    --         expectationFailure $ "Unexpected error: " <> show err)
