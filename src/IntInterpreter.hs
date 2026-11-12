{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}

module IntInterpreter (interpret, prepareSnapshotBenchmark, InterpError(..)) where

import qualified TypedIR as IR
import Types (
    Mutability(..),
    ECons(..),
    EffCons(..),
    LetPattern(..),
    AtomLetPattern(..),
    LetPatternRecordProp(..),
    LambdaParam(..), EffRow (..)
  )
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Scientific (Scientific, fromFloatDigits)
import Control.Monad.Cont (ContT(..), callCC)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Span (Span, noSpan)
import Utils (TextMap, Pretty (..))
import Data.Foldable (find)
import Data.List (intercalate)
import TypedIR (
    TypedExpr(..),
    pattern TEInt, pattern TEFloat, pattern TEBoolean, pattern TEString,
    pattern TENil, pattern TEXVar, pattern TEArray, pattern TEPair,
    pattern TEXLambda, pattern TENLambda, pattern TEApply, pattern TERecord,
    pattern TEHandle, pattern TEParen, pattern TEResume, pattern TELet,
    pattern TEPropAccess, pattern TEIfElse,
    Lambda(..), Block, TERecordProp(..))
import Control.Monad.State
import Control.Monad (foldM, forM, forM_, void, replicateM, foldM_, when)
import Infer (freezeMutability, freeze, freezeBlock, freezeLambda)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Eff
import qualified Parser
import System.Random (randomIO, randomRIO)
import Data.Char (chr)
import System.CPUTime (getCPUTime)
import Control.Concurrent (threadDelay)
import Resume (ResumeInfo(..))
import Text.Printf (printf)
import Data.Traversable (for)
import Data.Maybe (fromMaybe, isJust)
import System.Environment (lookupEnv)
import Control.Exception (evaluate)
import qualified Data.IntMap.Strict as IM
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap as IntMap

-- Address to Int
addrToInt :: Address -> Int
addrToInt (Address n) = n

class Stringify a where
  stringify :: a -> Interp Text
  default stringify :: (Pretty a) => a -> Interp Text
  stringify = pure . pretty

-- | Значения во время выполнения
data Value
  = VInt Integer
  | VFloat Scientific
  | VBoolean Bool
  | VString Text
  | VNil
  | VArray [Address]
  | VPair Address Address
  | VRecord EnvId
  | VClosure EnvId (Maybe (IntMap Address)) (Address -> Interp Address)
  | VThunk TypedExpr EnvId
  | VBThunk Block EnvId
  | VBottom
  -- deriving Show

instance Show Value where
  show = \case
    VInt i -> concat ["(VInt ", show i, ")"]
    VFloat f -> concat ["(VFloat ", show f, ")"]
    VBoolean b -> concat ["(VBoolean ", show b, ")"]
    VString s -> concat ["(VString '", show s, "')"]
    VNil -> "VNil"
    VArray as -> concat ["(VArray [", unwords $ map show as, "])"]
    VPair l r -> concat ["(VPair ", show l, " ", show r, ")"]
    VRecord fields -> "!record" <> show fields <> "!"
    VClosure eid _ _ -> "!closure[" <> T.unpack (pretty eid) <> "]!"
    VThunk te _ -> "!vthunk" <> show te <> "!"
    VBThunk b _ -> "!bthunk" <> show b <> "!"
    VBottom -> "!bottom!"

instance Pretty Value where
  pretty = \case
    VInt i -> T.pack $ show i
    VFloat f -> T.pack $ show f
    VBoolean True -> "true"
    VBoolean False -> "false"
    VString s -> s
    VNil -> "()"
    VPair l r -> T.concat ["(", pretty l, ", ", pretty r, ")"]
    VArray vals -> "[" <> T.intercalate ", " (map pretty vals) <> "]"
    VRecord eid -> "!record[" <> pretty eid <> "]!"
    VClosure eid _ _ -> "!closure[" <> pretty eid <> "]!"
    VThunk e _env -> T.concat ["!vthunk: ", pretty e,"!"]
    VBThunk b _env -> T.concat ["!vthunk: ", pretty b,"!"]
    VBottom -> "⊥"

instance Stringify Value where
  stringify = \case
    VInt i -> pure $ pretty i
    VFloat f -> pure $ pretty f
    VBoolean True -> pure "true"
    VBoolean False -> pure "false"
    VString s -> pure s
    VNil -> pure "()"
    VPair l r -> do
      l' <- stringify l
      r' <- stringify r
      pure $ T.concat ["(", l', ", ", r', ")"]
    VArray vals -> pure $ "[" <> T.intercalate ", " (map pretty vals) <> "]"
    VRecord eid -> do
      env <- getEnv eid
      bindings' <- go env []
      pure $ "#{" <> T.intercalate "; " bindings' <> "}"
      where
        go :: Env -> [Text] -> Interp [Text]
        go env' acc = do
          bindings' <- forM (Map.toList env'.bindings)
            (\(n, (m, a)) -> do
              a' <- stringify a
              pure $ T.unwords [pretty m, n, "=", a'])
          case env'.parent of
            Nothing -> pure $ acc <> bindings'
            Just p -> do
              e <- getEnv p
              go e bindings'
    VClosure eid _ _ -> pure $ "!closure[" <> pretty eid <> "]!"
    VThunk e _env -> pure $ T.concat ["!vthunk: ", pretty e,"!"]
    VBThunk b _env -> pure $ T.concat ["!bthunk: ", pretty b,"!"]
    VBottom -> pure "⊥"

-- | Окружение переменных
newtype Address = Address Int deriving (Ord, Eq, Show)
instance Pretty Address where pretty (Address a) = T.pack $ printf "#%08x" a

instance Stringify Address where
  stringify a = derefOr a >>= stringify

newtype EnvId = EnvId Int deriving (Ord, Eq, Show)
instance Pretty EnvId where pretty (EnvId i) = T.pack $ printf "&%08x" i

data Env = Env {
  bindings :: TextMap (Mutability, Address),
  parent   :: Maybe EnvId
}

-- TODO: instance Stringify Env (using #{parent | bindings})

type Heap = IntMap Value

getEnv :: EnvId -> Interp Env
getEnv eid = do
  st <- get
  case Map.lookup eid st.sEnvs of
    Just e -> pure e
    Nothing -> rtError $ "internal error: environment " <> pretty eid <> " does not exist"

updateEnv :: EnvId -> Env -> Interp EnvId
updateEnv eid env = do
  modify $ \s -> s {sEnvs = Map.insert eid env s.sEnvs}
  pure eid

newEnv :: Env -> Interp EnvId
newEnv env = do
  n <- gets sNextEnv
  let eid = EnvId n
  modify $ \s -> s {sNextEnv = n + 1, sEnvs = Map.insert eid env s.sEnvs}
  pure eid

getCurrentEnv :: Interp Env
getCurrentEnv = getEnv =<< gets sEnv

modifyCurrentEnv :: (Env -> Env) -> Interp EnvId
modifyCurrentEnv f = flip modifyEnv f =<< gets sEnv

modifyEnv :: EnvId -> (Env -> Env) -> Interp EnvId
modifyEnv eid f = updateEnv eid . f =<< getEnv eid

findBindingEnv :: EnvId -> Text -> Interp (EnvId, Mutability, Address)
findBindingEnv eid name = go Set.empty eid
  where
    go visited eid' = do
      when (Set.member eid' visited) $
        rtError $ "internal error: the environment chain of " <> pretty eid' <> " is cyclic"
      env <- getEnv eid'
      case Map.lookup name env.bindings of
        Just (m,a) -> pure (eid', m, a)
        Nothing -> case env.parent of
          Just p -> go (Set.insert eid' visited) p
          Nothing -> rtError $ "`" <> name <> "` is not in scope"

getCell :: Env -> Text -> Maybe (Mutability, Address)
getCell e x = Map.lookup x e.bindings

getRef :: Env -> Text -> Maybe Address
getRef e x = snd <$> getCell e x

getMut :: Env -> Text -> Maybe Mutability
getMut e x = fst <$> getCell e x

deref :: Heap -> Address -> Maybe Value
deref h a = IM.lookup (addrToInt a) h

derefIn :: Address -> Interp (Maybe Value)
derefIn a = do
  st <- get
  pure $ deref st.sHeap a

-- | Read an address that must be live.  A hole in the heap means the
--   interpreter lost track of a value — a bug in this module, not in the
--   program being run — so it is reported as a diagnostic instead of
--   crashing.
derefOr :: Address -> Interp Value
derefOr a = do
  st <- get
  case deref st.sHeap a of
    Just v -> pure v
    Nothing -> rtError $ "internal error: address " <> pretty a <> " is not in the heap"

unpackRef :: Env -> Heap -> Text -> Maybe Value
unpackRef e h x = getRef e x >>= deref h

-- | Код замыкания (нужен, чтобы снимок мог переписать функцию, а не только её данные)
data Code
  = CodeLam IR.Lambda
  | CodeFun [Text] IR.Block

-- | События мутации (теорема об эффектах): чтение var, перепривязка, создание var, чтение снимком
data Event = EvRead | EvRebind | EvCreate | EvSnapRead
  deriving (Eq, Ord, Show)

data InterpState = InterpState
  { sEnv        :: EnvId
  , sEnvs       :: Map EnvId Env
  , sHeap       :: IntMap Value          -- было Heap = Map Address Value
  , sKstack     :: [HandlerFrame]
  , sNextAddr   :: Int
  , sNextEnv    :: Int
  , sCode       :: IntMap Code           -- было Map Address Code
  , sFreezeMemo :: IntMap Address        -- было Map Address Address
  , sTrace      :: Bool
  , sEvents     :: Map Event Int
  , sNoMemo     :: Bool
  , sSpan       :: Span                  -- ^ where the interpreter currently is
  }

type Clause = [Address] -> (Address -> Interp Address) -> Interp Address

data HandlerFrame = HandlerFrame {
  hEffect     :: ECons,
  hClauses    :: Map Text Clause,
  hThen       :: Address -> Interp Address
}

-- | A failure of the interpreter itself: a value of the wrong shape reached a
--   primitive, an address was read after it was freed, a handler went missing.
--
--   These are never consequences of a well-typed program, so reaching one is a
--   bug — but a bug should be a message with a position, not an exception that
--   unwinds through the user's screen.
data InterpError = InterpError {
    ieMessage :: Text
  , ieSpan    :: Span
  } deriving (Eq)

instance Pretty InterpError where
  pretty = ieMessage

-- | 'show' is used by the few places that print a value of this type; make it
--   print the message rather than a constructor application.
instance Show InterpError where
  show = T.unpack . ieMessage

-- | Raise a runtime error at the node currently being evaluated.
rtError :: Text -> Interp a
rtError msg = do
  sp <- gets sSpan
  raise sp msg

-- | Raise a runtime error at a known node.
rtErrorAt :: Span -> Text -> Interp a
rtErrorAt = raise

raise :: Span -> Text -> Interp a
raise sp msg = lift $ throwError (InterpError msg sp)

-- | Mонада интерпретации: CPS с IO, ошибки — отдельный канал.
--
--   'ExceptT' sits under 'ContT' so that an error aborts the whole evaluation,
--   including continuations captured by 'callCC': a runtime error is not
--   something a handler clause may resume from.
type Interp a = ContT Value (ExceptT InterpError (StateT InterpState IO)) a

-- | Run an interpretation, keeping the final state.
runInterp :: Interp Value -> InterpState -> IO (Either InterpError Value, InterpState)
runInterp action = runStateT (runExceptT (runContT action pure))

-- | Запуск интерпретации
interpret :: IR.Chunk -> [String] -> IO (Either InterpError Value)
interpret chunk cmdArgs = fst <$> runInterp (do
    root <- newEnv $ Env Map.empty Nothing
    modify $ \st -> st {sEnv = root}
    _ <- buildInitialEnv
    evalChunk chunk
  ) initialInterpState

-- | Операция эффекта: арность и клауза объявляются вместе (единственный источник арности)
data Op = Op {
  opArity  :: Int,
  opClause :: Clause
}

-- | Встроенные эффекты и их операции
globalOps :: [(ECons, [(Text, Op)])]
globalOps = [
    (Eff.elabel "Output", [
      ("say", Op 1 $ \case
        [addrArg] -> \_ -> do
          liftIO . putStr . T.unpack =<< stringify =<< forceValue addrArg
          alloc VNil
        args -> \_ -> arityError "say" 1 args),
      ("sayn", Op 1 $ \case
        [addrArg] -> \_ -> do
          liftIO . putStrLn . T.unpack =<< stringify =<< forceValue addrArg
          alloc VNil
        args -> \_ -> arityError "sayn" 1 args),
      ("trace", Op 1 $ \case
        [addrArg] -> \_ -> do
          v <- derefOr addrArg
          liftIO $ putStrLn $ T.unpack $ pretty v
          pure addrArg
        args -> \_ -> arityError "trace" 1 args)
    ]),
    (Eff.elabel "Input", [
      ("read_string", Op 1 $ \_ _ -> do
        input <- T.pack <$> liftIO getLine
        case Parser.parseFromText Parser.stringLiteral input of
          Left _ -> rtError $ "`read_string` could not parse the line " <> quoted input
          Right s -> alloc $ VString s),
      ("read_int", Op 1 $ \_ _ -> do
        input <- T.pack <$> liftIO getLine
        case Parser.parseFromText Parser.intLiteral input of
          Left _ -> rtError $ "`read_int` could not parse the line " <> quoted input
          Right i -> alloc $ VInt i),
      ("read_float", Op 1 $ \_ _ -> do
        input <- T.pack <$> liftIO getLine
        case Parser.parseFromText Parser.floatLiteral input of
          Left _ -> rtError $ "`read_float` could not parse the line " <> quoted input
          Right f -> alloc $ VFloat f),
      ("read_boolean", Op 1 $ \_ _ -> do
        input <- T.pack <$> liftIO getLine
        case Parser.parseFromText Parser.bool input of
          Left _ -> rtError $ "`read_boolean` could not parse the line " <> quoted input
          Right b -> alloc $ VBoolean b)
    ]),
    (Eff.elabel "Random", [
      ("random_int", Op 2 $ \case
        [minI, maxI] -> \_ -> do
          lo <- forceValue minI
          hi <- forceValue maxI
          case (lo, hi) of
            (VInt a, VInt b) -> do
              r <- liftIO $ toInteger <$> (randomRIO (fromIntegral a, fromIntegral b) :: IO Int)
              alloc $ VInt r
            _ -> rtError "`random_int` needs an Int as both its lower and upper bound"
        args -> \_ -> arityError "random_int" 2 args),
      ("random_float", Op 1 $ \_ _ -> do
        r <- liftIO $ fromFloatDigits <$> (randomRIO (0.0, 1.0) :: IO Double)
        alloc $ VFloat r),
      ("random_boolean", Op 1 $ \_ _ -> alloc . VBoolean =<< randomIO),
      ("random_string", Op 1 $ \case
        [addr] -> \_ -> do
          v <- derefOr addr
          case v of
            VInt n | n <= 0 -> alloc $ VString ""
            VInt n -> do
              chars <- mapM (const $ chr <$> randomRIO (32, 126)) [1 .. fromInteger n]
              alloc $ VString (T.pack chars)
            _ -> rtError "`random_string` needs an Int as its length"
        args -> \_ -> arityError "random_string" 1 args)
    ]),
    (Eff.elabel "Time", [
      ("time_ms", Op 1 $ \_ _ -> do
        cpuTime <- liftIO getCPUTime
        alloc $ VInt $ fromInteger $ cpuTime `div` 1_000_000_000),
      ("sleep", Op 1 $ \case
        [addr] -> \_ -> do
          v <- derefOr addr
          case v of
            VInt i -> liftIO (threadDelay $ fromInteger i) >> alloc VNil
            _ -> rtError "`sleep` needs an Int as its duration in microseconds"
        args -> \_ -> arityError "sleep" 1 args)
    ])
  ]

-- | The argument list of an operation whose arity is fixed did not match.
arityError :: Text -> Int -> [Address] -> Interp a
arityError op expected args =
  rtError $ T.concat [
      "`", op, "` takes ", T.pack (show expected), " argument",
      if expected == 1 then "" else "s",
      ", but was applied to ", T.pack (show (length args))
    ]

-- | A line of input, quoted so that trailing spaces are visible in the message.
quoted :: Text -> Text
quoted t = "`" <> t <> "`"

-- | How a value is named in a runtime error.  The full 'Pretty' instance
--   prints records and closures by address, which is noise in a message that
--   only says "this was not an Int".
describe :: Value -> Text
describe = \case
  VInt _ -> "an Int"
  VFloat _ -> "a Float"
  VBoolean _ -> "a Boolean"
  VString _ -> "a String"
  VNil -> "the unit value"
  VArray _ -> "an array"
  VPair _ _ -> "a pair"
  VRecord _ -> "a record"
  VClosure _ _ _ -> "a function"
  VThunk _ _ -> "an unevaluated expression"
  VBThunk _ _ -> "an unevaluated expression"
  VBottom -> "an undefined value"

-- | The heap has no value at this address; the interpreter itself is broken.
undead :: Address -> Interp a
undead addr =
  rtError $ "internal error: address " <> pretty addr <> " is not in the heap"

globalHandlers :: [HandlerFrame]
globalHandlers = [
    HandlerFrame {
      hEffect = eff,
      hClauses = Map.fromList [(n, opClause o) | (n, o) <- ops],
      hThen = pure
    }
  | (eff, ops) <- globalOps
  ]

buildInitialEnv :: Interp EnvId
buildInitialEnv = do
  -- замыкания операций строятся из той же таблицы, что и клаузы (арность не дублируется)
  let allocEffectCall eff (op, o) = do
        env <- gets sEnv
        clos <- makeEffectClosure env o.opArity eff op
        addr <- alloc $ VClosure env Nothing clos
        pure (op, (Val, addr))
  opBindings <- fmap concat $ forM globalOps $ \(eff, ops) -> mapM (allocEffectCall eff) ops
  let operations = Map.fromList opBindings
  st <- get

  let getInt :: Address -> Interp Integer
      getInt addr = do
        st' <- get
        case deref st'.sHeap addr of
          Just (VThunk _ _) -> do
            _ <- force addr
            st'' <- get
            case deref st''.sHeap addr of
              Just (VInt i) -> pure i
              Just v -> rtError $ "expected an Int, got " <> describe v
              Nothing -> undead addr
          Just (VInt i) -> pure i
          Nothing -> undead addr
          Just v -> rtError $ "expected an Int, got " <> describe v
      getBool :: Address -> Interp Bool
      getBool addr = do
        st' <- get
        case deref st'.sHeap addr of
          Just (VThunk _ _) -> do
            _ <- force addr
            st'' <- get
            case deref st''.sHeap addr of
              Just (VBoolean b) -> pure b
              Just v -> rtError $ "expected a Boolean, got " <> describe v
              Nothing -> undead addr
          Just (VBoolean b) -> pure b
          Nothing -> undead addr
          Just v -> rtError $ "expected a Boolean, got " <> describe v

  let emptyCache = Just (IM.empty :: IntMap Address)

  plusAddr <- alloc $ VClosure st.sEnv emptyCache $ \addrA -> do
      a <- getInt addrA
      st' <- get
      alloc $ VClosure st'.sEnv emptyCache $ \addrB -> do
        b <- getInt addrB
        alloc $ VInt $ a + b
  minusAddr <- alloc $ VClosure st.sEnv emptyCache $ \addrA -> do
      a <- getInt addrA
      st' <- get
      alloc $ VClosure st'.sEnv emptyCache $ \addrB -> do
        b <- getInt addrB
        alloc $ VInt $ a - b
  forceAddr <- alloc $ VClosure st.sEnv emptyCache force
  ieqAddr <- alloc $ VClosure st.sEnv emptyCache $ \addrA -> do
      a <- getInt addrA
      st' <- get
      alloc $ VClosure st'.sEnv emptyCache $ \addrB -> do
        b <- getInt addrB
        alloc $ VBoolean $ a == b
  igtAddr <- alloc $ VClosure st.sEnv emptyCache $ \addrA -> do
      a <- getInt addrA
      st' <- get
      alloc $ VClosure st'.sEnv emptyCache $ \addrB -> do
        b <- getInt addrB
        alloc $ VBoolean $ a > b
  iltAddr <- alloc $ VClosure st.sEnv emptyCache $ \addrA -> do
      a <- getInt addrA
      st' <- get
      alloc $ VClosure st'.sEnv emptyCache $ \addrB -> do
        b <- getInt addrB
        alloc $ VBoolean $ a < b
  notAddr <- alloc $ VClosure st.sEnv emptyCache $ \addrA -> do
      a <- getBool addrA
      alloc $ VBoolean $ not a
  andAddr <- alloc $ VClosure st.sEnv emptyCache $ \addrA -> do
      a <- getBool addrA
      st' <- get
      alloc $ VClosure st'.sEnv emptyCache $ \addrB -> do
        b <- getBool addrB
        alloc $ VBoolean $ a && b
  let justNatives = Map.fromList $ map (\(n, a) -> (n, (Val, a))) [
          ("+", plusAddr),
          ("-", minusAddr),
          ("force", forceAddr),
          ("ieq", ieqAddr),
          (">", igtAddr),
          ("<", iltAddr),
          ("and", andAddr),
          ("not", notAddr)
        ]
  modifyCurrentEnv $ \e -> e {bindings = operations <> justNatives <> e.bindings}

-- | Выполнение чанка (игнорируем декларации, просто идём дальше)
evalChunk :: IR.Chunk -> Interp Value
evalChunk chunk = do
  st <- get
  let env0 = st.sEnv

  let functDefs = [fd | IR.SFunctDef fd <- chunk, fd.fName /= "main"]
  forM_ functDefs $ \fd -> do
    let cache = case fst fd.fRet of
          Just fxs -> if isPureClosure fxs then Just IM.empty else Nothing
          _ -> Just IM.empty
    fn <- makeTopLevelClosure fd
    a <- bindValIn env0 fd.fName (VClosure env0 cache fn)
    modify $ \s -> s {sCode = IM.insert (addrToInt a) (CodeFun (map fst $ IR.fArgs fd) (IR.fBlock fd)) s.sCode}

  let mainDecl = findMain chunk
  case mainDecl of
    Nothing -> liftIO (putStrLn "Warning: No 'main' function found") >> pure VNil
    Just (IR.SFunctDef mainFunct) -> do
      resultAddr0 <- evalBlock (IR.fBlock mainFunct) pure
      -- результат main доводится до значения: иначе отложенный хвост (ветка if) не выполнится
      resultAddr <- whnfAddr resultAddr0
      reportEvents (fst $ IR.fRet mainFunct)
      traceEval $ T.unpack $ "evalChunk resultAddr: " <> pretty resultAddr
      derefOr resultAddr
    Just _ -> rtError "'main' is not a function definition"

findMain :: IR.Chunk -> Maybe IR.TopLevelStat
findMain = find $ \case
  (IR.SFunctDef fd) -> fd.fName == "main"
  _ -> False

makeTopLevelClosure :: IR.FunctDecl -> Interp (Address -> Interp Address)
makeTopLevelClosure fd = makeClosureChain (map fst $ IR.fArgs fd) (IR.fBlock fd)

makeClosureChain :: [Text] -> IR.Block -> Interp (Address -> Interp Address)
makeClosureChain [] _ =
  rtError "internal error: a top-level function was declared with no arguments"
makeClosureChain [argName] block = pure $ \argAddr -> do
  oldEnv <- gets sEnv
  eid <- newEnv Env {
      bindings = Map.singleton argName (Val, argAddr),
      parent = Just oldEnv
    }
  modify $ \s -> s {sEnv = eid}
  evalBlock block pure
makeClosureChain (argName:rest) block = do
  restClosure <- makeClosureChain rest block
  pure $ \argAddr -> do
    oldEnv <- gets sEnv
    eid <- newEnv Env {
        bindings = Map.singleton argName (Val, argAddr),
        parent = Just oldEnv
      }
    modify $ \s -> s {sEnv = eid}
    allocClosure eid (Just IM.empty) (CodeFun rest block) restClosure

-- | Замыкание с кодом: код нужен снимку, чтобы переписать функцию (модель: freezeV на замыканиях)
allocClosure :: EnvId -> Maybe (IntMap Address) -> Code -> (Address -> Interp Address) -> Interp Address
allocClosure env cache code fn = do
  a <- alloc (VClosure env cache fn)
  modify $ \s -> s {sCode = IM.insert (addrToInt a) code s.sCode}
  pure a

-- | Run an action as if the interpreter stood at this node, so that a runtime
--   error raised inside it points at the right place.  The previous position is
--   restored afterwards: the caller is still evaluating its own node.
atSpan :: Span -> Interp a -> Interp a
atSpan sp action = do
  old <- gets sSpan
  modify $ \s -> s {sSpan = sp}
  result <- action
  modify $ \s -> s {sSpan = old}
  pure result

-- | Выполнение выражения
evalExpr :: TypedExpr -> (Address -> Interp Address) -> Interp Address
evalExpr expr cont = atSpan (teSpan expr) $ case expr of
    TEInt i -> do
      traceEval $ "evalExpr [TEInt] | " <> show i
      cont =<< alloc (VInt i)
    TEFloat f -> do
      traceEval $ "evalExpr [TEFloat] | " <> show f
      cont =<< alloc (VFloat f)
    TEBoolean b -> do
      traceEval $ "evalExpr [TEBoolean] | " <> show b
      cont =<< alloc (VBoolean b)
    TEString s -> do
      traceEval $ "evalExpr [TEString] | " <> T.unpack s
      cont =<< alloc (VString s)
    TENil -> do
      traceEval $ "evalExpr [TENil]"
      cont =<< alloc VNil
    TEXVar n _ -> do
      traceEval $ "evalExpr [TEXVar] | " <> T.unpack n
      env <- gets sEnv
      (_, m, a) <- findBindingEnv env n
      when (m == Var) $ logEvent EvRead
      cont a
    TEArray _ xs -> do
      traceEval $ "evalExpr [TEArray] | [" <> T.unpack (T.intercalate ", " $ map pretty xs) <> "]"
      st <- get
      xs' <- mapM (\x -> alloc $ VThunk x st.sEnv) xs
      cont =<< alloc (VArray xs')
    TEPair l r -> do
      env <- gets sEnv
      traceEval $ "evalExpr [TEPair] | l: " <> T.unpack (pretty l) <> ", r: " <> T.unpack (pretty r)
      l' <- alloc $ VThunk l env
      r' <- alloc $ VThunk r env
      cont =<< alloc (VPair l' r')
    TEXLambda lam -> do
      env <- gets sEnv
      traceEval $ "evalExpr [TEXLambda] | " <> T.unpack (pretty lam)
      body <- evalLambda env lam
      let cache = if isPureClosure lam.lFxs then Just IM.empty else Nothing
      cont =<< allocClosure env cache (CodeLam lam) body
    TENLambda _ -> rtError "native lambdas are not implemented in the interpreter"
    TEApply f x -> do
      traceEval $ "evalExpr [TEApply] | f: " <> T.unpack (pretty f) <> ", x: " <> T.unpack (pretty x)
      fAddr <- force =<< evalExpr f pure
      xAddr <- delayArg x
      v <- derefOr fAddr
      case v of
        VClosure env' (Just cache) clos -> do
          noMemo <- gets sNoMemo
          case (if noMemo then Nothing else IM.lookup (addrToInt xAddr) cache) of
            Just cached -> do
              traceEval $ concat [
                  "evalExpr [TEApply] | fAddr: ",
                  T.unpack $ pretty fAddr,
                  ", xAddr: ",
                  T.unpack $ pretty xAddr,
                  ", don't need to eval: xAddr is cached"
                ]
              pure cached
            _ -> do
              oldEnv <- gets sEnv
              modify $ \s -> s {sEnv = env'}
              result <- clos xAddr
              modify $ \s -> s {sEnv = oldEnv}
              let newCache = IM.insert (addrToInt xAddr) result cache
              modify $ \s -> s {sHeap = IM.insert (addrToInt fAddr) (VClosure env' (Just newCache) clos) s.sHeap}
              pure result
        VClosure env' _ clos -> do
          oldEnv <- gets sEnv
          modify $ \s -> s {sEnv = env'}
          result <- clos xAddr
          modify $ \s -> s {sEnv = oldEnv}
          pure result
        _ -> rtError $ "the left side of an application is not a function: it is " <> describe v
    TERecord _ ps -> do
      st <- get
      when (any (\p -> p.terMut == Var) ps) $ logEvent EvCreate
      triples <- mapM (\p -> (p.terMut, p.terName, ) <$> alloc (VThunk p.terExpr st.sEnv)) ps
      eid <- newEnv Env {
        bindings = Map.fromList [(n, (m, a)) | (m, n, a) <- triples],
        parent = Nothing
      }
      cont =<< alloc (VRecord eid)
    TEPropAccess r x -> do
      rAddr <- whnf =<< evalExpr r pure
      v <- derefOr rAddr
      case v of
        VRecord eid -> do
          env <- getEnv eid
          case getCell env x of
            Just (m, a) -> do
              when (m == Var) $ logEvent EvRead
              cont a
            Nothing -> rtError $ "this record has no field `" <> x <> "`"
        _ -> rtError $ "cannot read the field `" <> x <> "` of " <> describe v <> "; only records have fields"
    TEHandle (IR.Handler fx b clauses thenLam) _ -> do
      env <- gets sEnv
      thenFn <- evalLambda env thenLam
      kstack0 <- gets sKstack
      callCC $ \finish -> do
        let finishWithThen result = do
              traceEval $ "running then"
              -- обработчик снимается до then: эффекты в then обрабатывает внешний обработчик
              modify $ \s -> s {sKstack = kstack0}
              thenResult <- thenFn result
              modify $ \s -> s {sEnv = env}
              finish thenResult
        let clausesMap = Map.fromList $ map (makeClause finishWithThen) clauses
            handler = HandlerFrame fx clausesMap finishWithThen
        -- операции эффекта живут в собственном окружении, а не в текущем
        opsEnv <- newEnv Env {bindings = Map.empty, parent = Just env}
        forM_ clauses $ \(name, _, _, arity) -> do
          fn <- makeEffectClosure opsEnv arity fx name
          void $ bindValIn opsEnv name (VClosure opsEnv (Just IM.empty) fn)
        modify $ \s -> s {sEnv = opsEnv, sKstack = handler : s.sKstack}
        result <- evalBlock b pure
        finishWithThen result
    p@(TEParen _) -> do
      env <- gets sEnv
      cont =<< alloc (VThunk p env)
    TEResume t _ -> do
      -- resume живёт в окружении клаузы, а вызов идёт в его потомке: ищем по цепочке
      env <- gets sEnv
      rAddr <- lookupRef env "resume"
      rVal <- derefOr rAddr
      case rVal of
        VClosure _ _ clos -> do
          tAddr <- evalExpr t pure
          clos tAddr
        _ -> rtError "`resume` is not a continuation here; it may only be used inside a handler clause"
    TELet pat bound body -> do
      addr <- evalExpr bound pure
      bindings' <- matchPattern pat addr
      -- модель: let открывает область; привязки паттерна не выходят за тело
      outer <- gets sEnv
      letEnv <- newEnv Env {
        bindings = Map.fromList [(n, (m, a)) | (n, m, a) <- bindings'],
        parent = Just outer
      }
      modify $ \s -> s {sEnv = letEnv}
      result <- evalExpr body pure
      modify $ \s -> s {sEnv = outer}
      cont result
    TEIfElse cond thenExpr elseExpr -> do
      condVal <- forceValue =<< evalExpr cond pure
      env <- gets sEnv
      case condVal of
        VBoolean True -> cont =<< alloc (VThunk thenExpr env)
        VBoolean False -> cont =<< alloc (VThunk elseExpr env)
        _ -> rtError $ "the condition of an `if` must be a Boolean, but this one is " <> describe condVal

-- | Приводит VThunk к значению и возвращает его адрес
force :: Address -> Interp Address
force addr = do
  heap <- gets sHeap
  case deref heap addr of
    Just (VThunk expr env') -> do
      traceEval $ "force | Forcing " <> T.unpack (pretty addr) <> ": " <> show expr
      oldEnv <- gets sEnv
      modify $ \s -> s {sEnv = env'}
      resultAddr <- case expr of
        TEParen b -> evalBlock b pure
        _ -> evalExpr expr pure
      traceEval $ "force | resultAddr: " <> T.unpack (pretty resultAddr)
      resultAddr' <- force resultAddr
      traceEval $ "force | resultAddr': " <> T.unpack (pretty resultAddr')
      resultVal <- derefOr resultAddr'
      traceEval $ "force | resultVal: " <> T.unpack (pretty resultVal)
      modify $ \s -> s {sEnv = oldEnv, sHeap = IM.insert (addrToInt addr) resultVal s.sHeap}
      pure addr  -- возвращаем тот же адрес, но теперь там значение
    Just (VArray es) -> do
      mapM_ force es
      pure addr
    Just (VPair l r) -> do
      _ <- force l
      _ <- force r
      pure addr
    Just (VRecord eid) -> do
      _ <- go eid
      pure addr
      where
        go :: EnvId -> Interp EnvId
        go eid' = do
          env <- getEnv eid'
          forM_ (Map.elems env.bindings) $ force . snd
          case env.parent of
            Just p -> go p
            _ -> pure eid'
    Just _ -> do
      traceEval $ "force | No need to force " <> T.unpack (pretty addr)
      pure addr
    Nothing -> undead addr

-- | Слабая головная нормальная форма (модель: S-Expr, E-Prop): thunk вычисляется до
--   значения, компоненты записей, массивов и пар остаются ленивыми (в отличие от force)
whnf :: Address -> Interp Address
whnf addr = do
  heap <- gets sHeap
  case deref heap addr of
    Just (VThunk expr env') -> do
      oldEnv <- gets sEnv
      modify $ \s -> s {sEnv = env'}
      resultAddr <- case expr of
        TEParen b -> evalBlock b pure
        _ -> evalExpr expr pure
      resultAddr' <- whnf resultAddr
      resultVal <- derefOr resultAddr'
      modify $ \s -> s {sEnv = oldEnv, sHeap = IM.insert (addrToInt addr) resultVal s.sHeap}
      pure addr
    Just _ -> pure addr
    Nothing -> undead addr

-- | Приводит VThunk к значению и возвращает само значение
forceValue :: Address -> Interp Value
forceValue addr = do
  st <- get
  case deref st.sHeap addr of
    Just (VThunk expr env') -> do
      traceEval $ "forceValue | Forcing " <> T.unpack (pretty addr) <> ": " <> show expr
      oldEnv <- gets sEnv
      modify $ \s -> s {sEnv = env'}
      resultAddr <- force =<< evalExpr expr pure
      resultVal <- derefOr resultAddr
      modify $ \s -> s {sEnv = oldEnv, sHeap = IM.insert (addrToInt addr) resultVal s.sHeap}
      pure resultVal
    Just v -> do
      traceEval $ "forceValue | No need to force " <> T.unpack (pretty addr)
      pure v
    Nothing -> undead addr

callEffect :: ECons -> Text -> [Address] -> Interp Address
callEffect eff opName args = do
  callCC $ \k -> do
    traceEval $ concat [
        "callEffect: ", show eff, " ", show opName, " with args [", intercalate ", " $ map show args, "]"
      ]
    st <- get
    case find ((== eff) . hEffect) st.sKstack of
      Just handler -> do
        case Map.lookup opName handler.hClauses of
          Just clauseFn -> clauseFn args k
          Nothing -> rtError $ T.concat [
              "the handler for `", effectName eff, "` does not handle `", opName, "`"
            ]
      Nothing -> rtError $ T.concat [
          "there is no handler for the effect `", effectName eff, "` in scope"
        ]

-- | The name of an effect, without its type arguments.
effectName :: ECons -> Text
effectName (ECons n _) = n

evalLambda :: EnvId -> IR.Lambda -> Interp (Address -> Interp Address)
evalLambda eid lam =
  pure $ \addr -> do
    -- модель (E-App): каждый вызов получает собственное окружение с параметром;
    -- окружение замыкания не меняется
    outer <- gets sEnv
    callEnv <- newEnv Env {
        bindings = Map.singleton lam.lArg (Val, addr),
        parent = Just eid
      }
    modify $ \s -> s {sEnv = callEnv}
    result <- evalBlock lam.lBlock pure
    modify $ \s -> s {sEnv = outer}
    pure result

makeEffectClosure ::
  EnvId
  -> Int
  -> ECons
  -> Text
  -> Interp (Address -> Interp Address)
makeEffectClosure env arity eff op =
    go [] arity
  where
    go acc n =
      pure $ \arg -> case n of
        1 -> callEffect eff op $ reverse (arg : acc)
        _ -> alloc . VClosure env (Just IM.empty) =<< go (arg : acc) (n - 1)

makeClause ::
  (Address -> Interp Address)     -- finishWithThen
  -> IR.HandlerClause
  -> (Text, Clause)
makeClause finishWithThen
  (name, lam, hasResume, _) =
    (name, runClause)
  where
    runClause args k = do
      traceEval $ "makeClause: " <> show name <> " called with args " <> show args
      cur <- gets sEnv
      resumeAddr <- alloc $ VClosure cur (Just IM.empty) k

      -- resume живёт в собственном окружении клаузы
      eid <- newEnv Env {
        bindings = Map.singleton "resume" (Val, resumeAddr),
        parent = Just cur
      }

      clos <- evalLambda eid lam
      result <- applyMany clos eid IM.empty args
      modify $ \s -> s {sEnv = cur}

      case hasResume of
        NoResume -> finishWithThen result
        _ -> k result

applyMany :: (Address -> Interp Address) -> EnvId -> IntMap Address -> [Address] -> Interp Address
applyMany clos eid cache args = do
  traceEval $ "applyMany: args = " <> show args
  case args of
    [] -> rtError "internal error: a handler clause was applied to no arguments"
    [x] -> applyClos x clos eid cache
    (x:xs) -> do
      addr <- clos x
      v <- derefOr addr
      case v of
        VClosure eid' (Just cache') next -> applyMany next eid' cache' xs
        VClosure eid' _ next -> applyMany next eid' IM.empty xs
        _ -> rtError $ "a handler clause returned " <> describe v <> " instead of a function"
  where
    applyClos :: Address -> (Address -> Interp Address) -> EnvId -> IntMap Address -> Interp Address
    applyClos xAddr cl eid' cache' =
      case IM.lookup (addrToInt xAddr) cache' of
        Just cached -> do
          traceEval $ T.unpack $ "Don't have to apply many closure: " <> pretty xAddr <> " is cached"
          pure cached
        _ -> do
          traceEval $ T.unpack $ "Apply many closure to " <> pretty xAddr
          oldEnv <- gets sEnv
          modify $ \s -> s {sEnv = eid'}
          result <- cl xAddr
          traceEval $ T.unpack $ "Apply many result address: " <> pretty result
          modify $ \s -> s {sEnv = oldEnv}
          pure result

evalBlock :: Block -> (Address -> Interp Address) -> Interp Address
evalBlock (sts, expr) cont = do
  -- модель (E-Block): привязки блока видны только внутри него
  outer <- gets sEnv
  forM_ sts evalStat
  result <- evalExpr expr pure
  modify $ \s -> s {sEnv = outer}
  cont result

-- | Новое окружение для остатка блока: одна привязка поверх текущего
--  (модель: S-Val/Var/Imm). Ранее созданные замыкания и thunk'и остаются
--  в прежнем окружении и поэтому не видят новую привязку.
extendEnv :: Text -> Mutability -> Address -> Interp EnvId
extendEnv n m a = do
  cur <- gets sEnv
  eid' <- newEnv Env {
      bindings = Map.singleton n (m, a),
      parent = Just cur
    }
  modify $ \s -> s {sEnv = eid'}
  pure eid'

-- | Аргумент применения откладывается (E-App): атомарные выражения вычисляются
--  сразу, остальные становятся thunk'ом над текущим окружением.
delayArg :: TypedExpr -> Interp Address
delayArg x = case x of
  TEXVar _ _ -> evalExpr x pure
  TEInt _ -> evalExpr x pure
  TEFloat _ -> evalExpr x pure
  TEBoolean _ -> evalExpr x pure
  TEString _ -> evalExpr x pure
  TENil -> evalExpr x pure
  TEXLambda _ -> evalExpr x pure
  _ -> do
    env <- gets sEnv
    alloc (VThunk x env)

-- | Довести отложенное вычисление по адресу до значения (без глубокого форсирования
--  уже вычисленных структур)
whnfAddr :: Address -> Interp Address
whnfAddr = whnf

evalStat :: IR.Stat -> Interp ()
evalStat stat = atSpan (IR.tStatSpan stat) $ case stat of
  IR.Bind m n t -> do
    eid <- gets sEnv
    case m of
      Imm -> void $ bindImm n t
      _ -> do
        -- thunk замкнут на окружение ДО привязки: привязки не рекурсивны
        a <- alloc $ VThunk t eid
        when (m == Var) $ logEvent EvCreate
        void $ extendEnv n m a
  IR.Rebind n t -> do
    env <- gets sEnv
    m <- lookupMut env n
    case m of
      Var -> void $ rebind n t
      _ -> rtError $ T.concat [
          "cannot assign to `", n, "`: it is bound with `", pretty m, "`"
        ]
  IR.Expr t -> do
    -- модель (S-Expr): оператор-выражение вычисляется до слабой головной нормальной формы;
    -- иначе эффекты в отложенных ветках if и в скобках (...) никогда не выполнятся
    a <- evalExpr t pure
    void $ whnfAddr a

-- | Поиск привязки без ошибки (по цепочке родителей)
findBindingMaybe :: EnvId -> Text -> Interp (Maybe (Mutability, Address))
findBindingMaybe eid0 name = go Set.empty eid0
  where
    go visited eid
      | Set.member eid visited = pure Nothing
      | otherwise = do
          env <- getEnv eid
          case Map.lookup name env.bindings of
            Just ma -> pure (Just ma)
            Nothing -> maybe (pure Nothing) (go (Set.insert eid visited)) env.parent

-- | Корневое (глобальное) окружение: функции верхнего уровня и встроенные операции
rootEnvOf :: EnvId -> Interp EnvId
rootEnvOf eid = do
  env <- getEnv eid
  maybe (pure eid) rootEnvOf env.parent

-- | Окружение снимка (модель: snapshot): свободные переменные ищутся по всей цепочке
--  окружений, каждая привязка заменяется замороженной копией ячейки; живого родителя нет,
--  кроме глобального окружения.
snapshotEnv :: EnvId -> Set Text -> Interp EnvId
snapshotEnv envId names = do
  root <- rootEnvOf envId
  env <- newEnv Env {
    bindings = Map.empty,
    parent = Just root
  }
  forM_ (Set.toList names) $ \name -> do
    found <- findBindingMaybe envId name
    case found of
      -- имя связано внутри самого выражения
      Nothing -> pure ()
      Just (m, addr) -> do
        when (m == Var) $ logEvent EvSnapRead
        addr' <- freezeCell addr
        void $ modifyEnv env $ \env' -> env' {
          bindings = Map.insert name (freezeMutability m, addr') env'.bindings
        }
  pure env

-- | Свободные переменные кода замыкания
codeFreeVars :: Code -> Set Text
codeFreeVars = \case
  CodeLam lam -> Set.delete lam.lArg (freeVarsBlock lam.lBlock)
  CodeFun args block -> foldr Set.delete (freeVarsBlock block) args

-- | Переписанный код и функция, собранная из него в окружении env'
freezeCode :: EnvId -> Code -> Interp (Code, Address -> Interp Address)
freezeCode env' = \case
  CodeLam lam -> do
    let lam' = freezeLambda lam
    fn <- evalLambda env' lam'
    pure (CodeLam lam', fn)
  CodeFun args block -> do
    let block' = freezeBlock block
    fn <- makeClosureChain args block'
    pure (CodeFun args block', fn)

-- | Замороженная копия ячейки (модель: freezeV). Копирование транзитивно: данные,
--  thunk'и и код замыканий, достижимые по свободным переменным. Общая таблица
--  sFreezeMemo сохраняет разделение и обрывает циклы (рекурсия функций).
freezeCell a = do
  memo <- gets sFreezeMemo
  case IM.lookup (addrToInt a) memo of
    Just a' -> pure a'
    Nothing -> do
      st <- get
      v <- case IM.lookup (addrToInt a) st.sHeap of
        Just v0 -> pure v0
        Nothing -> undead a
      case v of
        VClosure env cache _ ->
          case IM.lookup (addrToInt a) st.sCode of
            Nothing -> share a
            Just code -> do
              a' <- placeholder
              env' <- snapshotEnv env (codeFreeVars code)
              (code', fn') <- freezeCode env' code
              setCell a' (VClosure env' (fmap (const IM.empty) cache) fn')
              modify $ \s -> s {sCode = IM.insert (addrToInt a') code' s.sCode}
              pure a'
        VThunk expr env -> do
          a' <- placeholder
          env' <- snapshotEnv env (freeVars expr)
          setCell a' (VThunk (freeze expr) env')
          pure a'
        VArray as -> do
          a' <- placeholder
          as' <- mapM freezeCell as
          setCell a' (VArray as')
          pure a'
        VPair l r -> do
          a' <- placeholder
          l' <- freezeCell l
          r' <- freezeCell r
          setCell a' (VPair l' r')
          pure a'
        VRecord eid -> do
          a' <- placeholder
          env <- getEnv eid
          bs <- forM (Map.toList env.bindings) $ \(n, (m, x)) -> do
            when (m == Var) $ logEvent EvSnapRead
            x' <- freezeCell x
            pure (n, (freezeMutability m, x'))
          eid' <- newEnv Env {bindings = Map.fromList bs, parent = Nothing}
          setCell a' (VRecord eid')
          pure a'
        _ -> share a
  where
    remember x y = modify $ \s -> s {sFreezeMemo = IM.insert (addrToInt x) y s.sFreezeMemo}
    share x = remember x x >> pure x
    -- placeholder = do
    --   a' <- alloc VBottom
    --   remember a a'
    --   pure a'
    placeholder = do
      st <- get
      let a' = Address st.sNextAddr
      put st {sNextAddr = st.sNextAddr + 1}
      remember a a'
      pure a'
    setCell x val = modify $ \s -> s {sHeap = IM.insert (addrToInt x) val s.sHeap}

-- | Модель (S-Rebind): привязка перенаправляется в том окружении, где она
--  объявлена, на новую ленивую ячейку; правая часть видит старую привязку.
rebind :: Text -> TypedExpr -> Interp Address
rebind x t = do
  e <- gets sEnv
  (ex, m, addr) <- findBindingEnv e x
  case m of
    Var -> do
      rhsEnv <- newEnv Env {
        bindings = Map.singleton x (Var, addr),
        parent = Just e
      }
      addr' <- alloc $ VThunk t rhsEnv
      _ <- modifyEnv ex $ \env -> env {bindings = Map.insert x (Var, addr') env.bindings}
      logEvent EvRebind
      pure addr'
    _ -> rtError $ T.concat [
        "cannot assign to `", x, "`: it is bound with `", pretty m, "`"
      ]

allocIn :: InterpState -> Value -> (InterpState, Address)
allocIn st v =
  let addri = st.sNextAddr
      addr  = Address addri
      heap' = IM.insert (addrToInt addr) v st.sHeap
  in (st {sHeap = heap', sNextAddr = addri + 1}, addr)

-- | Трассировка вычислений: включается переменной окружения MARRAN_TRACE
traceEval :: String -> Interp ()
traceEval msg = do
  on <- gets sTrace
  when on $ liftIO $ putStrLn msg

-- | Запись события мутации (счётчики по видам событий)
logEvent :: Event -> Interp ()
logEvent ev = modify $ \s -> s {sEvents = Map.insertWith (+) ev 1 s.sEvents}

-- | Проверка теоремы об эффектах на выполнении: каждое событие мутации должно быть разрешено
--   объявленным рядом main. Включается переменной MARRAN_CHECK_EVENTS. Открытый ряд не проверяется.
reportEvents :: Maybe EffRow -> Interp ()
reportEvents declared = do
  chk <- liftIO $ isJust <$> lookupEnv "MARRAN_CHECK_EVENTS"
  when chk $ do
    evs <- gets sEvents
    let count e = Map.findWithDefault 0 e evs
        reads' = count EvRead + count EvSnapRead
    liftIO $ putStrLn $ concat [
        "EVENTS: read=", show (count EvRead),
        " snapshot-read=", show (count EvSnapRead),
        " rebind=", show (count EvRebind),
        " create=", show (count EvCreate)
      ]
    case declared of
      Just (RClosed cs) -> do
        let has n = EffCons (Eff.elabel n) `elem` cs
            bad = [ "Read" | reads' > 0, not (has "Read") ]
              <> [ "Rebind" | count EvRebind > 0, not (has "Rebind") ]
              <> [ "Var/Cell" | count EvCreate > 0, not (has "Var" || has "Cell") ]
        liftIO $ putStrLn $
          if null bad then "EVENTS: licensed"
          else "EVENT-VIOLATION: not in the declared row: " <> intercalate ", " bad
      _ -> liftIO $ putStrLn "EVENTS: declared row is open or missing, not checked"

alloc :: Value -> Interp Address
alloc v = do
  st <- get
  let (st', a) = allocIn st v
  put st'
  pure a

bindVal :: Text -> Value -> Interp Address
bindVal x v = do
  eid <- gets sEnv
  bindValIn eid x v

bindValIn :: EnvId -> Text -> Value -> Interp Address
bindValIn e x v = bindValAddrIn e x =<< alloc v

bindValAddrIn :: EnvId -> Text -> Address -> Interp Address
bindValAddrIn e x a = do
  _ <- modifyEnv e $ \env ->
    env {bindings = Map.insert x (Val, a) env.bindings}
  pure a

bindVarIn :: EnvId -> Text -> Value -> Interp Address
bindVarIn e x v = bindVarAddrIn e x =<< alloc v

bindVarAddrIn :: EnvId -> Text -> Address -> Interp Address
bindVarAddrIn e x a = do
  _ <- modifyEnv e $ \env ->
    env {bindings = Map.insert x (Var, a) env.bindings}
  pure a

bindImm :: Text -> TypedExpr -> Interp Address
bindImm name expr = do
  st <- get
  -- общая таблица копий на один снимок: сохраняет разделение и обрывает циклы (рекурсивные функции)
  saved <- gets sFreezeMemo
  modify $ \s -> s {sFreezeMemo = IM.empty}
  frozenEnv <- snapshotEnv st.sEnv (freeVars expr)
  modify $ \s -> s {sFreezeMemo = saved}
  addr <- alloc $ VThunk expr frozenEnv
  _ <- extendEnv name Imm addr
  pure addr

lookupCell :: EnvId -> Text -> Interp (Mutability, Address)
lookupCell eid name = do
  (_, m, a) <- findBindingEnv eid name
  pure (m, a)

lookupRef :: EnvId -> Text -> Interp Address
lookupRef eid name = do
  (_, _, a) <- findBindingEnv eid name
  pure a

lookupMut :: EnvId -> Text -> Interp Mutability
lookupMut e name = do
  (_, m, _) <- findBindingEnv e name
  pure m

freeVars :: TypedExpr -> Set Text
freeVars = \case
  TEXVar n _ -> Set.singleton n
  TEArray _ es -> Set.unions (map freeVars es)
  TEPair l r -> Set.union (freeVars l) (freeVars r)
  TEXLambda lam ->
    let bodyFV = freeVarsBlock lam.lBlock
    in Set.delete lam.lArg bodyFV  -- аргумент связан
  TEApply f x -> Set.union (freeVars f) (freeVars x)
  TERecord _ props -> Set.unions [freeVars (terExpr p) | p <- props]
  TEHandle handler _ -> freeVarsHandler handler
  TEParen b -> freeVarsBlock b
  TEResume e _ -> freeVars e
  TELet pat bound body ->
    let boundFV = freeVars bound
        bodyFV = freeVars body
        -- удаляем имена, связанные в паттерне
        patternVars = letPatternVars pat
    in Set.union boundFV (Set.difference bodyFV patternVars)
  TEPropAccess e _ -> freeVars e
  TEIfElse p t f -> Set.unions [freeVars p, freeVars t, freeVars f]
  _ -> Set.empty

-- | Свободные переменные блока: имена, связанные его операторами, исключаются
--  (привязки последовательны и не рекурсивны).
freeVarsBlock :: IR.Block -> Set.Set Text
freeVarsBlock (stats, expr) = go Set.empty stats
  where
    go bound [] = Set.difference (freeVars expr) bound
    go bound (s : ss) =
      let (fvS, bound') = statFree bound s
      in Set.union fvS (go bound' ss)
    statFree bound = \case
      IR.Bind _ n e -> (Set.difference (freeVars e) bound, Set.insert n bound)
      IR.Rebind n e -> (Set.difference (Set.insert n (freeVars e)) bound, bound)
      IR.Expr e -> (Set.difference (freeVars e) bound, bound)

freeVarsStat :: IR.Stat -> Set.Set Text
freeVarsStat = \case
  IR.Bind _ _ e -> freeVars e
  IR.Rebind _ e -> freeVars e
  IR.Expr e -> freeVars e

freeVarsHandler :: IR.Handler -> Set.Set Text
freeVarsHandler = \case
  IR.Handler _ block clauses thenLam ->
    Set.unions $ [freeVarsBlock block]
    <> map (\(_, l, _, _) -> freeVarsLambda l) clauses
    <> [freeVarsLambda thenLam]

freeVarsLambda :: IR.Lambda -> Set.Set Text
freeVarsLambda lam = freeVarsBlock lam.lBlock

letPatternVars :: LetPattern -> Set.Set Text
letPatternVars = \case
  LPATom alp -> atomLetPatternVars alp
  LPParam (LambdaParam n _) -> Set.singleton n

atomLetPatternVars :: AtomLetPattern -> Set.Set Text
atomLetPatternVars = \case
  ALPPair l r -> Set.union (letPatternVars l) (letPatternVars r)
  ALPRecord props -> Set.unions [maybe Set.empty atomLetPatternVars alp | LetPatternRecordProp _ _ alp <- props]
  _ -> Set.empty

matchPattern :: LetPattern -> Address -> Interp [(Text, Mutability, Address)]
matchPattern pat addr = do
  v <- derefOr addr
  case pat of
    LPATom (ALPUnderscore; ALPNil) -> pure []
    LPATom (ALPPair l r) -> case v of
      VPair addrL addrR -> do
        bindL <- matchPattern l addrL
        bindR <- matchPattern r addrR
        pure (bindL <> bindR)
      _ -> rtError $ "this pattern expects a pair, but the value is " <> describe v
    LPATom (ALPRecord props) -> case v of
      VRecord eid -> do
        env <- getEnv eid
        foldM (\acc (LetPatternRecordProp m (LambdaParam n _) mPat) -> do
            case getRef env n of
              Just fieldAddr -> do
                case mPat of
                  Nothing -> pure $ (n, m, fieldAddr) : acc
                  Just subPat -> do
                    subBindings <- matchPattern (LPATom subPat) fieldAddr
                    pure $ acc <> subBindings
              Nothing -> rtError $ "this pattern names the field `" <> n <> "`, which the record does not have"
          ) [] props
      _ -> rtError $ "this pattern expects a record, but the value is " <> describe v
    LPParam (LambdaParam n _) -> pure [(n, Val, addr)]

isImmutableValue :: Heap -> Value -> Interp Bool
isImmutableValue heap v = evalStateT (go v) IntMap.empty
  where
    go = \case
      VArray addrs -> foldM (\acc a -> (acc &&) <$> checkAddr a ) True addrs
      VPair l r -> (&&) <$> checkAddr l <*> checkAddr r
      VRecord eid -> do
        env <- lift $ getEnv eid
        foldM
          (\acc (mut, addr) ->
            -- `Var` is checked first: a `Var` field is not frozen
            -- even if its target is an ancestor (a cycle).
            if mut == Var
            then pure False
            else (acc &&) <$> checkAddr addr)
          True
          $ Map.elems env.bindings

      VBottom; VThunk{} -> pure False
      _ -> pure True

    checkAddr (Address i) = do
      memo <- get
      case IM.lookup i memo of
        Just b -> pure b
        Nothing -> do
          -- Coinductive assumption: a cycle re-entering `i` sees `True`.
          put (IM.insert i True memo)
          v' <- case IntMap.lookup i heap of
                  Just v0 -> pure v0
                  Nothing -> pure VBottom
          result <- go v'
          modify' (IM.insert i result)
          pure result


isPureClosure :: EffRow -> Bool
isPureClosure (RClosed []) = True
isPureClosure (ROpen [] _) = True  -- открытый ряд без эффектов
isPureClosure _ = False

initialInterpState :: InterpState
initialInterpState = InterpState {
  sEnv        = EnvId 0,
  sEnvs       = Map.empty,
  sHeap       = IM.empty,
  sKstack     = globalHandlers,
  sNextAddr   = 0,
  sNextEnv    = 1,
  sCode       = IM.empty,
  sFreezeMemo = IM.empty,
  sTrace      = False,
  sEvents     = Map.empty,
  sNoMemo     = False,
  sSpan       = noSpan
}

prepareSnapshotBenchmark :: Int -> [(Int, Int)] -> IO (IO (Int, Int, Int))
prepareSnapshotBenchmark rootNode graphEdges = do
  when (rootNode < 0) $
    ioError $ userError "Snapshot graph: negative root node"

  when (any (\(from, to) -> from < 0 || to < 0) graphEdges) $
    ioError $ userError "Snapshot graph: negative node index"

  let allNodes = rootNode : concatMap (\(from, to) -> [from, to]) graphEdges
      nodeCount = maximum allNodes + 1
      adjacency = Map.fromListWith (<>) [(from, [to]) | (from, to) <- graphEdges]

  -- Build the graph exactly once.  Building it cannot legitimately fail, so a
  -- runtime error here is a bug in the interpreter and is raised as an
  -- exception rather than turned into a benchmark result.
  (built, initialState) <-
    runInterp
      (do
        root <- newEnv $ Env Map.empty Nothing
        modify $ \st -> st {sEnv = root}

        -- Allocate all vertices before connecting them.
        -- This allows arbitrary sharing and forward references.
        addresses <- mapM (const $ alloc VBottom) [0 .. nodeCount - 1]
        let addressMap = Map.fromList (zip [0 ..] addresses)

        -- Fill every vertex with its outgoing references.
        forM_ [0 .. nodeCount - 1] $ \node -> do
          let children = Map.findWithDefault [] node adjacency
              childAddresses = map (addressMap Map.!) children
              nodeAddress = addressMap Map.! node
          modify $ \st -> st {
            sHeap = IM.insert (addrToInt nodeAddress) (VArray childAddresses) st.sHeap
          }

        -- Expose the selected root through the root environment.
        let rootAddress = addressMap Map.! rootNode
        _ <- modifyEnv root $ \env -> env {
          bindings = Map.insert "root" (Val, rootAddress) env.bindings
        }
        pure VNil
      )
      initialInterpState

  case built of
    Left err -> ioError $ userError $ T.unpack $ "Snapshot graph: " <> pretty err
    Right _ -> pure ()

  let rootEnv = initialState.sEnv
      initialAddr = initialState.sNextAddr
      initialEnv = initialState.sNextEnv

  -- This action always starts from the same pristine state.
  let runSnapshot = do
        (res, finalState) <-
          runInterp (snapshotEnv rootEnv (Set.singleton "root") >> pure VNil) initialState

        case res of
          Left err -> ioError $ userError $ T.unpack $ "Snapshot traversal: " <> pretty err
          Right _ -> pure ()

        let visited = IM.size finalState.sFreezeMemo
            allocated = finalState.sNextAddr - initialAddr
            allocatedEnvs = finalState.sNextEnv - initialEnv

        -- Force all statistics before returning.
        _ <- evaluate (visited + allocated + allocatedEnvs)

        pure (visited, allocated, allocatedEnvs)

  pure runSnapshot