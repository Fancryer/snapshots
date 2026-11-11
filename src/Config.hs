{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE LambdaCase #-}

module Config (
  resolveConfig
)
where

import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)
import Data.Map (Map)
import Data.Aeson (
    FromJSON(parseJSON),
    ToJSON(toJSON),
    fieldLabelModifier,
    genericParseJSON,
    defaultOptions,
    genericToJSON, eitherDecode
  )
import Data.Maybe (fromMaybe)
import qualified Data.ByteString.Lazy as BS
-- import Data.Aeson.Types (Parser)
import Options.Applicative (execParser, (<|>), Alternative (many), ReadM, eitherReader, optional, option, Parser, long, metavar, help, strOption, short, value, showDefault, switch, ParserInfo, info, helper, (<**>), fullDesc, progDesc, header, auto, strArgument)
import qualified Data.Map as Map
import Data.Text.Encoding (encodeUtf8)
import Data.Bifunctor (Bifunctor(first))
import Data.Either (fromLeft)
import System.Directory (doesFileExist, getHomeDirectory)
import System.FilePath ((</>))
import Control.Monad (when)
import Text.Read (readMaybe)
import Text.Printf (printf)

data LogLevel = Error | Warning | Info | Debug | Trace
  deriving (Read, Eq, Ord, Enum, Bounded, Generic)

instance Show LogLevel where
  show = \case
    Error -> "error"
    Warning -> "warning"
    Info -> "info"
    Debug -> "debug"
    Trace -> "trace"

instance FromJSON LogLevel
instance ToJSON LogLevel

data OutputFormat = Pretty | Sexp deriving (Generic, Read, Eq)
instance FromJSON OutputFormat
instance ToJSON OutputFormat

instance Show OutputFormat where show = \case Pretty -> "pretty"; Sexp -> "sexp"

data Phase = Lex | Parse | Elaborate | Infer | Interpret
  deriving (Read, Eq, Ord, Enum, Bounded, Generic)

instance FromJSON Phase
instance ToJSON Phase
instance Show Phase where
  show = \case
    Lex -> "lex"
    Parse -> "parse"
    Elaborate -> "elaborate"
    Infer -> "infer"
    Interpret -> "interpret"

data OutputTarget = OutputTarget {otFile :: FilePath, otFormat :: OutputFormat}
  deriving (Show, Generic)

instance FromJSON OutputTarget
instance ToJSON OutputTarget

data Config = Config {
  -- source code file. if not set -> './main.marr'
  cfgInputFile          :: Maybe FilePath,
  -- source code file. if not set -> './'
  cfgOutputDir          :: Maybe FilePath,
    -- Куда и в каком формате (Pretty/Sexp) сохранять результат лексинга
  cfgLexedFile          :: Maybe OutputTarget,
  -- Куда и в каком формате сохранять AST
  cfgParsedFile         :: Maybe OutputTarget,
  -- Куда и в каком формате сохранять IR после элаборации
  cfgElaboratedFile     :: Maybe OutputTarget,
  -- Куда и в каком формате сохранять TypedIR после вывода типов
  cfgInferredFile       :: Maybe OutputTarget,
  -- global logging level (Error, Warning, Info, Debug, Trace)
  cfgLogLevel           :: Maybe LogLevel,
  -- Файл для логов (если не указан → stdout/stderr)
  cfgLogFile            :: Maybe FilePath,
  -- Тонкая настройка логирования для конкретных компонентов
  cfgLoggingRules       :: Map Text Bool,
  -- Отключаемые предупреждения по коду или имени
  cfgOffWarnings        :: [Text],
  -- Показывать прогресс выполнения (текущую фазу, количество шагов и т.д.).
  cfgShowProgress       :: Maybe Bool,
  -- Подавить все не-критические сообщения (работает как `--quiet`). Переопределяет `cfgLogLevel` в `Error`
  cfgQuiet              :: Maybe Bool,
  -- Логировать вызовы эффектов и `resume` (полезно для отладки эффектов)
  cfgMaxRecursionDepth  :: Maybe Int,
  -- Логировать вызовы эффектов и `resume` (полезно для отладки эффектов)
  cfgTraceEffects       :: Maybe Bool,
  -- Имя функции, которая считается точкой входа (по умолчанию `"main"`). Полезно для модульных тестов
  cfgMainFunction       :: Maybe Text,
  -- Остановка после указанной фазы (Lex, Parse, Elaborate, Infer, Interpret)
  cfgRunUntilPhase      :: Maybe Phase,
  -- Аргументы для программы
  cfgArgs               :: [Text]
} deriving (Show, Generic)

instance FromJSON Config where
  parseJSON = genericParseJSON defaultOptions {fieldLabelModifier = drop 3}  -- убираем "cfg"
instance ToJSON Config where
  toJSON = genericToJSON defaultOptions {fieldLabelModifier = drop 3}

defaultConfig :: Config
defaultConfig = Config {
  cfgInputFile          = Just "main.marr",
  cfgOutputDir          = Just "./",
  cfgLexedFile          = Nothing,
  cfgParsedFile         = Nothing,
  cfgElaboratedFile     = Nothing,
  cfgInferredFile       = Nothing,
  cfgLogLevel           = Just Info,
  cfgLogFile            = Nothing,
  cfgLoggingRules       = mempty,
  cfgOffWarnings        = [],
  cfgShowProgress       = Nothing,
  cfgQuiet              = Nothing,
  cfgMaxRecursionDepth  = Nothing,
  cfgTraceEffects       = Nothing,
  cfgMainFunction       = Just $ T.pack "main",
  cfgRunUntilPhase      = Just Interpret,
  cfgArgs               = []
}

findConfigFile :: IO (Maybe FilePath)
findConfigFile = do
  let local = "marr.ilyn"
  exists <- doesFileExist local
  if exists then pure (Just local) else do
    home <- getHomeDirectory
    let homeFile = home </> ".config" </> "marr" </> "marr.ilyn"
    existsHome <- doesFileExist homeFile
    pure $ if existsHome then Just homeFile else Nothing

loadConfig :: Maybe FilePath -> IO Config
loadConfig Nothing = pure defaultConfig
loadConfig (Just path) = do
  content <- BS.readFile path
  either (error . ("Failed to parse config: " <>)) pure (eitherDecode content)

mergeConfig :: Config -> Config -> Config
mergeConfig base override = base {
    cfgInputFile          = override.cfgInputFile         <|> base.cfgInputFile,
    cfgOutputDir          = override.cfgOutputDir         <|> base.cfgOutputDir,
    cfgLexedFile          = override.cfgLexedFile         <|> base.cfgLexedFile,
    cfgParsedFile         = override.cfgParsedFile        <|> base.cfgParsedFile,
    cfgElaboratedFile     = override.cfgElaboratedFile    <|> base.cfgElaboratedFile,
    cfgInferredFile       = override.cfgInferredFile      <|> base.cfgInferredFile,
    cfgLogLevel           = override.cfgLogLevel          <|> base.cfgLogLevel,
    cfgLogFile            = override.cfgLogFile           <|> base.cfgLogFile,
    cfgLoggingRules       = Map.union override.cfgLoggingRules base.cfgLoggingRules,
    cfgOffWarnings        = base.cfgOffWarnings           <> override.cfgOffWarnings,
    cfgShowProgress       = override.cfgShowProgress      <|> base.cfgShowProgress,
    cfgQuiet              = override.cfgQuiet             <|> base.cfgQuiet,
    cfgTraceEffects       = override.cfgTraceEffects      <|> base.cfgTraceEffects,
    cfgMaxRecursionDepth  = override.cfgMaxRecursionDepth <|> base.cfgMaxRecursionDepth,
    cfgRunUntilPhase      = override.cfgRunUntilPhase     <|> base.cfgRunUntilPhase,
    cfgMainFunction       = override.cfgMainFunction      <|> base.cfgMainFunction,
    cfgArgs               = base.cfgArgs                  <> override.cfgArgs
  }

parseLogLevel :: ReadM LogLevel
parseLogLevel = eitherReader $ \s ->
  maybe
    (Left $ printf "Invalid log level: %s. Valid: Error, Warning, Info, Debug, Trace" s)
    Right
    $ readMaybe s

parsePhase :: ReadM Phase
parsePhase = eitherReader $ \s ->
  maybe
    (Left $ printf "Invalid phase: %s. Valid: Lex, Parse, Elaborate, Infer, Interpret" s)
    Right
    $ readMaybe s

parseOutputFormat :: ReadM OutputFormat
parseOutputFormat = eitherReader $ \s ->
  maybe
    (Left $ printf "Invalid format: %s. Valid: Pretty, Sexp" s)
    Right
    $ readMaybe s

parseOutputTarget :: String -> Parser (Maybe OutputTarget)
parseOutputTarget longName = optional $ option parseTarget $
  long longName <>
  metavar "FILE[,FORMAT]" <>
  help (printf "Output %s to FILE in PRETTY or SEXP format" longName)

  where
    parseTarget = eitherReader $ \s ->
      case break (== ',') s of
        (file, ',' : format) ->
          case readMaybe format of
            Just fmt -> Right $ OutputTarget file fmt
            Nothing  -> Left $ printf "Invalid format: %s. Use 'Pretty' or 'Sexp'" format
        (file, _) -> Right $ OutputTarget file Pretty

configParser :: Parser Config
configParser = Config
  <$> optional (strOption
        ( long "input-file"
       <> short 'i'
       <> metavar "FILE"
       <> help "Input source file (default: main.marr)" ))
  <*> optional (strOption 
        ( long "output-dir"
       <> short 'o'
       <> metavar "DIR"
       <> help "Output directory (default: ./)" ))
  <*> parseOutputTarget "lexed-file"
  <*> parseOutputTarget "parsed-file"
  <*> parseOutputTarget "elaborated-file"
  <*> parseOutputTarget "inferred-file"
  {-
  cfgMainFunction       :: Maybe Text,
  cfgRunUntilPhase      :: Maybe Phase,
  cfgArgs               :: [Text]
  -}
  <*> optional (option parseLogLevel
        ( long "log-level"
       <> short 'l'
       <> metavar "LEVEL"
       <> help "Log level: LogError, LogWarning, LogInfo, LogDebug, LogTrace"
       <> value Info
       <> showDefault ))
  <*> optional (strOption
        ( long "log-file"
       <> metavar "FILE"
       <> help "Log file (default: stdout/stderr)" ))
  <*> parseLoggingRules
  <*> parseOffWarnings
  <*> optional (switch
        ( long "show-progress"
       <> help "Show progress" ))
  <*> optional (switch
        ( long "quiet"
       <> short 'q'
       <> help "Suppress all non-critical messages" ))
  <*> optional (option auto
        ( long "max-recursion-depth"
       <> metavar "N"
       <> help "Maximum recursion depth" ))
  <*> optional (switch
        ( long "trace-effects"
       <> help "Trace effects and resume calls" ))
  <*> optional (strOption
        ( long "main-function"
       <> metavar "NAME"
       <> help "Entry point function (default: main)" ))
  <*> optional (option parsePhase
        ( long "run-until"
       <> metavar "PHASE"
       <> help "Stop after phase: Lex, Parse, Elaborate, Infer, Interpret"
       <> value Interpret
       <> showDefault ))
  <*> many (strArgument
        ( metavar "ARGS..."
       <> help "Program arguments" ))

parseLoggingRules :: Parser (Map Text Bool)
parseLoggingRules = Map.fromList <$> many parseRule
  where
    parseRule = option parseRule' $
      long "log-rule" <>
      metavar "COMPONENT=TRUE|FALSE" <>
      help "Enable/disable logging for component"
    
    parseRule' = eitherReader $ \s ->
      case break (== '=') s of
        (key, '=' : val) ->
          case readMaybe val of
            Just bool -> Right (T.pack key, bool)
            Nothing   -> Left $ "Invalid boolean: " <> val
        _ -> Left "Expected COMPONENT=TRUE|FALSE"

parseOffWarnings :: Parser [Text]
parseOffWarnings = many $ strOption $
  long "off-warning" <>
  metavar "CODE" <>
  help "Disable warning by code or name"

configInfo :: ParserInfo Config
configInfo = info (configParser <**> helper)
  ( fullDesc
 <> progDesc "Mårran language interpreter"
 <> header "Mårran - A lazy language with algebraic effects and environment snapshots" )

parseCommandLine :: IO Config
parseCommandLine = execParser configInfo

resolveConfig :: IO Config
resolveConfig = do
  cmdConfig <- parseCommandLine  -- функция с optparse-applicative
  fileConfig <- loadConfig =<< findConfigFile
  pure $ mergeConfig (mergeConfig defaultConfig fileConfig) cmdConfig

-- log :: LogLevel -> Text -> IO ()
-- log level msg = when (level <= currentLevel) $ putStrLn $ "[" ++ show level ++ "] " ++ T.unpack msg

{-
data Config = Config {
  cfgInputFile          :: Maybe FilePath
  cfgOutputDir          :: Maybe FilePath,
  cfgLexedFile          :: Maybe OutputTa
  cfgParsedFile         :: Maybe OutputTarget,
  cfgElaboratedFile     :: Maybe OutputTarget,
  cfgInferredFile       :: Maybe OutputTarget,
  cfgLogLevel           :: Maybe LogLevel,
  cfgLogFile            :: Maybe FilePath,
  cfgLoggingRules       :: Map Text Bool,
  cfgOffWarnings        :: [Text],
  cfgShowProgress       :: Maybe Bool,
  cfgQuiet              :: Maybe Bool,
  cfgMaxRecursionDepth  :: Maybe Int,
  cfgTraceEffects       :: Maybe Bool,
  cfgMainFunction       :: Maybe Text,
  cfgRunUntilPhase      :: Maybe Phase,
  cfgArgs               :: [Text]
} deriving (Show, Generic)

{
  "inputFile": "src/main.marr",
  "outputDir": "build/",
  "lexedFile": {
    "otFile": "lexed.txt",
    "otFormat": "Pretty"
  },
  "parsedFile": {
    "otFile": "parsed.json",
    "otFormat": "Sexp"
  },
  "elaboratedFile": {
    "otFile": "elab.json",
    "otFormat": "Sexp"
  },
  "inferredFile": {
    "otFile": "inferred.json",
    "otFormat": "Sexp"
  },
  "logLevel": "LogDebug",
  "logFile": "logs/marr.log",
  "loggingRules": {
    "Parser": true,
    "TypeChecker": false,
    "CodeGen": true,
    "Optimizer": false
  },
  "offWarnings": [
    "UnusedVar",
    "Shadowing",
    "RedundantImport"
  ],
  "showProgress": true,
  "quiet": false,
  "maxRecursionDepth": 100,
  "traceEffects": true,
  "mainFunction": "myMain",
  "runUntilPhase": "Infer",
  "args": [
    "--verbose",
    "input.dat",
    "--output",
    "result.out"
  ]
}
{
  "inputFile": "src/main.marr",
  "outputDir": "build/",
  "lexedFile": {
    "otFile": "lexed.txt",
    "otFormat": "Pretty"
  },
  "parsedFile": {
    "otFile": "parsed.json",
    "otFormat": "Sexp"
  },
  "elaboratedFile": {
    "otFile": "elab.json",
    "otFormat": "Sexp"
  },
  "inferredFile": {
    "otFile": "inferred.json",
    "otFormat": "Sexp"
  },
  "logLevel": "LogDebug",
  "logFile": "logs/marr.log",
  "loggingRules": {
    "Parser": true,
    "TypeChecker": false,
    "CodeGen": true,
    "Optimizer": false
  },
  "offWarnings": [
    "UnusedVar",
    "Shadowing",
    "RedundantImport"
  ],
  "showProgress": true,
  "quiet": false,
  "maxRecursionDepth": 100,
  "traceEffects": true,
  "mainFunction": "myMain",
  "runUntilPhase": "Infer",
  "args": [
    "--verbose",
    "input.dat",
    "--output",
    "result.out"
  ]
}
-}