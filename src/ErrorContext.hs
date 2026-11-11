{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

module ErrorContext (
  ErrorStack,
  ErrorFrame(..),
  AstFrame(..),
  IrFrame(..),
  TypedIrFrame(..),
  ToErrorText,
  toErrorText,
  withFrame
)
where
import Data.Text (Text)
import Text.Megaparsec (SourcePos(..), MonadParsec, getSourcePos, TraversableStream, mkPos, unPos)
import Types (Typ)
import qualified Data.Text as T
import Text.Printf (printf)
import Utils (pretty)
import Control.Arrow ((>>>))

type ErrorStack = [ErrorFrame]

data AstFrame = AstFrame {afNode :: Text, afSource :: Maybe SourcePos} deriving Show
data IrFrame = IrFrame {ifNode :: Text, ifSource :: Maybe SourcePos} deriving Show
data TypedIrFrame = TypedIrFrame {tifNode :: Text, tifType :: Typ, tifSource :: Maybe SourcePos} deriving Show

data ErrorFrame =
  EFAst AstFrame
  | EFIr IrFrame
  | EFTypedIr TypedIrFrame
  | EFMessage Text
  deriving Show

class ToErrorText a where toErrorText :: a -> Text

data SourceSpan = SourceSpan {
  ssStart :: SourcePos,
  ssEnd   :: SourcePos
} deriving (Eq, Show, Ord)

-- | Пустая позиция (для случаев, когда позиция неизвестна)
emptyPos :: SourcePos
emptyPos = SourcePos "Unknown module" (mkPos 0) (mkPos 0)

instance ToErrorText AstFrame where
  toErrorText (AstFrame n s) =
    maybe n (\p -> n <> " at " <> showPos p) s

instance ToErrorText IrFrame where
  toErrorText (IrFrame n s) =
    maybe n (\p -> n <> " at " <> showPos p) s

instance ToErrorText TypedIrFrame where
  toErrorText (TypedIrFrame n t s) =
    maybe n (\p -> n <> ":" <> pretty t <> " at " <> showPos p) s

instance ToErrorText ErrorFrame where
  toErrorText = \case
    EFAst a     -> "AST: " <> toErrorText a
    EFIr i      -> "IR: " <> toErrorText i
    EFTypedIr t -> "TypedIR: " <> toErrorText t
    EFMessage m -> m

-- | Добавить фрейм в стек
withFrame :: ErrorFrame -> ErrorStack -> (ErrorStack -> ErrorStack) -> ErrorStack
withFrame frame stack = ($ (frame : stack))

-- | Добавить AST фрейм
-- withAstFrame :: Located a -> (a -> Text) -> ErrorStack -> ErrorStack
-- withAstFrame (Located span node) showNode =
--   ((EFAst $ AstFrame (showNode node) (Just span)) :)

-- | Пустой промежуток (для случаев, когда позиция неизвестна)
emptySpan :: SourceSpan
emptySpan = SourceSpan emptyPos emptyPos

-- | Преобразование позиции в читаемый текст
showPos :: SourcePos -> Text
showPos pos =
  let name = sourceName pos
      line = sourceLine pos
      col  = sourceColumn pos
  in if null name
      then T.pack $ printf "line %d, column %d" (unPos line) (unPos col)
      else T.pack $ printf "%s:%d:%d" name (unPos line) (unPos col)

-- | Компактное представление позиции
prettyPos :: SourcePos -> Text
prettyPos pos =
  let name = sourceName pos
      line = unPos $ sourceLine pos
      col  = unPos $ sourceColumn pos
  in if null name
      then T.pack $ show line <> ":" <> show col
      else T.pack $ name <> ":" <> show line <> ":" <> show col

-- | Преобразование промежутка в текст
showSpan :: SourceSpan -> Text
showSpan (SourceSpan start end) =
  let startPos = showPos start
      endPos   = showPos end
  in if startPos == endPos
      then startPos
      else startPos <> " - " <> endPos

-- | Компактное представление промежутка
prettySpan :: SourceSpan -> Text
prettySpan (SourceSpan start end) =
  let startPos = prettyPos start
      endPos   = prettyPos end
  in if startPos == endPos
      then startPos
      else startPos <> " - " <> endPos

-- | Получить промежуток для выражения в парсере
-- Использование: start <- getSourcePos; ... ; end <- getSourcePos; pure $ getSourceSpan start end
getSourceSpan :: SourcePos -> SourcePos -> SourceSpan
getSourceSpan = SourceSpan

-- | Вспомогательная функция для обёртки узла с позицией
withSpan :: (MonadParsec e s m, TraversableStream s) => m a -> m (SourceSpan, a)
withSpan parser = do
  start <- getSourcePos
  result <- parser
  end <- getSourcePos
  pure (SourceSpan start end, result)