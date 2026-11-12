{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Every node the parser produces must carry a real position.
--
--   Span information is invisible in normal operation: a node that lost its
--   span still type-checks and still runs, and only produces a diagnostic
--   without a location much later.  This test walks the whole AST of every
--   example program and fails on the first node with 'noSpan', so a forgotten
--   'loc'/'locStat' in the parser is caught here instead of in a bug report.
module SpanSpec (spanSpec) where

import Control.Monad (forM_)
import Data.List (isPrefixOf, sort)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (doesDirectoryExist, listDirectory)
import Test.Hspec

import Ast
import Parser (chunk, parseFromTextNamed)
import Span (Span, isNoSpan, spanStartLine)

spanSpec :: Spec
spanSpec = describe "source spans" $ do
  files <- runIO exampleFiles
  forM_ files $ \path ->
    it (path ++ " has a span on every node") $ do
      src <- TIO.readFile path
      case parseFromTextNamed path chunk src of
        Left e -> expectationFailure $ "parse failed: " ++ e
        Right c ->
          let bad = unspannedNodes c
          in if null bad
               then pure ()
               else expectationFailure $
                 "nodes without a position:\n" <> unlines (map show bad)

-- | Where a node without a position was found.
newtype Bad = Bad String

instance Show Bad where
  show (Bad s) = "  " <> s

-- | All the example programs, found relative to whatever directory the test
--   runs in (the repository root under @stack test@).
exampleFiles :: IO [FilePath]
exampleFiles = do
  dirs <- filterM' doesDirectoryExist ["app/marr", "../app/marr", "../../app/marr"]
  case dirs of
    [] -> pure []
    (d:_) -> do
      names <- listDirectory d
      pure $ sort [ d <> "/" <> n | n <- names, ".marr" `isSuffixOf` n ]

isSuffixOf :: String -> String -> Bool
isSuffixOf suf s = reverse suf `isPrefixOf` reverse s

filterM' :: (a -> IO Bool) -> [a] -> IO [a]
filterM' _ [] = pure []
filterM' p (x:xs) = do
  ok <- p x
  rest <- filterM' p xs
  pure (if ok then x : rest else rest)

-- | Walk the AST and collect every node whose span is missing.
--
--   Type-level nodes have no spans yet, so only declarations, expressions and
--   statements are checked; that is where diagnostics are reported from.
unspannedNodes :: Chunk -> [Bad]
unspannedNodes (Chunk stats) = concatMap topLevel stats
  where
    topLevel stat =
      spanCheck ("declaration at line " <> show (spanStartLine (topLevelSpan stat))) (topLevelSpan stat)
        <> case stat of
          FunctDef _ n _ _ _ _ _ b -> prefix ("in funct " <> T.unpack n <> ": ") (walkBlock b)
          _ -> []

prefix :: String -> [Bad] -> [Bad]
prefix p = map (\(Bad s) -> Bad (p <> s))

walkBlock :: Block -> [Bad]
walkBlock (Block sts e) = concatMap walkStat sts <> walkExp e

walkStat :: BlockStat -> [Bad]
walkStat st@(BlockStat sp n) =
  spanCheck ("statement at line " <> show (spanStartLine sp)) sp
    <> case n of
      BExpNode e -> walkExp e
      BBindDefNode b -> walkBindDef b
      BAssignNode (Assign _ e) -> walkExp e

spanCheck :: String -> Span -> [Bad]
spanCheck what sp
  | isNoSpan sp = [Bad (what <> " has no span")]
  | otherwise = []

walkBindDef :: BindDef -> [Bad]
walkBindDef (BindDef _ _ e) = walkExp e

walkExp :: Exp -> [Bad]
walkExp (Exp sp n) = spanCheck (tag n <> " expression") sp <> walkChildren n
  where
    tag = \case
      NName _ -> "name"
      NApply _ _ -> "application"
      NDollar _ _ -> "application ($)"
      NLiteral _ -> "literal"
      NPair _ _ -> "pair"
      NLet _ _ _ -> "let"
      NBacktick _ _ _ -> "infix"
      NPropAccess _ _ -> "property access"
      NIfThenElse _ _ _ -> "if"
      NUnder _ -> "handler"
      NResume _ -> "resume"
      NParen _ -> "parenthesised block"
      NWith _ _ _ -> "with"

walkChildren :: ExpNode -> [Bad]
walkChildren = \case
  NName _ -> []
  NApply f x -> walkExp f <> walkExp x
  NDollar f x -> walkExp f <> walkExp x
  NLiteral l -> walkLiteral l
  NPair l r -> walkExp l <> walkExp r
  NLet _ w b -> walkExp w <> walkExp b
  NBacktick _ l r -> walkExp l <> walkExp r
  NPropAccess e _ -> walkExp e
  NIfThenElse p t f -> walkExp p <> walkExp t <> walkExp f
  NUnder u -> walkUnder u
  NResume e -> walkExp e
  NParen b -> walkBlock b
  NWith e _ _ -> walkExp e

walkLiteral :: Literal -> [Bad]
walkLiteral = \case
  LAtom _ -> []
  LArray (ArrayLiteral entries) -> concatMap entryNode entries
  LLambda (LambdaLiteral _ _ _ b) -> walkBlock b
  LRecord (RecordLiteral anchor props) ->
    maybe [] walkExp anchor <> concatMap walkBindDef props
  where
    entryNode = \case
      AEExp e -> walkExp e
      AEBlock b -> walkBlock b

walkUnder :: Under -> [Bad]
walkUnder (Under _ b clauses _ t) =
  walkBlock b <> concatMap clauseNode clauses <> walkBlock t
  where
    clauseNode (HandlerClause _ _ blk) = walkBlock blk
