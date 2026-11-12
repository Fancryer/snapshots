# Changelog for `Mårran`

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to the
[Haskell Package Versioning Policy](https://pvp.haskell.org/).

## 0.1.0.1 - 2026-11-12

- Spans at the AST, IR and TypedIR levels (`src/Span.hs`); every node parsed
  from source carries a position, and `SpanSpec` checks that every example
  program is fully spanned.
- Diagnostics in the Rust style: `error[CODE]: message`, a `--> file:line:col`
  header, a gutter with the offending source line and carets, and `= note`
  lines for the frame stack. `ErrorContext` renders them; `docs/errors.md`
  documents the format and every code.
- Syntax errors are reported by the same renderer: `Parser` converts
  Megaparsec bundles into `ParseErrorInfo` at the boundary, so an unexpected
  token, keyword or end of input comes out as `E0013` with a caret of the
  right width.
- `E0001` was split by kind: `E0014` duplicate definitions, `E0015` records,
  `E0016` handlers, `E0017` application and arity, `E0018` inference
  limitations. `E0001` now means an internal invariant only.
- The interpreter reports runtime errors through `ExceptT InterpError` instead
  of `error`, so a failed `read_*` or an unreachable binding is a diagnostic
  with a span rather than a crash.
- `Pretty ExprNode` covered neither arrays, records, `with`, `let` nor native
  lambdas, so a diagnostic that mentioned one of them killed the process; all
  five are rendered now.
- A new example, `app/marr/quote.marr`: `imm` freezes a unit price together
  with the code that reads it, so a quote taken before a price change keeps
  the old price while a later `val` sees the new one.
- "Did you mean?" suggestions (`Suggest`): optimal string alignment distance,
  a threshold of `max 1 (length / 3)`, and silence on a tie. They are attached
  to `E0007` for an unknown value, to `E0015` for an unknown record field, and
  to an unknown type or row alias in the elaborator. `SuggestSpec` covers both
  the hits and the cases where nothing must be suggested.
- Top-level declarations carry a span (`Ast.TopLevelStat`,
  `Types.TopLevelStat`), so `E0014` for a function or an effect defined twice
  points at the second declaration instead of printing without a location.
- A suggestion is carried as a message frame on the error stack. The renderer
  prints it after the trace, uncapped and never merged with a neighbouring
  frame, and the location of a diagnostic comes from the innermost frame that
  actually has one.

## 0.1.0.0 - 2026-11-11

- A single interpreter (`IntInterpreter`); `Interpreter` is a compatibility
  re-export. The heap, the table of copies and the table of code are
  `IntMap`s, and a snapshot is 1.5–3.9 times faster than with `Map`s.
- Freezing of types and effect rows (`freezeTyp`, `freezeRowMutIn`) with
  row-lacks constraints for open rows; generalisation and instantiation carry
  the constraints.
- The executable runs the example programs of the paper and checks their
  output; the same checks are part of `stack test`.
- The unused `--always-strict` and `--forbid-memo` options were removed:
  memoisation of pure closures is always on and there is no strict mode.
- Debug tracing removed from the parser and the type checker.
