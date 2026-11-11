# Changelog for `Mårran`

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to the
[Haskell Package Versioning Policy](https://pvp.haskell.org/).

## 0.1.0.0 - YYYY-MM-DD

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