# Mårran

Mårran is an experimental statically typed programming language exploring the interaction between non-strict evaluation, controlled mutation, and algebraic effects.

Instead of restricting aliasing through ownership or linear types, Mårran introduces environment snapshot semantics via the imm binding qualifier. Mutation affects bindings rather than values, while lazy evaluation remains explicit and effect-aware.

The language combines:

- demand-driven evaluation with explicit forcing
- environment-based mutation semantics
- row-polymorphic algebraic effects
- higher-rank polymorphism
- elaboration into a typed intermediate representation

Mårran investigates whether environment freezing can serve as a semantic alternative to ownership systems in non-strict functional languages.

## Building and testing

The project is a Stack project and needs GHC 9.12.4 (see `stack.yaml`).

```
stack build          # library and the marran-exe driver
stack test           # unit tests and the example programs of the paper
```

`stack test` runs two things: the Hspec suites for unification,
generalisation and freezing, and every example program under `app/marr`.
The programs are elaborated, type-checked and interpreted with the mutation
event check enabled; each one is compared against its expected output, and
`app/marr/imm_needs_read.marr` must be rejected by the type checker. A
failure fails the test suite.

The executable runs the same examples by hand:

```
stack exec marran-exe                    # run the examples
stack exec marran-exe -- --run NAME      # run one program
stack exec marran-exe -- --bench --csv bench.csv
                                         # the graphs of Table 2
stack exec marran-exe -- --bench-edges --csv bench_edges.csv
                                         # the wider edge sweep
```

## Layout

- `src/` — the implementation: lexer, parser, elaborator, type-and-effect
  inference (`Infer`, `Unify`, `Scope`, `Types`, `TypedIR`), the interpreter
  (`IntInterpreter`), the benchmark harness and the test driver (`Suite`).
- `app/` — the executable (`Main.hs`) and the example programs (`app/marr`).
- `test/` — the Hspec suites.
- `prover/marr/` — a Lean 4 development that checks the syntactic facts about
  `freeze` used by the paper (that `freeze` yields frozen terms, is the
  identity on them, preserves bound names and does not add free variables).
  The metatheory of the paper is proved on paper, not in Lean.

## Acknowledgment

Work on the language, its implementation and the paper on environment
snapshots was done with the help of an AI assistant, as described in the
paper's AI-use statement.
