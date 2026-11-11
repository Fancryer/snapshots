# marr

A Lean 4 development that accompanies the paper *Environment Snapshots in
Mårran: Taming Mutation under Non-Strict Evaluation*.

## Scope

The development defines the term, statement and block syntax of the core, the
mutation markers `val` / `var` / `imm`, the rewrite `freeze` on terms,
statements and blocks, the predicates that a term (statement, block) is frozen,
the bound and free names, and it **proves**:

| Theorem | Statement |
| --- | --- |
| `frozen_freeze`, `frozen_freezeTerms`, `frozen_freezeFields`, `frozen_freezeStmt`, `frozen_freezeStmts`, `frozen_freezeBlock` | `freeze` always yields a frozen object |
| `frozen_freeze_id` (and the variants for terms, fields, statements, blocks) | `freeze` is the identity on frozen objects, hence idempotent |
| `bindingsOf_freezeStmt` | freezing preserves the set of bound names |
| `frozen_fv_subset` (via `frozen_fv_aux` and its variants) | `fv (freeze t) ⊆ fv t` |

These are exactly the syntactic facts used by the paper's freeze-typing and
snapshot lemmas.

## What is *not* here

The isolation theorem, preservation, effect soundness, the consistency
invariant, the operational lemmas and referential transparency are proved on
paper (Appendix A of the paper) and are **not** mechanised. Nothing in this
development models the interpreter or the dynamic behaviour of a snapshot.

## Building

```
lake build
```

The build was checked with `leanprover/lean4:v4.36.0-rc2` (see
`lean-toolchain`); the only axiom used by the checked facts is `propext`.
