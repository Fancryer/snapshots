# Diagnostics

Every error the front end reports is rendered in the style of Rust's
diagnostics: a header line with a stable code, the location, the offending
line with a caret run under the region the error is about, and the chain of
expressions the checker passed through as notes.

```
error[E0003]: cannot unify the type `Boolean` with the type `Int`
 --> app/marr/x.marr:2:9
  |
2 |   sayn (+ true 1)
  |         ^^^^^^^
  |
  = + true
  = + true 1
  = (+ true 1) at app/marr/x.marr:2:8
  = sayn (+ true 1) at app/marr/x.marr:2:3
```

Notes are the innermost frames first, adjacent duplicates are collapsed, and
a stack longer than six frames ends with `... N more`. The location of the
frame that is already shown as the primary label is omitted from its note.
A note that is a message rather than a frame (a `did you mean` hint, see below)
is never capped, never merged with its neighbours, and comes after the trace.

Positions are attached by the parser and carried through every stage: the
declarations (`Ast.TopLevelStat`, `Types.TopLevelStat`), the AST
(`Ast.Exp`, `Ast.BlockStat`), the IR (`Types.Expr`, `Types.Stat`) and the
typed IR (`TypedIR.TypedExpr`, `TypedIR.Stat`) all record the region of source
they came from. `test/SpanSpec.hs` walks every example program and fails if any
declaration, node or statement lost its span, so a forgotten position in the
parser is a test failure rather than a diagnostic without a location.

## Syntax errors

The lexer and the grammar report failures through Megaparsec. `Parser.hs`
converts the first error of a bundle into the same `Diagnostic` value the
checker uses: `reachOffset` turns the reported offset into a line and column,
and the rendering of the offending token gives the caret run its width, so a
three-letter token gets three carets rather than one.

```
error[E0013]: unexpected `sayn`
 --> app/marr/bad.marr:2:3
  |
2 |   sayn 1
  |   ^^^^
  |
```

At the end of a line the message names what the grammar would have accepted
there, capped at four alternatives so that a parser with many branches does
not produce a wall of text. End of input is reported as such instead of as an
empty token. `test/ParserSpec.hs` pins the header, the position and the
carets.

## Suggestions

An unknown name is often a typo, so the checker looks for a name that is close
to the one it could not resolve and appends a note when it finds one:

```
error[E0007]: `coutner` is not in scope
 --> app/marr/x.marr:3:8
  |
3 |   sayn coutner
  |        ^^^^^^^
  |
  = coutner
  = sayn coutner at app/marr/x.marr:3:3
  = did you mean `counter`?
```

The distance is the optimal string alignment distance: insertions, deletions,
substitutions and transpositions of adjacent characters, where a transposition
counts as one edit (`lenght` → `length` is one, not two). A candidate is
offered when its distance is at most `max 1 (length / 3)`, so a typo in a long
identifier may be further away than one in a short one.

The note is deliberately quiet:

- nothing is suggested when the nearest candidate is beyond the threshold;
- nothing is suggested when two candidates are equally close, because picking
  one of them by the order of a `Map` would teach the wrong name;
- the name itself is never suggested.

Suggestions are produced for four kinds of mistake:

| Where | Candidates |
|-------|-----------|
| a value (`E0007`) | every binding visible from the current scope, walking `parent` |
| a record field (`E0015`) | the fields of the record being projected |
| a type alias name | the declared aliases plus the built-in type names |
| a row alias name | the declared rows |

The first two keep the name and add a note. The last two cannot: an unknown
type or row name has no sensible meaning, so it is rejected at elaboration,
with the hint in the message itself:

```
error: unknown type 'Prise'; did you mean `Price`?
error: Unknown row alias: Mutatoin; did you mean `Mutation`?
```

The threshold there is stricter, because a program may legitimately name a type
that it does not declare (an opaque `TFlat`). A name is reported only when it is
at least four characters long, exactly one edit from a known name, and that name
is the unique candidate at that distance; `Prise` next to `Price` is a typo,
while `Foo` next to `Food` is left alone and stays opaque. A name that is not
close to anything also stays opaque and fails later at unification.

## Codes

| Code  | Meaning |
|-------|---------|
| E0001 | an internal type error; reaching the user means a gap in the checker |
| E0002 | a type-argument error |
| E0003 | two types cannot be unified |
| E0004 | two type arguments cannot be unified |
| E0005 | two effect rows cannot be unified, or the body performs effects the signature does not declare |
| E0006 | two effects cannot be unified |
| E0007 | a name is not in scope |
| E0008 | assignment to a `val` or `imm` binding |
| E0009 | a binding shadows another binding in the same scope |
| E0010 | a handler-related effect error, such as `resume` outside a handler clause |
| E0011 | a handler clause resumes more than once |
| E0012 | an unimplemented construct reached the checker |
| E0013 | a syntax error reported by the lexer or the grammar |
| E0014 | a duplicate definition (a function, an effect, or a handler clause) |
| E0015 | a record error (an unknown field, a non-record base, a field whose mutability changes) |
| E0016 | a handler error (an operation the effect does not declare, a missing or repeated clause) |
| E0017 | an application or arity error (`with` arguments, an effect parameter list, a non-function head) |
| E0018 | an inference limitation (an occurs check, an escaping rigid variable, a binding that cannot be generalised) |

Errors raised by the elaborator (the phase between the parser and the type
checker) carry a message but no code: they are about the shape of the program
rather than about types. They still go through the same renderer, and their
`Show` instance prints the user-facing message instead of a constructor.
