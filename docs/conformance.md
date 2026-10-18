# G17M conformance corpus

The `conformance/` directory is the executable compatibility contract for
Grace17 proof-machine checkers. It is language-neutral: a checker needs only
the files in that directory and the rules in `kernel-format.md`.

Version 1 contains 66 authenticated G17M v4 tapes:

- 30 accepted tapes, one whose proof uses each opcode from 0 through 29;
- 30 rejected tapes, one per opcode with a false claimed conclusion;
- a universal-introduction attack whose eigenvariable is hidden beneath a
  sibling binder in the context;
- datatype-induction attacks whose constructor field collides with the open
  motive or a datatype parameter term;
- a computation tape with an inexact definition dependency list;
- open standalone-root and linked-theorem export attacks.

`manifest.json` records the expected result, rule, invariant, relative path,
and SHA-256 checksum of every tape. It also authenticates the shared
`environment.g17env` and records its logical environment digest. Checkers must
fail closed on unknown manifest or G17M versions, checksum mismatches,
environment mismatches, malformed files, and unexpected acceptance or
rejection.

## Running the corpus

The TypeScript implementation:

```sh
npm run conformance
```

The dependency-free Python implementation:

```sh
npm run conformance:python
```

The Python command does not execute Node or import the TypeScript kernel. It
parses the manifest, environment, and certificate bytes independently.

To regenerate the checked-in corpus from the named-AST fixture:

```sh
npm run conformance:generate
```

Generation is not part of checking. An external implementation consumes the
checked-in bytes and never runs the generator. After regenerating, run both
checkers and review the manifest changes.

## What conformance means

Passing this corpus is necessary but not sufficient for being a sound Grace17
checker. It detects disagreement on the present vectors; it cannot prove that
an implementation rejects every invalid tape. The normative definition remains
`kernel-format.md`, including all arena, binding, context, freshness,
environment, computation, and resource-limit requirements.

The corpus environment contains simple local axioms so that each primitive
inference can be isolated. Those axioms are inputs to the tests; they are no
part of Grace17's foundational theory.

Future corpus versions should add a focused negative vector for every distinct
side condition, malformed binary encoding, environment event, and computation
schema. Existing vector IDs and bytes should remain stable within a corpus
version so checker authors can diagnose regressions.

## OCaml and Rust implementations

`npm run build:rust` builds the Rust checkers and runs their unit tests, and
`npm run conformance:rust` checks all 66 vectors with the Rust checker: 30
accepted and 36 rejected, with no unsupported opcodes, plus three
authentication mutations. `npm run test:rust` runs both after a build, and
`npm run check:g17c:rust` replays the exported library; see
`checkers/rust/README.md`.

`npm run build:ocaml` builds the independent OCaml checkers and runs support
tests. `npm run conformance:ocaml` checks all 66 vectors: 30 accepted and 36
rejected, with no unsupported opcodes. `npm run test:ocaml` also checks
computation examples and declaration obligations. Use
`npm run test:ocaml:cumulus` for fresh complete-library export and replay.
See `checkers/ocaml/README.md` for scope and the distinction between a supplied
G17M environment and independently reconstructed G17C declarations.
