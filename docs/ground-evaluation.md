# Ground evaluation

The primitive `compute` rule proves an equality between two closed terms by
normalizing both sides with the kernel's ground evaluator and comparing the
normal forms. This document describes what that evaluator does and what it
places inside the trusted boundary.

## Exact arithmetic

The exact integer engine is native JavaScript `BigInt`. It has arbitrary
precision and runs in Node and the browser without a platform GMP
dependency. Natural literals are stored as big integers; `zero` and `succ`
fold into them.

The evaluator unfolds only the definitions named in a certificate's
allow-list, records which definitions it used, and rejects a certificate
whose list does not match. It recognizes the admitted equations of `add`, `mul`, `factorial`, `equalNat`, natural
`less`, and truncated `minus`, including their helper definitions, and
executes them as direct `BigInt` operations. The recognizer checks the
equation bodies and the permitted definition list on each evaluation; a near
miss falls back to the general equation interpreter. The independent Python,
OCaml, and Rust checkers implement the same guarded reductions, and all of
them recognize the helper definitions by their canonical names, such as
`Grace.Core.Nat.Rec.predecessor`.

## Ground rational equality

The `rationalClassCompute` proof rule checks equality of two ground quotient
rational representatives using native `BigInt` cross products. It requires the
proved `rationalClass.eq` criterion with its exact statement, positive ground
denominators, and the admitted natural addition and multiplication equations.
The G17M instruction has no auxiliary data; the TypeScript, Python, OCaml, and Rust
checkers each recompute the equality, and positive and negative conformance
vectors cover the opcode. A theorem comparing two 30-digit rational
representatives is one proof instruction. The checked theorem
`sameValue.quotient_iff` supplies the set-theoretic interpretation of that
Boolean decision when the denominators are nonzero.

## Trust boundary

The trusted part is compact-literal canonicalization, the closed-value
equation interpreter, its arithmetic schema recognizers, host `BigInt`
equality and arithmetic, the ground rational equality check, and the
comparison of normal forms. Running out of fuel or host resources rejects
the certificate.

Tactics, rewrite search, direct `eval` results, the compiler, and every
computation service outside the kernel are untrusted. A direct evaluation
returns a value; it does not admit a theorem.

## Fast exact linear algebra

`src/rational-matrix.ts` is a separate computation service, outside the
trusted boundary. It exposes canonical signed `BigInt` fractions with
positive denominators and Euclidean gcd reduction, conversions to and from
the Cumulus `RationalCell` fields, exact row reduction, a pivot list, and
replayable row-operation steps.

There is no certificate for a whole matrix reduction. That would need
solution-preservation theorems and a checked link from the normalized
executor to its row-operation certificate. `RationalCell.fraction` cannot be
normalized in place, because its constructor is injective as a set-encoded
datatype while quotient rationals identify many fraction triples. The
`meaning`, `sameValue.quotient_iff`, and arithmetic soundness theorems
provide the bridge for an explicit canonical-rational layer, and row scaling
and add-multiple have generic entrywise quotient interpretation lemmas.
Source-level matrix `compute` proofs over uncancelled representatives remain
slow for larger dimensions because `RationalCell` arithmetic does not cancel
common factors.
