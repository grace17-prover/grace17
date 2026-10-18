# Axiom audits

An axiom audit lists the assumptions a checked proof uses. Importing a module
that contains Choice does not mean every theorem in it uses Choice.

```sh
node --disable-warning=ExperimentalWarning bin/g17.ts axiom-audit \
  --module-root lib lib/Grace/Cumulus/Set/Choice.g17 \
  --theorem Grace.Cumulus.Set.Choice.choose.member
```

Add `--json` for structured output, or `--foundation ZF` when loading a
ZF-compatible module. The theorem name is its fully qualified name.

## In the Workbench

Hover over a theorem to see direct/inherited axiom counts and Choice status. Choose
**Open axiom audit** for the full panel, or use the small **Axioms** action
beside QED. That action appears only at a completed, current proof state,
including completion modulo sorries; it stays out of intermediate goal states. Each named axiom expands to its statement and a dependency path.
The panel distinguishes Choice usage, no Choice usage, and an incomplete audit.

Audits run on demand in the worker. Identical requests share their result;
changing any workspace source invalidates that cache. Obsolete hover requests
are discarded. Precompiled dependencies are audited from their verified
proof-machine certificates, without rebuilding source proof trees.

## Meaning of the report

- **Direct**: named axiom nodes in the theorem's own proof certificate.
- **Hereditary**: all named axioms reachable through theorem references,
  definition admission certificates, and special computation/induction rules.
  This set includes the direct axioms. The UI's “inherited” count excludes
  axioms already counted as direct.
- **Paths**: one shortest declaration-dependency path to each named axiom.
  Other routes may exist.
- **Definition/schema mechanisms**: Separation, Replacement, datatypes,
  recursion, and unique description are listed separately, since they are
  kernel mechanisms with logical strength of their own. Unique description
  does not use the axiom of Choice. Natural induction also reports
  `set.infinity.minimal`, which enables its canonical registration.
- **Classical logic**: use of double-negation elimination is reported separately.
- **Unavailable**: any missing proof or admission provenance makes the report
  incomplete. An incomplete CLI audit exits with status 1; it cannot certify
  the absence of Choice. An unknown theorem is an error.

All named axioms are included, including user-supplied axioms and assumptions
introduced by `sorry`. Local hypotheses are discharged by the theorem's
implications and quantifiers, so they are not listed.

The audit reports what the recorded proof used. It does not show that those
assumptions are necessary, and it does not reduce the kernel's schema
mechanisms to a minimal list of ZF axioms. A theorem may have another proof
that uses fewer axioms. An imported choice symbol that occurs in a reflexive
equality need not use the axiom of Choice at all.

## ZF checks

The mathematical modules `Int`, `NumberTheory`, `Cardinal`, `Geometry`,
`LinearAlgebra`, `GraphTheory`, the group theory up to Lagrange's and
Sylow's theorems, and the finite combinatorics are checked under ZF by
`tests/zf-library.test.ts` and `npm run compile:zf-library`. Selections in
analysis import `Set.Choice`; uniquely determined values use `defunique`.
