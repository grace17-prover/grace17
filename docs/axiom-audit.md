# Axiom audits

An axiom audit lists the assumptions a checked proof uses. Importing a module
that contains Choice does not mean every theorem in it uses Choice.

```sh
node --disable-warning=ExperimentalWarning bin/g17.ts axiom-audit \
  lib/Grace/Cumulus/Set/Choice.g17 \
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

## Large cardinal hypotheses

What the hypotheses mean, with pictures, is in [large cardinals](large-cardinals.md).

Grace17 adds no large cardinal axiom to any foundation. A predicate that
states a large cardinal hypothesis, a sentence or a property of a set, is
registered as one in the module that defines it:

```g17 fragment
register largecardinal TarskiGrothendieck "every set lies in a Grothendieck universe"
register largecardinal Inaccessible "an inaccessible cardinal"
```

A theorem that needs one takes it as a premise, usually as a hypothesis of
its theorem section, and its certificate is a certificate, from the
foundation's axioms, of the implication: the theorem holds in every model
of the foundation in which the hypothesis holds.

The audit reports, as `largeCardinals.reliesOn`, every registered
hypothesis the result relies on, over the whole proof:

- **A premise of the statement.** A sentence such as `TarskiGrothendieck()`
  as a premise, or a property of something the conclusion does not
  mention: `Inaccessible(κ) → φ` with κ not in φ says that φ holds if some
  inaccessible exists. A premise inside another formula, as in
  `(∃ κ, Inaccessible(κ)) → φ`, counts the same way.
- **A lemma that relies on it.** Reliance passes to every theorem whose
  proof uses the lemma, through any number of steps.
- **A lemma about it, used without it.** A lemma with the premise
  `Inaccessible(κ)` whose conclusion mentions κ is a fact about
  inaccessibles, true whether or not any exists. A proof that applies it
  without mentioning the hypothesis anywhere in its own statement (or in
  the definitions of the registered predicates its statement mentions)
  has produced an inaccessible from elsewhere, and relies on one.

Each entry has the `predicate`, its `label` (the registration's words), the
`module` that registers it, and where the reliance starts: `via: "premise"`
with the `path` to the nearest declaration whose statement relies on it, or
`via: "supplied"` with the `path` to the declaration that used the lemma
about it, named in `lemma`. `about` lists the hypotheses the statement is
about and the proof relies on nowhere, such as Williamson's theorem that
every Grothendieck universe is a stage `V(κ)`; `mentions` those that occur
only as what the theorem proves, or on a side of an equivalence, which
rests on neither side.

The classification reads registered predicates only: a premise equivalent
to a large cardinal hypothesis but stated with unregistered predicates is
not recognized as one.

In the Workbench a completed proof whose statement relies on a hypothesis
carries a badge naming it; the audit, on hover and in its panel, states
that the result relies on a large cardinal hypothesis, with the path for
each, whether the reliance comes from the statement or from the proof. The
check result's theorems carry the statement's hypotheses as
`largeCardinals`; the command-line audit prints a line for each.

## ZF checks

The mathematical modules `Int`, `NumberTheory`, `Cardinal`, `Geometry`,
`LinearAlgebra`, `GraphTheory`, the group theory up to Lagrange's and
Sylow's theorems, and the finite combinatorics are checked under ZF by
`tests/zf-library.test.ts` and `npm run compile:zf-library`. Selections in
analysis import `Set.Choice`; uniquely determined values use `defunique`.
