# Grace17 foundation contract

Grace17 uses one universe of sets and first-order equality. The proof kernel
knows logic, signatures, definitions, and checked extension events. Executable
values have no separate foundational status.

## Profiles

| Profile | Set axioms | Choice strength |
|---|---|---|
| `ZF` | Extensionality, Empty, Pairing, Union, Power Set, Infinity, Foundation, Separation, Replacement | none |
| `ZFC` | all of `ZF` | choice function for every set-sized family of nonempty sets |
| `ZFG` | all of `ZFC` | additionally, a global selector `choose(A) ∈ A` for nonempty `A` |

The function symbols `empty`, `pair`, `union`, `powerset`, and `omega` choose
the unique witnesses supplied by the corresponding textbook existence axioms.
This Skolemized presentation is convenient for computation and theorem
statements. Their membership laws fix the intended sets extensionally.

## Schemas and definitions

Separation and Replacement cannot be captured by one fixed first-order formula.
Grace17 therefore represents them as audited environment events:

- `defineSubset` accepts parameters, a bounding set, and a formula, checks all
  free variables, and records the resulting membership characterization as a
  `separation` definition;
- `defineReplacement` accepts an arbitrary parameterized relation and checks a
  proof that it is total and single-valued on the chosen set before recording
  its image as a `replacement` definition;
- `reifyUnaryOperation` is optimized sugar for the common executable case and
  supplies graph membership, `functionOn`, and application bridge properties.

The surface notation `{ f(x) | x in A }` is the equality-functional special
case of `defineReplacement`; its totality and uniqueness proof is generated
as a proof term and checked by the same event.

`foundationReport()` exposes the profile, the axiom names, and all admitted
Separation, Replacement, and datatype instances. The environment digest also
commits to the profile and capabilities.

## Sets and computation

`orderedPair(x,y)` is definitionally the Kuratowski set `{{x},{x,y}}`.
`functionOn(f,A,B)` says that `f` is a set of ordered pairs, total and
single-valued on `A`, with range in `B`. `apply(f,x)` is connected to the unique
graph value by `function.apply`.

An executable recursive definition is admitted only after structural or
well-founded decrease checks. On any set-sized domain, Replacement can then
materialize its graph as a set, and the application bridge identifies
graph evaluation with fast computation. Runtime pairs, naturals, and ordinal
notations may use compact native representations, but representation theorems
must connect them to these set objects. Natural literals are a kernel term
representation: canonical decimal `n` is definitionally identified with the
corresponding finite `succ(...succ(zero))` term without materializing that
unary tree.

The injectivity of `orderedPair` is not a foundation axiom. `Grace.Cumulus.Set`
derives it from Pairing, alongside the theorem that an ordered pair of members
of `A` and `B` lies in the Cartesian product `product(A,B)`. Cumulus uses
those results to prove graph functionality and composition laws.

Closed definitional equality is a primitive kernel judgment. A `compute`
certificate contains its two terms and the sorted list of admitted function
definitions it uses. The trusted ground evaluator unfolds only that
allow-list, records what it reduced, rejects missing or unused dependencies,
and accepts only when both normal forms are structurally equal. Its value
domain consists of arbitrary-precision nonnegative `bigint`s and recursively
normalized constructor/application values. Recognizers for the admitted
addition, multiplication, and factorial equation schemas may use host `bigint`
operations; every near-miss definition goes through the general equation
interpreter. The certificate contains no per-reduction proof tree.

The trusted implementation therefore includes compact-literal
canonicalization, the closed-value equation interpreter, its arithmetic
schema recognizers, host `bigint` equality and arithmetic, and the comparison
of ground normal forms. Tactics, rewrite search, direct `eval` results, and
the compiler are untrusted. Fuel and host resource bounds affect availability
only: exhaustion rejects a certificate. This is a larger trusted surface than
explicit reduction proofs would be, which is why independent native or Wasm
reimplementation and differential testing matter.

Portable checking uses two authenticated artifacts. A `.g17env` file contains
the canonical logical environment and its SHA-256 digest. G17M version 4 embeds
that digest in the proof tape's authenticated header. A checker first validates
the environment, then requires the embedded digest to match, then replays the
primitive instructions. The independent Python, OCaml, and Rust checkers implement this
process without importing the TypeScript kernel. Within a linked tape, a
theorem may be cited only after its own boundary has checked, so the finished
environment cannot authorize circular theorem proofs. The protocol is
specified in `kernel-format.md`.

## What remains above the kernel

The foundation is expressive enough for ZF/ZFC mathematics; the library on
top of it is still young. The library constructs bounded Cartesian products,
domains, ranges, relation restrictions, transitive closures, and Replacement
images as sets. Membership induction is derived by applying
the existing set-sized well-founded rule to that closure. It proves that the
Foundation-recursive `rank(x)` is always an ordinal and, after derived ordinal
trichotomy and hierarchy monotonicity, that `x in V(rank(x))`. Hence the full
class equality `CumulativeUniverse = Universe` is checked. Datatype
constructors have explicit tagged Kuratowski representations, but the least-fixed-point/induction principle is still an
audited foundation capability. Its eventual bootstrap must construct the
corresponding least inductive classes (and set carriers when the field domains
are bounded) from Infinity, Separation, Replacement, and intersections.

