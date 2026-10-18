# Grace17 foundation bootstrap

The full G17C checker does not accept a serialized kernel environment as its
foundation. It constructs one of the normative `ZF`, `ZFC`, or `ZFG` profiles
directly, checks the bootstrap operations, and authenticates the resulting
logical-environment digest before replaying any library module.

Derived declarations and preloaded theorems therefore stay outside the
external trust boundary.

## Bootstrap stages

The checker performs these stages in order:

1. Install the one-sorted first-order signature and the selected set-theory
   axioms. Separation, Replacement, and inductive definitions are explicit
   profile capabilities whose instances must pass their kernel guards.
2. Install transparent symbols such as `subset`, `singleton`, `union2`,
   `orderedPair`, `relates`, and `functionOn` using the same conservative
   definition checks used for every other module.
3. Register the built-in von Neumann natural-number datatype through a guarded
   metadata operation that adds no proposition.
4. Canonically hash this axiomatic/schema base and seal it as the foundation
   boundary.
5. Replay the separately authenticated `Grace.Bootstrap` G17C certificate. Its
   proof-derived public interface is the first dependency of Cumulus; it is
   no part of the logical foundation.

The stages are fast, but the distinction between them is logical. A
transparent definition available at the sealed boundary is still a
definition. A checked theorem prelude cached at that boundary is still a set
of theorems, and none of its statements becomes an inference rule.

## Foundation inventory

The primitive function signature is `empty/0`, `pair/2`, `union/1`,
`powerset/1`, `omega/0`, `apply/2`, and `epsilon0/0`, plus `choose/1` in ZFG.
Primitive membership is `in/2`. Equality and the logical connectives belong to
the first-order proof language and are outside this signature. `epsilon0.less`
is absent here and first appears in the checked Bootstrap certificate.

The following are the strength-bearing laws. This table uses mathematical
notation; `src/zfg.ts` and the matching constructor in
`checkers/python/g17c_check.py` give the canonical AST spelling whose digest is
normative.

| Name | Law |
| --- | --- |
| `set.empty` | `∀x, x ∉ empty` |
| `set.pairing` | `∀x y z, z ∈ pair(x,y) ↔ (z=x ∨ z=y)` |
| `set.extensionality` | `∀x y, (∀z, z∈x ↔ z∈y) → x=y` |
| `set.union` | `∀A x, x∈union(A) ↔ ∃y, y∈A ∧ x∈y` |
| `set.powerset` | `∀x y, x∈powerset(y) ↔ ∀z, z∈x → z∈y` |
| `set.infinity` | `empty∈omega ∧ ∀n∈omega, n∪{n}∈omega` |
| `set.foundation` | every nonempty set has an ∈-minimal member |
| `function.apply` | application returns the unique value of a total function graph |
| `set.choice` | set-sized choice, in ZFC and ZFG |
| `set.globalChoice` | `A≠empty → choose(A)∈A`, in ZFG |

`empty.membership`, `pair.membership`, `extensionality`,
`powerset.membership`, and `foundation` are compatibility aliases for the
corresponding `set.*` laws. `Grace.Bootstrap` installs them as machine-checked
theorems, so they are not axiom entries. The `nat.zero`, `nat.succ`, and
`nat.omega` bridge laws are likewise checked theorems derived from the
transparent `zero`, `succ`, and `Nat` definitions; the guarded
natural-datatype registration adds no proposition. Bootstrap derives the rest
of the epsilon-zero interface the same way. It proves the cancellation and
injectivity properties of Kuratowski pairs, proves that a pair from two sets
lies in `𝒫(𝒫(A ∪ B))`, defines `epsilon0.less` by
Separation from that bound, and proves `epsilon0.less.membership`. Separation
suffices; no Replacement instance or coordinate projection is needed.

The source of this prelude is under `lib/Grace/Bootstrap/`. It is elaborated
in the fixed order `Aliases`, `Nat`, `OrderedPair`, `Epsilon0`. These files
omit module declarations because they establish root names before the module
graph is loaded. They are written in the library's notation: `∅`, `{x, y}`,
`(x, y)`, `𝒫(A)`, `⋃ A`, `ε₀`, and `ℕ` are read by the parser itself, and
`Aliases` declares the one further token it needs, `notation infixl 60 "∪"
=> union2`, as a global notation that a module's own `∪` shadows.

Separation and Replacement are profile-level axiom schemas, so their strength
does not show in the table. A concrete instance is admitted only after its
side conditions and, for Replacement, its functionality proof have checked.
The datatype and recursion operations are kernel schema rules of the same
kind; their syntactic guards are part of the trusted checker specification
until their soundness theorems are machine formalized.

Everything else installed before sealing (`subset`, `singleton`, `union2`,
`orderedPair`, `cons`, `relates`, `functionOn`, `wellFoundedOn`, and
`E0Ordinal`) is a transparent conservative definition made by the definition
operation.

## Tiny portable receipt

A `.g17f` file is canonical UTF-8 JSON:

```json
{
  "format": "grace17.foundation",
  "version": 1,
  "profile": "ZFG",
  "environment": "64 lowercase hexadecimal characters"
}
```

It contains no signature maps, definitions, datatypes, recursive equations,
or theorems. The checker constructs `profile` itself and accepts the receipt
only when the constructed environment equals `environment`. Passing the name
`ZFG` directly is equivalent; the G17C artifact already contains the expected
foundation digest.

The strict Python G17C checker rejects `.g17env` snapshots as foundation
inputs. `.g17env` is for standalone G17M tapes, where the environment is part
of that lower-level checker API.

## Trust and efficiency

The logical trust base is:

- the first-order proof rules;
- the selected set-theory axioms;
- the syntactic guards implementing admitted ZF schema instances and
  conservative extensions;
- canonical decoding and SHA-256.

Parsing, elaboration, tactics, computation strategy, module resolution,
surface indexes, and cached kernel objects are outside it. Constructing the
foundation and replaying the bootstrap certificate are fast; delivery uses the
independently replayed machine certificate, and the surface prelude is not
re-elaborated.

The plan for shrinking the trust base is to keep moving derivable bridges
into the checked bootstrap prelude, derive the von Neumann `Nat` interface
from the set-theoretic development, and eventually formalize soundness for one
or more external checkers. Such a prelude may be cached by its checked
receipt, but it must stay reproducible from the smaller axiomatic base.
