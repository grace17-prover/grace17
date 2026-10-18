# Grace17 soft types and classes

Grace17 keeps one foundational universe: every kernel term denotes a set. The
surface elaborator may nevertheless assign a term one or more soft types. A
simple soft type is a checked unary predicate; a family such as `List(A)` is a
checked parameterized refinement `List(A, xs)`. Neither restricts the kernel.

The operational typing judgment is:

```text
Γ ⊢ e ⇐ T  ↝  term, proof of T(term)
```

The elaborator and Tau index are untrusted. A successful result contains a
proof object, and the kernel checks that proof in `Γ` before it can discharge
an obligation.

## Declared function results

A non-`Set` result annotation on `def` generates a checked `functionName.type`
theorem. Bounded inference tries first; an attached `proof` block can establish
the result by hand. Structural recursion can synthesize a checked induction.
See [definitions.md](definitions.md) for the syntax and same-module closure
obligations. An annotation by itself is never a Tau rule.

## Tau

The soft-type inference engine is called Tau, after the Tau system of ACL2
based on a decision procedure for monadic predicates. ACL2's Tau system
takes the theorems a user has proved about
unary recognizers, such as "every natural is an integer" and "the sum of two
integers is an integer", indexes them by shape, and decides many membership
questions about terms by chaining them, without any search over the rest of
the logic. Grace17's Tau does the same job for soft types: it works only with
unary predicates and parameterized refinements, it uses only theorems the
kernel has already checked, and it answers a query by composing those
theorems into a proof object. The restriction to monadic predicates is what
makes the procedure fast and predictable, and it is why soft typing in
Grace17 never needs a type checker in the trusted base: the kernel checks the
proof Tau assembles, exactly as it checks any other proof.

## Certified Tau rules

The Tau index recognizes checked propositions of these forms:

```text
P(x) -> Q(x)
P(x) -> Q(y) -> R(f(x, y))
(P(x) and Q(x)) -> R(x)
Q(constant)
member(x, A) -> List(A, xs) -> List(A, cons(x, xs))
```

Universally quantified variants, including local induction hypotheses, are instantiated by first-order matching.
A variable that the conclusion leaves open is bound by matching a premise of
a hypothesis shape or guard predicate, the predicates that `via hypothesis`
and `notation guard` declarations name, against a local fact, or, when no
local fact has the premise's shape, by completing it through the rules and
instances, each completion being tried in turn; so `Morphism(C, f, a, b) →
f ∈ mor(C)` applies to a guarded morphism, `(f : a ⟶ b) → (g : b ⟶ c) →
g ∘ f : a ⟶ c` types a composite, and `Functor.map_comp` rewrites
`G(F(g) ∘ F(f))` once `F(f) : F(a) ⟶ F(b)` is completed by the instance
`Functor.map_hom`. Local facts of a transparent guard predicate are opened to
their definitional conjuncts. A side condition of a `simp` or `rw` rule is
relieved by this search when it is a unary soft type, a membership, a guard,
or a hypothesis shape, and a rule variable that the rewritten term leaves
open is bound the same way; other parameterized refinements are relieved
only by direct evidence. A membership premise of an instance that no
instance proves is relieved by these rules as well, so that `F(a) ∈ obj(D)`
types the image of an object; a sort premise is not, so that instances that
differ by a sort premise stay distinct.
Atomic predicate equivalences contribute checked forward and backward bridges,
including `Nat(n) ↔ n ∈ ω`. Rules are indexed by their result predicate. Inference recursively composes
constructor facts, subtype implications, conjunctive premises, and function
signatures. Cycles are cut by an active-goal set, and results are memoized for
the duration of a prepared proof context. Automatic refinement search is also
bounded: depth 256, 4,096 visited goals, 100,000 rule attempts, and 4,096 expanded
term nodes per goal. The term bound is checked before constructing canonical
memo keys, so recursively growing terms cannot evade cycle detection by
creating ever larger keys. Exhaustion returns no inferred evidence; a proof
you write can still discharge the premise. Exact local evidence and cached
results are consulted before the work and depth limits. These limits bound
elaboration; they say nothing about what the kernel can check.

The index holds every checked declaration of the kernel, but a scope
consults only the rules of the declarations it sees: those declared outside
any module, those of the current module, and those of the modules it
imports, directly or through their imports. This is the rule that governs
names and instances, so a module checks the same way alone as in a full
library load, whatever was loaded before it. A guard predicate is visible by
the same rule: a `notation guard` or `via hypothesis` declaration of one
module opens or binds its predicate in that module and in the modules that
import it, and nowhere else. A kernel used without modules sees everything.

The public APIs are:

- `proveSoftType`: return a proof or `undefined`;
- `proveRefinement`: prove `P(parameters..., term)` or return `undefined`;
- `checkSoftType`: return a proof or a structured `SoftTypeError`;
- `inferSoftTypes`: enumerate unary predicates found within the refinement search limits;
- `softTypeReport`: expose the deterministic certified-rule database.

## Implicit arguments

Brace binders declare elaboration-level implicit parameters:

```text fragment
def length {A : Set} (xs : List(A)) -> Nat
  | List.nil => 0
  | List.cons(x, tail) => succ(length(tail))

lemma length.nonnegative {A : Set} (xs : List(A))
  shows length(xs) >= 0
```

The kernel still sees the complete application `length(A, xs)` and the
complete quantified theorem. The elaborator inserts a metavariable for `A`
and solves it by deterministic first-order unification against local binder
refinements and known result signatures. It does not invoke open-ended theorem
search. Checked Tau evidence discharges the resulting soft-type side conditions
when an implicit theorem is instantiated.

Some arguments are ambiguous. A nullary `List.nil`, for example,
can inhabit `List(A)` for every carrier `A`. Use either a named or positional
override:

```text
eval length{A := omega}(List.nil)
eval length{omega}(List.nil)
```

Failure reports the unresolved parameter and suggests the named form. Implicit
metadata is untrusted and absent from kernel proof rules. Native execution
receives the elaborated full-arity term; an optimizing runtime may erase the
datatype parameters.

## Type-class outputs

Type-class resolution is separate from Tau. An `instance` is first checked as
a theorem and then entered in an import-scoped registry. Besides
proving a fully specified proposition, the resolver can synthesize marked
output arguments from known inputs. For example, the query
`AddOperation(ℝ, _)` returns the unique operation graph and its checked proof.
Search is first-order, indexed, memoized, cycle-checked, resource-bounded, and
ambiguity rejecting.

Typed notation composes the two systems: Tau determines that an operand has
soft type `Real`; the type-class query selects the operation graph for carrier
`ℝ`; and notation erases to a `call2` term. `OfNat(ℝ, 0, _)` handles the
constant `0` in the same way. Identifier names play no part, and neither
mechanism adds a kernel-level type judgment.

## Classes

A class is the extension of a formula with one distinguished element variable
and zero or more parameters:

```text
class Natural (x : Set) := Nat(x)
class Universe (x : Set) := { x | x = x }
class SubsetsOf (A : Class) := { X : Set | forall x, x in X -> x ∈ A }
```

Internally these are conservative predicate definitions. Class membership is
formula syntax:

```text
n ∈ Natural
X ∈ SubsetsOf(A)
```

`Class` parameters are elaborator-level predicate parameters; the kernel never
sees them. Supplying a set where a class is expected coerces it to its
membership class. Supplying a defined class substitutes its membership formula. Class
equality is extensional surface syntax:

```text
SubsetsOf(Universe) = Universe
```

It elaborates to `forall X, X ∈ SubsetsOf(Universe) <-> X ∈ Universe`, after
which all class-parameter placeholders are eliminated. The kernel therefore
checks a first-order statement and proof.

A class is not a term and cannot be supplied where a set is expected. A
bounded class can be realized as a set using Separation:

```text
def naturalsIn (A : Set) : Set := { x in A | x ∈ Natural }
```

This distinction permits universal and other proper classes without a
universal set. Quantification remains over sets. Quantification over classes
would be a second-order extension, and the kernel does not have it.

## Trust and execution

Typing information is erased for execution. Native evaluation operates on the
same admitted untyped terms as before. A defective type inference algorithm
can reject a good program or produce an inconvenient diagnostic, but it cannot
admit a false typing claim because every positive answer carries a kernel proof.

## Type classes and overloaded notation

Soft types answer “does this set belong to this carrier?” Type classes answer
“which operations and laws are being used on that carrier?” They are separate
indexes with the same discipline: resolution is untrusted and a positive
result contains a checked proof.

The `class` declaration above is a different thing: the set-theoretic notion
of a possibly proper collection. `notation ... for Rational` is also different;
it selects an implementation from unary soft-type evidence.

An `instance` declaration is a theorem with predicate premises and a predicate
conclusion. After the theorem passes the kernel, its name is entered in a
separate registry. `synthesize` searches the visible registry, exact local
evidence takes precedence, and multiple successful global declarations are an
ambiguity error. The registry and search are untrusted metadata; the result is
a theorem-application proof. Registry visibility follows transitive module
imports, as the visibility of typing rules and guard predicates does, and
survives compiled surface-index sidecars.

Resolution is first-order and predictable. The registry is
indexed by conclusion predicate and per-argument discrimination tries over the
complete term structure. Instance variables form wildcard edges, and queries
intersect the candidates from every known input before first-order matching. Each proof context has success/failure tabling and active-goal cycle
detection; hard limits bound depth, distinct goals, and rule attempts. This is
the first-order specialization of the tabled approach described by Selsam,
Ullrich, and de Moura in *Tabled Typeclass Resolution*. Every quantified
instance variable must occur in the conclusion, preventing the unconstrained
metavariable searches that frequently make general type-class systems
expensive.

`typecheck` is an ACL2-style Tau query for unary soft types and refinements;
instance synthesis is a separate command. `with *` first tries the instance
registry for a predicate premise and then falls back to Tau refinement
reconstruction; an equation premise between the endpoints of guarded
morphisms is closed by congruence over the opened guards. A `simp` whose
goal is a transparent guard, such as `G(F(f)) : G(F(a)) ⟶ G(F(b))`,
rewrites the goal to a fixpoint and then closes it by the search or by the
instance registry.

Every quantified instance variable must occur in the conclusion or in a
premise of a hypothesis shape or guard predicate, which synthesis matches
against the local facts; this keeps the search first-order and indexed while
letting `Morphism.comp` fix the middle object of a composite from the guards
of its factors.

`linarith` uses this registry for abstract carriers. Over the reals it is a
complete decision procedure for linear consequences of the local comparisons:
it negates the goal, runs Fourier–Motzkin elimination with products treated as
atoms, and emits a certificate from `realLe.add`, `realLess.add`, their mixed
forms, and one commutative-ring identity. Over `Nat` it shares the discrete
ordered-additive presentation used by `arith`. For an abstract ordered ring it
queries the registry for `OrderedAdditiveGroup(A, add, zero, neg, le)`; if only
an `OrderedRing(A, add, zero, neg, mul, one, le)` instance or local hypothesis
is available, it projects the additive interface through a checked theorem.
The carrier, operation graphs, and relation are read from the resulting proof,
so the tactic needs no special carrier name. An ordered ring may register the
additive interface directly, as the reals do, and its multiplication law
separately. In every case the certificate is a checked sum of order facts
transported through additive normalization and cancellation.

Every tactic that needs algebraic structure obtains it the same way: from an
`instance` in the registry or from a local hypothesis, through a checked
projection theorem when only a stronger structure is at hand, and the
carrier, operation graphs, and relations are then read from that proof rather
than from a carrier's name. For example, over rings, `ring` resolves a
`CommRing` instance or projects it from `OrderedRing` and builds
kernel-checked equational certificates over that carrier's operation
graphs. It expands transparent wrappers for those operations, so
Real subtraction and recursive real sums participate without naming Real in
the generic normalizer. Polynomial expansion is bounded at 256 monomials.
The `ring_nf` and `ring at` forms reuse these checked certificates for registered
rings. On equality and predicate goals or hypotheses, `ring_nf` normalizes
value arguments and leaves the transformed goal open; Nat retains its
specialized normalizer.

Numerals and operator notation are resolved from the expected carrier:

```text
Γ ⊢ e ⇐ A using i  ↝  term, proof of A(term), explicit instance i
```

`0`, numerals, `+`, `*`, and order notation are resolved from the expected
carrier. Natural zero is the empty set by the ZF encoding; a real or ring zero
is the zero field of that instance and need not have the same representation.
Checked embeddings such as `Nat -> Real` relate them. See
[algebra.md](algebra.md) for the structure representation, resolution,
ambiguity, and coercion rules.
