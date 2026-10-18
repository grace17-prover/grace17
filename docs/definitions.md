# Defining mathematical objects in Grace17

A definition in Grace17 is a conservative extension of the set theory it is
made in. Each one introduces a new symbol together with a defining law that
the kernel checks and records.

Mathematical objects come in a few kinds, and each has its own declaration:

- **Sets** are the values of the theory. `def f (...) : Set := term` names a
  term built from existing symbols; it introduces a function symbol `f`
  whose defining equation is the law `f(...) = term`. A `def` does not
  construct the set of pairs that represents the function as an object.
- **Classes** are collections that may be too large to be sets, such as the
  ordinals or the collection of all groups. `class C (...) := formula` is a
  predicate with membership notation, so `x ∈ C` is written as for a set
  while no claim is made that `C` is one.
- **Predicates** are propositions about sets: `predicate P (...) := formula`
  names a property or relation, and its defining law is the equivalence
  `P(...) ↔ formula`.
- **Functions as sets** are graphs, sets of ordered pairs with a domain and a
  codomain. `defgraph` builds one from a displayed value and a proof that the
  value lies in the codomain, so the function can be quantified over, passed
  to theorems about `FunctionBetween`, and applied with `f(x)`.
- **Values determined by a property** come from `defunique`, which needs a
  proof of existence and uniqueness and no Choice, and from `defchoose`,
  which selects a witness of a bounded existence and retains its hypotheses.
- **Inductive data** such as lists and trees are `datatype` declarations with
  validated set encodings, and functions over them are defined by structural
  recursion whose clauses, coverage, and decrease are checked.
- **Recursive constructions** along the ordinals, along membership, or along
  a certified well-founded relation are `noncomputable` definitions justified
  by the corresponding recursion theorem.

Sets built by Separation and Replacement are written as terms:
`{x ∈ A | P(x)}` is a bounded subset, and `{term(x) | x ∈ A}` is an image,
whose functionality certificate the elaborator constructs and checks. An
unbounded comprehension is never admitted as a set, which is what keeps the
proper classes above honest.

## Choose the mechanism

| Need | Form | What justifies it |
| --- | --- | --- |
| A name for a term | `def f (...) : Set := term` | A checked defining equation |
| A property or relation | `predicate P (...) := formula` | A defining equivalence |
| A mathematical collection, possibly a proper class | `class C (...) := formula` | A predicate, also usable as `x ∈ C` |
| A bounded subset | `def S (...) : Set := {x ∈ A \| P(x)}` | Separation over the existing set A |
| The image of a set | `def S (...) : Set := {term(x) \| x ∈ A}` | Replacement with a checked functionality certificate |
| A function represented by a set of pairs | `defgraph` | A codomain proof and generated function/value laws |
| A uniquely determined value | `defunique` | Checked existence and uniqueness, using only ZF |
| A selected witness | `defchoose` | A proof of bounded existence; selection retains the hypotheses |
| Finite constructor data | `datatype` | Validated set encodings and inductive-definition laws |
| Executable structural recursion | Equation-style `def`, or legacy `define` | Checked clauses, coverage, and structural decrease |
| Recursion along ordinals | `noncomputable transfinite def` | Checked zero, successor, and limit schema |
| Recursion along membership | `noncomputable foundation def` | Foundation and a member-history graph |
| Recursion along a certified set relation | `noncomputable well-founded def` | A checked `wellFoundedOn` certificate and predecessor history |

A `def` introduces a function symbol. It does not construct the set graph of
that function. The distinction matters when a theorem expects
`FunctionBetween(f, A, B)`, or when functions are quantified over as sets.

A return annotation such as `: Integer` is a checked obligation. A `def` runs
bounded type inference and publishes `f.type`, with the declaration's
parameters and input type guards. For example:

```g17 import=Grace.Cumulus.Int
def chineseCombination (m n a b u v : Integer) : Integer := a * v * n + b * u * m
-- chineseCombination.type proves Integer(chineseCombination(m, n, a, b, u, v)).
```

When inference needs help, attach a `proof` block. Its goal is the declared
result predicate applied to the defined function; input guards are available:

```g17
predicate EqualZero (x : Set) := x = 0
def zeroValue (x : Set) : EqualZero := 0
proof
  unfold EqualZero
  unfold zeroValue
  rfl
```

Structural definitions also attempt a checked induction over their decreasing
argument. Foundational definitions may establish closure later in the same
module, including by an explicit theorem named `f.type`. Pending annotations
supply no proof evidence, and the module fails if any obligation remains
unproved. A hand-written `f.type` must have the declared guards and
conclusion. `Set` is the kernel sort and needs no type theorem. A function
whose stronger type needs extra hypotheses should take refined input binders,
or return `Set` and come with a conditional closure theorem. Datatype
predicates are not carrier sets: `List(List(A))` needs a set of lists, which
the datatype declaration does not construct. Executable Set-valued functions
can still use exhaustive constructor patterns for structural recursion.

## Function graphs: `defgraph`

Here is an inclusion map, with its domain and codomain explicit:

```g17
defgraph inclusionMap (A B : Set) (x ∈ A) : B := x
requires subset : A ⊆ B
proof
  unfold Subset at subset
  exact subset with x, member
```

The parameterized result `inclusionMap(A, B)` is a set of ordered pairs.
Inside the closure proof, `member : x ∈ A` is available, and the goal is
`x ∈ B`. The binder variable x is the function input; it is not a parameter
of the graph construction.

The generated interface includes:

| Law | Meaning |
| --- | --- |
| `.closed` | The displayed value belongs to the codomain |
| `.relates` | The input and its displayed value form an entry of the graph |
| `.function` | The graph is a `FunctionBetween` the declared domain and codomain |
| `.value` | Set-function application returns the displayed value |

These laws retain `requires` hypotheses and any applicable input guard. For
example, this checked use appears in `examples/Definitions.g17`:

```g17
theorem inclusion_value (A B x : Set)
  requires subset : A ⊆ B
  requires member : x ∈ A
  shows inclusionMap(A, B)(x) = x
proof
  exact inclusionMap.value with subset, member
```

The graph is a bounded Replacement image. Each output is a term, so its
functionality certificate can be constructed from equality and checked. A
relation does not become functional by being declared.

The shorter form `defgraph g (n : Nat) : Real := value` also supports Nat/Real
input and output combinations. It uses `typecheck` to prove output closure,
without a user-written proof block. The bounded form supports explicit Set,
Nat, and Real parameters and named, potentially multiline `requires` clauses.
For domains ℕ and ℝ, the generated input laws can use the corresponding
Nat/Real guard. A graph over an infinite domain is not an executable table,
and these laws say nothing about behavior outside its domain.

## Unique values: `defunique`

Use this for a canonical value described by a bounded predicate. It needs no
Choice axiom, including when the value is an equivalence class.

```g17
defunique identityValue (A : Set) (x ∈ {A}) := x = A
proof
  witness A
  refine ⟨singleton.self at A, rfl⟩
uniqueness
  intro x
  intro xMember
  intro xValue
  intro y
  intro yMember
  intro yValue
  cc
```

The `proof` block proves `∃ x ∈ A, P(x)`. The `uniqueness` block proves
`∀ x ∈ A, P(x) → ∀ y ∈ A, P(y) → x = y`, under the same `requires` clauses.
Introduce the two values, their membership assumptions, and their properties
in that order. The generated laws are `.exists`, `.unique`, and `.selected`.
The last states that the defined value lies in A and satisfies P.

The implementation forms `.candidates` by Separation and defines the value
as `union(candidates)`. Existence and uniqueness make that set a singleton;
the union of `{z}` is z. The generated selection proof is ZF reasoning, with
no new kernel rule or axiom. The definition is total, but its selected law
keeps the stated hypotheses.

Integer addition, multiplication, negation, their set-function graphs, and
natural magnitude use this mechanism. Finite cardinality, set indicators,
Cartesian coordinates, matrix indices, and diagonal coefficients do too.
Use their laws or `ring`; there is no need to unfold the set construction.

## Selected witnesses: `defchoose`

```g17
defchoose selected (A : Set) (x ∈ A) := x ∈ A
requires inhabited : ∃ x, x ∈ A
proof
  obtain ⟨x, member⟩ := inhabited
  witness x
  refine ⟨member, member⟩
```

Import `Grace.Cumulus.Set.Choice` to use this mechanism.
The general obligation is `∃ x ∈ A, P(x)`. The declaration constructs
`selected.candidates` by bounded Separation and selects an element of that
candidate set using the foundation's choice interface. It checks `.exists`
and `.selected`; the latter provides both membership in the bound and the
chosen property, under the declaration's hypotheses.

The generated candidate set is named `selected.candidates`. Its defining law
characterizes membership. Unfolding it can
expand a statement `z ∈ selected.candidates(A)`, but does not replace a bare
set term inside `choose(selected.candidates(A))` with a term equation.
Use `.selected` to reason about the chosen value.

This mechanism does not prove uniqueness, and it does not compute a witness.
For a canonical mathematical value, prefer `defunique` and supply its
uniqueness proof. The selection property depends on the existence
hypothesis.

## Predicates, classes, and bounded sets

`predicate FixedBy (f x : Set) := f(x) = x` names a proposition. Soft-typed
parameters are part of the predicate's extension: `predicate P (x : Nat) := Q(x)`
means `Nat(x) ∧ Q(x)`. Thus a proved P(x) can provide its domain information.

`class Natural (x : Set) := Nat(x)` makes collection notation available. It
is a view of a predicate and makes no claim that the collection is a set. The
mathematical `class` keyword has nothing to do with type-class registration.

Subset and image definitions are bounded by an existing set. They generate
membership characterizations usable in proofs. The predicate in a subset may
be undecidable; an arbitrary unbounded comprehension is not admitted as a set.

## Datatypes and executable recursion

A `datatype` introduces set-encoded constructors. Fields marked `self` are
recursive; a field typed by a carrier A requires membership in A. Validated
schema products include constructor closure, injectivity, disjointness,
cases, and the induction interface. See `datatypes.md` for representations.

Equation-style `def` supplies constructor clauses. The checker verifies
coverage, pattern linearity, arity, fixed parameters, and permitted structural
recursive calls. This is the executable recursion interface used by `compute`;
unrestricted self-reference is rejected. `define` is its legacy spelling.
The complete examples include a two-parameter recursion with one fixed Set
parameter and one decreasing natural argument.

## Noncomputable recursion

These forms define set constructions; none of them traverses an infinite
set. "Noncomputable" does not mean admitted: the defining events and laws are
validated and independently replayable.

- **Transfinite:** provide the supported `0`, `succ β`, and `limit λ` clauses.
  The final index is Ordinal and the result is currently Set. Recursion
  positions and fixed parameters are checked. `Set/Hierarchy.g17` defines V
  this way.
- **Foundation:** `| x using history => step` receives the graph of values on
  members of x. The final argument and result are currently Set. The history
  membership law and defining equation expose the construction for proofs.
  Recursive calls are restricted to the history.
- **Well-founded:** provide `over A ordered by r`, `certified by theorem`, and
  a predecessor-history clause. The certificate must establish the required
  `wellFoundedOn` statement. Generated laws include `.solution.existsUnique`,
  `.history.membership`, `.equation`, and `.outside`; inspect the laws when
  reasoning about arguments outside A. The final argument and result are Set.

The corresponding complete examples, including the certificate for membership
restricted to a set, are in `examples/Definitions.g17`.

## Declarations that organize reasoning

`notation` changes how existing symbols are written; it adds no mathematical
object or axiom. `instance` proves a theorem and registers it as candidate
type-class evidence; registry search is untrusted. `tactic` declares a
bounded-expansion macro built from existing tactics. These declaration
keywords have contextual hovers too.

Bounded `defgraph` bodies may use infix expressions, for example
`defgraph arithmeticTerms (A D : Real) (n ∈ ℕ) : ℝ := A + (realNat(n):R) * D`.
The generated graph entry groups the entire value expression, preserving its
precedence in both the definition and the generated membership proof.

## Theorem sections

A theorem section shares parameters and hypotheses without adding a
namespace; each theorem in the section exports the shared variables as
parameters and the shared hypotheses as premises. See
[modules, namespaces, and sections](modules.md) for nested contexts,
exported signatures, applications, and a runnable example.

## Scoped ring operations

Inside a theorem section, write `notation ring R := (A, add, zero, neg, mul, one)`
to use algebra syntax for those operation graphs. Several rings can coexist,
with `R[expression]` picking one, and polynomial rings, quotients, and
restrictions are named `R[I]`, `P ⧸ J`, and `R ↾ T`. The declaration adds no
hypotheses, axioms, or kernel operations. See
[ring scopes over separate pieces](algebra.md#ring-scopes-over-separate-pieces).
