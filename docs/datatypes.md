# Grace17 datatypes

Lists, trees, options, booleans, and syntax trees are inductively defined
data. In Grace17 they are inductively defined *classes of sets*: a
`datatype` declaration names constructors, and every value a constructor
builds is an ordinary set in the one universe, with a checked equation
saying exactly which set it is. There is no second universe of runtime
values, so a list may hold ω as an element, a theorem about lists is a
theorem of set theory, and the same structural recursion that defines
`length` executes natively inside a proof. The same mechanism declares
mathematical structures: a `structure` is a datatype with one constructor
and named fields, so a group, a ring, an order, or a category is one set
with projections for its carrier, operations, and laws; see
[Structures](#structures).

## Declaring a datatype

`Grace.Core.Data` declares the four datatypes the rest of the library builds
on:

<!-- cumulus-source: lib/Grace/Core/Data.g17 -->
```g17
datatype Bool
  | false
  | true

datatype Option(A : Set)
  | none
  | some(value : A)

datatype List(A : Set)
  | nil
  | cons(head : A, tail : self)
```

<!-- cumulus-source: lib/Grace/Core/Data.g17 -->
```g17
datatype Tree(A : Set)
  | leaf(value : A)
  | node(left right : self)
```

A field is typed by `Set`, by `self`, or by one of the datatype's
parameters. `self` marks a recursive field, and a field typed by a parameter
`A` carries the side condition that its value belongs to `A`. That is the
whole vocabulary, and it expresses sums, products, options, lists, trees, and
syntax objects.

The declaration `List(A : Set)` creates the refinement predicate
`List(A, xs)`, read "`xs` is a list over `A`", together with the constructor
functions `List.nil` and `List.cons`. Soft-type binders such as
`(xs : List(A))` are hypotheses `List(A, xs)` like any other
[soft type](types.md), and Tau infers `List(A, xs)` for a constructor value
whose fields satisfy their conditions.

## What a declaration produces

The kernel records one audited inductive-definition event per datatype. The
event carries, for every constructor `C`:

- `D.inductive.constructor.C`, the closure law: a constructor applied to
  fields that satisfy their conditions is a member of the datatype;
- `D.inductive.injective.C`, injectivity: equal constructor values have
  equal fields;
- `D.inductive.disjoint.C.C'`, for every pair of distinct constructors:
  their values are never equal;
- `D.inductive.representation.C`, the set-theoretic identity of the
  constructor value, below;
- `D.inductive.cases`, exhaustiveness: every member of the datatype is a
  constructor value;

and the induction principle that the `induction` tactic consumes. All of
them are consequences of the one inductive definition and its
representation; none is an axiom. The first three are what `settle` reaches
for when it reasons about constructors:

```g17 import=Grace.Core.List
theorem cons.injective (A x y : Set) (xs ys : List(A))
  requires same : x :: xs = y :: ys
  shows x = y ∧ xs = ys
proof
  settle with List.inductive.injective.cons

theorem nil.ne_cons (A x : Set) (xs : List(A))
  shows [] ≠ x :: xs
proof
  settle with List.inductive.disjoint.nil.cons
```

`Grace.Core.List` packages exhaustiveness as the theorem `List.cases`: a
list over `A` is `List.nil`, or it is `x :: tail` for some `x ∈ A` and some
list `tail` over `A`.

## Sets all the way down

Every generic constructor value is an ordered pair of a tag and a tuple of
its fields, written in the ordinary notation for Kuratowski pairs:

```text
C(x₁, …, xₙ) = (tag, (x₁, (x₂, (…, (xₙ, ∅)))))
```

The tag is a hereditarily finite set that spells the fully qualified
constructor name, so the encoding does not depend on module load order, and
the fields form a nested pair ending in `∅`, so `List.nil = (tag, ∅)` and
`x :: xs = (tag, (x, (xs, ∅)))` with the two tags distinct sets. The
representation law `D.inductive.representation.C` states this equation,
and a proof can descend to it whenever it needs the set-level view of a
constructor. The von Neumann naturals are the one exception: `0 = ∅`
and `succ(n) = n ∪ {n}`, as in the rest of mathematics, with no tag.

Because constructor values are sets, their payloads can be anything at all.
A three-element list may contain ω, the stage `V(ω)` of the cumulative
hierarchy, and its powerset:

```g17 import=Grace.Cumulus.Set.Hierarchy,Grace.Core.List
lemma length.infinite_notation
  shows length([ω, V(ω), 𝒫(V(ω))]) = 3 by compute
```

Only the three-cell spine is reduced. The infinite payloads are neither
traversed nor approximated; the shape of a datatype value is finite even
when its elements are not.

`Grace.Core.Syntax` uses these datatypes for executable set-level syntax
trees of terms, formulas, goals, and compiled tactic plans, so Grace17's own
syntax is data of the same kind.

## Structural recursion and computation

Functions over a datatype are defined by one equation per constructor, and
recursive calls are allowed only on fields marked `self`:

<!-- cumulus-source: lib/Grace/Core/Data.g17 -->
```g17
def length {A : Set} (xs : List(A)) -> Nat
  | List.nil => 0
  | List.cons(x, tail) => succ(length(tail))
```

The elaborator checks coverage, constructor arity, linearity, and structural
decrease; a definition that recurses on anything other than a smaller value
is rejected with "not on a structurally smaller value". The checked
definition is also executable: the native evaluator keeps a constructor as
a compact node holding its tag and children, so evaluation never expands a
pair into raw membership structure, and a closed equation is proved by
`compute` with a constant-size kernel computation certificate, not with one
proof node per element.

A datatype of your own works the same way. Here are arithmetic expressions
over the naturals, with an evaluator, a size function, a computed value, and
a theorem proved by induction:

```g17 import=Grace.Cumulus.Nat
datatype Expr(A : Set)
  | lit(value : A)
  | plus(left right : self)

def eval (e : Expr(ℕ)) -> Nat
  | Expr.lit(n) => n
  | Expr.plus(a, b) => eval(a) + eval(b)

def size (e : Expr(ℕ)) -> Nat
  | Expr.lit(n) => 1
  | Expr.plus(a, b) => size(a) + size(b)

theorem eval.sample
  shows eval(Expr.plus(Expr.lit(2), Expr.plus(Expr.lit(3), Expr.lit(4)))) = 9
proof
  compute

theorem size.positive (e : Expr(ℕ))
  shows 0 < size(e)
proof
  induction e
  | Expr.lit(n) =>
    rw size
    arith
  | Expr.plus(a, b) using ihA, ihB =>
    rw size
    arith
```

The field `value : A` of `lit` becomes the hypothesis `n ∈ ℕ` in the `lit`
branch, which is why `eval` may return `n` as a natural.

## Induction

`induction x` on a datatype value opens one branch per constructor, named by
the constructor pattern. Every `self` field contributes an induction
hypothesis, introduced after `using` in field order, and a field typed by a
parameter adds its membership to the branch's context:

<!-- cumulus-source: lib/Grace/Core/Data.g17 -->
```g17
theorem mirror.involutive {A : Set} (tree : Tree(A))
  shows mirror(mirror(tree)) = tree
proof
  induction tree
  | Tree.leaf(value) => settle with mirror
  | Tree.node(left, right) using ihLeft, ihRight => settle with mirror, ihLeft, ihRight
```

The kernel checks the parameters, exact constructor coverage, and the
context and goal of every branch; `induction xs generalizing s` strengthens
the hypothesis over further variables, as described under
[induction](tactics.md#induction).

## Lists

Lists are the datatype everything else uses, so they have notation. Write
`[a, b, c]` and `[]` for literals and `a :: xs` for cons, which associates
to the right below arithmetic. Recursive definitions and induction branches
may use the same spellings in patterns:

```g17 import=Grace.Cumulus.Nat
def total (xs : List(ℕ)) -> Nat
  | [] => 0
  | x :: tail => x + total(tail)

theorem total.sample
  shows total([1, 2, 3, 4]) = 10
proof
  compute

theorem total.append (ys xs : List(ℕ))
  shows total(append(ys, xs)) = total(xs) + total(ys)
proof
  induction xs
  | [] => settle with append, total, add
  | x :: tail using ih => settle with append, total, add, add.associative, ih
```

A literal's carrier is inferred as a finite set containing its elements; an
explicit carrier such as `length{A := omega}([1, 2, 3])` overrides it, and a
carrier may be any set-valued expression, as in
`(terms : List(idealProducts(A, mul, G)))`. `append(ys, xs)` traverses `xs`
and appends `ys`, so `append(ys, x :: tail) = x :: append(ys, tail)`.

Import `Grace.Core.List` for the datatype and its basic interface
(`length`, `append`, `reverse`, `List.cases`, and the unit and
associativity laws), and `Grace.Cumulus.List` for the library: take and
drop, filtering by a set, counts and permutations, sums, indexing by
position, prefixes and suffixes, sortedness with insertion sort, ranges,
duplicate-free lists, and the bridge between a list and a function on a
natural number. Do not redeclare `List` in your own modules; every library
result assumes the one datatype in `Grace.Core.Data`.

## Structures

A structure is a datatype with one constructor whose fields have names: a
bundle of mathematical data read back by projections. `Grace.Cumulus.Category.Core`
declares a small category as

<!-- cumulus-source: lib/Grace/Cumulus/Category/Core.g17 -->
```g17
structure Category
  | obj mor : Set
  | dom cod : mor → obj
  | id : obj → mor
  | comp : composablePairsOf(mor, dom, cod) → mor
  where
    identities : ∀ a ∈ obj, dom(id(a)) = a ∧ cod(id(a)) = a
    composites : ∀ g f ∈ mor, dom(g) = cod(f) →
      dom(comp(g, f)) = dom(f) ∧ cod(comp(g, f)) = cod(g)
    units : ∀ f ∈ mor, comp(id(cod(f)), f) = f ∧ comp(f, id(dom(f))) = f
    associative : ∀ h g f ∈ mor, dom(h) = cod(g) → dom(g) = cod(f) →
      comp(comp(h, g), f) = comp(h, comp(g, f))
```

Each `|` line is a group of fields with one type, written as a theorem
binder is: `Set`, a soft type such as another structure's name, a mixfix
guard such as `mor → obj` for `FunctionBetween`, or an earlier field or
parameter, as `zero : carrier` in `structure Ring`, which is the membership
`zero ∈ carrier`. The `where` block names the
laws, stated over the fields and the parameters as variables; the typing of
the fields and the earlier laws are in scope for the notation of the later
ones, so a law may say `f : a ⟶ b` once a law `Category(C)` precedes it. A
structure may take parameters, `structure Functor (C D : Set)`, which index
its predicate after the value: `Functor(F, C, D)`. A parameter may carry a
soft type, `structure Module (R : Ring)`, whose predicate `Ring(R)` is then
the first conjunct after the shape and in scope for the fields and laws, so
that a field may be typed `R.carrier × carrier → carrier`. A structure
without a `where` block, such as `structure Order | points le : Set`,
carries no laws, and the order structures are separate predicates over its
data.

The declaration `structure Category` produces, in the one namespace
`Category`:

- the datatype `Category.inductive` with the constructor
  `Category.mk(obj, mor, dom, cod, id, comp)`, encoded as every constructor
  is, and its refinement predicate `Category.Data(C)`, "`C` is a value of
  the structure";
- the projections `Category.obj`, …, `Category.comp`, each defined by
  structural recursion on the one constructor, so that
  `Category.obj(Category.mk(obj, …)) = obj` is its defining equation; the
  theorems `Category.mk.obj`, …, `Category.mk.comp` state these equations;
- `Category.mk.data`, the shape of a constructed value, and `Category.eta`:
  `Category.Data(self) → self = Category.mk(self.obj, …, self.comp)`;
- the predicate `Category(C)`, which conjoins `Category.Data(C)`, the typing
  of the fields, and the laws, each at the projections of `C`, in the order
  declared: `Category.Data(C) ∧ (C.dom : C.mor → C.obj) ∧ … ∧
  (∀ h g f ∈ C.mor, …)`, so that `obtain ⟨shape, domF, codF, idF, compF,
  identities, composites, units, associative⟩ := category` names them all;
- `Category.intro`, which takes the fields and asks for the typing and the
  laws over them, in that order, and concludes
  `Category(Category.mk(obj, mor, dom, cod, id, comp))`.

Every generated theorem is a kernel proof assembled from the datatype's own
laws (`constructor.mk`, `cases`) and the projection equations; nothing new
is trusted. The kernel sees one inductive-definition event, one structural
recursion per field, one predicate definition, and the theorems.

A projection is written in dot notation, `C.obj`, applied as `C.dom(f)` and
`C.comp(g, f)`, and chained, `F.src.obj`; `obj(C)` and `Category.obj(C)`
are accepted too, and statements and goals print every spelling as `C.obj`
when the receiver is a variable or a chain of projections and as
`Category.obj(t)` otherwise. The structure whose field is meant is decided
by the receiver: there is one structure in scope with that field, or a
hypothesis in scope places the receiver in one (`Category(C)`,
`Functor(F, C, D)`, a guard `F : C ⥤ D`, or a fact such as `IsProduct(C, …)`
whose definition already applies the projections of one structure to `C`),
or the receiver is built by a structure's constructor or by a definition
whose body is, or a soft-typed field names the structure of its value, or
the declaration's own text leaves one candidate: the fields it writes on
the receiver, `R.carrier` beside `R.add` and `R.mul` being the ring's since
no group has `add`, and the symbols it passes the receiver to,
`quotientRing(R, I)` treating `R` as a ring.
Otherwise the projection is an error that names the qualified spellings,
`Category.obj(C)` or `Functor.obj(C)`, and a plain `def` over a bare
variable writes the qualified one. A declared function of the same name as
a field wins the bare spelling. Here is a checked example:

```g17 import=Grace.Cumulus.Set.Function
structure Pointed
  | carrier : Set
  | point : Set
  where
    member : point ∈ carrier

theorem Pointed.laws (P : Set)
  requires pointed : Pointed(P)
  shows P.point ∈ P.carrier ∧ P = Pointed.mk(P.carrier, P.point)
proof
  obtain ⟨shape, member⟩ := pointed
  have eta := Pointed.eta with shape
  refine ⟨member, eta⟩

theorem Pointed.of_member (A x : Set)
  requires xIn : x ∈ A
  shows Pointed(Pointed.mk(A, x))
proof
  exact Pointed.intro with xIn
```

### Extending a structure

A structure may extend others, naming each parent with `as`:

<!-- cumulus-source: lib/Grace/Cumulus/Algebra/Ring/Basic.g17 -->
```g17
structure Ring extends
    AbelianGroup as additive (mul := add, one := zero, inv := neg),
    Monoid as multiplicative (inv := ∅)
  where
    distributive : Distributive(carrier, add, mul)
```

A parent is a structure or a unary predicate over one; `AbelianGroup` and
`Monoid` are predicates over `Group`. The parent's fields become fields of
the child, in the parent's order and before the child's own `|` lines,
each under its own name unless the clause assigns it another, `mul := add`,
or fixes it to a term over the child's fields and parameters, `inv := ∅`,
which is then no field at all; a field two parents share by name, here
`carrier`, is one field. So `Ring.mk(carrier, add, zero, neg, mul, one)`
takes the fields flat, and `R.carrier`, `R.add`, …, `R.one` are its
projections as for any structure. Each parent is a value of the child:
`Ring.additive(R)`, written `R.additive`, is the parent's constructor at
the child's fields, `Group.mk(R.carrier, R.add, R.zero, R.neg)`, and
`R.multiplicative` is `Group.mk(R.carrier, R.mul, R.one, ∅)`. The parent
predicate at that value is a law of the child under the `as` name, so
`Ring(R)` is `Ring.Data(R) ∧ (R.add : R.carrier × R.carrier → R.carrier) ∧
R.zero ∈ R.carrier ∧ … ∧ AbelianGroup(R.additive) ∧
Monoid(R.multiplicative) ∧ Distributive(R.carrier, R.add, R.mul)`, the
typing of every field first, and `Ring.intro` asks for the typing,
`AbelianGroup(Group.mk(carrier, add, zero, neg))`,
`Monoid(Group.mk(carrier, mul, one, ∅))`, and distributivity over the
fields. A fixed field should be one the parent predicate leaves
unconstrained, as `Monoid` does the inverse.

For each parent `p` of a structure `S`, over the parent structure `P`, the
declaration adds to the namespace `S`:

- the function `S.p`, with `S.p.value : ∀ self, self.p = P.mk(…)` its
  defining equation and `S.p.f : ∀ self, self.p.f = self.g` for each field
  `f` of the parent, `g` being the child field it is or the fixed term;
- `S.mk.p`, the parent value of a constructed child,
  `S.p(S.mk(fields)) = P.mk(…)`;
- the instance `S.p.<parent>`, the parent predicate in lowercase with
  underscores, `Ring.additive.abelian_group : Ring(R) →
  AbelianGroup(R.additive)`, so that a theorem about the parent applies to
  the parent value through `with *`;
- the instance `S.p.mem : x ∈ self.carrier → x ∈ self.p.carrier`, for the
  parent's first field when it is a field of the child, so that the carrier
  guards of such a theorem are discharged the same way.

A fact about `R.additive` reads in the ring's own projections after
rewriting with `Ring.additive.carrier`, `Ring.additive.mul`, and
`Ring.additive.one`, gathered in the tactic `ring_additive`; a declared
tactic applies at a hypothesis as `ring_additive at abelian`.

The hypothesis notations of a parent pass to the child where the fields
they mention keep their names: `*` via `Monoid(G) for G.carrier` is also
`*` via `Ring(R) for R.carrier`, since the ring's multiplication is still
`mul`, while the additive group's `*` is not inherited, its operation
having become `add`, and the ring module declares `+` itself. A form whose
template mentions a renamed or fixed field, or whose carrier is not a
projection of the child, is not inherited; where a template names the
parent itself, the parent value stands.

The groups and rings of Cumulus are structures too, `structure Group` with
`carrier : Set`, `mul : carrier × carrier → carrier`, `one : carrier`, and
`inv : carrier → carrier` as its fields and the group laws as `where`
clauses, `structure Ring` extending the abelian group and the monoid as
above, and `structure Module (R : Ring)` extending the abelian group by a
scalar action; see [algebra](algebra.md#groups). The topological and metric spaces are
`structure TopologicalSpace | carrier opens : Set` with the open-set axioms
as `where` clauses and `structure MetricSpace` with
`dist : carrier × carrier → ℝ` and the metric laws; see
[topology and metric spaces](cumulus.md#topology-and-metric-spaces).

The hypothesis notations of an area are declared over the projections,
`notation infixr 70 "∘" => call2(C.comp, _, _) via hypothesis Category(C) for C.mor`,
as [operations supplied by a hypothesis](notation.md#operations-supplied-by-a-hypothesis)
describes.
