# Cumulus

Cumulus is Grace17's library of mathematics. The name refers to the
cumulative hierarchy: every object in the library lives in the set-theoretic
universe, built up from the empty set by the ZF operations. The library
extends the kernel conservatively. Every definition is a checked declaration
event, every theorem has a certificate the kernel replayed, and every proof
can be exported in the proof-machine format and replayed by the independent
checkers.

The TypeScript kernel supplies logic and the primitive set-theory rules.
`Grace.Core` is the small computational bootstrap: natural number programs,
algebraic datatypes, and syntax datatypes. The set theory, including classes,
finite sets, relations, Foundation consequences, ordinals, rank, and the
hierarchy, lives under `Grace.Cumulus.Set`. Everything else in Cumulus is
built on that.

This guide explains how the library is organized and how each subject is
approached, so that a reader knows where to look and what to expect. It does
not list every theorem: the library grows, and its current contents are
always visible in the [Cumulus module browser](../cumulus/), where every
module opens in the Workbench, in the [library search](library-search.md),
and in the [Top 100](top-100.md), whose statements are extracted from
source. [Getting started](#getting-started) below says which module to
import for each kind of mathematics.

![The cumulative hierarchy: V₀ = ∅, each successor stage is the powerset of the stage before, and a limit stage is the union of the stages below it](images/cumulative-hierarchy.svg "The cumulative hierarchy. Every set appears at some stage V(α), and the stages are indexed by the ordinals.")

## Getting started

Source lives under the single module root `lib/`, in `lib/Grace/Cumulus/`.
If Claude Code is your editor, install the Grace17 skill first; it knows
the conventions this guide describes:

```sh
/plugin install grace17 --marketplace grace17-prover/grace17
```

Start a development with:

```g17
module MyMathematics
import Grace.Cumulus.Main

lemma subset.chain (A B C : Set)
  requires hAB : Subset(A, B)
  requires hBC : Subset(B, C)
  shows Subset(A, C)
proof
  have chain := Subset.transitive with hAB, hBC
  exact chain
```

`Grace.Cumulus.Main` is the compact default environment: extensional sets,
classes, finite sets, natural arithmetic, and natural order, with no separate
`open` block. Each subject has an entry point of its own, such as
`Grace.Cumulus.Set`, `Grace.Cumulus.Nat`, `Grace.Cumulus.NumberTheory`,
`Grace.Cumulus.Real`, `Grace.Cumulus.Algebra`, `Grace.Cumulus.LinearAlgebra`,
`Grace.Cumulus.Geometry`, and `Grace.Cumulus.GraphTheory`. An entry point
imports its subject's implementation graph and re-exports the public names
through `export open`, so a proof file imports one module and writes
mathematics. `import Grace.Cumulus` is the complete-library entry point when
breadth matters more than cold-start cost.

`npm run check:cumulus` checks the complete import graph and stops at the
first failing module; `npm run check:cumulus -- --continue` goes on past a
failure, skips the modules that import the failed one, and lists every
failure and skipped module at the end (add `--quiet` to print only those
and the summary), with exit status 1 when anything
failed. The command line and the Workbench need only the module root `lib/`. The files in `examples/` are
clients of the library: short, runnable developments that show a subject's
public interface in use. How files, imports, namespaces, and sections fit
together is described in [modules, namespaces, and sections](modules.md).

## Organization

Each subject lives in its own directory under `lib/Grace/Cumulus/`, and the
file directly under `lib/Grace/Cumulus/` with the subject's name is its entry
point: it declares a public module and imports the implementation graph.
Mathematical content belongs in the subject directory, never in the entry
point.

Within a subject, `Defs` files hold vocabulary and the weakest useful
interfaces, and `Core` files hold the subject's reusable consequences.
`Core` here is always nested under `Grace.Cumulus.<Subject>`; the bootstrap
namespace `Grace.Core` is a different thing. Beyond that, mathematical
cohesion decides file boundaries. Definitions stay together with their laws
while the file is still comfortable to edit, and a split happens at a
mathematical interface, not at a line count. Real analysis, for example, is
split by subject into sequences, continuity, differentiation, intervals,
compactness, and integration, each importing what it builds on.

The import graph is shallow and acyclic. Set theory is the base; natural
numbers, number theory, and the integers, rationals, and reals build upward
from it; algebra, analysis, geometry, linear algebra, and graph theory build
on those. Import the narrowest module you need, and prefer a subject entry
point over an implementation file: entry points are stable interfaces, and
implementation files move as the subject grows.

Throughout, carriers, operations, relations, and homomorphisms are sets;
algebraic structures are formulas about those sets; and structure resolution
is elaboration that produces kernel-checkable proofs. No algebraic law is
built into the kernel.

Choice is used sparingly and visibly. The set theory, order theory, cardinal
arithmetic, and most of the algebra are developed in ZF, and results that
need Choice, such as Zorn's lemma and its applications, live in separately
imported modules. The [axiom audit](axiom-audit.md) reports which axioms a
given theorem depends on, so a Choice dependency is never silent.

## Set theory and ordinals

`Grace.Cumulus.Set` is the foundation of everything else: extensional set
algebra, classes as predicates with a distinguished element variable,
relations and equivalence relations with their quotients, set-theoretic
function graphs with identity, composition, and bijections, and the
consequences of Foundation, from membership induction to the rank function.
Von Neumann ordinals are a defined class, and the cumulative hierarchy `V` is
built by transfinite recursion, with the theorem that every set belongs to
the stage indexed by its rank. See [ordinals](ordinals.md) for the ordinal
development and its executable Cantor normal forms.

`Grace.Cumulus.Cardinal` develops size without Choice wherever possible:
countability by injection into ℕ and its closure properties, Cantor's
diagonal theorem, equipotence as the existence of a bijection, finiteness by
bijection with a von Neumann natural, and the arithmetic of finite
cardinalities, including the subset count of a finite set. Order theory
covers partial, linear, and well-orders, chains and maximal elements, order
embeddings and isomorphisms, and the Hartogs bound, all in ZF; Zorn's lemma
and the maximal principles are the Choice-dependent layer above them.

`Grace.Cumulus.Lattice` continues order theory into lattices. An ordered
set is one set `P`, the `structure Order` with projections `P.points` and
`P.le` and constructor `Order.mk(A, r)`, and the structures are properties
of it: `PartialOrder(P)`, `Lattice(P)`,
`BoundedLattice(P)`, `CompleteLattice(P)`, `DistributiveLattice(P)`,
`BooleanAlgebra(P)`. Under such a hypothesis the order is written `a ≤ b`,
the join and meet `a ⊔ b` and `a ⊓ b`, the bounds `⊥` and `⊤`, the
supremum and infimum of a subset `⨆ S` and `⨅ S`, and the complement `aᶜ`,
and the laws have short standard names (`le_antisymm`, `sup_le`,
`sup_comm`, `sup_absorb`, `le_sSup`, `compl_compl`) gathered in
`lattice_simp`. The area covers suprema and
infima with their duality, the lattice laws, bounded, complete,
distributive, modular, and Boolean lattices, the powerset lattice
`powersetLattice(X)` with `B ⊔ C = B ∪ C`, monotone maps `MonotoneMap(f, P, Q)`
and Galois connections, the Knaster–Tarski theorem `f(lfp(f)) = lfp(f)` on
a complete lattice, lattice homomorphisms, sublattices, ideals, and
filters, each over an unbundled engine `IsLattice(A, r)` with `join(A, r, x, y)`
that the bridges `Lattice.mk` and `sup.join` connect to the bundled form.

`Grace.Cumulus.Category` treats small categories as sets: a category is one
set `C`, the `structure Category` with projections `C.obj`, `C.mor`,
`C.dom`, `C.cod`, `C.id`, and `C.comp` and laws in its `where` block, a
functor is one set `F`, the `structure Functor` with `F.obj`, `F.map`,
`F.src`, and `F.tgt`, written `F : C ⥤ D`, and a natural transformation `η : F ⟹ G` is
a function on the objects. The area covers hom-sets, isomorphisms,
monomorphisms and epimorphisms, terminal and initial objects, functors,
natural transformations, opposite categories, products by their universal
property, example categories built from preorders, monoids, and the subsets
of a universe set `U` (the category `Sets(U)`, whose morphisms apply as
functions), the covariant and contravariant hom functors, and the Yoneda
lemma: for a functor `F : C ⥤ Sets(U)` and an object `a`,
`NatTrans(homFunctor(C, U, a), F) ≃ F(a)`, by explicit mutually inverse
maps. Composition is written `g ∘ f` and a morphism is typed by its
endpoints, `(f : a ⟶ b)`, both resolved from the category, functor, or
transformation hypothesis in scope; the guard opens to `f ∈ mor(C)`,
`dom(C)(f) = a`, and `cod(C)(f) = b` for the tactics, composites,
identities, and images are typed by instances, `F(a)` and `F(f)` are the
object and morphism maps of a functor, and the unit laws, associativity,
functoriality, and naturality are stated on hom binders so that
`category_simp`, `functor_simp`, and `rw` apply them wherever the guards are
in scope. Equational proofs are `calc` chains or rewrite chains with one law
per step.

Everyday arithmetic uses compact native big integers and `Nat` soft typing,
and `Grace.Cumulus.Nat.Foundation` is the bridge to the raw sets: the von
Neumann membership law for successors, and the foundational equation
`succ(n) = n ∪ {n}` behind the efficient representation. A proof can descend
to pairing, union, and membership when it needs to, without changing how
arithmetic is written elsewhere.

## Natural numbers and number theory

`Grace.Cumulus.Nat` provides the arithmetic of ℕ as a soft-typed layer over
the set-theoretic naturals: cancellation laws, powers, factorials, parity,
truncated subtraction, natural order with its membership interpretation,
executable remainders `n % d` and quotients, and the least element of an
inhabited subset of ℕ, from which the principle of mathematical induction
for subsets of ℕ is proved. Arithmetic evaluates with native large integers,
so `compute` settles ground equations at any size. The everyday lemma
library covers order, minimum and maximum, powers, parity, truncated
subtraction, and the distance between naturals.

`Grace.Cumulus.List` develops finite sequences as the `List` datatype:
append and reverse, take and drop, filtering by a set, counts and
permutations, sums, indexing, prefixes and suffixes, sortedness with
insertion sort, ranges, and duplicate-free lists.

`Grace.Cumulus.NumberTheory` is classical elementary number theory in that
language: divisibility and primes, the infinitude of the primes, the
Euclidean algorithm with an executable `gcd` proved correct, Bézout's
identity with executable coefficients, coprimality and modular inverses, the
Chinese remainder theorem, Euclid's lemma and the fundamental theorem of
arithmetic, binomial coefficients, Fermat's little theorem and its Euler
generalization, Wilson's theorem in both directions, and the irrationality
of √2. Statements
are written as a number theorist would write them, with `n!`, `p - 1`,
`a ^ k % p`, and `n choose k`, and the executable functions evaluate inside
proofs.

`Grace.Cumulus.Combinatorics` counts: inclusion–exclusion, the pigeonhole
principle in its injective, surjective, and preimage forms, Pascal's rule
and the other binomial identities, the numbers of functions, injections,
bijections, and permutations between finite sets, Fibonacci and Lucas
numbers with Cassini's identity, counting a finite set by the fibers of a
map, Catalan, Stirling, and Bell numbers, derangements, Vandermonde's
identity, the infinite Ramsey theorem, and Möbius inversion: the Möbius
function from the prime factorization, its multiplicativity, the identity
`∑_{d ∣ n} μ(d) = [n = 1]`, and the inversion formula in both directions for
integer-valued functions on the positive naturals.

`Grace.Cumulus.Probability` is finite probability: probability spaces as
weight functions on a finite sample space, events and their probabilities,
uniform distributions, conditional probability and Bayes' theorem,
independence, random variables with expectation and variance, Markov's and
Chebyshev's inequalities, and Bernoulli, coin, die, and point-mass
examples.

## Integers, rationals, and reals

The number systems are constructed, not postulated. Integers are equivalence
classes of pairs of naturals, rationals are a quotient of signed natural
fractions, and reals are Dedekind cuts ordered by inclusion. Each
construction comes with its operations as total functional graphs, the laws
that make them a ring, an ordered field, or a complete ordered field, and
the embeddings between them: ℕ into ℤ, ℤ into ℚ, ℚ into ℝ. The integer
commutative-ring instance supports direct `ring` proofs, and executable
signed fractions give rational computation with checked bridges to the
quotient. On ℤ the library adds the order with its compatibility laws,
minimum and maximum, signs, parity, natural powers, and the absolute value
against the order.

The reals are where most of the library's analysis and geometry live.
`Grace.Cumulus.Real` proves the least-upper-bound property directly from the
cut construction, develops addition, negation, multiplication, inverses,
order, absolute value and distance, square roots of nonnegative reals,
natural powers `A ^ n`, division, numerals, and the typed notation that lets
real arithmetic be written as `x + y`, `x * y`, `-x`, `x / y`, `√x`, and
`x ≤ y`. Finite sums `∑ k < n, uₖ` over real sequences, with their algebra,
the arithmetic and geometric series, and the sums of powers, are part of
this layer.

## Real analysis

`Grace.Cumulus.Real.Analysis` follows a first course in analysis, with
sequences as function graphs from ℕ to ℝ written `uₙ`. Convergence and its
algebra, monotone and bounded sequences, subsequences and sequential
compactness, limits and continuity of real functions and their closure
properties, uniform continuity on compact domains, differentiation with the
usual rules, the intermediate value, extreme value, Rolle, and mean value
theorems, and Riemann integration on closed intervals with both directions
of the fundamental theorem of calculus are all proved from the Dedekind
construction. The derivative of `f` is the function `f′`, its value `f′(X)`,
and `f⁽ᵏ⁾` the k-th derivative; a theorem about a real function takes it as
`(f : ℝ → ℝ)`, so the mean value theorem reads
`f′(C) * (B - A) = f(B) - f(A)`, the Cauchy mean value theorem
`f′(C) * (g(B) - g(A)) = g′(C) * (f(B) - f(A))`, and Taylor's theorem with
the Lagrange remainder, for `f⁽ᵏ⁾` differentiable on `[A, B]` for every
`k ≤ n`, gives `C` strictly between `A` and `B` with
`f(B) = ∑ k ≤ n, f⁽ᵏ⁾(A) * (B - A) ^ k / k! + f⁽ⁿ⁺¹⁾(C) * (B - A) ^ (n + 1) / (n + 1)!`,
the factorials read as reals. L'Hôpital's rule in the `0/0` form carries
`f/g` to the limit of `f′/g′`. The notation `∫[A, B] f` is a real value, and
the integrability hypotheses its laws require are the checked ones. Infinite series are limits
of prefix sums: `SumsTo(u, S)` with its algebra, `xⁿ → 0` for `|x| < 1`, the
geometric series summing to `1/(1 − x)`, and the reciprocals of the
triangular numbers summing to 2.

## Topology and metric spaces

`Grace.Cumulus.Topology` is point-set topology. A space is the structure
`TopologicalSpace` with projections `X.carrier` and `X.opens`, and under a
hypothesis `TopologicalSpace(X)` the predicates `Open(X, U)`,
`Closed(X, C)`, `Neighborhood(X, N, x)`, `Dense(X, A)`, `Compact(X, A)`,
and `ConnectedSubset(X, A)`, the values `interior(X, A)`, `closure(X, A)`,
and `boundary(X, A)`, the properties `Compact(X)`, `Hausdorff(X)`,
`T1Space(X)`, and `Connected(X)`, and convergence `u ⇝ x` are stated over
the one set `X`; a binder `(x : X)` is membership in the carrier.
Continuity is the guard `f : X ⇒ Y`; `subspace(X, A)`,
`productSpace(X, Y)`, `realLine`, and `plane` are spaces, and
`Compact.prod` (the tube lemma), `Compact.interval` (Heine–Borel),
`Compact.continuous_image`, `Compact.closed_of_hausdorff`, and
`Converges.unique` are stated in these terms. `IsTopology(A, T)`,
`IsClosed(A, T, C)`, `IsCompact(A, T, S)`, `ContinuousMap(f, A, T, B, S)`, and
the rest over separate pieces remain the engine underneath, bridged by
`TopologicalSpace.parts`, `Compact.of_parts`, `Continuous.of_parts`, and
their kin, with bases, separation axioms, the finite intersection property,
components, and open and closed maps stated there.

`Grace.Cumulus.Metric` is the theory of metric spaces. A metric space is
the structure `MetricSpace` with projections `X.carrier` and `X.dist`, the
distance written `d(x, y)`; under `MetricSpace(X)` the laws are
`dist_nonneg`, `dist_self`, `dist_comm`, `dist_triangle`, and
`dist_eq_zero`, a distance is a real number by the instance `dist_real`,
`ball(X, x, r)` and `closedBall(X, x, r)` are the balls,
`metricTopology(X)` is the induced space (an instance of
`TopologicalSpace` and of `Hausdorff`), `u ⇝ x` is convergence with
`Converges.iff_dist` its ε–N form, `MetricContinuous(f, X, Y)` is ε–δ
continuity, equivalent to `f : metricTopology(X) ⇒ metricTopology(Y)`, and
`Cauchy(X, u)`, `Bounded(X, S)`, `Complete(X)`, `Lipschitz(f, X, Y, K)`,
`Isometry(f, X, Y)`, and `UniformlyContinuous(f, X, Y)` are the remaining
notions, with `realMetric`, `discreteMetric(A)`, `metricSubspace(X, S)`,
and `productMetric(X, Y)` as values. `IsMetric(A, d)` with the distance
`d(x, y)` and the forms over separate pieces remain underneath: open and
closed balls, the metric topology and its bridge to the topology engine,
ε–δ continuity in both directions against topological continuity,
Lipschitz maps and isometries, convergent and Cauchy sequences,
completeness, boundedness, and uniform continuity, with the real line,
discrete, subspace, and product metrics as instances; the real line is
complete by Bolzano–Weierstrass.

## Algebra

An algebraic structure in Cumulus is represented as a set: `structure
Group`, `structure Ring`, and `structure Order` bundle a carrier with its
operations, read back by projections such as `G.carrier`, `G.mul`, and
`R.add`, and under a hypothesis `Group(G)`, `CommRing(R)`, or
`Lattice(P)` a proof writes `a * b`, `a⁻¹`, `x + y`, `-x`, `R[2]`, and
`a ⊔ b`, binds `(a b : G)` and `(x : R)` as membership in the carrier, has
the closure facts as instances, and rewrites with `group_simp`, `ring`, and
`lattice_simp`. Underneath, `Grace.Cumulus.Algebra.Foundation` defines
magmas, semigroups, monoids, groups, semirings, rings, fields, and ordered
fields as predicates over carrier sets and operation graphs, with checked
projection lemmas, and every bundled structure is bridged to that form by
`parts` and `of_parts` theorems. The [algebraic hierarchy](algebra.md)
explains the structures, the instances, and the notation, and how `x + y`
is written inside a theorem section for an abstract ring `R`.

Group theory covers subgroups `Subgroup(H, G)` with the binder `(h : H)`,
cosets `g • H`, and Lagrange's theorem
`order(G) = index(G, H) * cardinality(H)` by the coset partition,
homomorphisms `f : G →* H` with kernels and images, normal subgroups and
the quotient group `G ⧸ N`, the first isomorphism theorem
`inducedMap(f) : G ⧸ ker(f) ≃* H`, direct products, generated
and cyclic subgroups, the order of an element and its divisibility of the
group order, centers and centralizers, and group isomorphisms `f : G ≃* H`.

Commutative algebra is stated over the ring structure: an ideal is
`Ideal(R, I)`, defined under `Ring(R)` as a subset closed under `+`, `-`,
and multiplication by the ring, with `ProperIdeal`, `MaximalIdeal`,
`PrimeIdeal`, and `Subring` alongside; the quotient ring is `R ⧸ I`, a
homomorphism is `f : R →+* S`, the first isomorphism theorem reads
`inducedMap(f) : R ⧸ ker(f) ≃+* S`, and the correspondence of ideals
under a surjection, generated ideals, and the existence of maximal ideals
above every proper ideal (Krull's theorem, the Zorn-dependent exception in
its own module) follow. Polynomial rings are the ring values
`polynomialRing(R, I)`, commutative rings by instance, with variables
`X(R, I, j)`, constants `polynomialConstant(R, I) : R →+* polynomialRing(R,
I)`, evaluation `evaluationHom(R, S, I, f, v)` with its universal property,
point ideals `pointIdeal(R, I, v)` maximal over a field, the one-variable
factor theorem and finiteness of roots over `Field(R)`, and the weak
Nullstellensatz over `AlgebraicallyClosed(R)`. The engine over separate
pieces carries the rest: finite sums and products over finite sets,
determinants of matrices over a commutative ring, polynomial rings in an
arbitrary set of variables with evaluation, base change, and Dickson's
finite-basis theorem, and field theory through integral extensions,
Zariski's lemma, and the Nullstellensatz. Almost all of this is in ZF.

## Complex numbers

`Grace.Cumulus.Complex` constructs the complex numbers as ordered pairs of
Dedekind reals, proves that they form a field, and develops the squared
modulus and its geometry without square roots. The analytic development
leads to the fundamental theorem of algebra, from which the library derives
that ℂ is algebraically closed and specializes the abstract Nullstellensatz
to concrete polynomial systems. Solutions of the cubic and quartic are
checked identities in this field. The axiom audit records where this
development inherits Choice from the analytic minimum-attainment results.

## Linear algebra

`Grace.Cumulus.LinearAlgebra` is finite real coordinate calculation. A vector
is a real sequence observed below a dimension, and a matrix is a total
function from pairs of natural indices to real entries, so dot products,
norms, matrix–vector and matrix–matrix products, transposes, and identity
matrices are defined once for every finite dimension. Cauchy–Schwarz with its
equality case, orthogonal projection, and an unnormalized Gram–Schmidt step
are proved in this setting. Abstract vector spaces with bases and dimension
are not yet developed, and determinants over abstract commutative rings
live in Algebra.

## Geometry

`Grace.Cumulus.Geometry` is plane geometry over the Dedekind reals with
named points, Euclidean distance as a real square root, and the cosine of an
angle as a normalized dot product. Pythagoras and its converse, the triangle
inequality, the law of cosines, the isosceles and Thales theorems, midpoints,
medians, centroids, circumcenters, the Euler line, Heron's formula, and the
power of a point are stated in these terms. Public theorems use geometric
lemmas; the coordinate identities behind them stay in a helper layer.

## The Banach–Tarski paradox

`Grace.Cumulus.Geometry.BanachTarski` proves that the closed unit ball of ℝ³
is paradoxical under the orientation-preserving isometries: `banachTarski`
gives two disjoint subsets of the ball, each equidecomposable with the whole
ball under the motions of ℝ³, and `banachTarski.two_balls_part` a part of
the ball equidecomposable with the disjoint union of the ball and a
translate of it. `Geometry.BanachTarski.Strong` proves the strong form,
`banachTarski.two_balls`: the ball itself is equidecomposable with that
disjoint union of two balls, by the Banach–Schröder–Bernstein theorem of
`Algebra.Group.Paradox.SchroederBernstein` (mutual embeddings by
equidecomposable subsets give equidecomposability, through the piece maps
of `Algebra.Group.Paradox.PieceMaps` and the back-and-forth chain of
`Cardinal.Dominance`). `Algebra.Group.Words` and `Algebra.Group.FreeGroup` build the free group
on two generators as reduced words; `Rotation.Freeness` proves
Swierczkowski's theorem that two rotations generate it freely, by integer
vectors modulo 5; `Geometry.Hausdorff` proves Hausdorff's paradox on the
sphere minus the countable set of points fixed by nontrivial words, through
a free action and the transfer theorem of `Algebra.Group.Paradox`;
`Geometry.Absorption` and `Geometry.Sphere` absorb that countable set by a
rotation of infinite order, so the sphere is paradoxical; `Geometry.Euclid`
lifts the pieces to cones in the punctured ball and absorbs the center by a
rotation about an off-center axis. The audit of `banachTarski` names the ZF
axioms and the axiom of choice, used exactly for the orbit representatives.

## Graph theory

`Grace.Cumulus.GraphTheory` provides simple graphs, induced subgraphs,
complements, reachability and connectivity for graphs of arbitrary
cardinality, the handshaking lemma, Ramsey's theorem for triangles,
multigraphs with walks, trails, and Euler trails, the Königsberg bridges,
and weighted paths with a structurally recursive, executable Dijkstra solver
proved correct for arbitrary graph sizes. See
[the correctness argument](dijkstra-correctness.md) for how an executable
algorithm and its proof live together in Cumulus.

## Fixed points and games

`Grace.Cumulus.FixedPoint` proves the Knaster–Tarski theorem for monotone
maps on a powerset and Brouwer's fixed point theorem for the cube by way of
a combinatorial labelling argument, and `Grace.Cumulus.GameTheory` applies
Brouwer to prove that finite polymatrix games have a Nash equilibrium.

## How the library grows

The library grows by subject, and the [Top 100](top-100.md) records which of
the classical results are verified, which are proved in a restricted scope,
and which are planned. Cumulus is much smaller than mature mathematical
libraries, and large areas of mathematics are not yet represented. When an
elementary proof is awkward, the elaborator or the tactic language is
improved without enlarging the trusted kernel, and a feature goes in when a
Cumulus proof shows the need for it. Contributions of mathematics, better
proofs, and awkward examples are all welcome; see
[contributing](../CONTRIBUTING.md).
