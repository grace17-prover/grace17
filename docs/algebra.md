# Algebraic hierarchy

An algebraic structure in Cumulus is represented as a set. A group `G` is a
[structure](datatypes.md#structures) value bundling a carrier with its
operations, read back by the projections `G.carrier`, `G.mul`, `G.one`,
and `G.inv`, and `Group(G)` is the predicate saying the value satisfies the
group laws. Rings, fields, orders, lattices, and categories are built the
same way. Under a hypothesis `Group(G)` or `CommRing(R)` a proof writes
`a * b`, `a⁻¹`, `x + y`, `-x`, and `R[2]`, binds `(a b : G)` and
`(x : R)` as carrier membership, and has the closure facts and rewrite sets
of the area at hand.

The kernel knows nothing about algebra. A carrier is a set or a `Class`;
operations are set-theoretic graphs when their domains are sets and
formula-level interfaces when a carrier is a proper class; a structure
value is a datatype value, so its fields are sets; and every law is a
first-order statement about those sets. The surface type system treats
membership in a carrier as a soft typing judgment.

## Structures

A `structure` declaration names the fields and the laws:

```g17 fragment
structure Group
  | carrier : Set
  | mul : carrier × carrier → carrier
  | one : carrier
  | inv : carrier → carrier
  where
    mul_assoc : ∀ a b c ∈ carrier, mul(mul(a, b), c) = mul(a, mul(b, c))
    …
```

A field's type is a soft type over the earlier fields, so `one : carrier` is
`one ∈ carrier` and `mul : carrier × carrier → carrier` is
`FunctionBetween(mul, carrier × carrier, carrier)`; these typings are the
first conjuncts of the predicate, before the laws. It produces a constructor
`Group.mk(A, m, e, i)`, the projections with their laws (`Group.mk.mul :
Group.mk(A, m, e, i).mul = m`, gathered in `group_projections`), the shape
`Group.Data(G)`, the predicate `Group(G)` (the shape with the laws at the
projections), and `Group.intro`, which builds a group from its pieces and the
laws. A stronger structure is usually a predicate over the same value:
`AbelianGroup(G)` is `Group(G)` with a commutative operation, `CommRing(R)` is
`Ring(R)` with a commutative multiplication, `Field(R)` is a ring value with
the field laws at its projections. A structure with more data extends the
others: `structure Ring extends AbelianGroup as additive (…), Monoid as
multiplicative (…)` takes its fields from its parents and carries them as
the values `R.additive` and `R.multiplicative`, each with its predicate as
an instance; see [extending a structure](datatypes.md#extending-a-structure).
The bundled structure is the
mathematical object and keeps the plain noun; the parameterized predicates
over separate pieces carry an `Is` prefix, `IsGroup(A, op, unit, inv)` and
`IsCommRing(A, add, zero, neg, mul, one)`, and are what the concrete number
systems and the engine modules use. The bridges `Group.parts` and
`Group.of_parts` (likewise for rings and fields) move between them, so an
instance for the integers becomes the bundled value `integerRing` and a
bundled hypothesis supplies the parameterized predicate to `with *`,
`typecheck`, and `ring`.

Three conventions make a bundled structure pleasant to work under, and
each area declares them for its own structure:

- **Hypothesis notation.** `notation infixl 70 "*" => call2(G.mul, _, _)
  via hypothesis Group(G) for G.carrier` binds an operator to a projection
  whenever a hypothesis `Group(G)` is in scope and an operand lies in the
  carrier; see [notation](notation.md#operations-supplied-by-a-hypothesis).
  Constants, prefix, and postfix forms work the same way, as `⊥`, `⨆ S`,
  and `aᶜ` do for lattices.
- **Carrier binders.** `(a b : G)` in a theorem header is `a b ∈ G.carrier`,
  and `x ∈ G`, `S ⊆ G`, `Finite(G)`, and `cardinality(G)` read the carrier
  off the structure variable, so statements mention `G` and not
  `G.carrier`.
- **Closure instances and rewrite sets.** `Group.mul_mem`, `Group.one_mem`,
  `Group.inv_mem`, and `Group.pow_mem` are instances, so the carrier
  membership of a compound term is synthesized, and `group_simp`,
  `ring`, and `lattice_simp` rewrite with the laws of the area.

## Groups

`Grace.Cumulus.Algebra.Group.Basic` declares the group structure in full:

<!-- cumulus-source: lib/Grace/Cumulus/Algebra/Group/Basic.g17 -->
```g17
structure Group
  | carrier : Set
  | mul : carrier × carrier → carrier
  | one : carrier
  | inv : carrier → carrier
  where
    mul_assoc : ∀ a b c ∈ carrier, mul(mul(a, b), c) = mul(a, mul(b, c))
    one_mul : ∀ a ∈ carrier, mul(one, a) = a
    mul_one : ∀ a ∈ carrier, mul(a, one) = a
    inv_mul : ∀ a ∈ carrier, mul(inv(a), a) = one
    mul_inv : ∀ a ∈ carrier, mul(a, inv(a)) = one
```

The field types are part of the predicate: `Group(G)` says that `G.mul` is a
function `G.carrier × G.carrier → G.carrier`, `G.one ∈ G.carrier`, and `G.inv
: G.carrier → G.carrier`, before the laws, and `Group.intro` takes those
typings and then the laws. `Monoid(G)` is the Foundation monoid at the
projections and `AbelianGroup(G)` a group whose operation commutes;
`Group.parts` and `Group.of_parts` bridge to `IsGroup(A, op, unit, inv)` over
separate pieces (likewise for monoids and abelian groups).

Under a hypothesis `Group(G)` the operation is `a * b`, the inverse `a⁻¹`,
the power `a ^ n`, and a binder `(a b : G)` is membership in the carrier;
see [notation](notation.md#groups-carrier-binders-and-unary-operations).
The laws are stated under short standard names on such binders, and
`group_simp` is the rewrite set of associativity to the right with the unit
and inverse cancellations. The rest of the area is
built on this basis: `Subgroup(H, G)` with the binder `(h : H)` and the
instances `Subgroup.mul_mem`, `Subgroup.one_mem`, `Subgroup.inv_mem`;
cosets `g • H` (the set `leftCoset(G, g, H)`) and the coset space
`leftCosets(G, H)`, which partitions the group; the order `order(G)` of a
group and the index `index(G, H)` of a subgroup, with Lagrange's theorem
`order(G) = index(G, H) * cardinality(H)` and `cardinality(H) ∣ order(G)`
for a finite group, and `elementOrder(G, g) ∣ order(G)`;
homomorphisms `f : G →* H` with `GroupHom.map_mul`, `map_one`, `map_inv`,
`map_pow`; the kernel `ker(f)` (the set `kernel(f, G, H)`) and the image
`functionImage(f, G.carrier, H.carrier)`; `NormalSubgroup(N, G)` with
`conjugate(G, g, x)`;
the quotient group `G ⧸ N` (the value `quotientGroup(G, N)`, written with
the group as the left operand under a group or normal-subgroup hypothesis)
with its projection; the first isomorphism theorem
`inducedMap(f) : G ⧸ ker(f) ≃* H`, the induced map being the descent of
`f` to the quotient by its kernel;
`productGroup(G, H)`; `subgroupGroup(G, H)`, the group on a subgroup;
`generatedSubgroup(G, S)`, `powers(G, g)`, `elementOrder(G, g)`,
`centralizer(G, S)`, `center(G)`, and `f : G ≃* H`.

## Rings

`Grace.Cumulus.Algebra.Ring.Basic` declares a ring as the child of its two
parents, the additive abelian group and the multiplicative monoid:

<!-- cumulus-source: lib/Grace/Cumulus/Algebra/Ring/Basic.g17 -->
```g17
structure Ring extends
    AbelianGroup as additive (mul := add, one := zero, inv := neg),
    Monoid as multiplicative (inv := ∅)
  where
    distributive : Distributive(carrier, add, mul)
```

The fields of the parents are the ring's own: `carrier`, `add`, `zero`,
and `neg` from the abelian group, whose operation, unit, and inverse are
renamed, and `mul` and `one` from the monoid, whose inverse slot, which
`Monoid` does not constrain, is fixed to `∅`. The parents are the values
`R.additive = Group.mk(R.carrier, R.add, R.zero, R.neg)` and
`R.multiplicative = Group.mk(R.carrier, R.mul, R.one, ∅)`, and `Ring(R)`
is the shape, the typing of the six fields, `AbelianGroup(R.additive)`,
`Monoid(R.multiplicative)`, and `Distributive(R.carrier, R.add, R.mul)`,
so `obtain ⟨shape, addF, zeroIn, negF, mulF, oneIn, additive,
multiplicative, distributive⟩ := ring` opens a hypothesis `Ring(R)`, the
five field typings first. The instances `Ring.additive.abelian_group` and
`Ring.multiplicative.monoid` give the parents' predicates wherever `Ring(R)`
is, and `Ring.additive.mem` places the ring's elements in the parent's
carrier, so a theorem about abelian groups applies to `R.additive` by
`with *`; `ring_additive` and `ring_multiplicative` rewrite the parent's
projections, `R.additive.mul`, to the ring's own, `R.add`.
`Ring.mk(A, add, zero, neg, mul, one)` is a ring
value, read back by `R.carrier`, `R.add`, `R.zero`, `R.neg`, `R.mul`, and
`R.one`, with the projection laws gathered in `ring_projections`. The
stronger structures are predicates over the same value: `CommRing(R)` is
`Ring(R)` with a commutative multiplication, `Field(R)` is `IsField` at the
projections (an inverse exists for every nonzero element; no inverse graph
is part of the data), and `OrderedField(R, lt)` adds a strict linear order
compatible with the operations. The parameterized forms
`IsCommRing(A, add, zero, neg, mul, one)`, `IsField(…)`,
`IsFieldWithInverse(…, inv)`, and `IsOrderedField(…, inv, lt)` remain the
engine underneath, and the bridges
go both ways: the instances `Ring.parts`, `CommRing.parts`, and
`Field.parts` read the parameterized predicate off a bundled hypothesis, so
`with *`, `typecheck`, and `ring` see it, and `Ring.of_parts`,
`CommRing.of_parts`, `Field.of_parts`, `Field.of_inverse`, and
`OrderedField.of_parts` bundle a parameterized instance;
`CommRing.of_projections` and `Ring.of_projections` close the loop for a
value whose shape is known. The closure facts `Ring.add_mem`, `Ring.mul_mem`,
`Ring.neg_mem`, `Ring.zero_mem`, `Ring.one_mem`, and `Ring.numeral_mem` are
instances, so the carrier membership of a compound term is synthesized.

Under a hypothesis `Ring(R)`, `CommRing(R)`, `Field(R)`, or
`OrderedField(R, lt)` the operations are `x + y`, `x * y`, and `-x`, a
binder `(x : R)` is membership in the carrier, and `R[0]`, `R[1]`, `R[2]`
are the ring's own constants and numerals, so a section reads

```grace17 import=Grace.Cumulus.Algebra.Ring
section Rings
variable (R : Set)
hypothesis ring : CommRing(R)

theorem square_sum (x y : R)
  shows (x + y) * (x + y) = x * x + R[2] * (x * y) + y * y
proof
  ring
end Rings
```

and `ring`, `ring_nf`, and `linear_combination` read the operation graphs
off `R.add`, `R.mul`, `R.neg`, `R.zero`, and `R.one` through
`CommRing.parts`. An existing instance becomes a bundled value by
`CommRing.of_parts`: `integerRing := Ring.mk(ℤ, integerAdd, integerZero,
integerNeg, integerMul, integerOne)` with `CommRing(integerRing)`, after
which `square_sum` instantiates at it with the same notation, `(x + y) *
(x + y) = x * x + integerRing[2] * (x * y) + y * y` for `x y ∈
integerRing.carrier`, the closed instance supplying the operations. The
parameterized section form with `notation ring R := (A, add, zero, neg,
mul, one)` is described in
[ring scopes over separate pieces](#ring-scopes-over-separate-pieces).

### Ideals, quotients, and homomorphisms

The ideal theory is stated over the same structure. Under a hypothesis
`Ring(R)` an ideal is `Ideal(R, I)`, a predicate defined inside a section
on that hypothesis as

```g17 fragment
predicate Ideal (I : Set) :=
  I ⊆ R ∧ R[0] ∈ I ∧ (∀ x y ∈ I, x + y ∈ I) ∧
  (∀ x ∈ I, -x ∈ I) ∧ (∀ a ∈ R, ∀ x ∈ I, a * x ∈ I ∧ x * a ∈ I)
```

which is a formula over the projections of `R`; `ProperIdeal(R, I)`,
`MaximalIdeal(R, M)`, `PrimeIdeal(R, I)`, and `Subring(R, S)` are defined
the same way. Under `Ideal(R, I)` a binder `(x : I)` is `x ∈ I` and the
elements of `I` carry the ring notation, and the closure facts
`Ideal.zero_mem`, `Ideal.add_mem`, `Ideal.neg_mem`, `Ideal.sub_mem`,
`Ideal.mul_left_mem`, and `Ideal.mul_right_mem` are instances, so
`a * x + y ∈ I` for `(a : R)` and `(x y : I)` is synthesized.

The quotient by an ideal is the ring value `quotientRing(R, I)`, written
`R ⧸ I` under `Ring(R)`, `CommRing(R)`, or `Ideal(R, I)` with the ring as the
left operand (the set quotient `A ⧸ r` is unchanged on every other left
operand), on the classes of `quotientRelation(R, I)`, with
`quotientRing.comm_ring`, `quotientRing.class_eq_iff`
(`⟦x⟧ = ⟦y⟧ ↔ x - y ∈ I`), and `quotientRing.projection_hom`. A
homomorphism is the guard `f : R →+* S`,
which opens to `Ring(R)`, `Ring(S)`, the function, and the preservation of
zero, one, negation, addition, and multiplication (`RingHom.map_zero`,
`map_one`, `map_neg`, `map_add`, `map_mul`, `map_sub`, and the instance
`RingHom.map_mem`); `f : R ≃+* S` is a bijective one. The kernel `ker(f)`,
the set `ringKernel(f, R.carrier, S.zero)`, is an ideal by
`ringKernel.ideal`, the map `f` induces on the quotient by its kernel is
`inducedMap(f)`, and for a surjective `f` the first isomorphism theorem
reads

```g17 fragment
theorem RingHom.first_isomorphism
  requires onto : SurjectiveBetween(f, R.carrier, S.carrier)
  shows inducedMap(f) : R ⧸ ker(f) ≃+* S
```

Both names are [functions supplied by the
hypothesis](notation.md#functions-supplied-by-a-hypothesis) `f : R →+* S`.

Generated ideals are `generatedIdeal(R, G)`; a maximal ideal lies above
every proper ideal (`ProperIdeal.extends_maximal`, `MaximalIdeal.exists`,
`MaximalIdeal.prime`); and the correspondence theorems are
`idealComap.ideal`, `idealMap.ideal`, `RingHom.correspondence`, and, for a
surjection, `idealComap.prime_iff` and `idealComap.maximal_iff`.

The forms over separate pieces, `IsIdeal(A, add, zero, neg, mul, I)`,
`IsRingHom(f, A, …, B, …)`, `IsSubring(A, …, S)`, and the rest, remain the
engine in `IdealCore`, `PrimeIdealCore`, `QuotientCore`,
`HomomorphismCore`, and `SubringCore`, where the closure facts are
`IsIdeal.add_closed`, `IsIdeal.zero_closed`, `IsIdeal.subset_carrier`, and so
on. The instances `Ideal.parts`, `PrimeIdeal.parts`, `RingHom.parts`, and
`Subring.parts` read them off a bundled hypothesis, and `Ideal.of_parts`
and `Ideal.of_projections` (likewise for the others) come back for a ring
value. Under a ring scope, `IsIdeal(R, J)` names the predicate over the
scope's six pieces, and `Ideal(R, J)` always means the bundled one.

### Polynomial rings

Polynomial rings are bundled the same way. Under `CommRing(R)` the value
`polynomialRing(R, I)` is `Ring.mk` of the finite-support coefficient maps
on the monomials in the variables `I` with the convolution operations, and
the instance `polynomialRing.comm_ring` makes it a commutative ring, so
`Ideal(polynomialRing(R, I), J)`, `MaximalIdeal(polynomialRing(R, I), M)`,
and `g : polynomialRing(R, I) →+* S` are the bundled predicates at it. The
instance supplies the ring the way a hypothesis does: a binder
`(p q : polynomialRing(R, I))` is membership in its carrier, so is
`p ∈ polynomialRing(R, I)`, its elements carry `p + q`, `p * q`, and
`p - q`, its numerals are `polynomialRing(R, I)[2]`, and `ring` proves
identities between polynomials, with no hypothesis naming the instance; see
[notation](notation.md#rings-supplied-by-a-hypothesis). The
variables are `X(R, I, j)` and the constants the homomorphism
`polynomialConstant(R, I) : R →+* polynomialRing(R, I)`. Evaluation at
`v : I → S.carrier` through `f : R →+* S` is
`evaluationHom(R, S, I, f, v) : polynomialRing(R, I) →+* S`, with
`evaluationHom.map_constant`, `evaluationHom.map_X`, and the universal
property `polynomialRing.universal`: it is the only homomorphism extending
`f` and sending each `X(R, I, j)` to `v(j)`; `evaluationAt(R, I, v)` is
evaluation at a point of `R`. The polynomials vanishing at `v` form
`pointIdeal(R, I, v)`, an ideal by `Ideal.point`, the kernel of
`evaluationAt(R, I, v)`, maximal over a field by `MaximalIdeal.point`, and
over an algebraically closed field `AlgebraicallyClosed(R)` the weak
Nullstellensatz `polynomialRing.unit_iff_no_common_zero` says that `R.one`
lies in `generatedIdeal(polynomialRing(R, I), G)` exactly when `G` has no
common zero. In one variable, `horner(R, leading, x, cs)` is the value of
the Horner form with lower coefficients `cs`, `horner.remainder` and
`horner.factor` are the remainder and factor theorems with the synthetic
quotient `syntheticQuotient(R, leading, a, cs)`,
`hornerPolynomial(R, I, j, leading, cs)` is the same form inside
`polynomialRing(R, I)`, and over `Field(R)` a nonzero form has the finite
root set `rootSet(R, leading, cs)`. The engine over separate pieces,
`polynomials(I, A, zero)` with `polynomialAt`, `polynomialAtOver`, and
`pointIdeal(I, A, …, v)`, stays in the `Polynomial` modules, bridged by
`polynomialRing.engine`, `Ideal.polynomial_parts`,
`Ideal.polynomial_of_parts`, `MaximalIdeal.polynomial_parts`,
`RingHom.polynomial_parts`, and their converses, and by the `.graph` and
`.engine` lemmas of each bundled function.

## Modules

`Grace.Cumulus.Algebra.Module.Basic` declares a module over a ring as the
abelian group of its vectors extended by a scalar action:

<!-- cumulus-source: lib/Grace/Cumulus/Algebra/Module/Basic.g17 -->
```g17
structure Module (R : Ring) extends
    AbelianGroup as additive (mul := add, one := zero, inv := neg)
  | smul : R.carrier × carrier → carrier
  where
    smul_add : ∀ r ∈ R.carrier, ∀ v w ∈ carrier,
      smul(r, add(v, w)) = add(smul(r, v), smul(r, w))
    add_smul : ∀ r s ∈ R.carrier, ∀ v ∈ carrier,
      smul(r + s, v) = add(smul(r, v), smul(s, v))
    mul_smul : ∀ r s ∈ R.carrier, ∀ v ∈ carrier,
      smul(r * s, v) = smul(r, smul(s, v))
    one_smul : ∀ v ∈ carrier, smul(R.one, v) = v
```

The parameter `(R : Ring)` makes `Ring(R)` the first conjunct of
`Module(M, R)` after the shape, so the ring's `r + s` and `r * s` are
available in the laws; `Module.mk(A, add, zero, neg, smul)` is a module
value, read back by `M.carrier`, `M.add`, `M.zero`, `M.neg`, and `M.smul`,
with the additive group `M.additive` and `AbelianGroup(M.additive)` as the
instance `Module.additive.abelian_group`. Under hypotheses `Ring(R)` and
`Module(M, R)` the operations are `v + w`, `-v`, and `r • v`, the
operands' carriers deciding between the module's `+` and the ring's, and a
binder `(v : M)` is membership in the carrier:

```grace17 import=Grace.Cumulus.Algebra.Module.Basic
section Modules
variable (R M : Set)
hypothesis ring : Ring(R)
hypothesis module : Module(M, R)

theorem two_smul (r : R) (v : M)
  shows (r + r) • v = r • v + r • v
proof
  exact add_smul with *
end Modules
```

The closure facts `Module.add_mem`, `Module.neg_mem`, `Module.zero_mem`,
and `Module.smul_mem` are instances. The additive laws `Module.add_comm`,
`Module.add_assoc`, `Module.zero_add`, `Module.add_zero`, `Module.neg_add`,
and `Module.eq_zero_of_add_self` are the group laws applied to
`M.additive`, each proved by instantiating the group theorem at
`M.additive` with `with group, *` and rewriting with `module_additive`;
`smul_add`, `add_smul`, `mul_smul`, and `one_smul` restate the structure's
laws under the notation, and `zero_smul` and `smul_zero` follow from them.
A ring is a module over itself: `selfModule(R)` is
`Module.mk(R.carrier, R.add, R.zero, R.neg, R.mul)`, and the instance
`Ring.to_module` gives `Module(selfModule(R), R)` from `Ring(R)`.

## Orders and lattices

`Grace.Cumulus.Lattice.Order` bundles an ordered set as
`structure Order | points le : Set`, a carrier with the graph of its
order, without laws: `Preorder(P)`, `PartialOrder(P)`, `LinearOrder(P)`,
`Lattice(P)`, `DistributiveLattice(P)`, `ModularLattice(P)`,
`BoundedLattice(P)`, `CompleteLattice(P)`, and `BooleanAlgebra(P)` are
the Foundation predicates at the projections `P.points` and `P.le`, and
the parameterized forms `IsLattice(A, r)` and the rest stay the engine
underneath. Under such a hypothesis the order is `a ≤ b` (a predicate
supplied by the hypothesis, with the typed `≤` of the number systems as
the fallback), a binder `(a b : P)` is membership in the points, the join
and meet are `a ⊔ b` and `a ⊓ b`, the bounds of a bounded lattice `⊥` and
`⊤`, the suprema and infima of a complete lattice `⨆ S` and `⨅ S`, and the
complement of a Boolean algebra `aᶜ`. The lattice laws carry short
standard names, `sup_comm`, `sup_assoc`, `sup_absorb`, `inf_absorb`,
`bot_le`, `le_top`, `le_sSup`, `sInf_le`, `compl_compl`, and
`lattice_simp` is their rewrite set. Monotone and antitone maps,
`MonotoneMap(f, P, Q)` and `AntitoneMap(f, P, Q)`, Galois connections
`GaloisConnection(l, u, P, Q)`, closure operators, lattice homomorphisms,
sublattices, and lattice ideals and filters are predicates over the same
values. In a complete lattice the least and greatest fixed points of a
monotone map are `lfp(f)` and `gfp(f)`, definitions inside the section on
the lattice, with `lfp_fixed : f(lfp(f)) = lfp(f)`, `lfp_le`, `lfp.unfold`,
`lfp.eq_sInf`, and the instance `lfp.member`, and
`IsMonotoneMap.exists_fixed_point` is the fixed-point theorem of Knaster and
Tarski; see [notation](notation.md#orders-supplied-by-a-hypothesis).

## Ring scopes over separate pieces

A development over a concrete number system, a polynomial ring, or a
quotient has its ring as six separate pieces, and the parameterized
predicates `IsCommRing(A, add, zero, neg, mul, one)`, `IsIdeal(A, add, …,
J)`, and `IsRingHom(f, A, add, …, B, plus, …)` take all of them. A
`notation ring`
declaration names such a tuple for the rest of a theorem section, and
ordinary syntax then resolves against it:

```grace17 import=Grace.Cumulus.Algebra.Ring
section Rings
variable (A add zero neg mul one : Set)
hypothesis source : IsCommRing(A, add, zero, neg, mul, one)
notation ring R := (A, add, zero, neg, mul, one)

theorem simplify (x y : Set)
  requires hx : x ∈ A
  requires hy : y ∈ A
  shows (x + y) * 1 - y + 0 = x
proof
  ring
end Rings
```

The declaration binds syntax only; functionhood, closure, and the ring laws
stay proof obligations. Under it, `x + y` is `add(x, y)`, the kernel term
`call2(add, x, y)`; `x * y` is `mul(x, y)`; `-x` is `apply(neg, x)`;
`x - y` is `add(x, neg(y))`; `0` and `1` are `zero` and `one`; a larger
numeral is `ringNat(add, zero, one, n)`, which goals print as the numeral
again and `ring` treats as a coefficient; `x ^ n` is `monoidPow` for the
ring's multiplication (import `Grace.Cumulus.Algebra.Group.Power`), with a
natural exponent. Multiplication binds more tightly than addition, unary
minus more tightly than multiplication, and a numeral annotation such as
`(2:Nat)` keeps a natural index natural inside the scope. A complete
checked file is [ScopedRingNotation.g17](../examples/ScopedRingNotation.g17).

**Scoped forms.** A scope name stands for its pieces in `IsCommRing(R)`,
`IsIdeal(R, J)`, `IsRingHom(f, R, S)`, `determinant(n, R, M)`, and the
other predicates and functions over separate pieces, and those print back
the same way. Which ones take a scope name is declared beside them:

```g17 fragment
notation scoped IsIdeal(R, I) => IsIdeal(R.carrier, R.add, R.zero, R.neg, R.mul, I)
```

The written parameters are pattern variables, and each argument of the
target is one passed through or a piece of one, `R.carrier`, `R.add`,
`R.zero`, `R.neg`, `R.mul`, or `R.one`, which must name an active scope; a
parameter used only as `R.carrier` also accepts a set. A development
declares the same for its own predicates and functions, and the form is
visible wherever its module is imported.

**Several rings.** A second declaration `notation ring S := (B, plus, z,
minus, times, unit)` may stand in the same or a nested section. Which ring
an operator means is decided syntactically from the context, with no
search: a local membership `x ∈ A` selects `R` for `x + y`, and a local
`IsRingHom` or `FunctionBetween` fact for `f : A → B` selects `S` for
`f(x) + f(y)`. When nothing decides, the elaborator reports ambiguity
rather than choosing by declaration order, and a named term scope decides
explicitly: `f(R[x * y]) = S[f(x) * f(y)]`, or `f(R[1]) = S[1]` for
constants. `R[…]` chooses operations and asserts nothing about membership.

**Constructed rings.** With `Grace.Cumulus.Algebra.Polynomial.Ring`
imported, a scope can name the rings built from another:

```grace17 fragment
notation ring P := R[I]        -- polynomials over R in the variables I
notation ring Q := P ⧸ J       -- the quotient by an ideal candidate J
notation ring L := R ↾ T       -- the operations restricted to T
```

Each expands to the six pieces of the constructed ring: the
finite-support polynomial carrier with its operations, the quotient carrier
with the induced operations and the classes of zero and one, or
`(T, restrict(add, T × T), zero, restrict(neg, T), restrict(mul, T × T),
one)`. The registered instance `polynomials.comm_ring` gives `P` its ring
laws from the laws of `R`, so `ring` works in `P` directly, including for
iterated polynomial rings; `Q` is a ring once `J` is an ideal, and `L`
needs `IsSubring(R, T)`. None of this is assumed by the declaration. A ring
name on its own denotes its carrier, as in `p ∈ P` and `∃ p ∈ P`, and
goals print the constructed carriers by their scope names.

**Predicates and objects.** Every library form over a ring's pieces accepts
a scope name in their place and expands to the full argument list, with no
laws inferred: `IsCommRing(R)`, `IsField(R)`, `IsIntegralDomain(R)`,
`IsIdeal(R, J)`, `IsMaximalIdeal(P, M)`, `IsSubring(R, S)`,
`IsRingHom(f, R, S)`, `IsRingIso(f, R, S)`, and the polynomial, matrix,
and finite-sum
constructions such as `polynomialAt(I, R, v)`, `pointIdeal(I, R, v)`,
`idealSpan(P, G)`, `generatedSubring(R, G)`, `algebraAdjoin(f, R, S, G)`,
`determinant(n, R, M)`, and `finiteRingSum(V, R, w)`. A slot that needs
only a carrier also accepts a plain set. Declare the scope before the
hypothesis that uses it. User-defined predicates and functions of the same
name keep precedence. Goals display the compact form when exactly one
active scope matches the components, and the full argument list otherwise.
The polynomial examples in `examples/` use these forms throughout, from
difference of squares to the Nullstellensatz reduction.

**Lifetime.** A scope lives in its theorem section, nested sections inherit
it, and ending a section removes the scopes it introduced. A shared
hypothesis is parsed with the scopes active where it is declared. Names
must differ from other active scopes and from section variables. Scopes
are not exported through imports and add nothing to kernel declarations.
With a scope `notation ring R := (A, add, …)` active, `IsCommRing(R)` is
the six-place predicate at the scope's pieces, while `CommRing(R)` always
means the predicate over a structure value; the bridges above move between
them. Division, order, scalar actions, and user-defined
scoped operators are not part of the mechanism.

## The parameterized hierarchy underneath

`Grace.Cumulus.Algebra.Foundation` defines `IsMagma`, `IsSemigroup`,
`IsMonoid`, `IsCommMonoid`, `IsGroup`, `IsAbelianGroup`, `IsSemiring`,
`IsRing`, `IsPreorder`, and `IsPartialOrder` as predicates over carrier
sets and operation graphs. Each
stronger predicate projects to the weaker ones through checked first-order
theorems, and the laws of a bundled structure are these predicates at its
projections, as `structure Ring` above shows. The engine modules of the
ideal theory and of polynomial rings (`IdealCore`, `QuotientCore`,
`HomomorphismCore`, `polynomials(I, A, zero)` with its operations) are
stated over separate pieces in this style, and the bundled layers above
bridge to them. For set-sized algebra, operations are function graphs;
native execution may use a proved computational realization of such a
graph.

## Instances and resolution

An `instance` declaration is a theorem whose conclusion is a structure
predicate. It is checked like any theorem and then entered in an untrusted,
import-scoped registry. `synthesize`, `with *`, and notation queries search
that registry. The search is first-order: the key is the predicate and the
known argument structure, search has depth and work bounds, success and
failure are memoized, and two global candidates that both succeed are an
error. A successful result is a proof of the requested predicate, so
resolution is predictable and a missing law produces a useful diagnostic.
See [types.md](types.md) for the registry's rules and limits.

## Numerals, operators, and zero

Foundation proves that the von Neumann natural `0` is the empty set. A ring's
zero need not be that set. A surface literal or operator is elaborated from
its expected carrier through a registered instance:

```text
0       ↝ OfNat.zero(instance)
7       ↝ OfNat.fromNat(instance, 7)
x + y   ↝ call2(operation, x, y)   via AddOperation(carrier, _)
```

An operation graph is a set of ordered pairs, and it applies as a function:
`op(x, y)` is `call2(op, x, y)`, the value of `op` at the pair `(x, y)`, and
`inv(x)` is ordinary function application. A theorem over the separate
pieces of a group therefore reads `shows op(inv(a), op(a, b)) = b`, and a
goal prints the same way; over a bundled group it reads
`a⁻¹ * (a * b) = b`, as described above. Inside a
theorem section with `notation ring R := (A, add, zero, neg, mul, one)` the
infix spellings `x + y`, `x * y`, and `-x` stand for the same terms.

Cumulus declares this notation with instance queries, for example
`notation infixl 60 "+" => call2 via AddOperation(ℚ, _) for Rational` and
`notation numeral "0" via OfNat(ℚ, 0, _) for Rational`. For `Nat`, the
canonical instance reduces these to compact kernel naturals. For integers,
rationals, reals, matrices, or residue rings, the instance selects that
structure's zero and its checked natural-number map. Without an expected
carrier, numerals default to `Nat`, and an ambiguous numeral is an elaboration
error. Coercions such as `Nat → Int` are named structure-preserving maps with
checked typing and homomorphism laws.

So you can write `0 + x = x`. The exported proof names the chosen instance
and zero; the kernel sees sets, function applications, predicates, and law
proofs. Inside a theorem section, a
[ring scope](#ring-scopes-over-separate-pieces) binds the same operator
syntax to a named structure's graphs.

Canonical names remain in certificates. Source and goal rendering use the
shortest unambiguous name available in the current module, so abstraction
does not make proof states unreadable.
