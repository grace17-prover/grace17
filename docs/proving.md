# Proving theorems in Grace17

This guide walks through writing proofs in Grace17: how a file is laid out,
how statements are read, what the basic moves are, how theorems are applied,
and where the automation can take over the routine work. It is the long form of
the Workbench **Help** panel. The per-tactic entries, with examples and the
natural-deduction rule each one reduces to, are in the
[tactic reference](tactics.md); declarations are in
[definitions](definitions.md); soft types and instances are in
[types](types.md); files, imports, namespaces, and sections are in
[modules, namespaces, and sections](modules.md). The guide starts with what
a first proof needs and reaches the elaboration machinery only at the end.

Tactics are untrusted. They transform goals and build a proof term, and the
kernel checks that term from scratch before admitting the theorem. A broken or
hostile tactic can fail, exhaust its budget, or produce a rejected proof. It
cannot prove a false statement. That is the whole trust story, and the rest of
this guide takes it for granted.

## Writing Grace17

A Grace17 file names its module, imports the mathematics it needs, and then
states and proves theorems. This complete file checks as it stands:

```g17
module My.FirstProof
import Grace.Cumulus.Main

theorem equality.copy (x y : Set)
  requires h : x = y
  shows x = y
proof
  exact h
```

The `module` line names the file, the `import` line brings in the compact
default library, and everything after that is mathematics. A theorem's
parameters introduce the objects under discussion, `requires` lists the
assumptions, and `shows` gives the claim. The `proof` block constructs
evidence for that claim, here by pointing at the assumption. Only after the
resulting proof term passes the kernel does the theorem become a checked fact
that later proofs may use with `exact`, `apply`, `specialize`, rewriting, and
the other tactics.

A file that imports a subject such as `Grace.Cumulus.NumberTheory` uses its
definitions and theorems by their short names. How module names relate to
file paths, how imports resolve, and how namespaces and sections organize a
larger development is the subject of
[modules, namespaces, and sections](modules.md); none of it is needed for a
first proof.

Definitions and statements are meant to look like mathematics. Use `def` when
a mathematical object is determined by some inputs. Its parameters come before
`:=`, and its value comes after it. A `predicate` instead names a relation or
property, while a `class` names a mathematical collection:

```g17
def duplicate (x : Set) : Set := {x, x}
predicate FixedBy (f x : Set) := f(x) = x
class Natural (x : Set) := Nat(x)
```

These declarations are conservative. A `def` introduces vocabulary and
asserts nothing that needs proof. Grace17 records its defining equation; later
proofs can unfold the definition, simplify with it, or use its raw name
directly. Notation is transparent in the same way: hover it to see the
underlying symbol.

Statements and steps are layout-aware, and one set of rules says when a
line continues the line above it. A more-indented line continues the
previous line when that line ended with a binary operator or a comma, or
left a parenthesis open; when it begins with a binary operator, `∧`, `∨`,
`→`, `∈`, `⊆`, and `∪` among them; when it begins with `at`, `with`, or
`using`; or when it follows a step that opens no block of its own
(`exact`, `apply`, `witness`, `refine`, `specialize`, `obtain`, `rw`,
`unfold`, `intro`, and their kin) and does not itself begin a step. So
`requires` and `shows` may be followed by an indented formula, itself
spanning several indented lines, with a return to the clause indentation
beginning the next clause or the `proof` block; a `have` proposition wraps
before or after an operator, with its proof block beneath the last line,
and may begin on the line after `have h :`; a proof expression after
`exact`, `witness`, `refine`, `apply`, or `have h :=` continues the same
way, so `have cancel := Thm` followed by a more-indented `at a, b, c with
h` is one application, as is an `at` list broken after a comma; and a
section's `hypothesis name : …` and `variable (…` continue on
more-indented lines too:

```g17
lemma combine (a b c : Set)
  requires
    hab : a = b
  shows
    a = b
    ∧
    c = c
proof
  constructor
  . exact hab
  . rfl
```

In the Workbench, type commands such as `\forall`, `\exists`, `\in`, `\to`,
`\iff`, `\and`, `\or`, and `\not`, then press Space, Tab, or Enter. Grace17
turns them into `∀`, `∃`, `∈`, `→`, `↔`, `∧`, `∨`, and `¬`. Every piece of
notation also has a plain ASCII spelling; see [notation](notation.md).

## The shape of a proof

Most proofs are built from a few moves. Read the goal, expose its outer
shape, and take the next small step:

| Goal or hypothesis | Tactic | Effect |
|---|---|---|
| `P -> Q` or `forall x, P` | `intro h` / `intro x` | introduce the premise or variable |
| several leading implications or quantifiers | `intros x hx y hy` | introduce their variables and premises from left to right |
| `P and Q` | `split` | make goals `P` and `Q` |
| `P <-> Q` | `split` | make goals `P -> Q` and `Q -> P` |
| nested `exists` and `and` | `refine ⟨a, ha, _⟩` | supply witnesses and facts together, leaving `_` as a goal |
| `P or Q` | `left` / `right` | choose a disjunct |
| `exists x, P(x)` | `witness t` or `use t` | supply the witness |
| `h : P and Q and R` | `rcases h with ⟨hp, hq, hr⟩` | recursively add all three conjuncts as facts |
| `h : P or Q` | `cases h with hp \| hq` | make one goal for each case |
| `h : P or Q or R` | `rcases h with hp \| hq \| hr` | flatten either association into three branches |
| `h : exists x, P(x) and exists y, Q(x,y)` | `obtain ⟨x, hx, y, hxy⟩ := h` | recursively open its witnesses and facts |
| packed data ending in `y = t` | `obtain ⟨y, hy, rfl⟩ := h` | open the data and substitute the equality immediately |
| any proposition from `⊥` | `exfalso` | change the goal to `⊥` |
| any proposition | `by_contra` | use checked classical double-negation elimination |
| any proposition | `by_cases h : P` | split into the cases `h : P` and `h : ¬P` |
| contradiction in context | `contradiction` | close by proof-producing logical search |

`by_cases h : P` is `have split : P ∨ ¬P by tauto` followed by `cases
split with h | h` in one step: two goals, the first with `h : P`, the
second with `h : ¬P`, each taking a bullet. `exact`, `show P := fact`,
`apply`, `assumption`, `have`, `unfold`, `rfl`, `compute`, and `simp`
provide the usual proof assembly and computation steps. `simp [f, h]` normalizes with checked definitions, equalities, and
ground computation, and closes a logical goal when its search succeeds; `rw h` rewrites forward and `rw ← h` backward; `symm`
reverses an equality goal and `symm at h` a named equality fact.
`specialize h with x, hx, y` instantiates alternating universal variables and
implication premises, replacing `h` with the resulting local fact.

### Patterns

`rcases` and `obtain` accept recursive patterns. Flat entries follow the usual
right-associated shape of `∧` and `∃`, nested brackets can make a subpattern
explicit, and `_` discards an entry:

```g17
-- packed : ∃ x, P(x) ∧ ∃ y, Q(x, y) ∧ R(y)
obtain ⟨x, hx, y, hxy, _⟩ := packed
```

The pattern is surface compression: Grace17 still emits each conjunction or
existential elimination separately. Destructuring follows transparent
predicates, so there is no need to `unfold P at h` before
`rcases h with ⟨…⟩`.

An `rfl` entry in an `rcases` or `obtain` pattern is equality elimination. If
packed data exposes `y = t` (or `t = y`), the pattern substitutes away the
discovered variable and rewrites the goal and local facts, so representation
equalities stay out of the rest of the proof.

Disjunction patterns may name every leaf at once:

```g17
rcases comparison with less | equal | greater
. exact less_case with less
. exact equal_case with equal
. exact greater_case with greater
```

The written disjunction may associate to the left or right. Grace17 reconstructs
the nested `∨E` proof in either case.

Construction has the matching `refine` form. It follows transparent predicate
definitions and recursively assembles nested `∃`, `∧`, and `↔` goals. A term
occupies an existential-witness position, a checked fact occupies a proposition
position, and `_` leaves that position as the next goal:

```g17
-- goal: ∃ x, x ∈ A ∧ ∃ y, y ∈ B ∧ R(x, y)
refine ⟨a, ha, b, hb, _⟩
-- goal: R(a, b)
```

Nested constructor patterns preserve grouping, and `?_`
leaves an entire proposition as a focused goal, including a conjunction or an
existential whose witness you want to supply later:

```g17
-- h : P ∧ (Q ∧ R); goal: (Q ∧ P) ∧ (∃ x, S(x))
refine ⟨⟨h.right.left, ?_⟩, ?_⟩
. exact h.left
. witness a
  exact ha
```

`_` is still a flattened leaf hole. `?_` is a hole for a proof; a term witness
must be written out. Every hole must be discharged before QED. Local
conjunction facts support `.left` and `.right`, nested as needed. Projections
work in proof expressions (`exact`, `have`, `apply`, `with`) and as rules for
`rw`, `simp`, and `simpa`. They can be applied to arguments, for
example `h.right at x with hx`, and an equivalence obtained by projection
supports `.forward` and `.backward`. They need a visible conjunction, so
unfold a named predicate first. Exact local names take priority; a dotted path
rooted in a local fact is resolved locally before global names, following only
the written path.

### Branches and local scope

For multi-step branches, put `.` at the branch boundary and indent the
tactics. A semicolon gives the same sequential meaning on one line
(`split; . rfl; . rfl`). Both are presentation only.

```g17
proof
  unfold BijectiveBetween
  constructor
  . have injective := compose.injective at g, f, A, B, C
    specialize injective with hf, hg
    exact injective
  . have surjective := compose.surjective at g, f, A, B, C
    specialize surjective with hf, hg
    exact surjective
```

A branch ends when its goal is closed. A step written after that in the
same branch, such as an `exact` after a `simp` that already closed the
goal, would be applied to the next goal; when it does not apply there, it
is reported as `no goals remain in this case; line 8 (simp [pow.two])
closed it`, naming the line that closed the branch, followed by the
message the step produced on the next goal.

Introduced term variables and existential witnesses belong to one proof goal,
like its assumptions and local facts. Sibling `have` proofs and sibling
constructor or case goals can reuse witness names:

```grace17
theorem local_witness_names (a : Set)
  requires inhabited : ∃ x, x = a
  shows a = a
proof
  have first : a = a
    obtain ⟨x, equation⟩ := inhabited
    rfl
  have second : a = a
    obtain ⟨x, equation⟩ := inhabited
    exact first
  exact second
```

Each `x` belongs only to its own local proof and is unavailable after that
proof closes. An outer witness remains in scope in nested proofs, so `obtain`
rejects an attempt to reuse its name there. See
[examples/DoubleSums.g17](../examples/DoubleSums.g17) for checked uses.

Unused assumptions need no mention. `clear h` removes a fact from the visible
context, `rename h => k` renames it, and `revert h` moves an assumption back
into the goal.

## Applying theorems

A proof expression may consume arguments immediately. Put mathematical terms
after `at`, then checked premise facts after `with`:

```g17
have result := transitive at x, y, z with hxy, hyz
exact result
```

The same expression works after `exact` or `apply`. Use `specialize` when the
unspecialized fact is already on the board and you want to replace it. Use
`with` when the applied result is the fact you want from the start.
Equivalences expose `.forward` and `.backward` directions. A `with` list
mixes facts and terms only where a fact instantiates the binders it
matches; a fact named where a binder wants a term is reported with the
entries of the list sorted into facts and terms and the `at` list to write
instead, and a named premise that fits no requirement is reported with its
formula and the requirement left open.

### Inferring parameters without an `at` list

For a source theorem, the `at` list is optional. Every parameter is found by
matching the conclusion against the goal, then the named premises against the
requirements, and finally the remaining requirements against local facts
that match uniquely:

```g17
exact insert.contains with remaining
exact Subset.antisymmetric with hBA, hAB
have imageRing := IsRingHom.image_comm_ring with source, target, hom
apply difference.membership.backward
```

Named premises may come in any order; each one is used where it matched.
Matching is structural, indexed by formula head, and capped at 2,048
attempts. It does not unfold definitions, backchain, or choose between
ambiguous substitutions, and quantified variables inside a premise stay local
to that premise. Carrier guards such as `Nat(n)`, and guards by a declared
class such as `Ordinal(α)`, are requirements too and are
discharged from local facts or by soft typing; a guard standing between the
supplied entries, after the last of a `with` list, or after an `at` list with
no `with` at all, is discharged on its own, so `choose.factorial at n` is the
equation and `mul.eq_zero with h` names only the product fact. A fact stated
through a defined predicate or class, such as `Rational(x)`, is accepted where
its body `x ∈ ℚ` is needed, and the other way round, by `exact`, `refine`,
a `with` entry, and a stated `have h : … := …`: the definition's equivalence
bridges the two. In the same
way `h.left`, `cases h with …`, `intros`, `constructor`, `left`, `right`, and
`witness` work through a defined predicate whose body has the shape they
need, unfolding a reducible head first. After `witness t` on
`∃ k, Nat(k) ∧ φ`, the carrier conjunct `Nat(t)` is discharged in the same
way and the goal is φ. A guard that
cannot be discharged stays as a premise of the named fact, or as the first
goal of an `apply`, where a line can prove it. Conflicting substitutions and
undetermined parameters produce an error asking for an `at` list, which is
always the fallback.

A bare `exact theorem` with an inferred instantiation discharges every
requirement from local facts, as `with *` does; the error names the first
requirement that has no evidence. A theorem named outside the import
closure is reported with the module that declares it, from the loaded
environment or the library under the module roots: `unknown proof
realDiv.eq_mul_inv; the library declares realDiv.eq_mul_inv in module
Grace.Cumulus.Real.Inverse, which this module does not import`.

Three more forms keep applications on one line. An anonymous constructor
`⟨a, b⟩` is a proof expression wherever its proposition is known, so a
conjunction or existential premise is supplied in place: `ih with y, ⟨hy,
earlier⟩`, `exact absent with ⟨J, hJ⟩`, and `have m : P := lemma.backward
with ⟨hJ, extendsJ⟩`; nested constructors go through predicate definitions,
as in `exact ⟨⟨x, hx⟩, hx⟩` for `Nonempty(S) ∧ x ∈ S`. When a requirement
is a conjunction and the `with` list supplies its conjuncts in order, they
are combined as the constructor would combine them, so `exact
difference.membership.backward with inSpace, notInjective` proves `x ∈ A ∖
B` from `inSpace : x ∈ A` and `notInjective : x ∉ B`; an entry that fits
no conjunct is still reported as matching no requirement. Parentheses group a
multi-premise application inside `refine ⟨…⟩`, where commas separate
components: `refine ⟨y, yInB, (constantFunction.relates with xInA, yInB)⟩`.
A local fact that is a transparent predicate application applies to
arguments through its definition, so `subset : A ⊆ B` gives `subset with x,
hx` without an `unfold Subset at subset` first; a predicate an application
derives takes further arguments the same way, so `transitive with hbInY, z,
hzInB` turns `Transitive(y)` into `z ∈ y`. Entries that are terms rather
than local facts keep their positional meaning, as in `have first :=
swapRows.two with a, b`, and switch inference off, except that evidence
standing where a binder is expected instantiates the leading binders from the
premise it matches.

`exact theorem.forward with *` and `exact theorem.backward with *` infer
parameters from the selected conclusion and unique local premise matches,
including the selected antecedent, which still needs evidence. The same works
in annotated local facts: `have h : P := theorem.backward with *`. An
implication or negation inside the selected conclusion stays intact.

Bare `apply theorem` uses the same matcher. Available generated carrier guards
are discharged; remaining requirements become subgoals in declaration order,
and missing carrier evidence also remains an obligation. `apply theorem.forward`
and `.backward` leave open requirements and the selected antecedent as goals
and stop when the residual conclusion equals the goal, preserving an
implication or negation that is itself the requested result. `apply theorem
with *` requests evidence for the declared premises; use bare `apply` when
those premises should remain to be proved.

`apply theorem at args` makes the carrier guards the first goals, before the
declared premise. When a premise needs its own derivation, prefer `have h : P`
followed by `exact theorem at args with *`.

Each proof component in `refine ⟨…⟩` and each direct `calc` justification
passes its own expected proposition to this inference. For example,
`refine ⟨first with *, second with *⟩` can infer different arguments for the two
components. The surrounding conjunction is not used as either component's goal,
and a complete conjunction or equivalence proof can fill its component directly.

### Filling routine premises with `with *`

Soft-type premises determined by the terms you supply are reconstructed from
the local context. For a source theorem, `with *` consumes its remaining
generated guards and declared `requires` clauses, then stops at `shows`. It
uses local evidence and the bounded instance and Tau machinery, and it does no
general propositional search. Refinement search has depth, work, and
term-growth limits (see [types.md](types.md)). If a premise is missing or
search runs out of budget, supply a named proof. For example:

```g17
theorem preserve (x y : Set)
  requires apart : x ≠ y
  shows x ≠ y
proof
  exact apart

theorem client (x y : Set)
  requires apart : x ≠ y
  shows x ≠ y
proof
  exact preserve at x, y with *
```

The final negation is preserved, even when evidence for its antecedent is
available. To apply an implication in the conclusion, name the evidence after
the star: `with *, evidence`. A named premise may precede `*` too. For local
proof values and declarations without source boundary metadata, `*` consumes
the leading implication chain and requires evidence for each implication. Name
the arguments when you want to keep a conditional local fact conditional.

`with *{3}, edge` expands to three `assumption` entries followed by `edge`.
The count is an integer from 1 to 256 and starts no search. A counted star
does not stop at the declared conclusion; it consumes the written number of
premises. That is how to pass a contradicting fact to a negated lemma, as in
`exact realLe.not_less at A, B with *{2}, le, lt`, and how to keep a remainder
when specializing a local fact: `specialize h with *{2}`.

`with *` finds local facts only. It does not find library theorems or prove
reflexivity, so bind `have one := realZero.lt_one` or `have same : t = t` with
`rfl` first, or list the premise.

## Local facts

`have h : P` opens an indented proof of the local proposition `P`. Once that
block closes, `h` is available in the surrounding proof as a checked local
lemma:

```g17
theorem conjunction_copy (P Q : Set)
  requires hP : P = Q
  shows P = Q ∧ P = Q
proof
  have diagonal : P = Q by exact hP
  constructor
  . exact diagonal
  . exact diagonal
```

Local proposition blocks may nest. A dedent resumes the surrounding goal;
dedenting while the local goal is unfinished produces a focused diagnostic.
A block can start immediately after a branch bullet, with its body indented
beneath the command and subsequent branch tactics aligned with that command:

```g17
  . have diagonal : x = x
      rfl
    exact diagonal
```

Local lemmas are scoped to their branch. Their proofs are reconstructed using
implication introduction and elimination, so a universally quantified local
lemma can be reused under a later binder with the same variable name without
capturing the lemma's bound variable. The local proposition is not available
as an assumption while proving itself. `have h := theorem at arguments` is the
short way to bind a fact that already exists.

Use `have h : P := fact with *` to supply an expected proposition for a
one-line local fact. As with `exact ... with *`, bounded structural inference
uses that proposition and the available premises to infer theorem parameters.
The annotation is checked against the proof even if `h` is never used; it
supplies no evidence and does not become an assumption while proving itself.
Missing evidence and ambiguous carriers are errors; an `at` list resolves
ambiguity. An unannotated `have` does not borrow the enclosing goal for
inference.

```g17
have diagonal : n = n := natural with *
```

A local fact with a short proof fits on one line with `by`, which runs
every tactic written after it, `;`-separated, on the local goal (`have h :
P by rw e; ring`), and `by` at the end of the line introduces the indented
block:

```g17
have alternatives : y = x ∨ y ≠ x by tauto
have notSingleton : ¬(y ∈ {x}) by
  intro singleton
  have equal := singleton.membership.forward with singleton
  exact different with equal
```

`exact ⟨first, second⟩` is `refine` with every component supplied.

`intros` is the compact form of several consecutive `intro` commands. Names
may be separated by spaces, commas, or both:

```g17
-- goal: ∀ x, P(x) → ∀ y, Q(y) → R(x, y)
intros x, hx y hy
-- x and y are arbitrary; hx : P(x), hy : Q(y)
```

The elaborator nests the same `∀I` and `→I` steps the singular commands would
produce. `intro a at hAB` specializes the leading universal quantifier of
`hAB` at the already-introduced term `a`.

Both commands see through a defined predicate whose body is a universal or
an implication, so a subset goal needs no `unfold Subset` first:

```g17
-- goal: A ⊆ C, with h : A ⊆ B and h2 : B ⊆ C
intros y hy
exact h2 with y, (h with y, hy)
```

For routine refinement closure, `typecheck` reconstructs a proof from registered
soft-type rules and the local context:

```g17
-- aNat : Nat(a), bNat : Nat(b), cNat : Nat(c)
have expressionNat : Nat(a * b + c)
  typecheck
```

A membership of literal naturals, `2 ∈ 4`, is decided by `typecheck` as well,
through the successor laws of the ordinals. A numeral literal of any length
is typed at once, `Nat(k)` and `k ∈ ℕ` alike: above 64 it is typed by the
closure rules of successor, addition, and multiplication, two steps per
binary digit, and above 128 binary digits by splitting it in halves of its
digits, so the nesting of the certificate grows with the logarithm of the
digit count; each step is closed by a computation certificate.

With a checked local `Ring(R)` or `CommRing(R)` certificate, `typecheck` can
also prove `R[0] ∈ R` and `R[1] ∈ R`. This fallback examines local
certificates only and emits existing projection and membership theorem
applications; it does not infer a ring structure from notation or prove that a
restricted carrier is closed.

## Calculation chains

`calc` presents equality and inequality reasoning in the order a mathematician
reads it:

```g17 import=Grace.Cumulus.Real
theorem realAddValue.commutative (A B : Real)
  shows A + B = B + A
proof
  calc
    A + B = realAddCut(A, B) :=
      realAddValue.cut at A, B with assumption, assumption
    _ = realAddCut(B, A) :=
      realAddCut.commutative at A, B with assumption, assumption
    _ = B + A := by simp [realAddValue.cut]
```

The `_` is the preceding right-hand endpoint. Each justification is either a
proof expression or a tactic sequence following `by`: `by rw h; ring` runs
both tactics on the step, as a `have … by` does. After a nonfinal line the visible
goal becomes the remaining equality, so cursor-based goal states follow the
calculation line by line. The elaborator checks every displayed equality and
combines them with equality transitivity. A wrong starting point, broken
intermediate endpoint, or wrong final endpoint is reported at the responsible
line.

Strict rational and real inequalities may be chained in the same notation:

```g17
have abLessUV : a * b < u * v
  calc
    a * b < u * b := abLessUB
    _ < u * v := ubLessUV
```

Natural-number calculations support homogeneous `<` and `≤`, as well as the
mixed compositions `<` followed by `≤` and `≤` followed by `<`. The relation
registry names a transitivity theorem for every supported composition. Tau
reconstructs routine soft-type premises from the local context, and the
resulting theorem applications are recorded in the proof term. Unsupported or
ambiguous compositions are rejected.

## Simplification and rewriting

`rw h` rewrites the goal with a local or library equality, `rw ← h` rewrites
backward, `rw [h₁, h₂]` rewrites with each rule in turn, and `rw moves with
p, hp` rewrites with the instance that application names, as `have inst :=
moves with p, hp` followed by `rw inst` would; a `with` list that does not
apply is reported with the application `rw` read. `unfold name`
exposes one definition. `rwa h` rewrites and then closes the goal from a
matching local fact, and `rwa h at fact` rewrites the fact and uses it. Transformation tactics
accept a common `at h` location suffix: `unfold Subset at hAB`, `rw hxy at h`,
and `simp [add] at h` transform a named hypothesis. `rw under h at fact`
rewrites through an unopened `∀` or `∃` when neither side of the instantiated
equality depends on the bound variable; the same form works on a goal and with
`←`.

A rule `P ↔ Q`, possibly under `∀` and premises, rewrites too: `rw h` replaces
the subformula `P` of the goal, or of the fact named by `at`, by `Q` at every
occurrence of the instance matched first, and `rw ← h` replaces `Q` by `P`;
the proof is carried through the connectives on the path, and `rw under h`
crosses a quantifier whose variable neither side mentions. A rule that
selects nothing is reported with its two sides and the goal or fact, printed
with the notation in scope: `rewrite rule pow_zero (x ^ 0 = G.one) does not
match the goal x = x`. In `rw [a, b, c]` the failing rule is reported by its
own name and located at that rule.

`unfold` handles both predicate definitions and equations, and unfolds a
defined predicate wherever the goal mentions it: at the head, under `∧`,
`∨`, `→`, and `¬`, and inside a `∀` or `∃` whose bound variable the
instance mentions. The foundational equations can expose a compact numeral
as a von Neumann set:

```g17
lemma two.encoding
  shows 2 = union(pair(1, pair(1, 1)))
proof
  unfold nat.succ
  rfl
```

The compact numeral stays the evaluator's native representation; unfolding
produces one equality proof. `unfold` also rewrites with local equalities in
the exposed body, so a following `rw h` may find nothing left to rewrite; `cc`
closes such goals directly.

A power with a literal exponent, `t ^ k` for `k ≤ 16`, is expanded by
`ring` and `ring_nf` into its product over ℕ, ℤ, ℚ, ℝ, and bundled rings,
with the certificate built from the power's defining equations, so `(a +
b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2` is `ring` alone and `ring_nf at h`
turns `h : a ^ 3 = 8` into `h : a * (a * a) = 8`; a larger exponent stays
an atom.

`ring [h₁, h₂]` closes an equation using the named equations as rewrite
rules modulo the semiring axioms: each rule's left side is applied wherever
a multiple of it fits inside a side's normal form, the rules reduce one
another first, and `ring` compares what remains. A proof that applies a
step law several times multiplies both sides by what the laws need and
finishes with one `ring [s1, s2, s3, s4]`. `ring_nf` and `ring` normalize
inside atoms too, so `f(n + n)` and `f(2 * n)` are one atom. A quotient
`t / k` is an atom for `ring`, which says so when the sides differ: use
`linarith` for a linear goal, or rewrite with `realDiv.eq_mul_inv` or a
named constant such as `oneHalf`.

`simp [rules]` normalizes with definitions, equalities, and ground
computation, and discharges routine logic. It also works incrementally. If its
rules do not close the goal but a supplied equivalence changes the outer
proposition, `simp` leaves the simplified proposition as the next goal and
records the backward implication needed to reconstruct the original proof. If
no outer equivalence applies, it rewrites with the named equalities inside a
logical goal, including a negated condition, repeating on the result to a
bounded fixed point, so `simp [fst.pair, snd.pair]` reduces every layer of
`fst(fst(((a, b), c))) ∈ A` and leaves `a ∈ A` as the residual goal for
later tactics. This fallback needs evidence for conditional rules and does not
rewrite beneath quantifiers or introduce case splits. For example:

```g17
proof
  simp with Subset
  simp with quotient.membership
```

The first line may expose the pointwise subset obligation; the second can then
simplify membership in the quotient.

`simp at` works on any proved proposition, forward-simplifying it through
equivalences and equality transport. So `simp [pair.membership] at h` changes
`h : x in pair(a, b)` into `h : x = a or x = b`.

For a disjunction, the incremental goal simplifier can use the negations of
all sibling literals while rewriting one literal, then reconstructs the whole
clause and discharges those assumptions. For example,
`simp [Dijkstra.mark.at_other]` transforms the equality disjunct of
`target = index ∨ flagAt(mark(flags, index), target) = flagAt(flags, target)`
using `target ≠ index`, and a subsequent `right; rfl` finishes the proof. This
clause pass transports one conditional equality; it does not distribute
formulas into CNF, rewrite beneath binders, or split cases during hypothesis
relief.

Membership in compound sets needs no lemma list. Before its structural
search, `simp` runs a ground classical procedure: every visible membership
characterization (the theorems and definition properties named
`membership`) and the `Subset` definition are instantiated where the goal's
and hypotheses' atoms match them, universal hypotheses such as an unfolded
subset are instantiated where their premises or conclusions match, and the
result is decided by case analysis on the atoms connected to the goal with
congruence closure at the leaves. So `insert(x, V ∖ {x}) = V` from `x ∈ V`
is `ext y` followed by `simp`, and `A ∖ C ⊆ B ∖ C` from `A ⊆ B` is a bare
`simp`. Hypotheses about other terms do not slow the search down: branching
stays on the atoms that share a fact with the goal, and the whole atom set
is tried only when that finds a countermodel. The procedure is bounded (128
atoms, a few thousand search nodes, 96 instances); beyond that the
structural search runs as before, and definitions other than `Subset` still
have to be named, as in `simp [pow]`.

`simp` can evaluate closed `Bool` expressions and discharge many constructive
propositional tautologies. For full classical propositional reasoning use
`tauto`. Context equalities used by `simp` get an occurs check: an expanding
fact such as `x = f(x)` is oriented as `f(x) -> x`, rewrite paths are
cycle-checked, and normalization has a depth limit. These are termination
controls; every rewrite still contributes its equality proof.

### Conditional rewriting and bounded backchaining

Rewrite hypotheses use direct contextual evidence and soft-type reasoning by
default. Recursive relief requires explicit limits:

```g17
simp (backchain := 2, work := 128) [rewriteLemma, guardLemma]
simp (backchain := 2, work := 128) [rewriteLemma, guardLemma] at h
simpa (backchain := 2, work := 128) [rewriteLemma, guardLemma] using h
```

`backchain` limits recursive rule applications along a hypothesis path; `work`
is shared across recursive relief entries, attempted rule conclusions and
conjuncts, contextual binding attempts, sibling guards, and the closure and
residual phases of this invocation. There are no defaults; you set both.
Direct evidence remains usable at depth or work zero. Exhaustion leaves a
conditional rewrite unapplied. Recursive relief does not guess witnesses or
split cases, and it uses the tactic's selected rules (including the default
simplification rules) rather than the whole library.

Relief can select conjuncts of a rule conclusion and use either checked
direction of an equivalence. A rule variable absent from the matched conclusion
may be bound by matching a hypothesis against an existing contextual fact.
The first hypothesis containing an unbound rule variable is used; its matching
facts are tried in context order. All hypotheses must still be proved under the
same substitution. These attempts consume the shared work allowance and do not
enumerate arbitrary terms or create existential witnesses. The maximum
recursive depth is 128 and the default recursive formula-size limit is 16,384
canonical characters. These controls bound relief search only; soft typing,
normalization fuel, forward propagation, and general logical closure have their
own. `settle` is an older spelling of `simp` and is still accepted.

### `simpa`

`simpa [rules] using fact` combines a common three-line pattern: simplify a
fact, normalize the goal, and finish when the statements agree.
Binder-independent terms can be rewritten beneath `∀` and `∃`. Rewrites that
depend on a bound variable or would capture it are not performed. Logical
formula normalization is cycle-checked and limited to 256 transport steps per
side. Equality normalization has its own rewrite-fuel budget. The logical
fallback has a 1,000-step default budget and stops at 64 nested search states;
use structural tactics when these limits are reached. For example, after
unpacking coordinates one can write:

```g17
have representative_less : rationalRepresentativeLess(u, v)
  simpa [uShape, vShape] using
    rationalRepresentativeLess.pair.backward at a, b, m, c, d, n with
      mNonzero, nNonzero, less
```

## Choosing an induction form

Grace17 has three induction invocations. They start from different
mathematical structure:

| What is decreasing? | Invocation | Shape after the invocation |
|---|---|---|
| a declared datatype value | `induction n` or `induction n generalizing s with` | one named branch per constructor |
| membership in the set-theoretic universe | `induction x using membership` | introduce `current`, then the member hypothesis `ih` |
| an arbitrary relation on a set | `induction x over A ordered by r certified by founded` | introduce `x`, `hx`, then the predecessor hypothesis `ih` |

### Structural induction on a datatype

Place `induction n` as the first command in the proof block, immediately below
the `proof` keyword. List any declared variables whose values must remain
arbitrary after `generalizing`; they may occur before or after `n`. The optional
final `with` names the cases in the usual spelling. Their soft-type premises,
dependent binders, and requirements depending on `n` or on a generalized
variable are moved into the induction motive and can be introduced in each case.
Requirements depending on the induction variable are moved into the motive even
for plain `induction n`, without a `generalizing` clause. Introduce them at the
start of each branch; the recursive hypothesis then takes the corresponding
requirements for the smaller constructor argument. Independent requirements
remain available by name.

Each constructor becomes a branch. Name constructor fields in parentheses; name one
induction hypothesis after `using` for each recursive field:

```g17
theorem add.right_unit (n : Nat)
  shows add(n, 0) = n
proof
  induction n
  | zero => simp [add]
  | succ(k) using ih => simp [add, ih]
```

The successor case may be written as arithmetic, `| k + 1 using ih =>`: its
goal is then stated with `k + 1` in place of `succ(k)`, so a proof by
induction on a natural number never sees `succ`, and `factorial.succ`-style
laws in the `+ 1` form apply directly. The elaborator transports the case's
proof to the constructor form the induction rule checks, through
`add.right_one`.

For example, `induction es generalizing s with` gives each recursive induction
hypothesis a fresh universally quantified `s` instead of fixing the original
one too early. The elaborator computes the dependency closure directly, with no
proof search, and uses a checked internal auxiliary when binder order must be
rearranged.

The case header introduces the constructor fields, their class facts, and the
named induction hypotheses before its tactic sequence begins. A nonrecursive
constructor has no `using` clause. For a datatype with several recursive fields,
list the hypotheses in the same order as those fields. Induction cases accept
the same arbitrary tactic sequence as the outer proof:

```text
proof
  induction b
  | Bool.false =>
    unfold not
    rfl
  | Bool.true => simp [not]
```

### Membership induction from Foundation

Use membership induction when the argument is an arbitrary set and every member
is structurally smaller. If the goal is `P(x)`, then

```g17
induction x using membership
intros current ih
```

changes the board to `P(current)` with
`ih : ∀ member, member ∈ current → P(member)`. For example:

```g17
theorem membership.irreflexive (x : Set)
  shows ¬x ∈ x
proof
  induction x using membership
  intros current ih hSelf
  have impossible := ih at current with hSelf, hSelf
  exact impossible
```

An assumption that mentions `x` cannot stay fixed while `x` changes. Move it
back into the goal first with `revert h`, then introduce it inside the
induction body. The side condition prevents an unsound induction motive. The
tactic is derived from Foundation through a set-sized transitive closure.

### Induction over a certified well-founded relation

The general form starts with a goal exactly shaped as
`∀ x, x ∈ A → P(x)` and a checked certificate
`founded : wellFoundedOn(r, A)`:

```g17
theorem relation_reflexive (A r : Set)
  requires founded : wellFoundedOn(r, A)
  shows ∀ x, x ∈ A → x = x
proof
  induction x over A ordered by r certified by founded
  intros x hx ih
  rfl
```

Inside the body, `hx : x ∈ A` and
`ih : ∀ y, y ∈ A ∧ relates(r, y, x) → P(y)`. To use `ih`, specialize it first
at the predecessor, then supply the membership fact and relation fact:

```g17
have smaller := ih at y
specialize smaller with hyA, hyrx
```

The relation, carrier, and certificate are visible, so the proof state shows
why recursion is legal. Use this form for custom measures, well-orders, and
other arguments whose descent is neither datatype recursion nor membership.

## Decision procedures

`tauto` is complete for classical propositional logic. Equality, predicate,
and quantified formulas are treated as atoms; `and`, `or`, implication,
equivalence, negation, and `⊥` are decided propositionally. The search branches
on an atom only while the current partial valuation leaves the goal and all
hypotheses undecided. Each split is a proof of excluded middle, and each leaf
is a natural-deduction proof.

```g17
theorem Peirce (x y z w : Set)
  shows ((x = y -> z = w) -> x = y) -> x = y
proof
  tauto
```

The default fuel is 65,536 search nodes. Propositional validity is co-NP
complete, so there are exponential worst cases; Grace17 fails at the fuel
boundary.

`cc`, with the long spelling `congruence`, decides ground equality under
uninterpreted functions. It chains local equalities, closes function
congruences, transports positive predicate facts across congruent arguments,
and derives arbitrary goals from a congruent disequality or positive/negative
predicate conflict.

```g17
theorem nested (x y : Set)
  requires h : x = y
  shows orderedPair(singleton(x), x) = orderedPair(singleton(y), y)
proof
  cc
```

The implementation uses union-by-rank with proof explanations and processes
applications from shallowest to deepest. Congruence signatures are indexed by
function symbol and argument-class representatives. The final explanation is
built from the original equalities, equality transitivity and symmetry,
function congruence, and equality elimination. Quantifier instantiation and
rewriting by conditional equations are the jobs of `specialize`, `rw`, and
`simp`, and `cc` does not attempt them.

`decide` settles closed statements about finite sets. Its terms are set
literals, numerals, `∪`, `∩`, `∖`, `𝒫`, `insert`, and `∅`; its goals are
`x ∈ A`, `x ∉ A`, `A ⊆ B`, `A = B`, `A ≠ B`, and `cardinality(A) = n`. It
evaluates the statement and, when it is true, writes a proof from the library's
membership lemmas, which the elaborator then checks like any proof you could
have written yourself. Numerals are atoms: `2 ∈ 5` goes through the
natural-number lemmas, but `{0} = 1` is outside the fragment, as is a
powerset on the left of `⊆` or `=`. A false statement is reported as false.

```g17 import=Grace.Cumulus.Cardinal
theorem three_members
  shows cardinality({1, 2} ∪ {2, 3}) = 3
proof
  decide
```

`compute` closes a closed equation by a computation certificate, and a
closed order goal over ℕ as well: for `a < b`, `a ≤ b`, or `a ≠ b` with
both sides evaluable, both sides are evaluated and the gap between them
is the witness of the order's definition, while `a ≠ b` goes through
`Less.irreflexive`, which must be in scope. A false comparison is reported
with the two values. Natural subtraction, predecessor, remainder, and
quotient evaluate natively, like addition and multiplication, so `2 *
fallingFactorial(365, 23) < 365 ^ 23` and `365 ^ 23 - (2 *
fallingFactorial(365, 23) + 1)` are each one step:

```g17 import=Grace.Cumulus.Nat.Pow
theorem powers.apart
  shows 2 ^ 10 < 3 ^ 7
proof
  compute
```

## Arithmetic automation

`ring` proves polynomial equalities by normalizing with semiring or
commutative-ring theorems from the current import environment. The Nat rule set
covers zero and one, successor as `n + 1`, additive rearrangement,
multiplication, associativity, annihilation by zero, and left and right
distributivity. For a registered `CommRing` or `OrderedRing` instance, the
carrier and operation graphs come from the instance, and transparent wrappers
such as real subtraction participate without naming the carrier.

```g17
theorem distribute (a b c : Nat)
  shows (a + b) * c = a * c + b * c
proof
  ring
```

`ring at h` normalizes a proved polynomial equality in place. `ring_nf`
normalizes every polynomial argument of the current equality or predicate goal
without trying to close it, and `ring_nf at h` does the same to a local
equality or predicate fact. In particular, an inequality such as
`(a + b) * c < d` becomes `a * c + b * c < d`. These forms are useful when
several facts must be combined before a final cancellation; equality
elimination transports every normalized fact back to its authored form.

For membership `p ∈ I`, `ring_nf` normalizes only p, since I is a set
parameter. A relation graph in `relates(r, p, q)` is left alone too. That
makes ideal calculations direct:

```g17
-- member : x + y ∈ I; goal: y + x ∈ I
ring_nf at member
ring_nf
exact member
```

`linear_combination k * h1 + m * h2` scales equality hypotheses, adds them,
and normalizes the resulting polynomial. Signed terms such as `h1 - h2` are
supported. The tactic selects the commutative-ring interface used by the goal
and named equations, so real and abstract-ring coefficients work as well as
Nat coefficients. In a ring, cancellation is normalization with additive
inverses; the certificate uses congruence and the ring laws. The Nat semiring
path keeps its additive cancellation. A coefficient is read as the goal is,
and a bare numeral in it is the ring's numeral, as `(2:R)` is, so
`linear_combination 2 * h` scales a real equation by the real two; a
coefficient the notation in scope cannot type, `2 * dotValue(u) * h` with
`dotValue(u)` typed only by its membership, is read in the ring the goal
selects. Write `identity + product + product` when `2` has no numeral
instance in that carrier. Missing carrier-membership evidence
and incorrect combinations are rejected. The tactic combines the named
equations and searches nothing.

`arith` handles natural-number equalities and linear-order goals. For
equalities it first combines goal-relevant hypotheses with the semiring
normalizer, which proves normalization, congruence, and affine substitution
goals. It then applies antisymmetry to matching opposite bounds, and keeps an
indexed equality graph for repeated nested additive cancellation:

```g17
theorem cancel (a b c : Nat)
  requires h : a + c = b + c
  shows a = b
proof
  arith

theorem chained (a b c d e : Nat)
  requires h1 : a + c = b + c
  requires h2 : b + d = e + d
  shows a = e
proof
  arith
```

For comparison goals it normalizes each side to a sparse affine form and runs
Fourier–Motzkin elimination. Strict Nat order is first converted by the
equivalence `a < b <-> a + 1 ≤ b`; equality hypotheses enter as two weak
comparisons, and every Nat atom receives a `0 ≤ x` constraint. Strict and weak
bounds may therefore be mixed:

```g17
theorem lower_bound (x y : Nat)
  requires hx : x > 2
  requires hy : y ≥ 3
  shows x + y > 5
proof
  arith
```

The procedure is complete for inconsistency of the resulting affine system
over the nonnegative rationals, with Nat's unit gap for strict comparisons. It
covers weakening, strict-to-weak conversion, arbitrary affine chains, and
natural coefficients. The certificate emitter uses binary scaling, the addition
and cancellation laws, a terminating additive normalizer, and a final
irreflexivity contradiction.

Elimination is exact in the sense of the Omega test's main step: a variable
whose coefficients on one side are all units is eliminated first, and every
comparison whose atom coefficients share a factor is divided through with its
constant rounded, so that `1 ≤ 2x` and `2x ≤ 1` contradict each other over the
naturals although not over the rationals. Each tightening is a checked
instance of `LessEqual.quotient_floor` or `LessEqual.quotient_ceiling` with a
computed quotient. What remains outside the procedure is the Omega test's dark
shadow for systems where no exact elimination exists, the usual boundary of
such a procedure. It also gives up, with a message, above 16,384 projected
constraints or a scalar expansion above 4,096.

`linarith` is the analysis-facing spelling of the linear fragment. Over the
reals it is a complete decision procedure for linear consequences of the
local comparisons: it negates the goal, runs Fourier–Motzkin elimination over
the atoms of the hypotheses, and emits a certificate that scales and adds the
hypotheses with the order laws (`realLe.add`, `realLess.add`, and their mixed
forms), normalizes the two sides with the commutative-ring normalizer, and
closes with irreflexivity.

```g17 import=Grace.Cumulus.Real
theorem combine (a b c : Real)
  requires ab : a ≤ b
  requires bound : c ≤ a - b
  shows c ≤ 0
proof
  linarith
```

Real `linarith` accepts goals of the forms `s ≤ t`, `s < t`, `s = t` (proved by
antisymmetry), `¬(s ≤ t)`, `¬(s < t)`, and `⊥`. It uses local facts of the same
forms, equalities between real terms, conjunctions of them, and the library
fact `0 < 1` whenever `1` occurs. Addition, subtraction, negation, and
scaling by a numeral are interpreted, and so is division by a numeral: for
a quotient `t / k` with `k ≠ 0` the identity `t = k * (t / k)` enters as a
hypothesis, proved from `realDiv.eq_mul_inv` and `realInvValue.mul_right`,
so `0 < x` gives `0 < x / 2` and `x / 2 + x / 2 = x` is proved outright.
Every other term, including a product such as `x * y` or a quotient by a
variable, is an atom. It does not multiply hypotheses by variables, so a
goal that needs
`0 ≤ x` and `0 ≤ y` to conclude `0 ≤ x * y` is outside its fragment. State
the nonlinear fact first with a library lemma, then let `linarith` finish.

Over the rationals the same elimination runs on the strict order `<`, which is
the only order ℚ carries. Facts are rational comparisons `s < t` and equalities;
goals may be `s < t`, `s = t`, `¬(s < t)`, or `⊥`. A comparison or equality
goal is settled by trichotomy, with each remaining case refuted by the
engine, and the certificate uses `rationalLess.add_right`,
`rationalLess.add_left`, `rationalLess.transitive`, and
`rationalLess.irreflexive`, with equalities carried by substitution:

```g17 import=Grace.Cumulus.Rat
theorem sums (a b p q r : Rational)
  requires rab : r < a + b
  requires ap : a < p
  requires bq : b < q
  shows r < p + q
proof
  linarith
```

Over `Nat` it uses the same ordered-additive presentation as `arith`:

```g17
theorem chain (x y z : Nat)
  requires hxy : x ≤ y + 2
  requires hyz : y < z
  shows x < z + 3
proof
  linarith
```

The inequality engine is organized around ordered-additive presentations. A
presentation supplies its carrier predicate, zero, addition, and order symbols,
and proofs that addition preserves strict and weak order. `Nat`, the reals,
and the rationals have their own; an abstract ordered ring supplies its `OrderedAdditiveGroup`
instance, projected from an `OrderedRing` instance or hypothesis through a
theorem. `arith` and `linarith` never move a term between carriers.

Both tactics are built for large libraries and large local contexts. `ring`
reuses a prepared, root-indexed rewrite program and admits only nontrivial
equality hypotheses connected to the goal. `arith` makes one linear context
pass, shares an indexed, memoized soft-type prover across its operand checks,
and partitions affine constraints into independent atom components. It
searches the goal component first, and the others when it needs an unrelated
contradiction.

`ring` and real `linear_combination` infer polynomial atom membership through
Tau soft-type rules. For points a and b, `x(a) * y(b) = y(b) * x(a)` is proved
by `ring` alone; there is no need to name `x.real` and `y.real` first. The
inference still needs Point evidence. When several ring structures are in
scope, polynomial tactics prefer the shallowest visible operations across the
goal and named equations. In `f(neg(x)) = minus(f(x))`, the
target-ring `minus` controls normalization; the source-ring `neg` inside the
opaque function argument does not override it. Opaque terms still need
membership in the selected carrier. This applies to `ring`, `ring_nf`, and
`linear_combination`.

## Soft typing and bounded quantifiers

Grace17 is one-sorted set theory: every kernel variable ranges over sets. A
soft type is a predicate the surface language uses to make those set-theoretic
guards readable. It introduces no typing judgment and grants no unchecked
fact.

For example, a theorem binder

```g17 import=Grace.Cumulus.Rat
theorem rational_self (q : Rational)
  shows q = q
proof
  rfl
```

elaborates to the kernel proposition

```g17
∀ q, Rational(q) → q = q
```

The `Rational(q)` premise is a proposition like any other. It can be named,
unfolded, passed by hand, or reconstructed by the proof-producing Tau system.

A binder may also be typed by a mixfix notation that begins with a colon:
`(f : A → B)` is a set variable `f` with the generated guard
`FunctionBetween(f, A, B)`, discharged like any other guard by `with *` from
a hypothesis in scope or by instance synthesis. See
[mixfix predicates](notation.md#mixfix-predicates).

Grace17 also supports bounded quantifiers. They abbreviate:

```g17
∃ q ∈ ℚ, P(q)    -- ∃ q, q ∈ ℚ ∧ P(q)
∀ q ∈ ℚ, P(q)    -- ∀ q, q ∈ ℚ → P(q)
```

The ASCII forms `exists q in ℚ, P(q)` and `forall q in ℚ, P(q)` are
equivalent. Supplying an existential witness leaves its membership condition as
a proof obligation; introducing a bounded universal gives both the arbitrary
set and its membership hypothesis.

When a unary soft type is defined exactly by membership in a carrier, as in

```g17 fragment
class Rational (q : Set) := q ∈ ℚ
```

the elaborator may recover `Rational` information for a variable bound by `ℚ`.
That lets it select the rational interpretations of `q < r`, `q + r`, `-q`,
and typed numerals inside the quantified body. The association is untrusted
elaboration metadata. What enters the kernel and the exported certificate is
the expanded membership guard and the selected raw operation or relation. If
no interpretation, or more than one, is compatible with the available
evidence, elaboration fails.

For an atomic transparent definition such as `Rational(q) := q ∈ ℚ`, Tau
also indexes the proof-producing direction `q ∈ ℚ → Rational(q)`. Thus:

```g17
-- qInQ : q ∈ ℚ
have qRational : Rational(q)
  typecheck
```

uses the predicate's defining equivalence automatically. This is a direct
lookup by the requested conclusion predicate followed by `↔` elimination. It
does not consult the type-class registry or enumerate candidate terms.
Among the rules of one predicate, those whose conclusion names the shape of
the term, `f(x) ∈ B` for an application, are tried before rules about a bare
variable such as `IntReal(x) → x ∈ ℝ`, so `u(k) ∈ ℝ` from `u : 3 → ℝ` and
`k ∈ 3` is found at once however many such general rules the imports bring.

Notation resolution may use soft types from theorem binders, local
unary-predicate facts, typed function results, and carrier associations like
the one above. Tau constructs routine soft-type proofs. The instance registry,
which selects structures and operation graphs, is a separate mechanism.

Two practical consequences. A numeral in a set comprehension or a bare
statement defaults to `Nat`; write `(0:R)`, `(T:R)`, and `-(1:R)` to select
the real interpretation. And when two soft-typed binders such as
`(X Y : NonnegativeReal)` do not determine one interpretation of `≤`, take
`(X Y : Real)` and state the extra property as a named `requires` premise.

## Mathematical classes, refinements, and overloading

Three different things have similar names:

- a `class` is set-theoretic syntax for a mathematical collection, possibly a
  proper class;
- a soft type or refinement is a proved predicate about a term;
- a type-class instance selects reusable predicate evidence for a carrier and
  its operations.

Every quantified object remains a set in the kernel, and neither Tau nor
instance search adds a kernel judgment. A declaration such as

```g17
class PositiveNatural (n : Set) := Nat(n) ∧ n ≠ 0
```

presents a predicate as a mathematical class. `n : PositiveNatural`,
`PositiveNatural(n)`, and `n ∈ PositiveNatural` are three spellings of the same
proposition. A class may be proper, so its name is not a set-valued term.

A hypothesis such as

```g17
requires qRational : Rational(q)
```

is predicate evidence: it proves `Rational(q)`, and it has nothing to do with
type-class instances. For a unary predicate goal, `typecheck` asks the
ACL2-style Tau system to construct a soft-type proof. This search is
independent of the instance registry. The proof given to the kernel contains
the facts and theorem applications selected.

The optional `for PredicateName` clause tells notation which soft type the
operands must have. A declaration may name its implementation directly:

```g17 fragment
notation infixl 60 "+" => rationalAddValue for Rational
```

When the operands are known to satisfy `Rational`, this notation elaborates to
`rationalAddValue`. That is selection from unary predicate evidence; no
type-class resolution is involved.

Algebraic structures use multi-argument predicates. A checked theorem can be
registered as an instance:

```g17 fragment
instance inherited (x : Set)
  requires source : Source(x)
  shows Target(x)
proof
  exact source_to_target at x with source
```

The declaration is first admitted as a theorem. Its name is then placed in an
untrusted, import-scoped instance registry. `synthesize` uses only visible
registered rules, prefers exact local evidence, and reports an error when
several global candidates succeed; it never picks one by load order.
Resolution is indexed first by conclusion predicate and then by discrimination
tries over the full structure of every known first-order argument. Candidate
sets are intersected, tabled per proof context, cycle-checked, and bounded by
depth, goal, and rule-attempt limits. Every quantified instance variable must
occur in its conclusion, which rules out open-ended metavariable enumeration.
Instance queries may leave output positions as `_`. Search then uses the known
inputs to instantiate one checked conclusion and returns its outputs together
with the proof.

Notation can consume such an output:

```g17 fragment
instance rationalAdd.operation
  shows AddOperation(ℚ, rationalAdd)
proof
  unfold AddOperation
  exact rationalAdd.function

notation infixl 60 "+" => call2 via AddOperation(ℚ, _) for Rational
```

Here Tau establishes that the operands are rational, the instance query
selects `rationalAdd`, and the elaborated term is `call2(rationalAdd, x, y)`.
Typed numerals use the same mechanism through `OfNat(ℚ, 0, _)`. Missing and
competing implementations are errors. Hover shows the selected graph and
adapter.

A trailing `with *` tries instance synthesis first and then Tau refinement
reconstruction.

## Search tactics and admissions

`exact?`, `apply?`, and `rw?` are deterministic query tactics. They search the
current import environment, including axioms and generated definition
properties such as `V.history.membership.backward` (and, for rewriting, local
equalities), show up to eight readable commands in the Workbench Info drawer,
and execute the first result. `exact?` closes the goal, `apply?` creates the
candidate theorem's premises as goals, and `rw?` performs one rewrite. A
finished proof should replace a `?` tactic with the suggested command, which
is faster to replay, stable as the library grows, and readable.

`sorry` closes the focused goal by introducing a uniquely named synthetic
axiom. Its source line, goal, theorem, and axiom name are retained in module
results; exported theorem dependencies include the axiom; the CLI prints a
warning; and the Workbench shows an amber admitted state instead of the green
proof-complete state. A check containing `sorry` succeeds so downstream work
can continue. Nothing with a `sorry` belongs in Cumulus.

## Proof maps

Proofs may carry an explanatory structure that does not affect their logic.
`--!` introduces a landmark and `--|` adds prose beneath it:

```g17
proof
  --! Reduce bijectivity to its components.
  constructor
  . --! Injectivity
    --| Pull equality back through the two maps.
    exact injective
  . --! Surjectivity
    --| Pull an output back through the two maps.
    exact surjective
```

The Workbench turns these annotations and their indentation into a hierarchical
Proof Map. It highlights and opens the current landmark as the editor cursor
moves. Expand a section to browse the checked tactics within it; each row shows
the resulting goal count and jumps to the tactic span, including tactics
chained on one line. With no annotations, no map is shown. The metadata is
retained in exported tactic traces and is absent from the proof term.

## User tactics

You can declare deterministic macros:

```text
tactic finish := assumption
tactic solve(rule) := simp [$rule]

theorem example (x y : Set)
  shows x in pair(x, y)
proof
  solve(pair.membership)
```

Macros are module-scoped, imported and resolved like other declarations,
expanded with a depth limit, and retained under their source spelling in proof
traces. Expansion produces built-in tactics, so a macro adds no trusted code.

## Sections and scoped notation

A theorem section shares parameters and hypotheses across a family of
theorems, and `notation ring R := (A, add, zero, neg, mul, one)` inside a
section writes the algebra of those operation graphs in ordinary syntax.
Both are described in [modules, namespaces, and sections](modules.md) and
the [algebraic hierarchy](algebra.md).
