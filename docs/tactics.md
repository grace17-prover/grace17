# Tactic reference

Every tactic in Grace17, organized as the Workbench **Help** panel presents
them: the first moves, logic and witnesses, changing the view, search and
automation, arithmetic, shaping a development, and induction. This page is
rendered from the Help source by `npm run docs:tactics`, so the two never
disagree. For a guided tour of writing proofs, read
[Proving theorems in Grace17](proving.md); for declarations, see
[definitions](definitions.md); for types and instances, see
[types](types.md).

Tactics are not part of the trusted kernel. They transform goals and build a
proof term, and the kernel checks that term from scratch before admitting the
theorem. A broken or hostile tactic can fail, exhaust its budget, or produce a
rejected proof; it cannot prove a false statement. Every entry below therefore
ends with the natural-deduction rule schema its proof term reduces to, with
`Γ` standing for the current local context.

## Conventions

- Almost always, we prefer proofs with one tactic per line. You can of
  course change this as you wish, for example by using semicolons to put
  several tactics on the same line. A leading `.` marks the next focused
  subgoal.
- Transformation tactics accept an `at h` suffix to act on a named local fact
  instead of the goal: `unfold Subset at hAB`, `rw hxy at h`,
  `simp [add] at h`, `ring_nf at h`, `symm at h`.
- A proof expression is a fact optionally applied to arguments: mathematical
  terms after `at`, checked premises after `with`, `.forward` and
  `.backward` for the directions of an equivalence, and `.left` and
  `.right` for the sides of a conjunction. The same expression grammar is
  used by `exact`, `show`, `apply`, `have`, `specialize`, `refine`,
  and `calc` justifications.
- `with *` fills omitted premises from checked local evidence and stops at a
  source theorem's `shows`; `with *{n}` fills exactly `n` premises.

## Command index

| Section | Commands |
|---|---|
| [The first moves](#the-first-moves) | [`intro h`](#intro-h), [`intros x hx y hy`](#intros-x-hx-y-hy), [`exact fact`](#exact-fact), [`show P := fact`](#show-p-fact), [`assumption`](#assumption), [`rfl  /  reflexivity`](#rfl-reflexivity), [`apply fact`](#apply-fact), [`have h := fact with premises`](#have-h-fact-with-premises), [`fact with ⟨a, b⟩`](#fact-with-a-b), [`fact at terms with *`](#fact-at-terms-with), [`fact at terms with *{n}`](#fact-at-terms-with-n), [`have h : P := fact with *`](#have-h-p-fact-with), [`have h : P`](#have-h-p), [`have h : P by tactic`](#have-h-p-by-tactic), [`calc`](#calc), [`specialize h with x, hx`](#specialize-h-with-x-hx) |
| [Logic and witnesses](#logic-and-witnesses) | [`constructor  /  split`](#constructor-split), [`refine ⟨a, ha, b, hb, _⟩`](#refine-a-ha-b-hb), [`left  /  right`](#left-right), [`witness t  /  use t`](#witness-t-use-t), [`rcases h with ⟨h₁, h₂, h₃⟩`](#rcases-h-with-h1-h2-h3), [`obtain ⟨x, hx, rfl⟩ := fact`](#obtain-x-hx-rfl-fact), [`cases h with hp \| hq`](#cases-h-with-hp-hq), [`rcases h with hp \| hq \| hr`](#rcases-h-with-hp-hq-hr), [`obtain ⟨x, hx, y, hy⟩ := fact`](#obtain-x-hx-y-hy-fact), [`exfalso`](#exfalso), [`by_contra h`](#bycontra-h), [`by_cases h : P`](#bycases-h-p), [`contradiction`](#contradiction), [`tauto`](#tauto) |
| [Changing the view](#changing-the-view) | [`symm  /  symm at h`](#symm-symm-at-h), [`rw h  /  rewrite h  /  rw ← h`](#rw-h-rewrite-h-rw-h), [`rw [h₁, h₂] / rwa h`](#rw-h1-h2-rwa-h), [`rw under h at fact`](#rw-under-h-at-fact), [`simp [rules]`](#simp-rules), [`simpa [rules] using fact`](#simpa-rules-using-fact), [`unfold name`](#unfold-name), [`ext x`](#ext-x), [`clear h`](#clear-h), [`rename h => betterName`](#rename-h-bettername), [`revert h`](#revert-h) |
| [Search and automation](#search-and-automation) | [`exact?`](#exact), [`apply?`](#apply), [`rw?`](#rw), [`settle with rules`](#settle-with-rules), [`typecheck`](#typecheck), [`synthesize`](#synthesize), [`cc  /  congruence`](#cc-congruence), [`decide`](#decide), [`compute`](#compute) |
| [Arithmetic](#arithmetic) | [`ring`](#ring), [`ring [h₁, h₂]`](#ring-h1-h2), [`ring_nf`](#ringnf), [`linear_combination 2 * h1 - h2`](#linearcombination-2-h1---h2), [`arith`](#arith), [`linarith`](#linarith) |
| [Shaping a development](#shaping-a-development) | [`sorry`](#sorry), [`. tactic`](#tactic), [`tactic1; . tactic2`](#tactic1-tactic2), [`tactic solve(rule) := simp [$rule]`](#tactic-solverule-simp-rule) |
| [Induction](#induction) | [`induction n [generalizing s ...] [with]`](#induction-n-generalizing-s-with), [`induction x using membership`](#induction-x-using-membership), [`induction x over A ordered by r certified by founded`](#induction-x-over-a-ordered-by-r-certified-by-founded) |

## The first moves

Most proofs are a handful of moves. Read the goal, expose its outer shape, and take one small step.

### `intro h`

**Introduce an implication premise or quantified variable.** For a goal P → Q, intro h extends Γ with the named local hypothesis h : P and leaves Q to prove. For a goal ∀ x, P(x), intro x chooses a fresh arbitrary x and leaves P(x). Use intro x at h to specialize the leading ∀ in a local fact.

For a bounded universal goal `∀ q ∈ ℚ, P(q)`, `intro q` introduces the set and the next `intro` names its membership hypothesis; `intros q qRational` does both.

`intro x at h` specializes the leading universal quantifier of a local fact `h` at an already-introduced term; it is the hypothesis-local form of universal elimination.

```g17
-- goal: P → P
intro h
-- h : P, goal: P
exact h
```

Rule schema:

```text
Γ, h : P ⊢ Q
────────────  →I
Γ ⊢ P → Q
discharges the local hypothesis h : P

Γ ⊢ P(a)
─────────────  ∀I
Γ ⊢ ∀ x, P(x)
a is fresh and does not occur free in Γ
```

### `intros x hx y hy`

**Introduce several leading variables and premises in one move.** Names are consumed from left to right across leading ∀ binders and implications. Use spaces, commas, or both. A defined predicate goal such as A ⊆ B is introduced through its definition, so no unfold is needed first. If the goal runs out of binders or premises, the error names where it stopped. The proof term is the same as for several intro lines.

`intros` is the compact form of consecutive `intro` commands. The elaborator nests the same checked ∀I and →I steps and stops with a diagnostic if the goal runs out of leading binders or premises.

```g17
-- goal: ∀ x, P(x) → ∀ y, Q(y) → R(x, y)
intros x, hx y hy
-- x and y are arbitrary; hx : P(x), hy : Q(y)
```

Rule schema:

```text
Γ, x : Set, hx : P(x), y : Set, hy : Q(y) ⊢ R(x, y)
───────────────────────────────────────────────────  ∀I, →I
Γ ⊢ ∀ x, P(x) → ∀ y, Q(y) → R(x, y)
x and y are fresh; hx and hy are discharged
```

### `exact fact`

**Finish with a fact whose statement is exactly the current goal.** The fact may be a local hypothesis, a theorem, or a theorem applied to arguments and premises. Carrier guards such as Nat(n + m) between or after the supplied premises are discharged on their own, by soft typing or from the context. Write theorem at terms with premises to consume leading ∀ binders and implications immediately. Equivalences expose .forward and .backward directions. For source theorems the at list is optional: exact theorem, exact theorem with h1, h2, and exact theorem with * infer the arguments from the goal, from the named premises in any order, and from uniquely matching local facts, including generated Nat and dependent List(A) guards. A bare exact theorem then discharges every requirement from local facts. Matching is structural, with a 2048-match limit, no unfolding or backtracking; an ambiguous match asks for explicit arguments. A local or derived predicate fact such as subset : A ⊆ B takes arguments through its definition (subset with x, hx), and evidence standing where a binder is expected instantiates the leading binders from the premise it matches. exact ⟨a, b⟩ is refine with every component supplied.

A proof expression may consume arguments immediately: mathematical terms after `at`, then checked premise facts after `with`, as in `exact transitive at x, y, z with hxy, hyz`. The same expression works after `have` and `apply`.

For a source theorem, `exact theorem with *`, `show P := theorem with *`, and `have h := theorem with *` can omit `at`: the conclusion is matched against the goal when there is one, then uniquely matching local premises determine the remaining parameters. Matching is structural, indexed by formula head, and capped at 2,048 attempts; it does not unfold definitions, backchain, or choose between ambiguous substitutions. Typed parameters participate through their generated guards, and every guard still needs checked evidence. An explicit `at` list is the fallback.

`exact theorem.forward with *` and `exact theorem.backward with *` infer parameters from the selected conclusion and unique local premise matches, including the selected antecedent, which still requires evidence. An implication or negation inside the selected conclusion remains intact.

```g17
-- f : P → Q, hP : P, goal: Q
exact f with hP
-- remaining : y ∈ W, goal: y ∈ insert(x, W)
exact insert.contains with remaining
```

Rule schema:

```text
fact establishes P
──────────────────  exact
Γ ⊢ P
```

### `show P := fact`

**State the conclusion and finish it with a fact.** P must be the focused goal, and the proof expression must establish it. Stating the conclusion makes a long proof readable, and the check catches a goal that has drifted.

`show` compares `P` with the focused goal and then closes the goal with the proof expression. Use it to make the conclusion of a long proof readable.

```g17
-- h : x = y, goal: x = y
show x = y := h
```

Rule schema:

```text
fact establishes P    P is the focused goal
───────────────────────────────────────────  exact
Γ ⊢ P
the displayed statement must match the goal
```

### `assumption`

**Finish from a matching local fact.** Use it when the fact's name does not matter. Only the local context is searched.

```g17
-- hxy : x = y, goal: x = y
assumption
```

Rule schema:

```text
h : P ∈ Γ
─────────  hyp
Γ ⊢ P
```

### `rfl  /  reflexivity`

**Finish a definitionally reflexive equality.** Both sides must reduce to the same term. The proof is equality reflexivity. A rewrite that ends its branch closes a goal it makes reflexive, so no rfl is needed after it; a rfl written there still closes the goal.

`rfl` also appears inside `rcases` and `obtain` patterns, where it means equality elimination of a discovered equation.

```g17
theorem self (x : Set)
  shows x = x
proof
  rfl
```

Rule schema:

```text
(no premises)
─────────────  =I
Γ ⊢ t = t
```

### `apply fact`

**Use a theorem or local fact backwards from its conclusion.** For a declared theorem, bare apply infers parameters from the goal and uniquely matching local premises. Carrier guards it can discharge are discharged, and so are the section hypotheses in scope among the declared premises, as with * discharges them, so a section theorem applied under its own hypotheses opens only the goals they leave; the remaining premises become goals in their written order, from the first that is not a section hypothesis. The equivalence directions work the same way. A conclusion equal to the goal stays as it is, implication included. Ambiguous parameters need explicit at arguments, and anything supplied with with is checked first.

`apply theorem at args` makes the generated carrier guards the first goals, before the declared premises. When a premise needs its own derivation, prefer `have h : P` followed by `exact theorem at args with *`.

`apply theorem with *` requests checked evidence for the declared premises; use bare `apply` when those premises should remain to be proved. `apply theorem.forward` and `.backward` leave open requirements and the selected antecedent as goals, and stop when the residual conclusion equals the goal, preserving an implication or negation that is itself the requested result.

```g17
-- goal: x ∈ {x}
apply singleton.membership.backward at x, x
rfl
```

Rule schema:

```text
Γ ⊢ P₁ → … → Pₙ → Q    Γ ⊢ P₁    …    Γ ⊢ Pₙ
────────────────────────────────────────────  →E
Γ ⊢ Q
```

### `have h := fact with premises`

**Apply an available fact and give the result a local name.** The optional at list supplies mathematical terms. For source theorems, omit at and name local premises in any order: parameters are inferred by matching each premise against the requirement it fits, and in exact, show, and apply also by matching the conclusion against the goal. For example: have image := IsRingHom.image_comm_ring with source, target, hom. Matching is structural, and a premise stated through a defined predicate meets a requirement stated by its body, or the other way round, through one layer of the definition, so relates(w, x, y) fills the requirement (x, y) ∈ w; a numeral matches the constructor term of the same value; a parenthesised application among the premises is read first when its facts fix its parameters, and otherwise after the other entries, against the requirement it fills, so that its statement fixes the remaining parameters. A conflict or an undetermined parameter is an error asking for an at list. A trailing * fills the remaining premises after inference. Entries that are terms rather than local facts are read as quantified arguments. Omit with to keep an unspecialized fact.

Use `specialize` when the unspecialized fact is already on the board and you want to replace it; use `have ... with` when the applied result is the fact you want from the start.

A premise meets its requirement through one layer of a predicate definition on either side, so `xy : relates(w, x, y)` fills `(x, y) ∈ w` without `unfold relates at xy`; a numeral such as `0` matches the constructor `zero` an induction case substitutes; and a parenthesised application, `thm with (inner with bound), h`, is read against the requirement it fills once the other entries have fixed what they can, so its statement can fix a parameter no other entry mentions.

`have h := fact` without `with` binds an available fact unchanged. This is separate from `have h : P`, which opens a proof block for a new proposition.

```g17
-- h : ∀ x, x ∈ A → P(x), hx : x ∈ A
have result := h with x, hx
-- result : P(x)
```

Rule schema:

```text
Γ ⊢ P    Γ, h : P ⊢ Q
─────────────────────  cut
Γ ⊢ Q
the at and with arguments first use ∀E and →E to obtain P
```

### `fact with ⟨a, b⟩`

**Supply a conjunction or existential premise in place.** An anonymous constructor is a proof expression wherever its proposition is known: in a with list, after exact or show, in an annotated have, and as a refine component. Nested constructors go through predicate definitions. In an unannotated have, the components fix the parameters of the applied theorem as named entries do: have m := lemma.backward with ⟨hJ, extendsJ⟩ matches hJ and extendsJ against the conjuncts of the requirement, so no at list is needed and no context fact of the same shape can choose another instance. When a requirement is a conjunction and the with list supplies its conjuncts in order, as difference.membership.backward with inSpace, notInjective does for x ∈ A ∧ x ∉ B, the entries are combined as ⟨inSpace, notInjective⟩ would be; a genuine mismatch keeps its message. Parentheses group a multi-premise application inside refine ⟨…⟩, where commas separate components. A local fact that is a transparent predicate application, such as subset : A ⊆ B, applies to arguments through its definition without unfolding it first.

```g17
-- ih : ∀ y, y ∈ H ∧ R(y, x) → P(y), hy : y ∈ H, earlier : R(y, x)
obtain ⟨closed, increasing⟩ := ih with y, ⟨hy, earlier⟩
```

Rule schema:

```text
Γ ⊢ A    Γ ⊢ B    fact establishes (A ∧ B) → P
──────────────────────────────────────────────  ∧I, →E
Γ ⊢ P
the constructor is checked against the premise it fills
```

### `fact at terms with *`

**Infer routine premises already visible on the board.** Grace17 reconstructs soft-type facts such as Nat(n) from the local context when applying a typed theorem. For source theorems, with * consumes generated guards and declared requires clauses, stopping at shows even if the conclusion is an implication or negation. Equivalence directions also consume the selected side. A missing requirement is an error. A local proof value has no declared boundary, so * consumes its leading implication chain. Name the premises when the choice matters mathematically.

Bare `*` stops at a source theorem's `shows` boundary even when evidence for an antecedent in the conclusion is available, so conditional and negative results are preserved. To eliminate such an implication, name the evidence after the star: `with *, evidence`. A named premise may also precede the star: `with named, *`.

`with *` draws on local facts, instance synthesis, and Tau refinement reconstruction, in that order. It does not find library theorems or prove reflexive equalities: bind `have one := realZero.lt_one` or `have same : t = t` with `rfl` first, or list the premise explicitly.

For local proof values and declarations without a source boundary, `*` consumes the leading implication chain; use a count to preserve a remainder.

```g17
-- aNat : Nat(a), bNat : Nat(b), h : a = b
have copied := equality.copy at a, b with *
-- copied : a = b
```

Rule schema:

```text
Γ contains checked evidence for every required premise
──────────────────────────────────────────────────────  ∀E, →E
Γ ⊢ Q
soft-type evidence and exact matching premises are reconstructed from Γ
```

### `fact at terms with *{n}`

**Fill exactly n premise arguments, preserving a partial application.** A counted star expands to n comma-separated assumption entries before proof-argument parsing. Counts range from 1 to 256. It can be mixed with named premises and used in specialize. A counted star does not stop at the declared conclusion. It consumes the written number of premises and fails if evidence is missing. Quantified terms still need explicit arguments.

A counted star can consume an implication inside a conclusion, for example to pass the contradicting fact to a negated lemma: `exact realLe.not_less at A, B with *{2}, le, lt` establishes `⊥` from `¬(B < A)` and the two comparisons.

```g17
-- h needs three guards followed by a mathematical premise
have partial := h at a, b, c with *{3}
-- The mathematical premise remains available as a goal when applying partial.
```

Rule schema:

```text
Γ ⊢ P₁ → … → Pₙ → R    Γ ⊢ P₁    …    Γ ⊢ Pₙ
────────────────────────────────────────────  repeated →E
Γ ⊢ R
1 ≤ n ≤ 256; R may retain further premises; counted stars expand to explicit assumption arguments
```

### `have h : P := fact with *`

**Infer a local fact from its stated proposition.** The annotation guides the same bounded parameter inference as exact with *. Equivalence .forward and .backward applications infer from the selected conclusion and antecedent; the antecedent still needs evidence. The proof must establish P; the annotation is checked against it and supplies no evidence. A missing premise or an ambiguous carrier is an error. An unannotated have never uses the enclosing goal for inference.

The annotation is checked against the proof even if `h` is never used. It supplies no evidence and does not become an assumption while proving itself.

```g17
have diagonal : n = n := natural with *
```

Rule schema:

```text
Γ ⊢ P    Γ, h : P ⊢ Q
─────────────────────  cut
Γ ⊢ Q
P guides bounded inference and is checked against the resulting proof
```

### `have h : P`

**Prove a local lemma in an indented block.** When the block closes, the checked fact is available in the surrounding proof. Small lemmas keep the shape of the argument visible. A local proposition may continue on a more-indented line after an operator or a comma, ∧, ∨, →, ↔, ∈, ⊆, ∪ and the others, or on a more-indented line that begins with one; the block follows beneath the last line. The terms of exact, witness, refine, apply, and have h := also continue on a more-indented line.

Blocks nest; a dedent resumes the surrounding goal, and dedenting while the local goal is unfinished is a focused diagnostic. A block can start immediately after a branch bullet with its body indented beneath the command.

Local lemmas are scoped to their branch. A universally quantified local lemma can be reused under a later binder with the same variable name without capture. The local proposition is not available as an assumption while proving itself.

Introduced term variables and existential witnesses also belong to one goal: sibling `have` proofs and sibling constructor or case branches may reuse witness names, and a witness never escapes its local proof.

```g17
have diagonal : x = x
  rfl
exact diagonal
```

Rule schema:

```text
Γ ⊢ P    Γ, h : P ⊢ Q
─────────────────────  cut
Γ ⊢ Q
```

### `have h : P by tactic`

**Prove a local lemma with the tactics on the same line.** The tactics after by, separated by ;, run in order on P in a nested script, and h is then available in the surrounding proof. With nothing after by, the indented block on the following lines is the proof, as for have h : P. The proposition may begin on the next line, more indented than the have.

```g17
have alternatives : y = x ∨ y ≠ x by tauto
have bounded : n < succ(n) by
  arith
```

Rule schema:

```text
Γ ⊢ P    Γ, h : P ⊢ Q
─────────────────────  cut
Γ ⊢ Q
the tactic proves P
```

### `calc`

**Present an equality or inequality as a chain of steps.** Each indented line has the form left relation right := justification. Write _ for the preceding right-hand endpoint. Equality, homogeneous < and ≤, mixed strict and non-strict order, and equality steps within an inequality chain are supported for registered numeric orders. A justification may be a proof expression or a tactic sequence after by, as in by rw h; ring, which runs every tactic on the step. Direct proof expressions receive the step proposition for bounded with * parameter inference. The goal-state panel follows the residual relation after every line. The elaborator uses the named transitivity theorems, equality elimination, and Tau for typing premises, leaving the kernel unchanged.

The `_` on a later line is the preceding right-hand endpoint. After a nonfinal line the visible goal becomes the remaining relation, so cursor-based goal states follow the calculation. A wrong starting point, broken intermediate endpoint, or wrong final endpoint is reported at the responsible line.

Strict rational and real inequalities may be chained in the same notation. Natural-number calculations support homogeneous `<` and `≤` as well as the mixed compositions `<` followed by `≤` and `≤` followed by `<`; the relation registry names a checked transitivity theorem for every supported composition, and unsupported or ambiguous compositions are rejected.

Each direct justification passes its own step proposition to bounded `with *` inference, so `_ = y := lemma with *` can infer the lemma's parameters from that step alone.

```g17
-- hab : a ≤ b, hbc : b < c, hcd : c = d
calc
  a ≤ b := hab
  _ < c := hbc
  _ = d := hcd
```

Rule schema:

```text
Γ ⊢ a R b    Γ ⊢ b S c    checked transitivity: R ; S ⇒ T
─────────────────────────────────────────────────────────  relation transitivity
Γ ⊢ a T c
each displayed justification and the named composition theorem are kernel-checked
```

### `specialize h with x, hx`

**Feed arguments and premises to a local theorem already on the board.** Grace17 consumes leading ∀ binders and implication premises in order, replacing h with the specialized result. Use with * to fill a local implication chain, or *{n} for exactly n premises. Local facts have no declared-requirement boundary. Use fact at terms with premises instead when you want to apply and name a fact in one line.

`specialize` uses the same proof-application parser as `have` and `exact`, including bare `*` and counted `*{n}`. Because a local fact has no declared-requirement boundary, bare `*` consumes its whole leading implication chain; use a count to keep a remainder.

```g17
-- h : ∀ x, x ∈ A → P(x), hx : x ∈ A
specialize h with x, hx
-- h : P(x)
```

Rule schema:

```text
h : ∀ x, R(x) → P(x) ∈ Γ    hx : R(t) ∈ Γ
─────────────────────────────────────────  ∀E, →E
Γ ⊢ P(t)
```

## Logic and witnesses

The natural-deduction moves. Each name says what shape the proof takes.

### `constructor  /  split`

**Split a conjunction or equivalence goal.** A conjunction yields its two sides. An equivalence yields its forward and backward implications.

```g17
-- goal: P ∧ Q
constructor
. exact hP
. exact hQ
```

Rule schema:

```text
Γ ⊢ P    Γ ⊢ Q
──────────────  ∧I
Γ ⊢ P ∧ Q
For P ↔ Q, the premises are Γ ⊢ P → Q and Γ ⊢ Q → P
```

### `refine ⟨a, ha, b, hb, _⟩`

**Build nested witnesses and conjunctions in one pattern.** Grace17 follows transparent predicate definitions, ∃, ∧, and ↔ recursively. Terms fill existential witnesses, checked facts fill proposition leaves, and _ leaves a focused goal. Nested patterns such as ⟨⟨h.right.left, ?_⟩, ?_⟩ preserve grouping; ?_ leaves a proposition as a focused goal, and at a conjunction with entries still to come it stands for the first conjunct, so ⟨a, ha, ?_, ?_, hc⟩ fills A ∧ B ∧ C. Local facts support checked .left/.right projections, including nested paths. A fact proving a whole nested conjunction may occupy one entry. Each proof component supplies its expected proposition for bounded with * inference. A final existential component can be a complete proof. The elaborator emits each introduction separately.

Nested patterns such as `⟨⟨h.right.left, ?_⟩, ?_⟩` preserve grouping. `_` is a flattened leaf hole; `?_` leaves an entire proposition as a focused goal, including a conjunction or an existential whose witness is supplied later. `?_` is a hole for a proof; a term witness must be written out. Every hole must be discharged before QED.

Local conjunction facts support `.left` and `.right`, nested as needed, in proof expressions, in `with` lists, and as rules for `rw`, `simp`, `simpa`, and `settle`. They require an explicit conjunction: unfold a named predicate first. A dotted path rooted in a local fact is resolved locally before global names and never searches the context.

The final component may be an existing existential proof: `refine ⟨xs, list, spans, table⟩` replaces a final hole followed by `exact table`. Earlier existential entries must be written witnesses.

```g17
-- goal: ∃ x, x ∈ A ∧ ∃ y, y ∈ B ∧ R(x, y)
refine ⟨a, ha, b, hb, _⟩
-- goal: R(a, b)
```

Rule schema:

```text
Γ ⊢ a ∈ A    Γ ⊢ b ∈ B    Γ ⊢ R(a, b)
─────────────────────────────────────  ∃I, ∧I
Γ ⊢ ∃ x, x ∈ A ∧ ∃ y, y ∈ B ∧ R(x, y)
_ leaves its corresponding premise as a goal
```

### `left  /  right`

**Choose a side of a disjunction.** The selected proposition becomes the focused goal.

```g17
-- h : P, goal: P ∨ Q
left
exact h
```

Rule schema:

```text
Γ ⊢ P
─────────  ∨I₁
Γ ⊢ P ∨ Q
right uses the symmetric rule ∨I₂
```

### `witness t  /  use t`

**Supply an existential witness.** After choosing t, the existential body with t substituted is the new goal.

Under a bounded existential `∃ q ∈ ℚ, P(q)`, supplying the witness leaves its membership condition `q ∈ ℚ` as a goal alongside `P(q)`.

```g17
-- goal: ∃ x, x = a
witness a
rfl
```

Rule schema:

```text
Γ ⊢ P(t)
─────────────  ∃I
Γ ⊢ ∃ x, P(x)
```

### `rcases h with ⟨h₁, h₂, h₃⟩`

**Open nested conjunctions or existentials in one checked step.** The pattern follows the logical structure recursively. A flat pattern descends through right-associated ∧ and ∃, nested brackets group entries, and _ ignores one. Parentheses may replace angle brackets.

Flat entries follow the usual right-associated shape of `∧` and `∃`; nested brackets make a subpattern explicit; `_` discards an entry. The elaborator still emits each conjunction or existential elimination separately.

Destructure a transparent predicate directly: `rcases h with ⟨…⟩` follows its definition, so an `unfold P at h` before it is unnecessary.

```g17
-- h : P ∧ Q ∧ R
rcases h with ⟨hP, hQ, hR⟩
-- hP : P, hQ : Q, hR : R
```

Rule schema:

```text
Γ ⊢ P ∧ Q ∧ R
─────────────────────────  ∧E
Γ, h₁ : P, h₂ : Q, h₃ : R
the recursive pattern abbreviates repeated conjunction elimination
```

### `obtain ⟨x, hx, rfl⟩ := fact`

**Open data and substitute an equality immediately.** An rfl pattern consumes an equality that identifies a discovered variable, rewrites the goal and local facts, and keeps the representative equation out of the rest of the proof. It is equality elimination, used for unpacking structured objects. The side substituted is a variable not occurring in the other side; an equation with no such side is reported. A goal binder that would capture the replacement is renamed, not skipped.

An `rfl` entry is equality elimination. If the packed data exposes `y = t` or `t = y`, the pattern substitutes away the discovered variable and rewrites the goal and local facts.

```g17
-- packed : ∃ y, P(y) ∧ y = x
obtain ⟨y, hy, rfl⟩ := packed
-- hy is now available in the rewritten context
```

Rule schema:

```text
Γ ⊢ ∃ x, P(x) ∧ x = t    Γ, hx : P(t) ⊢ Q
─────────────────────────────────────────  ∃E, =E
Γ ⊢ Q
x is fresh; equality elimination substitutes t for x
```

### `cases h with hp | hq`

**Reason by cases on a disjunction.** Grace17 creates one goal for each side, and each branch receives its own case fact.

Each branch receives its own case fact, and the branches are independent goals: witness names introduced in one branch may be reused in another.

```g17
-- h : P ∨ Q, goal: Q ∨ P
cases h with hP | hQ
. right; exact hP
. left; exact hQ
```

Rule schema:

```text
Γ ⊢ P ∨ Q    Γ, hp : P ⊢ R    Γ, hq : Q ⊢ R
───────────────────────────────────────────  ∨E
Γ ⊢ R
the branch hypotheses hp and hq are discharged
```

### `rcases h with hp | hq | hr`

**Flatten a finite disjunction into named branches.** Nested disjunctions associate in either direction. Grace17 gives each leaf its own branch and reconstructs the nested ∨ elimination proof, so trichotomy reads as one three-way split. A leaf may be a pattern instead of a name: rfl substitutes the alternative's equation in its branch, and ⟨x, hx, rfl⟩ opens the alternative's data, as in rcases h with rfl | ⟨x, hx, rfl⟩.

The written disjunction may associate to the left or to the right; Grace17 reconstructs the nested ∨-elimination proof in either case.

```g17
-- comparison : a < b ∨ a = b ∨ b < a
rcases comparison with less | equal | greater
. exact lessCase with less
. exact equalCase with equal
. exact greaterCase with greater
```

Rule schema:

```text
Γ ⊢ P ∨ Q ∨ R    Γ, hp : P ⊢ S    Γ, hq : Q ⊢ S    Γ, hr : R ⊢ S
────────────────────────────────────────────────────────────────  ∨E
Γ ⊢ S
nested disjunction elimination discharges all three branch hypotheses
```

### `obtain ⟨x, hx, y, hy⟩ := fact`

**Name all the witnesses and facts inside a packed result.** This is the expression form of recursive rcases. It opens alternating existentials and conjunctions from left to right and each ∃E freshness condition is checked.

The pattern grammar is the same as for `rcases`: flat right-associated entries, nested brackets, `_`, and `rfl`. An outer witness remains in scope in nested proofs, so `obtain` rejects reusing its name there.

```g17
-- packed : ∃ x, P(x) ∧ ∃ y, Q(x, y)
obtain ⟨x, hx, y, hxy⟩ := packed
-- x y : Set, hx : P(x), hxy : Q(x, y)
```

Rule schema:

```text
Γ ⊢ ∃ x, P(x) ∧ ∃ y, Q(x, y)    Γ, a : Set, ha : P(a), b : Set, hab : Q(a, b) ⊢ R
─────────────────────────────────────────────────────────────────────────────────  ∃E, ∧E
Γ ⊢ R
a and b are fresh; the recursive pattern abbreviates repeated eliminations
```

### `exfalso`

**Reduce the goal to a contradiction.** Once ⊥ is proved, false elimination gives the original proposition.

A contradiction branch must start with `exfalso`: a proof that establishes `⊥` against a goal that is still `∃ …` or another proposition is reported as establishing the wrong formula.

```g17
-- h : ⊥, goal: P
exfalso
exact h
```

Rule schema:

```text
Γ ⊢ ⊥
─────  ⊥E
Γ ⊢ P
```

### `by_contra h`

**Assume the negation of the goal as h and prove ⊥.** The negated goal becomes the local fact h, or this when no name is given. Grace17 reconstructs the result with checked classical double-negation elimination.

```g17
-- goal: x ∈ Y
by_contra absent
-- absent : ¬x ∈ Y, goal: ⊥
have member : x ∈ X ∖ Y by simp [hx, absent]
rw h at member
simp at member
```

Rule schema:

```text
Γ, h : ¬P ⊢ ⊥
─────────────  classical
Γ ⊢ P
discharges the local hypothesis h : ¬P
```

### `by_cases h : P`

**Split the goal on a proposition and its negation.** Two goals follow, the first with h : P and the second with h : ¬P, each taking a bullet as after cases; the name defaults to h. The split is excluded middle for P, reconstructed by checked classical double-negation elimination, so by_cases h : P is the idiom have split : P ∨ ¬P by tauto followed by cases split with h | h in one step. The proposition may begin on the next line, more indented than the by_cases, as after have h :.

`by_cases h : P` is the one-step form of `have split : P ∨ ¬P by tauto` followed by `cases split with h | h`. The proposition is read in the scope of the goal, so notation and soft types of the local context apply to it. With nothing after the colon, `by_cases h :` takes its proposition from the next, more indented line, as `have h :` does; a proposition may also break after an operator or a comma, or before an operator, like any other step.

```g17
-- goal: x = y ∨ x ≠ y
by_cases h : x = y
. left; exact h
. right; exact h
```

Rule schema:

```text
Γ, h : P ⊢ Q    Γ, h : ¬P ⊢ Q
─────────────────────────────  ∨E
Γ ⊢ Q
on P ∨ ¬P by classical double-negation elimination; the branch hypotheses h are discharged
```

### `contradiction`

**Finish from contradictory local facts.** A short search finds the clash and builds the proof.

```g17
-- hP : P, hnP : ¬P
contradiction
```

Rule schema:

```text
h : P ∈ Γ    hn : ¬P ∈ Γ
────────────────────────  ¬E, ⊥E
Γ ⊢ Q
search constructs the displayed natural-deduction steps
```

### `tauto`

**Finish classical propositional reasoning.** Predicates, equalities, and quantified formulas are atoms. An equation and its mirror image are one atom, so a = b, b = a, a ≠ b, and ¬(b = a) are decided together. The proof is a case split on those atoms.

`tauto` is complete for classical propositional logic. Equality, predicate, and quantified formulas are atoms; `∧`, `∨`, implication, equivalence, negation, and `⊥` are decided propositionally. An equation is the same atom in either orientation, so `a = b` and `b = a` are one atom, as are `a ≠ b` and `¬(b = a)`; from `h : a = b` the goal `¬(b ≠ a)` closes, and a lemma stated as `l = v ∨ r = v` meets a hypothesis `v ≠ l`. This is a reading of the atoms, not equality reasoning: `a = b` and `b = c` do not give `a = c`, which is for `cc`. Search branches on an atom only while the current partial valuation leaves the goal and all hypotheses undecided; each split is an instance of excluded middle, and each leaf is a natural-deduction proof. The default fuel is 65,536 search nodes, and exhaustion is an error.

```g17
-- goal: ((P → Q) → P) → P
tauto
```

Rule schema:

```text
certificate : propositional derivation of P from Γ
──────────────────────────────────────────────────  tauto
Γ ⊢ P
the derivation is a case split on atoms
```

## Changing the view

A proof often gets easy once the right definition is exposed or the goal is rewritten into the right shape.

### `symm  /  symm at h`

**Reverse an equality goal or a named equality fact.** The operation builds the kernel equality-symmetry proof. The at form updates only the named local fact; the goal form asks for the reversed equality as a new goal.

```g17
-- h : x = y, goal: y = x
symm
show x = y := h
```

Rule schema:

```text
Γ ⊢ s = t
─────────  =sym
Γ ⊢ t = s
the at form stores the result as a local fact
```

### `rw h  /  rewrite h  /  rw ← h`

**Rewrite forward or backward with an equality or an equivalence.** Add at localName to rewrite a local fact instead of the goal. rw moves with p, hp rewrites with the instance that application names, as have inst := moves with p, hp then rw inst would; the parameters the facts leave open are fixed by the one instance of the rule's rewritten side that occurs in the goal, or in the fact named after at, so rw crossing.restrict with edges needs no at list, and two different instances are reported with their bindings; a with list that does not apply is reported with the application rw read. A parenthesised application, rw (thm with facts), is a rule too, in rw, rwa, and the rule lists of simp. A goal the rewrite makes reflexive is closed when the rewrite ends its branch, the script, a dedent, or a sibling bullet following it, as simp closes one; a step written after it in the same branch, rfl included, still finds the goal as written. A rule P ↔ Q, possibly under ∀ and premises, rewrites the subformula P of the goal or fact by Q, at every occurrence of the instance matched first, with the implications built from the connectives on the path; ← rewrites Q by P. A rule that selects nothing is reported with its sides and the goal or fact, printed with the notation in scope.

Rewriting is equality elimination. A notation token names its underlying definition wherever a rule is expected.

`rw thm with facts` fixes the parameters the facts leave open from the goal, or from the fact named after `at`: the rule's left side, or its right side under `←`, is matched against every subterm, and the one instance that occurs fixes them, so `rw crossing.restrict with edges` needs no `at` list; two different instances are reported with their bindings, and an explicit `at` list chooses. `rw (thm with facts)` groups the application as a rule, in `rw`, `rwa`, and the rule lists of `simp`.

`unfold` leaves local equalities unapplied, so `rw h` after `unfold f` finds the instance the definition exposed; `cc` closes a goal that follows from the context equalities directly.

```g17
-- hxy : x = y, goal: pair(x, x) = pair(y, y)
rw hxy
-- h : x ∈ A ↔ P(x), goal: x ∈ A ∨ Q
rw h
-- goal: P(x) ∨ Q
```

Rule schema:

```text
Γ ⊢ s = t    Γ ⊢ P(s)
─────────────────────  =E
Γ ⊢ P(t)
the backward form exchanges s and t
```

### `rw [h₁, h₂] / rwa h`

**Rewrite with several rules in turn, or rewrite and close from the context.** A rewrite that ends its bullet branch and leaves an equality or an equivalence between identical sides closes the goal. rw [a, b, ← c] performs the single rewrites in order, on the goal or at a fact; a rule that fails is reported by its own name and located at the rule in the list. rwa h is rw h followed by closing the rewritten goal from a matching local fact; rwa h at fact rewrites the fact and then uses it to close the goal.

```g17
-- h1 : a = b, h2 : b = c, hc : Nat(c), goal: Nat(a)
rwa [h1, h2]
```

Rule schema:

```text
Γ ⊢ a = b    Γ, P(b) ⊢ Q  or  P(b) ∈ Γ
──────────────────────────────────────  =E
Γ ⊢ P(a)  or  Γ ⊢ Q
each rule rewrites in turn; rwa then closes by hypothesis
```

### `rw under h at fact`

**Rewrite safely inside a quantified proposition.** The explicit under form crosses ∀ or ∃ only when the equality's source and replacement do not depend on that binder's variable. It works on a goal or named fact and accepts ← for reverse rewriting. Plain rw does not look under binders. The rewrite is equality elimination; an equality that mentions the bound variable is not rewritten beneath it.

```g17
-- h : a = b, fact : ∃ x, R(a, x)
rw under h at fact
-- fact : ∃ x, R(b, x)
```

Rule schema:

```text
Γ ⊢ s = t    Γ ⊢ ∃ x, P(s, x)
─────────────────────────────  =E
Γ ⊢ ∃ x, P(t, x)
x occurs free in neither s nor t; ∀ and reverse rewriting are analogous
```

### `simp [rules]`

**Normalize, decide membership, and close with the logical search.** A rule that is an equivalence, such as a membership law, is opened at every instance of a fact under simp […] at h, inside binders included, as unfold opens it; the law x ∉ ∅ and any rule stating a negation rewrite the atom to ⊥, which is absorbed: ⊥ ∧ P is ⊥, ⊥ ∨ P is P, and P ↔ ⊥ is ¬P. A residue the rewrites leave is closed when it is a propositional consequence of the context or a closed numeral computation, as 1 + 1 = 2 is. simp with rules is equivalent. It closes the goal when normalization, ground reasoning, or the logical search suffice; otherwise a checked proposition equivalence may replace the focused goal so simplification can continue incrementally. Membership in compound sets needs no rules: the visible membership characterizations and the Subset definition are instantiated where the goal's atoms match them, universal hypotheses are instantiated at the terms in play, and the result is decided by case analysis with congruence closure, so ext y then simp proves insert(x, V ∖ {x}) = V from x ∈ V. Other definitions are named, as in simp [pow]. A predicate definition among the rules, simp [EvenSet] or simp [EvenSet] at h, is opened wherever the goal or fact mentions it, as unfold opens it. Inside a logical goal the named equalities are applied to a bounded fixed point, so simp [fst.pair, snd.pair] reduces every layer of fst(fst(((a, b), c))) ∈ A and leaves a ∈ A for the next tactic, or closes the goal when the context settles it. Add at h to simplify a proved proposition in place. Conditional rewrite hypotheses use context and soft typing by default; opt into recursive relief with simp (backchain := 2, work := 128) [rules]. Relief shares its work allowance and never splits cases. In a disjunction, the incremental pass may use negated sibling literals, discharging them in the reconstructed proof.

`simp` normalizes with checked definitions, equalities, ground computation, and routine logical assembly. It evaluates closed `Bool` expressions and discharges many constructive propositional tautologies; for complete classical propositional reasoning use `tauto`.

Incremental use: if the rules do not close the goal but a supplied equivalence changes the outer proposition, `simp` leaves the equivalent simplified proposition as the next goal and records the checked backward implication. If no outer equivalence applies, it can perform one equality rewrite inside a logical goal, including a negated condition, without rewriting beneath quantifiers or splitting cases. In a disjunction it may use the negations of sibling literals while rewriting one literal and discharges those assumptions in the reconstructed proof.

`simp [rules] at h` forward-simplifies an arbitrary proved proposition through checked equivalences and equality transport: `simp [pair.membership] at h` turns `h : x ∈ pair(a, b)` into `h : x = a ∨ x = b`.

A set-builder definition named among the rules, `simp [f] at h`, opens every `t ∈ f(…)` instance of the fact, as `simp [f.membership] at h` does; an equivalence such as `union2.membership` is opened at every instance too, under `∃` and `∀` included, so `simp [union2.membership, singleton.membership] at hf` turns `hf : x ∈ {a} ∪ {b}` into `hf : x = a ∨ x = b` in one step. The empty-set law is applied by default: `simp at h` with `h : a ∈ ∅ ∧ P` leaves `h : ⊥`.

A predicate definition named among the rules is opened at every instance first, as `unfold` opens it, so `simp [EvenSet] at parity` turns every `EvenSet(A)` in `parity` into `Even(cardinality(A))` before the rest of the simplification; the equivalence rewriting that follows reaches the outer proposition.

Conditional rewrite rules use direct contextual evidence and soft-type reasoning by default. Recursive relief needs explicit limits, `simp (backchain := 2, work := 128) [rules]`, also accepted by `simp ... at h` and `simpa`. `backchain` bounds recursive rule applications along a hypothesis path; `work` is one allowance shared across relief entries, attempted conclusions and conjuncts, contextual bindings, sibling guards, and the closure phases. Relief can select conjuncts of a rule conclusion and either direction of an equivalence, and may bind a rule variable absent from the conclusion by matching a hypothesis against a contextual fact; it never guesses witnesses or splits cases, and exhaustion leaves the rewrite unapplied.

Context equalities receive a conservative occurs check: an expanding fact `x = f(x)` is oriented as `f(x) → x`, rewrite paths are cycle-checked, and normalization has an explicit depth limit. These are termination controls.

```g17
-- goal: x ∈ {x, y}
simp [pair.membership]
```

Rule schema:

```text
checked equations reduce P to Q    Γ ⊢ Q
────────────────────────────────────────  simp
Γ ⊢ P
every reduction is justified by a named fact or definition
```

### `simpa [rules] using fact`

**Normalize a fact and the goal, then use the checked result.** Normalizes both sides before logical search, including capture-safe rewriting of binder-independent terms beneath quantifiers. Normalization is cycle-checked and bounded, and the logical fallback has work and depth limits.

Binder-independent terms are rewritten beneath `∀` and `∃` without guessing witnesses; a rewrite that depends on a bound variable or would capture it is not performed. Logical normalization is cycle-checked and limited to 256 transport steps per side, equality normalization keeps its separate rewrite fuel, and the logical fallback stops at a 1,000-step budget or 64 nested search states.

```g17
-- shape : u = (a ↦ b), pairLess : R((a ↦ b), v)
simpa [shape] using pairLess
```

Rule schema:

```text
Γ ⊢ P    checked equations normalize P and Q to the same formula
────────────────────────────────────────────────────────────────  simp, exact
Γ ⊢ Q
the normalized fact must match the normalized goal
```

### `unfold name`

**Expose one definition.** The named definition is opened at every instance of the goal, or of the fact named by at h, in one call: under every connective and relation, inside arguments, and inside a ∀ or ∃ whose bound variable the instance mentions. A set-builder def f(…) : Set := { x ∈ A | φ } is its membership law, so unfold f opens every t ∈ f(…) instance into t ∈ A ∧ φ and reports when the goal or fact mentions f(…) only as a set: reason about f(…) on a side of = or ⊆ with ext. A defined predicate at the head of the goal or fact is opened through its definition, with its generated carrier guards supplied or peeled. Nothing else changes: local equalities are never applied, so the result depends on the definition alone and not on the context; bring a context equality h in afterwards with rw h, with simp [name, h], or close from the context with cc. A definition the goal or fact does not mention is reported. Notation such as % may name its underlying definition directly. A name declared at two arities means the one the goal, or the fact named by at, mentions.

A set-builder `def f(…) : Set := { x ∈ A | φ }` has its membership law as its definition, so `unfold f` opens every `t ∈ f(…)` instance of the goal or fact into `t ∈ A ∧ φ`. When the only mentions of `f(…)` are as a set, on a side of `=` or `⊆`, `unfold f` reports that it opens membership instances and that `ext` is the way to reason about `f(…)` as a set.

`unfold` handles predicate definitions and defining equations alike, so `unfold nat.succ` exposes a compact numeral as its von Neumann set `union(pair(n, pair(n, n)))` in a checked equality without changing the evaluator's native representation. `unfold` never rewrites with local equalities: after `unfold f`, a context equality `h` is applied by `rw h` or by `simp [f, h]`, and `cc` closes a goal the context equalities settle. Every instance opens in one call, so a second `unfold f` on the same goal or fact reports that there is nothing left to unfold.

```g17
-- goal mentions a % b
unfold %
-- the goal now contains remainder's defining body
```

Rule schema:

```text
Γ ⊢ name(x) = body(x)    Γ ⊢ P(body(x))
───────────────────────────────────────  def
Γ ⊢ P(name(x))
```

### `ext x`

**Prove set equality one member at a time.** Grace17 introduces a fresh x and reduces A = B to x ∈ A ↔ x ∈ B using checked extensionality.

```g17
-- goal: {a, a} = {a}
ext x
simp
```

Rule schema:

```text
Γ, x : Set ⊢ x ∈ A ↔ x ∈ B
──────────────────────────  ext
Γ ⊢ A = B
```

### `clear h`

**Remove a local fact from the visible board.** It only changes what you see.

Unused assumptions never need to be mentioned.

```g17
-- hUnused : P, h : Q, goal: Q
clear hUnused
exact h
```

Rule schema:

```text
Γ ⊢ Q
────────────  weak
Γ, h : P ⊢ Q
```

### `rename h => betterName`

**Rename a local fact.** Only the name changes.

```g17
rename this => memberOfA
exact memberOfA
```

Rule schema:

```text
Γ, h : P ⊢ Q
─────────────────────  α
Γ, betterName : P ⊢ Q
```

### `revert h`

**Move an assumption back into the goal.** This is especially useful before induction when h depends on the variable that will change.

`revert` is required before `induction x using membership` for any assumption that mentions `x`; the induction then reintroduces it inside the body.

```g17
-- h : P(x), goal: Q(x)
revert h
-- goal: P(x) → Q(x)
```

Rule schema:

```text
Γ, h : P ⊢ Q
────────────  →I
Γ ⊢ P → Q
discharges the local hypothesis h : P
```

## Search and automation

Let Grace17 find the library fact or clear routine residue. Whatever search finds is checked like any other proof.

### `exact?`

**Find a checked fact that closes the goal.** The Workbench shows the suggestions and executes the first deterministic result.

The query tactics search the current checked import environment, including axioms and generated definition properties such as `V.history.membership.backward`, show up to eight readable commands in the Workbench Info drawer, and execute the first result. A finished proof should replace a `?` tactic with the suggested explicit command. Search is bounded: when it finds nothing, name the theorem yourself.

```g17
-- goal: ¬Finite(ω)
exact?
-- finds: exact omega.infinite
```

Rule schema:

```text
search finds an available fact establishing P
─────────────────────────────────────────────  exact?
Γ ⊢ P
the kernel checks the chosen fact
```

### `apply?`

**Find a theorem whose conclusion matches.** The selected theorem may leave its premises as new goals.

```g17
-- goal: x ∈ {x}
apply?
-- proposes a singleton membership direction
```

Rule schema:

```text
search finds Γ ⊢ P₁ → … → Pₙ → Q    Γ ⊢ P₁    …    Γ ⊢ Pₙ
─────────────────────────────────────────────────────────  apply?
Γ ⊢ Q
the kernel checks the chosen application
```

### `rw?`

**Find one checked rewrite that changes the goal.** Search includes local equalities and imported definition properties.

Rewrite search also considers local equalities.

```g17
-- hxy : x = y, goal: f(x) = f(y)
rw?
rfl
```

Rule schema:

```text
search finds Γ ⊢ s = t    Γ ⊢ P(s)
──────────────────────────────────  rw?
Γ ⊢ P(t)
the kernel checks the chosen rewrite
```

### `settle with rules`

**An older spelling of simp [rules].** settle and settle with rules mean simp and simp [rules]: the same normalization, the same ground reasoning with the automatic membership lemmas, and the same logical search. New proofs should write simp.

`settle` and `settle with rules` are older spellings of `simp` and `simp [rules]` and behave identically: normalization with the supplied equations and induction hypotheses, ground reasoning with the automatic membership lemmas, and the bounded logical search that introduces conjunctions, disjunctions, implications, and universal binders, instantiates named rules, chooses a direction through `↔`, and synthesizes bounded witnesses.

```g17
-- goal: x ∈ insert(x, A)
simp
```

Rule schema:

```text
bounded search constructs a derivation from Γ
─────────────────────────────────────────────  settle
Γ ⊢ P
only named rules, local facts, and standard checked reductions are used
```

### `typecheck`

**Reconstruct a routine soft-type or closure fact.** Use this for goals such as Nat(a * b + c) when the required Nat facts are already local, or a * b ∈ G under Group(G) with (a b : G), the closure theorems of the area being refinement rules; the zero and one of a ring over separate pieces are read off a local IsRing or IsCommRing fact. The elaborator searches the registered refinement rules and builds a proof from them. A numeral literal of any length is typed at once, Nat(k) and k ∈ ℕ alike: above 64 it is typed by the closure rules of successor, addition, and multiplication, two steps per binary digit, and above 128 binary digits by splitting it in halves of its digits, each step closed by a computation certificate. A membership m ∈ n of literal naturals, 2 ∈ 4, is decided by the successor laws of the ordinals, and a disequality of distinct literals, 1 ≠ 0, by the zero and successor laws, in any module.

Tau indexes checked propositions of the forms `P(x) → Q(x)`, `P(x) → Q(y) → R(f(x, y))`, `(P(x) ∧ Q(x)) → R(x)`, `Q(constant)`, constructor closure facts, and atomic predicate equivalences such as `Nat(n) ↔ n ∈ ω`, including local induction hypotheses. Refinement search is bounded by depth 256, 4,096 visited goals, 100,000 rule attempts, and 4,096 expanded term nodes per goal; exhaustion returns no evidence, and an explicit proof can still discharge the obligation.

```g17
-- aNat : Nat(a), bNat : Nat(b), cNat : Nat(c)
-- goal: Nat(a * b + c)
typecheck
```

Rule schema:

```text
registered refinement rules derive T(t) from Γ
──────────────────────────────────────────────  typecheck
Γ ⊢ T(t)
each step applies a registered rule
```

### `synthesize`

**Construct registered instance evidence.** Exact local evidence wins. Otherwise it searches the visible instance declarations, rejects ambiguity, and applies the instance theorem.

```g17
-- source : Source(x), goal: Target(x)
synthesize
```

Rule schema:

```text
visible instance declarations derive C(args) from Γ
───────────────────────────────────────────────────  instance
Γ ⊢ C(args)
search is indexed, tabled, cycle-checked, and bounded
```

### `cc  /  congruence`

**Finish a ground equality or predicate congruence.** Congruence closure by union-find, then an equality proof assembled from the facts it used. A disequality goal, or a denied predicate, is assumed and refuted from the conflict it creates with the local equalities.

`cc` chains local equalities, closes function congruences, transports positive predicate facts across congruent arguments, and derives arbitrary goals from a congruent disequality or a positive/negative predicate conflict. A disequality goal `s ≠ t`, or a denied predicate `¬P(t)`, is assumed and refuted: the equation or predicate joins the facts and ⊥ follows from the conflict it creates, so `rightEnd(e) ≠ v` follows from `leftEnd(e) = rightEnd(e)` and `leftEnd(e) ≠ v`. The explanation is built from the original equalities, equality transitivity and symmetry, function congruence, and equality elimination. `cc` does no quantifier instantiation and no conditional rewriting; use `specialize`, `rw`, and `simp` for those.

```g17
-- h : x = y, goal: f(g(x)) = f(g(y))
cc
-- loop : leftEnd(e) = rightEnd(e), atV : leftEnd(e) ≠ v
-- goal: rightEnd(e) ≠ v
cc
```

Rule schema:

```text
equalities in Γ place s and t in one congruence class
─────────────────────────────────────────────────────  cc
Γ ⊢ s = t
the equality explanation is checked
```

### `decide`

**Decide a closed statement about finite sets.** For goals x ∈ A, x ∉ A, A ⊆ B, A = B, A ≠ B, and cardinality(A) = n whose terms are set literals, numerals, ∪, ∩, ∖, 𝒫, insert, and ∅, decide evaluates the statement and, when it holds, writes a proof from the Cumulus membership lemmas (pair.membership, union2.membership, insert.membership, intersection.membership, difference.membership, powerset.membership_iff, set.empty) and the counting lemmas, which the elaborator then checks step by step. Numerals are atoms: 2 ∈ 5 goes through the natural-number lemmas, but a numeral is never unfolded into the set of its predecessors, so {0} = 1 is outside the fragment, as is a powerset on the left of ⊆ or =. A false statement is reported as false rather than left open.

```g17
theorem union_example
  shows {1, 2} ∪ {2, 3} = {1, 2, 3}
proof
  decide
```

Rule schema:

```text
evaluation finds the closed finite-set statement P true    a generated script proves P from the membership lemmas
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────  decide
Γ ⊢ P
every step of the generated script is checked
```

### `compute`

**Finish a supported closed computation.** The proof is a computation certificate: the equation and the list of definitions used. The kernel reruns the evaluation. A closed order goal over ℕ, a < b, a ≤ b, or a ≠ b, is accepted too: both sides are evaluated, the gap between them is the witness of the order's definition, and a ≠ b goes through Less.irreflexive; a false comparison is reported with the two values. Natural subtraction, predecessor, remainder, and quotient evaluate natively, like addition and multiplication, so 365 ^ 23 - (2 * fallingFactorial(365, 23) + 1) is one step.

`compute` accepts only closed terms. Its proof node stores the equality and the exact sorted list of admitted function definitions used during normalization; the kernel re-runs the trusted closed-value evaluator on both sides and compares normal forms, so the proof stays small however long the computation runs. Fuel or host resource exhaustion can only reject a certificate. A top-level `eval term` inspects a computation without adding a theorem.

```g17
theorem factorial.five
  shows 5! = 120
proof
  compute

theorem powers.apart
  shows 2 ^ 10 < 3 ^ 7
proof
  compute
```

Rule schema:

```text
evaluator emits a checked certificate
─────────────────────────────────────  compute
Γ ⊢ s = value
the kernel reruns the evaluation
```

## Arithmetic

These tactics do the algebraic bookkeeping so the proof can stay about its idea.

### `ring`

**Prove Nat or commutative-ring polynomial identities.** For a registered CommRing or OrderedRing, ring builds checked certificates for signed sums, products, distributivity, cancellation, zero, and one. The carrier and operation graphs come from type-class evidence: under a bundled hypothesis CommRing(R) or Field(R), or a closed instance such as CommRing(integerRing), they are read off the projections through CommRing.parts, so (x : R) and R[2] need no further setup, and under a notation ring scope they are the scope's pieces. The registered quotient integers support signed arithmetic and subtraction directly. Checked .notation equations can connect value functions to the selected operation graphs; their carrier hypotheses must be proved. Nat has its own normalizer, in which numerals are coefficients: 2 * a and a + a share the normal form 2 * a, and coefficient arithmetic is a computation certificate. A power with a literal exponent, t ^ k for k ≤ 16, is expanded into its product over ℕ, ℤ, ℚ, ℝ, and bundled rings, with the certificate built from the power's defining equations, so (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 is ring alone; a larger exponent stays an atom. ring at h and ring_nf use the same certificates, and ring_nf closes an equality whose sides normalize to the same term. A quotient t / k is an atom, which ring says when the sides differ; use linarith for a linear goal, or rewrite with realDiv.eq_mul_inv or a named constant such as oneHalf.

`ring` proves polynomial identities by normalizing with checked semiring or commutative-ring theorems from the import environment. The Nat rule set covers zero and one, successor as `n + 1`, additive rearrangement, multiplication, associativity, annihilation, and distributivity. For a registered `CommRing` or `OrderedRing` instance it builds certificates over that carrier's operation graphs, expands transparent wrappers such as real subtraction, and bounds polynomial expansion at 256 monomials. Opaque terms need checked membership in the selected carrier; polynomial atoms such as `x(a)` for a point `a` are typed through Tau.

When several ring structures are in scope, the shallowest visible operations across the goal and named equations select the ring: in `f(call1(neg, x)) = call1(minus, f(x))` the target-ring `minus` controls normalization. `ring` admits only nontrivial equality hypotheses connected to the goal and reuses a prepared, root-indexed rewrite program.

```g17
-- goal: succ(k) * n = k * n + n
ring
```

Rule schema:

```text
normalization certificate from Γ
────────────────────────────────  ring
Γ ⊢ lhs = rhs
each step is a semiring equality
```

### `ring [h₁, h₂]`

**Close an equation using equations as rewrite rules, modulo the ring axioms.** Each named equation is normalized and its left side is used as a rewrite rule wherever a multiple of it fits inside the normal form of a side of the goal; the rules first reduce one another, so a law stated with (n + 1)! applies after the factorial law has been used inside it. The sides are then compared by ring. This is how a step law is applied several times at once: multiply both sides by what the laws need and finish with ring [s1, s2, s3, s4]. Natural-number goals for now.

`ring [h₁, …]` closes a natural-number equation using the named equations as rewrite rules modulo the semiring axioms. Each rule is normalized; wherever a monomial multiple of a rule's left side fits inside the normal form of a side of the goal, that multiple is exposed by a checked normalization step and replaced through equality elimination by the same multiple of the right side; the rules reduce one another first; the sides are then compared by ring. Every step is a kernel-checked equality, and a goal the rules do not close reports the two residual normal forms.

```g17
-- step : x * (c + 1) = y * (2 * c + 2), expand : y = c + 1
ring [step, expand]
```

Rule schema:

```text
h₁ : p₁ = q₁ ∈ Γ    h₂ : p₂ = q₂ ∈ Γ    normalization certificates from Γ
─────────────────────────────────────────────────────────────────────────  ring
Γ ⊢ lhs = rhs
each rule rewrites an exposed multiple of its normal form by equality elimination
```

### `ring_nf`

**Normalize polynomial expressions inside an equality or predicate.** On a goal, ring_nf rewrites every polynomial argument to canonical form and leaves the normalized goal open. The ring_nf at h form does the same to a local equality or predicate fact, including inequalities and ideal membership. In p ∈ I only p is normalized; I and any relation graph are left alone.

`ring at h` normalizes a proved polynomial equality in place; `ring_nf` and `ring_nf at h` normalize every polynomial argument of an equality or predicate without closing it, so `(a + b) * c < d` becomes `a * c + b * c < d`. Equality elimination transports each normalized fact back to its authored form.

```g17
-- h : (a + b) * c < d
ring_nf at h
-- h : a * c + b * c < d
```

Rule schema:

```text
checked polynomial equalities for each argument
───────────────────────────────────────────────  ring_nf
Γ ⊢ P(normal forms)
equality elimination transports the original goal or fact
```

### `linear_combination 2 * h1 - h2`

**Combine checked polynomial equalities.** Expressions scale equalities, read as the goal is: a bare numeral coefficient is the ring's numeral, so 2 * h scales a real equation by the real two, and a coefficient the notation in scope cannot type is read in the ring the goal selects. A minus sign reverses that equality; if the normalized result has a common polynomial remainder, Grace17 removes it with checked natural-number cancellation.

The tactic selects the commutative-ring interface used by the goal and the named equations, so real and abstract-ring coefficients work as well as Nat coefficients. In a ring, cancellation is normalization with additive inverses; the Nat semiring path keeps its checked additive cancellation. A coefficient must be a term the elaborator can type in that ring. If `2` has no numeral instance in the carrier, write `identity + product + product`; `identity + 2 * product` fails. Missing carrier evidence and incorrect combinations are rejected. The combination is written by hand; there is no search.

```g17
theorem combine (a b c d e : Nat)
  requires h1 : a + c = b + c
  requires h2 : d = e
  shows a + e = b + d
proof
  linear_combination h1 - h2
```

Rule schema:

```text
h₁ : p₁ = q₁ ∈ Γ    h₂ : p₂ = q₂ ∈ Γ
────────────────────────────────────  lincomb
Γ ⊢ 2p₁ + q₂ = 2q₁ + p₂
```

### `arith`

**Finish supported natural equalities and affine order goals.** This includes cancellation, weakening, mixed strict and weak bounds, and checked Fourier-Motzkin elimination with integer tightening: exact eliminations are preferred, and a comparison whose coefficients share a factor is divided through with a rounded constant, each step a checked quotient lemma, so parity and divisibility contradictions close. On a ⊥ goal arith refutes the hypotheses; on a disequality it introduces the equation and refutes; on a conjunction it splits and settles each conjunct, so a list of index inequalities is one line; and when the goal itself is out of reach, contradictory bounds among the hypotheses close it. A disequality of distinct literals, 1 ≠ 0, and a hypothesis equating distinct literals need no order theory: they close in any module. Two equations meeting through succ or a common summand cancel, so cardinality(F) = succ(cardinality(F ∖ {e})) and cardinality(F) = succ(k) give cardinality(F ∖ {e}) = k. A cardinality is a natural atom from Finite(X) in context, and the right side of a bound a ≤ b or a < b from its typed left side, so k ≤ cardinality(X) needs no further typing.

For equalities `arith` combines goal-relevant hypotheses with the semiring normalizer, applies antisymmetry to matching opposite bounds, and keeps an indexed equality graph for repeated nested cancellation. Within one class of that graph two successors cancel by injectivity and two sums with a common summand by the cancellation laws, so `cardinality(F) = succ(cardinality(F ∖ {e}))` and `cardinality(F) = succ(k)` give `cardinality(F ∖ {e}) = k`, and a hypothesis stated with `succ` meets one stated with `+ 1`. For comparisons it normalizes each side to a sparse affine form and runs exact Fourier–Motzkin elimination: strict Nat order is converted by the checked equivalence `a < b ↔ a + 1 ≤ b`, equalities enter as two weak comparisons, and every Nat atom receives `0 ≤ x`. The procedure is complete for inconsistency over the nonnegative rationals with Nat's unit gap; it is narrower than Presburger arithmetic, since a contradiction that depends only on a congruence obstruction needs cuts it does not perform. It reports exhaustion above 16,384 projected constraints or a scalar expansion above 4,096.

`arith` makes one linear context pass, shares an indexed soft-type prover across operand checks, and partitions constraints into independent atom components, searching the goal component first.

An opaque term such as `cardinality(X)` is a natural atom when `Nat(t)`, `t ∈ ℕ`, or a library typing rule settles it from the local facts: `Finite(X)` in context types `cardinality(X)` through `cardinality.nat`, with no `have` needed. The right side of a local bound `a ≤ b` or `a < b` is typed from its left side by `LessEqual.natural_right` and `Less.natural_right`, chased through chains of bounds, so `k ≤ cardinality(X)` with `k : Nat` admits `cardinality(X)` without a finiteness fact. `linarith` on naturals types its atoms the same way.

```g17
-- hx : x > 3, hy : y > 2
-- goal: x + y > 4
arith
-- goal: a ≠ a + 1 ∧ a + 1 ≠ 2 * a
arith
-- removed : cardinality(F) = succ(cardinality(F ∖ {e})), size : cardinality(F) = succ(k)
-- goal: cardinality(F ∖ {e}) = k
arith
```

Rule schema:

```text
affine facts in Γ    Fourier–Motzkin certificate for P
──────────────────────────────────────────────────────  arith
Γ ⊢ P
the certificate is built from the ordered-additive lemmas
```

### `linarith`

**Decide linear inequalities over the reals and rationals, and Nat or ordered-ring affine goals.** Over the reals, linarith negates the goal, runs Fourier-Motzkin elimination over the atoms of the local comparisons, and emits a certificate from the checked order laws (realLe.add, realLess.add and their mixed forms) and one commutative-ring identity, closed by irreflexivity. Goals may be ≤, <, =, a negated comparison, or ⊥. Facts may be comparisons, real equalities, and conjunctions of them, and 0 < 1 is supplied whenever 1 occurs. Over the rationals the same elimination runs on the strict order: facts are rational comparisons s < t and equalities, goals may be <, =, ¬(s < t), or ⊥, and comparison or equality goals are settled by trichotomy with each remaining case refuted. Addition, subtraction, negation, scaling by a numeral, and division by a nonzero numeral are interpreted, the last through the identity t = k * (t / k) proved from the field laws, so 0 < x gives 0 < x / 2; every other term, including a product, is an atom, so state nonlinear facts such as 0 ≤ x * y first. Nat uses the same checked affine elimination as arith, and ordered-ring instances use their OrderedAdditiveGroup laws.

Over the reals, `linarith` accepts goals `s ≤ t`, `s < t`, `s = t` (by antisymmetry), `¬(s ≤ t)`, `¬(s < t)`, and `⊥`, and uses local comparisons, real equalities, and conjunctions of them, plus `0 < 1` whenever `1` occurs. It negates the goal, eliminates atoms by Fourier–Motzkin with integer multipliers, and emits a certificate from `realLe.add`, `realLess.add`, their mixed forms, one ring identity, and irreflexivity. Products are atoms: establish `0 ≤ x * y` first with a library lemma when a goal needs it.

Over `Nat`, `linarith` is the same checked affine elimination as `arith`. For an abstract carrier it queries the instance registry for `OrderedAdditiveGroup(A, add, zero, neg, le)`, projecting from an `OrderedRing` instance or hypothesis through a checked theorem; the carrier, operation graphs, and relation are read from that proof.

```g17
-- ab : a ≤ b, bound : c ≤ a - b
-- goal: c ≤ 0
linarith
```

Rule schema:

```text
linear facts in Γ    linear certificate for P
─────────────────────────────────────────────  linarith
Γ ⊢ P
the certificate is built from the carrier's order lemmas
```

## Shaping a development

These forms mark unfinished work and lay out finished work.

### `sorry`

**Admit the current goal.** The goal becomes a named axiom, with its source line recorded. The theorem shows amber, the admitted state.

A check containing `sorry` succeeds so downstream work can continue, and its source line, goal, theorem, and axiom name are retained in results and axiom audits. Nothing with a `sorry` belongs in Cumulus.

```g17
theorem future_result (x y : Set)
  shows x = y
proof
  sorry
```

Rule schema:

```text
(no premises)
─────────────  sorry
Γ ⊢ P
a synthetic axiom is introduced and recorded
```

### `. tactic`

**Start the next focused subgoal branch.** Indent the following steps beneath the dot. Branches make the proof's shape visible. A step written in a branch whose goal an earlier step already closed, and that does not apply to the next goal, is reported as no goals remain in this case, naming the line that closed the branch.

For multi-step branches, put `.` at the branch boundary and indent the tactics beneath it; a `have` block may begin right after the bullet.

```g17
constructor
. exact hP
. exact hQ
```

Rule schema:

```text
each focused goal is solved under Γ
─────────────────────────────────────────────  branches
Γ ⊢ every goal produced by the parent command
```

### `tactic1; . tactic2`

**Sequence compact moves on one line.** Semicolons preserve the same focused-goal order as the multiline form.

Tactics normally occupy one line; a semicolon gives the same sequence on one line.

```g17
constructor; . assumption; . rfl
```

Rule schema:

```text
tactic1 produces focused goals    tactic2 solves the next selected goal under Γ
───────────────────────────────────────────────────────────────────────────────  ;
Γ ⊢ the composed tactic result
```

### `tactic solve(rule) := simp [$rule]`

**Declare a small module-scoped tactic macro.** A macro is shorthand. It expands, with bounded depth, to built-in tactics before checking. Cumulus declares its rewrite sets this way: group_simp, lattice_simp, topology_simp, metric_simp, category_simp, and functor_simp are simp with the laws of the area, each applied where its operands lie in the carrier.

Macros are module-scoped, imported and resolved like other declarations, expanded with a depth limit, and retained under their source spelling in proof traces.

```g17
tactic finish(rule) := settle with $rule

proof
  finish(pair.membership)
```

Rule schema:

```text
macro expands to built-in tactic commands    expanded commands construct a derivation from Γ
────────────────────────────────────────────────────────────────────────────────────────────  macro
Γ ⊢ P
expansion happens before checking
```

## Induction

Three forms of induction, one for each kind of structure that decreases: a datatype, set membership, or a well-founded relation.

### `induction n [generalizing s ...] [with]`

**Follow the constructors of an inductive datatype and optionally strengthen the hypothesis.** The successor case of a natural number may be written | k + 1 using ih =>, and its goal is then stated with k + 1 rather than succ(k). Place this first in the proof block; recursive fields receive hypotheses named by using. Requirements depending on the induction variable are automatically moved into the motive, even without generalizing; introduce them in each branch, and supply them when using the recursive hypothesis. Generalized declared variables may occur before or after n. Their soft types, dependent binders, and dependent requirements move into the motive, so each recursive hypothesis works for every new value. The optional with changes nothing; an internal auxiliary theorem restores the public binder order.

Place `induction n` first in the proof block. Requirements depending on `n` or on a generalized variable are moved into the motive, even without `generalizing`; introduce them at the start of each branch, and the recursive hypothesis takes the corresponding requirements for the smaller argument. Independent requirements stay available by name.

Each constructor is a branch `| C(fields) using ih₁, ih₂ => tactics`, with one hypothesis per recursive field in field order and a full tactic sequence allowed after `=>`. A field typed by a datatype parameter adds membership in that carrier to the branch.

```g17 fragment
theorem walk (s : Set, es : List)
  shows P(es, s)
proof
  induction es generalizing s with
  | List.nil =>
    intro s
    exact base at s
  | List.cons(x, xs) using ih =>
    intro s
    exact step at x, xs, s with ih
```

Rule schema:

```text
Γ ⊢ P(zero)    Γ, k : Nat, ih : ∀ s, P(k, s) ⊢ ∀ s, P(succ(k), s)
─────────────────────────────────────────────────────────────────  Nat-ind
Γ, n : Nat ⊢ ∀ s, P(n, s)
```

### `induction x using membership`

**Descend through the members of an arbitrary set.** Introduce the current set, then ih. The hypothesis proves the motive for every member of the current set. Revert assumptions that depend on x before starting. The expansion names the Foundation library's lemmas in full, so another closure in scope, as the topology library declares, is no ambiguity.

The tactic builds the transitive closure of `x` by Replacement, proves membership on it well-founded from Foundation, and uses well-founded induction. An assumption that mentions `x` cannot stay fixed while `x` changes, so `revert` it first.

```g17
theorem membership.irreflexive (x : Set)
  shows ¬x ∈ x
proof
  induction x using membership
  intros current ih hSelf
  have impossible := ih at current with hSelf, hSelf
  exact impossible
```

Rule schema:

```text
Γ, current : Set, ih : ∀ y, y ∈ current → P(y) ⊢ P(current)
───────────────────────────────────────────────────────────  ∈-ind
Γ, x : Set ⊢ P(x)
well-foundedness comes from set-theoretic Foundation
```

### `induction x over A ordered by r certified by founded`

**Descend through any certified well-founded relation.** The goal must be ∀ x, x ∈ A → P(x), and founded must prove wellFoundedOn(r, A). The introduced ih maps a predecessor y with y ∈ A ∧ relates(r, y, x) to P(y).

Inside the body, `hx : x ∈ A` and `ih : ∀ y, y ∈ A ∧ relates(r, y, x) → P(y)`. Use `ih` by specializing it at the predecessor and supplying the membership and relation facts. The relation, carrier, and certificate stay explicit so the proof state shows why recursion is legal.

```g17
theorem relation_reflexive (A r : Set)
  requires founded : wellFoundedOn(r, A)
  shows ∀ x, x ∈ A → x = x
proof
  induction x over A ordered by r certified by founded
  intros x hx ih
  rfl
```

Rule schema:

```text
Γ ⊢ wellFoundedOn(r, A)    Γ, x : Set, hx : x ∈ A, ih : ∀ y, y ∈ A ∧ relates(r, y, x) → P(y) ⊢ P(x)
───────────────────────────────────────────────────────────────────────────────────────────────────  WF-ind
Γ ⊢ ∀ x, x ∈ A → P(x)
```
