// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Fuller reference notes for the tactic entries in tactics-guide.js, keyed by
// each entry's exact syntax line. The Workbench Help shows them beneath an
// entry on request, and `npm run docs:tactics` renders them into
// docs/tactics.md. Paragraphs are Markdown with inline code only.
export const tacticReference = new Map([
  ["intro h", [
    "For a bounded universal goal `∀ q ∈ ℚ, P(q)`, `intro q` introduces the set and the next `intro` names its membership hypothesis; `intros q qRational` does both.",
    "`intro x at h` specializes the leading universal quantifier of a local fact `h` at an already-introduced term; it is the hypothesis-local form of universal elimination.",
  ]],
  ["intros x hx y hy", [
    "`intros` is the compact form of consecutive `intro` commands. The elaborator nests the same checked ∀I and →I steps and stops with a diagnostic if the goal runs out of leading binders or premises.",
  ]],
  ["exact fact", [
    "A proof expression may consume arguments immediately: mathematical terms after `at`, then checked premise facts after `with`, as in `exact transitive at x, y, z with hxy, hyz`. The same expression works after `have` and `apply`.",
    "For a source theorem, `exact theorem with *`, `show P := theorem with *`, and `have h := theorem with *` can omit `at`: the conclusion is matched against the goal when there is one, then uniquely matching local premises determine the remaining parameters. Matching is structural, indexed by formula head, and capped at 2,048 attempts; it does not unfold definitions, backchain, or choose between ambiguous substitutions. Typed parameters participate through their generated guards, and every guard still needs checked evidence. An explicit `at` list is the fallback.",
    "`exact theorem.forward with *` and `exact theorem.backward with *` infer parameters from the selected conclusion and unique local premise matches, including the selected antecedent, which still requires evidence. An implication or negation inside the selected conclusion remains intact.",
  ]],
  ["show P := fact", [
    "`show` compares `P` with the focused goal and then closes the goal with the proof expression. Use it to make the conclusion of a long proof readable.",
  ]],
  ["rfl  /  reflexivity", [
    "`rfl` also appears inside `rcases` and `obtain` patterns, where it means equality elimination of a discovered equation.",
  ]],
  ["apply fact", [
    "`apply theorem at args` makes the generated carrier guards the first goals, before the declared premises. When a premise needs its own derivation, prefer `have h : P` followed by `exact theorem at args with *`.",
    "`apply theorem with *` requests checked evidence for the declared premises; use bare `apply` when those premises should remain to be proved. `apply theorem.forward` and `.backward` leave open requirements and the selected antecedent as goals, and stop when the residual conclusion equals the goal, preserving an implication or negation that is itself the requested result.",
  ]],
  ["have h := fact with premises", [
    "Use `specialize` when the unspecialized fact is already on the board and you want to replace it; use `have ... with` when the applied result is the fact you want from the start.",
    "`have h := fact` without `with` binds an available fact unchanged. This is separate from `have h : P`, which opens a proof block for a new proposition.",
  ]],
  ["fact at terms with *", [
    "Bare `*` stops at a source theorem's `shows` boundary even when evidence for an antecedent in the conclusion is available, so conditional and negative results are preserved. To eliminate such an implication, name the evidence after the star: `with *, evidence`. A named premise may also precede the star: `with named, *`.",
    "`with *` draws on local facts, instance synthesis, and Tau refinement reconstruction, in that order. It does not find library theorems or prove reflexive equalities: bind `have one := realZero.lt_one` or `have same : t = t` with `rfl` first, or list the premise explicitly.",
    "For local proof values and declarations without a source boundary, `*` consumes the leading implication chain; use a count to preserve a remainder.",
  ]],
  ["fact at terms with *{n}", [
    "A counted star can consume an implication inside a conclusion, for example to pass the contradicting fact to a negated lemma: `exact realLe.not_less at A, B with *{2}, le, lt` establishes `⊥` from `¬(B < A)` and the two comparisons.",
  ]],
  ["have h : P := fact with *", [
    "The annotation is checked against the proof even if `h` is never used. It supplies no evidence and does not become an assumption while proving itself.",
  ]],
  ["have h : P", [
    "Blocks nest; a dedent resumes the surrounding goal, and dedenting while the local goal is unfinished is a focused diagnostic. A block can start immediately after a branch bullet with its body indented beneath the command.",
    "Local lemmas are scoped to their branch. A universally quantified local lemma can be reused under a later binder with the same variable name without capture. The local proposition is not available as an assumption while proving itself.",
    "Introduced term variables and existential witnesses also belong to one goal: sibling `have` proofs and sibling constructor or case branches may reuse witness names, and a witness never escapes its local proof.",
  ]],
  ["calc", [
    "The `_` on a later line is the preceding right-hand endpoint. After a nonfinal line the visible goal becomes the remaining relation, so cursor-based goal states follow the calculation. A wrong starting point, broken intermediate endpoint, or wrong final endpoint is reported at the responsible line.",
    "Strict rational and real inequalities may be chained in the same notation. Natural-number calculations support homogeneous `<` and `≤` as well as the mixed compositions `<` followed by `≤` and `≤` followed by `<`; the relation registry names a checked transitivity theorem for every supported composition, and unsupported or ambiguous compositions are rejected.",
    "Each direct justification passes its own step proposition to bounded `with *` inference, so `_ = y := lemma with *` can infer the lemma's parameters from that step alone.",
  ]],
  ["specialize h with x, hx", [
    "`specialize` uses the same proof-application parser as `have` and `exact`, including bare `*` and counted `*{n}`. Because a local fact has no declared-requirement boundary, bare `*` consumes its whole leading implication chain; use a count to keep a remainder.",
  ]],

  ["refine ⟨a, ha, b, hb, _⟩", [
    "Nested patterns such as `⟨⟨h.right.left, ?_⟩, ?_⟩` preserve grouping. `_` is a flattened leaf hole; `?_` leaves an entire proposition as a focused goal, including a conjunction or an existential whose witness is supplied later. `?_` is a hole for a proof; a term witness must be written out. Every hole must be discharged before QED.",
    "Local conjunction facts support `.left` and `.right`, nested as needed, in proof expressions, in `with` lists, and as rules for `rw`, `simp`, `simpa`, and `settle`. They require an explicit conjunction: unfold a named predicate first. A dotted path rooted in a local fact is resolved locally before global names and never searches the context.",
    "The final component may be an existing existential proof: `refine ⟨xs, list, spans, table⟩` replaces a final hole followed by `exact table`. Earlier existential entries must be written witnesses.",
  ]],
  ["witness t  /  use t", [
    "Under a bounded existential `∃ q ∈ ℚ, P(q)`, supplying the witness leaves its membership condition `q ∈ ℚ` as a goal alongside `P(q)`.",
  ]],
  ["rcases h with ⟨h₁, h₂, h₃⟩", [
    "Flat entries follow the usual right-associated shape of `∧` and `∃`; nested brackets make a subpattern explicit; `_` discards an entry. The elaborator still emits each conjunction or existential elimination separately.",
    "Destructure a transparent predicate directly: `rcases h with ⟨…⟩` follows its definition, so an `unfold P at h` before it is unnecessary.",
  ]],
  ["obtain ⟨x, hx, rfl⟩ := fact", [
    "An `rfl` entry is equality elimination. If the packed data exposes `y = t` or `t = y`, the pattern substitutes away the discovered variable and rewrites the goal and local facts.",
  ]],
  ["cases h with hp | hq", [
    "Each branch receives its own case fact, and the branches are independent goals: witness names introduced in one branch may be reused in another.",
  ]],
  ["rcases h with hp | hq | hr", [
    "The written disjunction may associate to the left or to the right; Grace17 reconstructs the nested ∨-elimination proof in either case.",
  ]],
  ["obtain ⟨x, hx, y, hy⟩ := fact", [
    "The pattern grammar is the same as for `rcases`: flat right-associated entries, nested brackets, `_`, and `rfl`. An outer witness remains in scope in nested proofs, so `obtain` rejects reusing its name there.",
  ]],
  ["exfalso", [
    "A contradiction branch must start with `exfalso`: a proof that establishes `⊥` against a goal that is still `∃ …` or another proposition is reported as establishing the wrong formula.",
  ]],
  ["tauto", [
    "`tauto` is complete for classical propositional logic. Equality, predicate, and quantified formulas are atoms; `∧`, `∨`, implication, equivalence, negation, and `⊥` are decided propositionally. Search branches on an atom only while the current partial valuation leaves the goal and all hypotheses undecided; each split is an instance of excluded middle, and each leaf is a natural-deduction proof. The default fuel is 65,536 search nodes, and exhaustion is an error.",
  ]],

  ["rw h  /  rewrite h  /  rw ← h", [
    "Rewriting is equality elimination. A notation token names its underlying definition wherever a rule is expected.",
    "After `unfold`, local equalities may already have been applied to the exposed body, so a following `rw h` can report that the rule does not match; `cc` closes such goals directly.",
  ]],
  ["simp [rules]", [
    "`simp` normalizes with checked definitions, equalities, ground computation, and routine logical assembly. It evaluates closed `Bool` expressions and discharges many constructive propositional tautologies; for complete classical propositional reasoning use `tauto`.",
    "Incremental use: if the rules do not close the goal but a supplied equivalence changes the outer proposition, `simp` leaves the equivalent simplified proposition as the next goal and records the checked backward implication. If no outer equivalence applies, it can perform one equality rewrite inside a logical goal, including a negated condition, without rewriting beneath quantifiers or splitting cases. In a disjunction it may use the negations of sibling literals while rewriting one literal and discharges those assumptions in the reconstructed proof.",
    "`simp [rules] at h` forward-simplifies an arbitrary proved proposition through checked equivalences and equality transport: `simp [pair.membership] at h` turns `h : x ∈ pair(a, b)` into `h : x = a ∨ x = b`.",
    "Conditional rewrite rules use direct contextual evidence and soft-type reasoning by default. Recursive relief needs explicit limits, `simp (backchain := 2, work := 128) [rules]`, also accepted by `simp ... at h` and `simpa`. `backchain` bounds recursive rule applications along a hypothesis path; `work` is one allowance shared across relief entries, attempted conclusions and conjuncts, contextual bindings, sibling guards, and the closure phases. Relief can select conjuncts of a rule conclusion and either direction of an equivalence, and may bind a rule variable absent from the conclusion by matching a hypothesis against a contextual fact; it never guesses witnesses or splits cases, and exhaustion leaves the rewrite unapplied.",
    "Context equalities receive a conservative occurs check: an expanding fact `x = f(x)` is oriented as `f(x) → x`, rewrite paths are cycle-checked, and normalization has an explicit depth limit. These are termination controls.",
  ]],
  ["simpa [rules] using fact", [
    "Binder-independent terms are rewritten beneath `∀` and `∃` without guessing witnesses; a rewrite that depends on a bound variable or would capture it is not performed. Logical normalization is cycle-checked and limited to 256 transport steps per side, equality normalization keeps its separate rewrite fuel, and the logical fallback stops at a 1,000-step budget or 64 nested search states.",
  ]],
  ["unfold name", [
    "`unfold` handles predicate definitions and defining equations alike, so `unfold nat.succ` exposes a compact numeral as its von Neumann set `union(pair(n, pair(n, n)))` in a checked equality without changing the evaluator's native representation. `unfold` also rewrites with local equalities in the exposed body.",
  ]],
  ["clear h", [
    "Unused assumptions never need to be mentioned.",
  ]],
  ["revert h", [
    "`revert` is required before `induction x using membership` for any assumption that mentions `x`; the induction then reintroduces it inside the body.",
  ]],

  ["exact?", [
    "The query tactics search the current checked import environment, including axioms and generated definition properties such as `V.history.membership.backward`, show up to eight readable commands in the Workbench Info drawer, and execute the first result. A finished proof should replace a `?` tactic with the suggested explicit command. Search is bounded: when it finds nothing, name the theorem yourself.",
  ]],
  ["rw?", [
    "Rewrite search also considers local equalities.",
  ]],
  ["settle with rules", [
    "`settle` and `settle with rules` are older spellings of `simp` and `simp [rules]` and behave identically: normalization with the supplied equations and induction hypotheses, ground reasoning with the automatic membership lemmas, and the bounded logical search that introduces conjunctions, disjunctions, implications, and universal binders, instantiates named rules, chooses a direction through `↔`, and synthesizes bounded witnesses.",
  ]],
  ["typecheck", [
    "Tau indexes checked propositions of the forms `P(x) → Q(x)`, `P(x) → Q(y) → R(f(x, y))`, `(P(x) ∧ Q(x)) → R(x)`, `Q(constant)`, constructor closure facts, and atomic predicate equivalences such as `Nat(n) ↔ n ∈ ω`, including local induction hypotheses. Refinement search is bounded by depth 256, 4,096 visited goals, 100,000 rule attempts, and 4,096 expanded term nodes per goal; exhaustion returns no evidence, and an explicit proof can still discharge the obligation.",
  ]],
  ["cc  /  congruence", [
    "`cc` chains local equalities, closes function congruences, transports positive predicate facts across congruent arguments, and derives arbitrary goals from a congruent disequality or a positive/negative predicate conflict. The explanation is built from the original equalities, equality transitivity and symmetry, function congruence, and equality elimination. `cc` does no quantifier instantiation and no conditional rewriting; use `specialize`, `rw`, and `simp` for those.",
  ]],
  ["by_cases h : P", [
    "`by_cases h : P` is the one-step form of `have split : P ∨ ¬P by tauto` followed by `cases split with h | h`. The proposition is read in the scope of the goal, so notation and soft types of the local context apply to it.",
  ]],
  ["compute", [
    "`compute` accepts only closed terms. Its proof node stores the equality and the exact sorted list of admitted function definitions used during normalization; the kernel re-runs the trusted closed-value evaluator on both sides and compares normal forms, so the proof stays small however long the computation runs. Fuel or host resource exhaustion can only reject a certificate. A top-level `eval term` inspects a computation without adding a theorem.",
  ]],

  ["ring", [
    "`ring` proves polynomial identities by normalizing with checked semiring or commutative-ring theorems from the import environment. The Nat rule set covers zero and one, successor as `n + 1`, additive rearrangement, multiplication, associativity, annihilation, and distributivity. For a registered `CommRing` or `OrderedRing` instance it builds certificates over that carrier's operation graphs, expands transparent wrappers such as real subtraction, and bounds polynomial expansion at 256 monomials. Opaque terms need checked membership in the selected carrier; polynomial atoms such as `x(a)` for a point `a` are typed through Tau.",
    "When several ring structures are in scope, the shallowest visible operations across the goal and named equations select the ring: in `f(call1(neg, x)) = call1(minus, f(x))` the target-ring `minus` controls normalization. `ring` admits only nontrivial equality hypotheses connected to the goal and reuses a prepared, root-indexed rewrite program.",
  ]],
  ["ring [h₁, h₂]", [
    "`ring [h₁, …]` closes a natural-number equation using the named equations as rewrite rules modulo the semiring axioms. Each rule is normalized; wherever a monomial multiple of a rule's left side fits inside the normal form of a side of the goal, that multiple is exposed by a checked normalization step and replaced through equality elimination by the same multiple of the right side; the rules reduce one another first; the sides are then compared by ring. Every step is a kernel-checked equality, and a goal the rules do not close reports the two residual normal forms.",
  ]],
  ["ring_nf", [
    "`ring at h` normalizes a proved polynomial equality in place; `ring_nf` and `ring_nf at h` normalize every polynomial argument of an equality or predicate without closing it, so `(a + b) * c < d` becomes `a * c + b * c < d`. Equality elimination transports each normalized fact back to its authored form.",
  ]],
  ["linear_combination 2 * h1 - h2", [
    "The tactic selects the commutative-ring interface used by the goal and the named equations, so real and abstract-ring coefficients work as well as Nat coefficients. In a ring, cancellation is normalization with additive inverses; the Nat semiring path keeps its checked additive cancellation. A coefficient must be a term the elaborator can type in that ring. If `2` has no numeral instance in the carrier, write `identity + product + product`; `identity + 2 * product` fails. Missing carrier evidence and incorrect combinations are rejected. The combination is written by hand; there is no search.",
  ]],
  ["arith", [
    "For equalities `arith` combines goal-relevant hypotheses with the semiring normalizer, applies antisymmetry to matching opposite bounds, and keeps an indexed equality graph for repeated nested cancellation. For comparisons it normalizes each side to a sparse affine form and runs exact Fourier–Motzkin elimination: strict Nat order is converted by the checked equivalence `a < b ↔ a + 1 ≤ b`, equalities enter as two weak comparisons, and every Nat atom receives `0 ≤ x`. The procedure is complete for inconsistency over the nonnegative rationals with Nat's unit gap; it is narrower than Presburger arithmetic, since a contradiction that depends only on a congruence obstruction needs cuts it does not perform. It reports exhaustion above 16,384 projected constraints or a scalar expansion above 4,096.",
    "`arith` makes one linear context pass, shares an indexed soft-type prover across operand checks, and partitions constraints into independent atom components, searching the goal component first.",
  ]],
  ["linarith", [
    "Over the reals, `linarith` accepts goals `s ≤ t`, `s < t`, `s = t` (by antisymmetry), `¬(s ≤ t)`, `¬(s < t)`, and `⊥`, and uses local comparisons, real equalities, and conjunctions of them, plus `0 < 1` whenever `1` occurs. It negates the goal, eliminates atoms by Fourier–Motzkin with integer multipliers, and emits a certificate from `realLe.add`, `realLess.add`, their mixed forms, one ring identity, and irreflexivity. Products are atoms: establish `0 ≤ x * y` first with a library lemma when a goal needs it.",
    "Over `Nat`, `linarith` is the same checked affine elimination as `arith`. For an abstract carrier it queries the instance registry for `OrderedAdditiveGroup(A, add, zero, neg, le)`, projecting from an `OrderedRing` instance or hypothesis through a checked theorem; the carrier, operation graphs, and relation are read from that proof.",
  ]],

  ["sorry", [
    "A check containing `sorry` succeeds so downstream work can continue, and its source line, goal, theorem, and axiom name are retained in results and axiom audits. Nothing with a `sorry` belongs in Cumulus.",
  ]],
  [". tactic", [
    "For multi-step branches, put `.` at the branch boundary and indent the tactics beneath it; a `have` block may begin right after the bullet.",
  ]],
  ["tactic1; . tactic2", [
    "Tactics normally occupy one line; a semicolon gives the same sequence on one line.",
  ]],
  ["tactic solve(rule) := simp [$rule]", [
    "Macros are module-scoped, imported and resolved like other declarations, expanded with a depth limit, and retained under their source spelling in proof traces.",
  ]],

  ["induction n [generalizing s ...] [with]", [
    "Place `induction n` first in the proof block. Requirements depending on `n` or on a generalized variable are moved into the motive, even without `generalizing`; introduce them at the start of each branch, and the recursive hypothesis takes the corresponding requirements for the smaller argument. Independent requirements stay available by name.",
    "Each constructor is a branch `| C(fields) using ih₁, ih₂ => tactics`, with one hypothesis per recursive field in field order and a full tactic sequence allowed after `=>`. A field typed by a datatype parameter adds membership in that carrier to the branch.",
  ]],
  ["induction x using membership", [
    "The tactic builds the transitive closure of `x` by Replacement, proves membership on it well-founded from Foundation, and uses well-founded induction. An assumption that mentions `x` cannot stay fixed while `x` changes, so `revert` it first.",
  ]],
  ["induction x over A ordered by r certified by founded", [
    "Inside the body, `hx : x ∈ A` and `ih : ∀ y, y ∈ A ∧ relates(r, y, x) → P(y)`. Use `ih` by specializing it at the predecessor and supplying the membership and relation facts. The relation, carrier, and certificate stay explicit so the proof state shows why recursion is legal.",
  ]],
]);

export function tacticReferenceNotes(syntax) {
  return tacticReference.get(syntax) ?? [];
}
