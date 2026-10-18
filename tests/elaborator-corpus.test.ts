// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { checkWorkbenchFiles } from "../src/workbench.ts";

// A corpus of small modules that pin the elaborator's semantics where the
// library would not notice a regression: public binder order, positional
// premises, guard filling, numeral arithmetic, and rewriting shapes.

function check(name: string, body: string, imports = ["Grace.Core.Nat.Algebra"]) {
  const source = `module Corpus.${name}\n${imports.map(item => `import ${item}`).join("\n")}\n\n${body}\n`;
  return checkWorkbenchFiles([{ name: `${name}.g17`, source }], "ZFG", [`${name}.g17`], { includeKernelDetails: false });
}

const positions = [
  { binders: "(m n : Nat)", variable: "m", order: ["m", "n"] },
  { binders: "(m n : Nat)", variable: "n", order: ["m", "n"] },
  { binders: "(m n k : Nat)", variable: "m", order: ["m", "n", "k"] },
  { binders: "(m n k : Nat)", variable: "n", order: ["m", "n", "k"] },
  { binders: "(m n k : Nat)", variable: "k", order: ["m", "n", "k"] },
  { binders: "(A : Set) (m n : Nat)", variable: "m", order: ["A", "m", "n"] },
  { binders: "(m : Nat) (A : Set) (n : Nat)", variable: "m", order: ["m", "A", "n"] },
];

// Whatever parameter an induction descends on, the theorem is published with
// its header's binder order and guard order, and positional `at` and `with`
// lists follow the header.
for (const { binders, variable, order } of positions) {
  test(`induction on ${variable} of ${binders} keeps the declared order`, () => {
    const guards = order.filter(name => name !== "A");
    const last = order.at(-1)!;
    const body = `theorem probe ${binders}
  shows ${last} = ${last}
proof
  induction ${variable}
  | zero => rfl
  | succ(j) using ih => rfl

theorem use (${guards.join(" ")} : Nat) (A : Set)
  shows ${last} = ${last}
proof
  exact probe at ${order.join(", ")} with *

theorem positional (${guards.join(" ")} : Nat) (A : Set)
  shows ${last} = ${last}
proof
${guards.map(name => `  have ${name}Nat : Nat(${name})\n    typecheck`).join("\n")}
  exact probe at ${order.join(", ")} with ${guards.map(name => `${name}Nat`).join(", ")}`;
    const result = check(`Order_${variable}_${order.join("")}`, body);
    assert.equal(result.ok, true, result.message);
    const statement = result.theorems.find(theorem => theorem.name === "probe" || theorem.name.endsWith(".probe"))?.statement ?? "";
    // The statement prints its binders grouped by sort: `∀ A, ∀ m n : ℕ, …`.
    const quantifiers = [...statement.matchAll(/∀ ([A-Za-z ]+?)(?: : ℕ)?,/g)].flatMap(match => match[1]!.split(" "));
    assert.deepEqual(quantifiers, order, statement);
    const guardOrder = [...statement.matchAll(/∀ ([A-Za-z ]+) : ℕ,/g)].flatMap(match => match[1]!.split(" "));
    assert.deepEqual(guardOrder, guards, statement);
  });
}

// A supplied premise list fills every generated guard, whichever guard its
// evidence names, and a lone `with *` fills them all.
test("guards are inferred around named guard evidence", () => {
  const result = check("GuardFill", `theorem closed_use (a b c : Nat)
  shows Nat(add(a, add(b, c)))
proof
  have cNat : Nat(c)
    typecheck
  have inner := add.closed at c, b with cNat
  exact add.closed at add(b, c), a with inner

theorem closed_star (a b : Nat)
  shows Nat(add(a, b))
proof
  exact add.closed at b, a with *`);
  assert.equal(result.ok, true, result.message);
});

// Numerals are typed at any size, by halving above the successor chain.
for (const value of [1, 63, 64, 65, 1000, 65537, 1000000]) {
  test(`Nat(${value}) is typed`, () => {
    const result = check(`Numeral${value}`, `theorem probe\n  shows Nat(${value})\nproof\n  typecheck`);
    assert.equal(result.ok, true, result.message);
  });
}

// Nat ring carries numeral coefficients and closes numeral identities.
test("Nat ring identities with numeral coefficients", () => {
  const cases = [
    "2 * a = a + a",
    "(4 * a + 2) * (a + 1) = 4 * a * a + 6 * a + 2",
    "1234 * (37 * a) = 45658 * a",
    "(a + b) * (a + b) = a * a + 2 * (a * b) + b * b",
    "succ(succ(a)) * 3 = 3 * a + 6",
    "(8 * a * a + 8 * a + 1) + 1 = 2 * ((2 * a + 1) * (2 * a + 1))",
  ];
  for (const [index, statement] of cases.entries()) {
    const result = check(`Ring${index}`, `theorem probe (a b : Nat)\n  shows ${statement}\nproof\n  ring`, ["Grace.Cumulus.Nat"]);
    assert.equal(result.ok, true, `${statement}: ${result.message}`);
  }
});

// ring_nf closes a goal whose sides coincide and rewrites hypothesis
// arguments in place, including when one argument occurs inside another.
test("ring_nf closes coinciding sides and rewrites arguments positionally", () => {
  const result = check("RingNf", `theorem closes (a : Nat)
  shows (a + 1) * (a + 1) = a * a + 2 * a + 1
proof
  ring_nf

theorem positional (a b : Nat)
  requires h : a * 2 < a * 2 + b * (1 + 1)
  shows 2 * a < 2 * a + 2 * b
proof
  ring_nf at h
  ring_nf
  exact h`, ["Grace.Cumulus.Nat"]);
  assert.equal(result.ok, true, result.message);
});

// Glyphs resolve inside dotted names.
test("number-system glyphs resolve in every segment of a dotted name", () => {
  const result = check("Glyph", `theorem dotted (q : Set)
  requires member : q ∈ Grace.Cumulus.Rat.Defs.ℚ
  shows q ∈ Grace.Cumulus.Rat.Defs.rationals
proof
  exact member`, ["Grace.Cumulus.Rat.Defs"]);
  assert.equal(result.ok, true, result.message);
});

// Goal-directed application: parameters come from the goal and the named
// premises, so an `at` list is optional; bare `exact thm` discharges the
// requirements from local facts; nested arguments match their own premise.
test("exact and apply infer instantiations from the goal and named premises", () => {
  const result = check("GoalDirected", `theorem contains (y x W : Set)
  requires remaining : y ∈ W
  shows y ∈ insert(x, W)
proof
  exact insert.contains with remaining

theorem bare (y x W : Set)
  requires remaining : y ∈ W
  shows y ∈ insert(x, W)
proof
  exact insert.contains

theorem antisymmetric (A B : Set)
  requires h : A ⊆ B
  requires h2 : B ⊆ A
  shows A = B
proof
  exact Subset.antisymmetric with h2, h

theorem applied (y x V : Set)
  requires hy : y ∈ V
  requires different : y ≠ x
  shows y ∈ V ∖ {x}
proof
  have notSingleton : ¬(y ∈ {x}) by
    intro singleton
    have equal := singleton.membership.forward with singleton
    exact different with equal
  apply difference.membership.backward
  exact ⟨hy, notSingleton⟩

theorem oneLine (y x : Set)
  shows y = x ∨ y ≠ x
proof
  have alternatives : y = x ∨ y ≠ x by tauto
  exact alternatives`, ["Grace.Cumulus.Set.Finite", "Grace.Cumulus.Set.Core"]);
  assert.equal(result.ok, true, result.message);
});

test("goal-directed application reports an unmatched conclusion", () => {
  assert.throws(() => check("GoalMismatch", `theorem probe (A B : Set)
  requires h : A ⊆ B
  shows A = B
proof
  exact Subset.transitive with h`, ["Grace.Cumulus.Set.Core"]), /conclusion does not match the goal|cannot uniquely infer parameters/);
});

// settle and simp decide membership in compound sets from the visible
// characterization lemmas and the Subset definition without naming them,
// with equality reasoning at the leaves and case analysis on membership.
test("settle decides membership goals from the automatic lemma set", () => {
  const result = check("GroundSets", `theorem restore (V x : Set)
  requires member : x ∈ V
  shows insert(x, V ∖ {x}) = V
proof
  ext y
  settle

theorem meet_join (A B : Set)
  shows A ∩ B ⊆ A ∪ B
proof
  settle

theorem difference_mono (A B C : Set)
  requires h : A ⊆ B
  shows A ∖ C ⊆ B ∖ C
proof
  settle

theorem antisymmetric (A B : Set)
  requires h : A ⊆ B
  requires h2 : B ⊆ A
  shows A = B
proof
  ext y
  simp

theorem pair_order (a b : Set)
  shows {a, b} = {b, a}
proof
  ext y
  settle`, ["Grace.Cumulus.Set.Finite", "Grace.Cumulus.Set.Core"]);
  assert.equal(result.ok, true, result.message);
});

test("settle reports a membership goal that is false", () => {
  assert.throws(() => check("GroundFalse", `theorem probe (A B : Set)
  shows A ∪ B ⊆ A
proof
  settle`, ["Grace.Cumulus.Set.Finite", "Grace.Cumulus.Set.Core"]), /settle did not close/);
});

// rwa rewrites and then closes from the context, on the goal or on a fact.
test("rwa rewrites and closes", () => {
  const result = check("Rwa", `theorem goal (a b : Nat)
  requires h : a = b
  requires hb : Nat(b)
  shows Nat(a)
proof
  rwa h

theorem fact (a b : Nat)
  requires h : a = b
  requires ha : Nat(a)
  shows Nat(b)
proof
  rwa h at ha`);
  assert.equal(result.ok, true, result.message);
});

// Anonymous constructors as arguments, parenthesized applications inside
// refine, and local predicate facts applied through their definitions.
test("anonymous constructors, grouped applications, and local predicate facts apply in place", () => {
  const result = check("InPlace", `theorem conj (x S : Set)
  requires h : x ∈ S ∧ S ⊆ S
  shows x ∈ S
proof
  exact h.left

theorem useIt (x S : Set)
  requires hx : x ∈ S
  shows x ∈ S
proof
  exact conj with ⟨hx, Subset.reflexive at S⟩

theorem nested (x S : Set)
  requires hx : x ∈ S
  shows Nonempty(S) ∧ x ∈ S
proof
  exact ⟨⟨x, hx⟩, hx⟩

theorem grouped (x S : Set)
  requires hx : x ∈ S
  shows ∃ y, y ∈ S ∧ x ∈ S
proof
  refine ⟨x, hx, (conj with ⟨hx, Subset.reflexive at S⟩)⟩

theorem localPredicate (A B x : Set)
  requires h : A ⊆ B
  requires hx : x ∈ A
  shows x ∈ B
proof
  exact h with x, hx`, ["Grace.Cumulus.Set.Core"]);
  assert.equal(result.ok, true, result.message);
});

// arith refutes a ⊥ goal from the local comparisons.
test("arith closes a false goal from contradictory comparisons", () => {
  const result = check("ArithBottom", `theorem probe (a : Nat)
  requires h : succ(a) < a
  shows ⊥
proof
  arith

theorem probe2 (a b : Nat)
  requires h1 : a < b
  requires h2 : b < a
  shows a = b
proof
  exfalso
  arith`, ["Grace.Cumulus.Nat"]);
  assert.equal(result.ok, true, result.message);
});

// `intros` and `intro` see through a defined predicate whose body is a
// universal or an implication, as Lean's `intro` unfolds a reducible head.
test("intros introduces through a predicate definition", () => {
  const result = check("IntroThrough", `theorem subset_of_subset (A B C : Set)
  requires h : A ⊆ B
  requires h2 : B ⊆ C
  shows A ⊆ C
proof
  intros y hy
  have inB := h with y, hy
  exact h2 with y, inB

theorem transitive_powerset (A : Set)
  requires h : Transitive(A)
  shows Transitive(𝒫(A))
proof
  intros S member T inT
  have sub := powerset.membership_iff.forward with member
  have inA := sub with T, inT
  have subA := h with T, inA
  exact powerset.membership_iff.backward with subA`, ["Grace.Cumulus.Set.Hierarchy", "Grace.Cumulus.Set.Core"]);
  assert.equal(result.ok, true, result.message);
});

// Ground reasoning stays fast when the context carries many facts about
// other terms: branching is confined to atoms connected to the goal, and a
// bounded universal is instantiated only where its membership atoms occur.
test("simp decides a membership goal amid unrelated facts", () => {
  const result = check("GroundCrowded", `theorem rest_subset (A S x : Set)
  requires subset : S ⊆ insert(x, A)
  requires member : S ∈ 𝒫(insert(x, A))
  requires reflexive : 𝒫(A) ⊆ 𝒫(A)
  requires present : x ∈ S
  requires restIn : S ∖ {x} ∈ 𝒫(A)
  requires extra : A ∪ S ⊆ insert(x, A ∪ S)
  requires extra2 : S ∩ A ∈ 𝒫(S)
  shows insert(x, S ∖ {x}) = S
proof
  ext y
  simp

theorem smaller (A S x : Set)
  requires subset : S ⊆ insert(x, A)
  requires member : S ∈ 𝒫(insert(x, A))
  requires extra : A ∪ S ⊆ insert(x, A ∪ S)
  requires absent : ¬(x ∈ S)
  shows S ⊆ A
proof
  intros y hy
  have inInsert := subset with y, hy
  simp`, ["Grace.Cumulus.Set.Finite", "Grace.Cumulus.Set.Core"]);
  assert.equal(result.ok, true, result.message);
});

// A derived predicate fact takes further arguments through its definition,
// and evidence in a binder's position instantiates the leading binders.
test("derived predicate facts apply through their definition in mixed lists", () => {
  const result = check("DerivedPredicate", `theorem element_of_element (y b z : Set)
  requires ordinal : Ordinal(y)
  requires hbInY : b ∈ y
  requires hzInB : z ∈ b
  shows z ∈ y
proof
  have transitive := Ordinal.transitive with ordinal
  exact transitive with hbInY, z, hzInB

theorem element_of_element2 (y b z : Set)
  requires ordinal : Ordinal(y)
  requires hbInY : b ∈ y
  requires hzInB : z ∈ b
  shows z ∈ y
proof
  have bSubset := Ordinal.transitive with ordinal, b, hbInY
  exact bSubset with z, hzInB`, ["Grace.Cumulus.Set.Hierarchy"]);
  assert.equal(result.ok, true, result.message);
});

// A postfix operator and a function alias parse and print as declared.
test("postfix and alias notation parse and print", () => {
  const result = check("Notations", `theorem fact_two
  shows 2! = 2
proof
  compute

theorem alias_zero (n : Nat)
  shows (n choose 0) = 1
proof
  exact choose.zero_right at n with *

theorem printed (n : Nat)
  shows (n + 1)! = (n + 1) * n!
proof
  exact factorial.succ at n with *

theorem word_infix (n : Nat)
  shows (2 * n + 1 choose n) * 2 = choose(2 * n + 1, n) * 2
proof
  rfl`, ["Grace.Cumulus.NumberTheory.Binomial"]);
  assert.equal(result.ok, true, result.message);
  const statements = Object.fromEntries(result.theorems.map(theorem => [theorem.name.split(".").at(-1), theorem.statement]));
  assert.equal(statements.fact_two, "2! = 2");
  assert.equal(statements.alias_zero, "∀ n : ℕ, n choose 0 = 1");
  assert.equal(statements.word_infix, "∀ n : ℕ, ((2 * n + 1) choose n) * 2 = ((2 * n + 1) choose n) * 2");
  assert.equal(statements.printed, "∀ n : ℕ, (n + 1)! = (n + 1) * n!");
});

// `ring [h₁, …]` rewrites with equations modulo the semiring axioms, after
// reducing the equations by one another; `arith` splits conjunctions and
// introduces disequalities; a refine hole at a conjunction with entries
// still to come stands for the first conjunct.
test("ring with rules, arith on conjunctions, and flattened refine holes", () => {
  const result = check("RingRules", `theorem cancel (x y c : Nat)
  requires step : x * (c + 1) = y * (2 * c + 2)
  requires expand : y = c + 1
  shows x * (c + 1) * (c + 1) = 2 * (c + 1) * (c + 1) * (c + 1)
proof
  ring [step, expand]

theorem indices (a : Nat)
  requires large : 2 ≤ a
  shows a ≠ a + 1 ∧ a + 1 ≠ 2 * a ∧ 2 * a ≠ 8 * a * a + 8 * a + 2
proof
  have squareNat : Nat(a * a) by typecheck
  arith

theorem beyond (N : Nat)
  shows ∃ a ∈ ℕ, N < a ∧ 2 ≤ a ∧ a = a
proof
  have witnessNat : Nat(N + 2) by typecheck
  have member := nat.omega.forward with witnessNat
  refine ⟨N + 2, member, ?_, ?_, rfl⟩
  . arith
  . arith`, ["Grace.Cumulus.Nat"]);
  assert.equal(result.ok, true, result.message);
  const indices = result.theorems.find(theorem => theorem.name.endsWith("indices"))!;
  assert.equal(indices.statement, "∀ a : ℕ, 2 ≤ a → a ≠ a + 1 ∧ a + 1 ≠ 2 * a ∧ 2 * a ≠ 8 * a * a + 8 * a + 2");
});

// An induction case written `| k + 1 =>` presents its goal with k + 1 and
// never shows succ; the proof is transported to the constructor form.
test("induction cases spelled k + 1", () => {
  const result = check("SuccessorSugar", `theorem double_add (n : Nat)
  shows n + n = 2 * n
proof
  induction n
  | zero => ring
  | k + 1 using ih => ring

theorem presented (n : Nat)
  shows n + n = 2 * n
proof
  induction n
  | zero => ring
  | k + 1 using ih =>
    have h : k + 1 + (k + 1) = 2 * (k + 1) by ring
    exact h`, ["Grace.Cumulus.Nat"]);
  assert.equal(result.ok, true, result.message);
  const presented = result.theorems.find(theorem => theorem.name.endsWith("presented"))!;
  const have = presented.steps.find(step => step.command.startsWith("have h"))!;
  const goal = have.after.goals[0]!;
  assert.equal(goal.goal, "k + 1 + (k + 1) = 2 * (k + 1)");
  assert.ok(goal.locals.some(local => local.name === "ih" && local.formula === "k + k = 2 * k"), JSON.stringify(goal.locals));
  assert.ok(!JSON.stringify(presented.steps).includes("succ"), "no succ in the presented states");
});

// A fact through a defined predicate closes a goal stated by its body and
// the other way round, in exact, refine, and application premises.
test("a definition bridges a predicate and its body", () => {
  const result = check("DefinitionBridge", `theorem forward (x : Set)
  requires h : Rational(x)
  shows x ∈ ℚ
proof
  exact h

theorem backward (x : Set)
  requires h : x ∈ ℚ
  shows Rational(x)
proof
  exact h

theorem components (x : Set)
  requires h : Rational(x)
  shows x ∈ ℚ ∧ Rational(x)
proof
  refine ⟨h, h⟩

theorem premise (x : Set)
  requires h : Rational(x)
  shows ∃ u ∈ x, u ∈ rationalRepresentatives
proof
  exact Rational.some_representative at x with h`, ["Grace.Cumulus.Rat.Defs"]);
  assert.equal(result.ok, true, result.message);
});

// Projections, cases, left, right, constructor, and witness work through a
// defined predicate whose body has the shape they need, with the
// definition's carrier guards supplied from the context.
test("structural tactics see through predicate definitions", () => {
  const result = check("ThroughDefinitions", `predicate Dominates (a b : Nat) := ∀ k ∈ ω, k ≤ b → k ≤ a
predicate Trichotomy (a b : Nat) := a < b ∨ (a = b ∨ b < a)
predicate Between (a b c : Nat) := a ≤ b ∧ b ≤ c
predicate Reaches (a b : Nat) := ∃ k ∈ ω, a + k = b

theorem project (a b c : Nat)
  requires h : Between(a, b, c)
  shows b ≤ c
proof
  exact h.right

theorem introduce (a : Nat)
  shows Dominates(a, a)
proof
  intros k hk hkb
  exact hkb

theorem split (a b : Nat)
  requires h : Trichotomy(a, b)
  shows Trichotomy(b, a)
proof
  cases h with lt | rest
  . right
    right
    exact lt
  . cases rest with eq | gt
    . right
      left
      rw eq
      rfl
    . left
      exact gt

theorem build (a : Nat)
  shows Between(a, a, a)
proof
  constructor
  . exact LessEqual.reflexive at a
  . exact LessEqual.reflexive at a

theorem reach (a : Nat)
  shows Reaches(a, a)
proof
  witness 0
  constructor
  . exact Naturals.constructor.zero
  . exact add.right_unit at a`, ["Grace.Cumulus.Nat.Order"]);
  assert.equal(result.ok, true, result.message);
});

// The carrier guard conjunct on a witness is routine: `witness k` on
// `∃ k, Nat(k) ∧ φ` leaves φ, and a guard between two at-list binders is
// discharged on the way.
test("witness and at lists skip carrier guards", () => {
  const result = check("WitnessGuards", `theorem zero_le (a : Nat)
  shows 0 ≤ a
proof
  witness a
  simp [add]

theorem add_le (a b c d : Nat)
  requires hab : a ≤ b
  requires hcd : c ≤ d
  shows a + c ≤ b + d
proof
  obtain ⟨k, hkNat, hkEq⟩ := hab
  obtain ⟨l, hlNat, hlEq⟩ := hcd
  witness k + l
  have shuffle := add.four_shuffle at a, c, k, l
  rw [shuffle, hkEq, hlEq]
  rfl`, ["Grace.Cumulus.Nat.Order"]);
  assert.equal(result.ok, true, result.message);
});

// by_contra names the negated goal, this by default, and asks for ⊥.
test("by_contra names the negated goal", () => {
  const result = check("ByContra", `theorem named (X Y : Set, x : Set)
  requires h : X ∖ Y = ∅
  requires hx : x ∈ X
  shows x ∈ Y
proof
  by_contra absent
  have member : x ∈ X ∖ Y by simp [hx, absent]
  rw h at member
  simpa using member

theorem unnamed (x A : Set)
  requires h : x ∈ A
  shows x ∈ A
proof
  by_contra
  exact this with h`, ["Grace.Cumulus.Set.Core"]);
  assert.equal(result.ok, true, result.message);
});

// Library equivalences whose one side is bare, such as `{x} ⊆ A ↔ x ∈ A`
// and `𝒫(A) ⊆ 𝒫(B) ↔ A ⊆ B`, must not slow routine typing: Nat(1) and a
// premise found through a predicate's own lemma still come at once.
test("general set equivalences do not disturb routine typing", () => {
  const result = check("TypingUnderSetAlgebra", `theorem one_nat
  shows Nat(1)
proof
  typecheck

theorem subset_bridge (x A : Set)
  requires h : {x} ⊆ A
  shows x ∈ A
proof
  exact singleton.subset_iff.forward with h`, ["Grace.Cumulus.Set.Powerset"]);
  assert.equal(result.ok, true, result.message);
});

// A have statement restates a fact through a definition in either
// direction: a relates fact as a pair membership and back.
test("have statements restate facts through definitions", () => {
  const result = check("HaveBridge", `theorem restate (r x y : Set)
  requires h : relates(r, x, y)
  shows (x, y) ∈ r
proof
  have member : (x, y) ∈ r := h
  exact member

theorem restate_back (r x y : Set)
  requires h : (x, y) ∈ r
  shows relates(r, x, y)
proof
  have related : relates(r, x, y) := h
  exact related`, ["Grace.Cumulus.Set.Relation"]);
  assert.equal(result.ok, true, result.message);
});

// A guard by a declared class, such as Ordinal(α), is routine like a
// carrier guard: an application discharges it from the context.
test("class guards in applications are routine", () => {
  const result = check("ClassGuards", `theorem successor_ordinal (α : Ordinal)
  shows next(α) ∈ Ordinal
proof
  exact Ordinal.next at α

theorem below_successor (α : Ordinal)
  shows α ∈ next(α)
proof
  have fact := next.contains at α
  exact fact`, ["Grace.Cumulus.Set.Ordinal"]);
  assert.equal(result.ok, true, result.message);
});

// A rfl pattern substitutes the eliminated variable everywhere, including
// inside quantifier bodies of the goal, as long as no capture occurs.
test("rfl patterns substitute under binders", () => {
  const result = check("RflUnderBinders", `theorem witness_transfer (A x u : Set)
  requires both : x = u ∧ u ∈ A
  requires covered : ∃ n ∈ A, u = n
  shows x ∈ A ∧ ∃ n ∈ A, x = n
proof
  obtain ⟨rfl, hu⟩ := both
  exact ⟨hu, covered⟩`, ["Grace.Cumulus.Set"]);
  assert.equal(result.ok, true, result.message);
});

// A carrier guard between supplied entries is discharged by soft typing or
// from the context, so a proof names only the mathematical premises.
test("carrier guards in applications are routine", () => {
  const result = check("RoutineGuards", `theorem product_zero (a b : Nat)
  requires h : (a + 1) * b = 0
  shows b = 0
proof
  have zeroCases := mul.eq_zero with h
  cases zeroCases with left | right
  . arith
  . exact right

theorem skip_guard (n : Nat)
  shows (n + n choose n) * (n! * n!) = (n + n)!
proof
  exact choose.factorial at n with n

theorem trailing_guard (n : Nat)
  shows (n + n choose n) * (n! * n!) = (n + n)!
proof
  have equation := choose.factorial at n, n
  exact equation`, ["Grace.Cumulus.NumberTheory.Binomial"]);
  assert.equal(result.ok, true, result.message);
});
