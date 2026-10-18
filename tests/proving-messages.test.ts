// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Messages and syntax met while proving in a bundled-group section: a
// rewrite mismatch names its rule and target with the notation in scope, a
// named premise that fits no requirement shows both formulas, a fact named
// where a term is wanted says which entries are facts and which are terms,
// a stray line is quoted with the step kinds allowed, a rewrite list locates
// each rule, two notations sharing a token never share a spelling in one
// formula, a graph applied to a pair prints as the statement writes it, the
// naturals print as ℕ, propositions and terms continue on a more-indented
// line, an equivalence rewrites a subformula, a modifier letter is a postfix
// token, typecheck decides literal membership, a carrier binder may precede
// the requires clause that supplies it, (1 : G) is the unit, and a section
// hypothesis or variable continues on a more indented line.

import assert from "node:assert/strict";
import test from "node:test";
import { createZfKernel, loadModuleSourceGraph, SurfaceError } from "../src/index.ts";
import { rememberFailureDisplay, workbenchFailure } from "../src/workbench.ts";

const header = "module ProvingMessages\nimport Grace.Cumulus.Algebra.Group.Pow\nimport Grace.Cumulus.Nat.Pow\n";

const section = (body: string) => header + `
section S
variable (G : Set)
hypothesis group : Group(G)
${body}
end S
`;

function load(source: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "ProvingMessages.g17", source }], ["lib"]);
  return kernel;
}

/** The message and the displayed proof state at the failing step. */
function failure(source: string) {
  const kernel = createZfKernel();
  try {
    loadModuleSourceGraph(kernel, [{ file: "ProvingMessages.g17", source }], ["lib"]);
  } catch (error) {
    assert.ok(error instanceof SurfaceError, String(error));
    rememberFailureDisplay(error, kernel);
    const step = workbenchFailure(error).trace?.steps.at(-1);
    return { message: error.message, goal: step?.after.goals[0] };
  }
  assert.fail("the module should not check");
}

test("a rewrite mismatch prints the rule and the goal with the notation in scope", () => {
  const { message } = failure(section(`
theorem mismatch (x : G) (n : Nat)
  requires h : x ^ n = x
  shows x ^ n = x
proof
  rw [h, pow_zero]
`));
  assert.match(message, /rewrite rule pow_zero \(x \^ 0 = G\.one\) does not match the goal x = x/u);
});

test("a rewrite mismatch at a fact names the fact and its formula", () => {
  const { message } = failure(section(`
theorem mismatchAt (x : G) (n : Nat)
  requires h : ∀ y ∈ G.carrier, y ^ n = y ↔ y = y
  shows ∀ z ∈ G.carrier, z ^ n = z ∨ z = x
proof
  intros z hz
  rw h at hz
`));
  assert.match(message, /rewrite rule h \(y \^ n = y ↔ y = y\) does not match hz : z ∈ G$/u);
});

test("a named premise that fits no requirement shows both formulas", () => {
  const { message } = failure(section(`
theorem premise (x : G) (n : Nat)
  requires h : x = x
  shows x ^ (n + 1) = x * x ^ n
proof
  have step := pow_succ_left with h
  exact step
`));
  assert.match(message, /named premise h \(x = x\) matches no requirement; requirement 1 is x ∈ G\.carrier/u);
});

test("a fact where a binder wants a term lists the facts and the terms of the with list", () => {
  const { message } = failure(section(`
theorem mixed (x : G) (n : Nat)
  shows x ^ (n + 1) = x * x ^ n
proof
  exact pow_succ_left with group, x, n
`));
  assert.match(message, /group is a local fact, not a variable in scope/u);
  assert.match(message, /group \(1\) is a fact and x \(2\), n \(3\) are terms/u);
  assert.match(message, /pow_succ_left at x, n with group/u);
});

test("a stray line is quoted with the step kinds a theorem allows", () => {
  const { message } = failure(section(`
theorem stray (x : G)
  shows x ∈ G.carrier
proof
  foo bar
  assumption
`));
  assert.match(message, /unexpected line in theorem: `foo bar`; a theorem holds requires and shows clauses/u);
  assert.match(message, /tactic steps such as have, exact, apply, rw/u);
});

test("each rewrite of a list is located at its own rule", () => {
  const kernel = load(header + `
theorem chain (x y z : Set)
  requires h1 : x = y
  requires h2 : y = z
  shows x = z
proof
  rw [h1, h2]
`);
  const steps = kernel.theoremTacticTraces.get("ProvingMessages.chain")!.steps;
  assert.deepEqual(steps.map(step => step.command), ["rw h1", "rw h2"]);
  assert.ok(steps[0]!.columnStart! < steps[1]!.columnStart!);
  assert.equal(steps[1]!.columnStart! - steps[0]!.columnStart!, "rw [h1, ".length);
});

test("two power notations in one formula never share the spelling x ^ n", () => {
  const { goal } = failure(section(`
theorem powers (x : G) (m n : Nat)
  shows groupPow(G, x, n) = pow(m, n)
proof
  exact zz
`));
  assert.equal(goal!.goal, "x ^ n = pow(m, n)");
});

test("a graph applied to a pair prints as the two-argument application", () => {
  const { goal } = failure(header + `
def twice (f a : Set) : Set := call2(f, a, a)

theorem pairs (f a : Set)
  shows twice(f, a) = f(a, a)
proof
  unfold twice
  unfold call2
  exact zz
`);
  assert.equal(goal!.goal, "f(a, a) = f(a, a)");
});

test("the natural numbers print as ℕ in goals and facts", () => {
  const { goal } = failure(header + `
theorem naturals (A : Set)
  requires h : A ⊆ ℕ
  shows A ⊆ ω
proof
  exact zz
`);
  assert.equal(goal!.goal, "A ⊆ ℕ");
  assert.equal(goal!.locals.find(item => item.name === "h")!.formula, "A ⊆ ℕ");
});

test("a local proposition continues after ∈ on a more-indented line, then its block follows", () => {
  load(section(`
theorem continued (x : G)
  shows x ∈ G.carrier
proof
  have inside : x ∈
      G.carrier
    assumption
  exact inside
`));
});

test("a witness, an exact, and a have continue on a more-indented line", () => {
  load(section(`
theorem continuedTerms (x : G) (n : Nat)
  requires h : ∀ y ∈ G.carrier, y ^ (n + 1) = y * y ^ n
  shows ∃ y ∈ G.carrier, y ^ (n + 1) = y * y ^ n
proof
  have step := h with
    x, assumption
  witness
    x
  exact ⟨assumption,
    step⟩
`));
  load(section(`
theorem continuedOperator (x : G)
  shows x ∈ G.carrier ∧ x = x
proof
  have both : x ∈ G.carrier
    ∧ x = x
    exact ⟨assumption, rfl⟩
  exact both
`));
});

test("rw rewrites a subformula with an equivalence, at the goal, at a fact, and under a binder", () => {
  load(section(`
theorem atGoal (x : G) (n : Nat)
  requires h : x ^ n = x ↔ x = x
  shows x ^ n = x
proof
  rw h
  rfl

theorem atFact (x : G) (n : Nat)
  requires h : x ^ n = x ↔ x = x
  requires h2 : x ^ n = x ∧ x = x
  shows x = x ∧ x = x
proof
  rw h at h2
  exact h2

theorem conditional (x : G) (n : Nat)
  requires h : ∀ y ∈ G.carrier, y ^ n = y ↔ y = y
  shows ∀ z ∈ G.carrier, z ^ n = z ∨ z = x
proof
  intros z hz
  rw h
  left
  rfl

theorem underBinder (x : G) (n : Nat)
  requires h : x ^ n = x ↔ x = x
  shows ∀ z ∈ G.carrier, x ^ n = x
proof
  rw under h
  intros z hz
  rfl

theorem reversed (x : G) (n : Nat)
  requires h : x ^ n = x ↔ x = x
  shows x = x → x = x
proof
  rw ← h
  intro k
  exact k
`));
});

test("a modifier letter such as ᵀ is a postfix notation token", () => {
  load(header + `
def flip (M : Set) : Set := M
notation postfix 90 "ᵀ" => flip

theorem transpose (M : Set)
  shows Mᵀ = flip(M)
proof
  rfl
`);
});

test("typecheck decides m ∈ n for literal naturals", () => {
  load(header + `
theorem twoInFour
  shows 2 ∈ 4
proof
  typecheck
`);
  const { message } = failure(header + `
theorem fourInTwo
  shows 4 ∈ 2
proof
  typecheck
`);
  assert.match(message, /typecheck could not infer 4 ∈ 2/u);
});

test("a carrier binder may precede the requires clause that supplies its structure", () => {
  const kernel = load(header + `
theorem closed (G : Set) (g h : G)
  requires group : Group(G)
  shows g * h ∈ G.carrier
proof
  typecheck
`);
  assert.ok(kernel.theorems.has("ProvingMessages.closed"));
  const { message } = failure(header + `
theorem unsupplied (G : Set) (g : G)
  shows g = g
proof
  rfl
`);
  assert.match(message, /unknown soft type G; a binder \(g : G\) needs a hypothesis giving G a carrier, such as Group\(G\)/u);
});

test("(1 : G) under a group hypothesis is the unit G.one", () => {
  const { goal } = failure(section(`
theorem unit (g : G)
  shows g * (1 : G) = g
proof
  exact zz
`));
  assert.equal(goal!.goal, "g * G.one = g");
  load(section(`
theorem unitLaw (g : G)
  shows g * (1 : G) = g
proof
  exact mul_one with *
`));
});

test("a section hypothesis or variable continues on a more indented line", () => {
  load(header + `
section S
variable (G
  : Set)
hypothesis group :
  Group(G)
hypothesis twice : Group(G) ∧
  Group(G)

theorem useIt
  shows Group(G)
proof
  exact group

theorem useBoth
  shows Group(G) ∧ Group(G)
proof
  exact twice
end S
`);
});
