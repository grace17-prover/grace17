// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { and, iff, pred, app, assume, createSimpSession, createZfgKernel, elaborateModule, eq, forall, formulaEquals, imp, not, or,
  refl, simplifyEqualityGoal, simplifyFormulaGoal, v, type ReliefTrace } from "../src/index.ts";

const a = v("a"), b = v("b"), c = v("c"), d = v("d"), e = v("e"), f = v("f");

test("recursive relief is opt-in; depth zero retains direct contextual discharge", () => {
  const kernel = createZfgKernel();
  const p = eq(c, d), q = eq(e, f), guard = imp(p, eq(a, b)), step = imp(q, p);
  const options = { using: [assume(guard), assume(step)], assumptions: [guard, step, q], useContextEqualities: false };
  // Logical residuals avoid treating a=b itself as an ambient rewrite.
  const goal = not(eq(a, v("z")));
  assert.throws(() => simplifyFormulaGoal(kernel, goal, options), /did not simplify/);
  assert.throws(() => simplifyFormulaGoal(kernel, goal, { ...options, backchain: { depth: 0, work: 100 } }), /did not simplify/);
  const result = simplifyFormulaGoal(kernel, goal, { ...options, backchain: { depth: 1, work: 20 } });
  assert.ok(formulaEquals(result.goal, not(eq(b, v("z")))));
  assert.ok(formulaEquals(kernel.checkProof(result.lift(assume(result.goal)), [...options.assumptions, result.goal]), goal));
  const direct = simplifyFormulaGoal(kernel, goal, { ...options, assumptions: [guard, p], using: [assume(guard)], backchain: { depth: 0, work: 0 } });
  assert.ok(formulaEquals(direct.goal, result.goal));
});

test("all hypotheses and retries consume one shared request budget", () => {
  const kernel = createZfgKernel();
  const p = eq(c, d), q = eq(e, f), seed = eq(c, e);
  const guard = imp(p, imp(q, eq(a, b))), rp = imp(seed, p), rq = imp(seed, q);
  const events: ReliefTrace[] = [];
  const options = createSimpSession({ using: [assume(rp), assume(rq), assume(guard)], assumptions: [rp, rq, guard, seed],
    backchain: { depth: 2, work: 3, trace: event => events.push(event) } });
  assert.throws(() => simplifyFormulaGoal(kernel, not(eq(a, v("z"))), options), /did not simplify/);
  assert.throws(() => simplifyFormulaGoal(kernel, not(eq(a, v("z"))), options), /did not simplify/);
  assert.ok(events.some(event => event.result === "work"));
  assert.ok(events.every((event, i) => i === 0 || event.remaining <= events[i - 1]!.remaining));
  assert.ok(events.every(event => event.remaining >= 0));
});

test("cyclic and growing hypothesis chains stop without a proof", () => {
  const kernel = createZfgKernel();
  const p = eq(c, d), q = eq(e, f), guard = imp(p, eq(a, b));
  const rp = imp(q, p), rq = imp(p, q), events: ReliefTrace[] = [];
  assert.throws(() => simplifyFormulaGoal(kernel, not(eq(a, v("z"))), {
    using: [assume(guard), assume(rp), assume(rq)], assumptions: [guard, rp, rq],
    backchain: { depth: 10, work: 100, trace: event => events.push(event) },
  }));
  assert.ok(events.some(event => event.result === "cycle"));
  const x = v("x"), grow = forall("x", imp(eq(app("succ", x), d), eq(x, d)));
  const growingEvents: ReliefTrace[] = [];
  assert.throws(() => simplifyFormulaGoal(kernel, not(eq(a, v("z"))), {
    using: [assume(guard), assume(grow)], assumptions: [guard, grow],
    backchain: { depth: 3, work: 100, trace: event => growingEvents.push(event) },
  }));
  assert.ok(growingEvents.some(event => event.result === "depth"));
});

test("clause-local sibling negations are discharged in kernel proof transport", () => {
  const kernel = createZfgKernel();
  const p = eq(c, d), q = eq(e, f), rule = imp(not(p), imp(not(q), eq(a, b)));
  const goal = or(p, or(eq(a, b), q));
  const result = simplifyFormulaGoal(kernel, goal, { using: [assume(rule)], assumptions: [rule] });
  assert.ok(formulaEquals(result.goal, or(p, or(eq(b, b), q))));
  const proof = result.lift(assume(result.goal));
  assert.ok(formulaEquals(kernel.checkProof(proof, [rule, result.goal]), goal));
  assert.throws(() => kernel.checkProof(proof, [result.goal]));
  // The same conditional equality remains unavailable outside that clause.
  assert.throws(() => simplifyFormulaGoal(kernel, not(eq(a, v("z"))), { using: [assume(rule)], assumptions: [rule] }));
});

test("relief never guesses unproved rule hypotheses or splits disjunctive facts", () => {
  const kernel = createZfgKernel();
  const p = eq(c, d), q = eq(e, f), rule = imp(p, imp(q, eq(a, b)));
  assert.throws(() => simplifyFormulaGoal(kernel, not(eq(a, v("z"))), {
    using: [assume(rule)], assumptions: [rule, or(p, q)], backchain: { depth: 4, work: 100 },
  }));
});

test("normalization uses opt-in relief and validates its bounds", () => {
  const kernel = createZfgKernel();
  const p = eq(c, d), q = eq(e, f), rule = imp(p, eq(app("succ", a), b)), step = imp(q, p);
  const options = { using: [assume(rule), assume(step)], assumptions: [rule, step, q] };
  const goal = eq(app("succ", a), b);
  assert.ok(formulaEquals(simplifyEqualityGoal(kernel, goal, options).goal, goal));
  const result = simplifyEqualityGoal(kernel, goal, { ...options, backchain: { depth: 1, work: 20 } });
  assert.ok(formulaEquals(kernel.checkProof(result.lift(refl(b)), options.assumptions), goal));
  assert.throws(() => simplifyEqualityGoal(kernel, goal, { ...options, backchain: { depth: -1, work: 20 } }), /nonnegative/);
});

test("per-hypothesis caps only tighten the global depth", () => {
  const kernel = createZfgKernel();
  const p = eq(c, d), q = eq(e, f), seed = eq(c, e);
  const outer = imp(p, eq(a, b)), first = imp(q, p), second = imp(seed, q);
  const firstProof = assume(first);
  const options = { using: [assume(outer), firstProof, assume(second)], assumptions: [outer, first, second, seed] };
  const goal = not(eq(a, v("z")));
  assert.throws(() => simplifyFormulaGoal(kernel, goal, { ...options,
    backchain: { depth: 4, work: 100, hypothesisDepths: new Map([[firstProof, [0]]]) },
  }));
  assert.doesNotThrow(() => simplifyFormulaGoal(kernel, goal, { ...options,
    backchain: { depth: 4, work: 100, hypothesisDepths: new Map([[firstProof, [1]]]) },
  }));
  assert.throws(() => simplifyFormulaGoal(kernel, goal, { ...options,
    backchain: { depth: 1, work: 100, hypothesisDepths: new Map([[firstProof, [20]]]) },
  }));
});

test("negative conclusions are goals, not extra rule hypotheses", () => {
  const kernel = createZfgKernel();
  const p = eq(c, d), seed = eq(e, f), outer = imp(not(p), eq(a, b)), derive = imp(seed, not(p));
  const result = simplifyFormulaGoal(kernel, not(eq(a, v("z"))), {
    using: [assume(outer), assume(derive)], assumptions: [outer, derive, seed], backchain: { depth: 1, work: 30 },
  });
  assert.ok(formulaEquals(result.goal, not(eq(b, v("z")))));
});


test("surface simp requires explicit backchain bounds", () => {
  const source = (tactic: string) => `
    theorem controlled (a b c d e f : Set)
      requires rewrite : c = d → succ(a) = b
      requires derive : e = f → c = d
      requires seed : e = f
      shows succ(a) = b
    proof
      ${tactic} [rewrite, derive]
  `;
  assert.throws(() => elaborateModule(createZfgKernel(), source("simp")));
  const kernel = createZfgKernel();
  elaborateModule(kernel, source("simp (backchain := 1, work := 64)"));
  assert.ok(kernel.theorems.has("controlled"));
});


test("bounded relief works in simp at and simpa using", () => {
  for (const tactic of [
    "simp (backchain := 1, work := 64) [rewrite, derive] at h\n      exact h",
    "simpa (backchain := 1, work := 64) [rewrite, derive] using h",
  ]) {
    const kernel = createZfgKernel();
    elaborateModule(kernel, `
    theorem controlledFact (a b c d e f z : Set)
      requires rewrite : c = d → succ(a) = b
      requires derive : e = f → c = d
      requires seed : e = f
      requires h : succ(a) ≠ z
      shows b ≠ z
    proof
      ${tactic}
    `);
    assert.ok(kernel.theorems.has("controlledFact"));
  }
});

test("bounded relief binds hidden rule variables from contextual facts and projects conjunctions", () => {
  const source = (limits: string, membership = "requires member : x ∈ bag") => `
    theorem contextual (x bag y : Set)
      ${membership}
      requires classify : ∀ a, ∀ box, a ∈ box → a = a ∧ a ∈ succ(0)
      requires rewrite : x ∈ succ(0) → succ(x) = y
      shows succ(x) = y
    proof
      simp ${limits} [rewrite, classify]
  `;
  assert.throws(() => elaborateModule(createZfgKernel(), source("")));
  assert.throws(() => elaborateModule(createZfgKernel(), source("(backchain := 0, work := 100)")));
  assert.throws(() => elaborateModule(createZfgKernel(), source("(backchain := 1, work := 0)")));
  assert.throws(() => elaborateModule(createZfgKernel(), source("(backchain := 1, work := 100)", "")));
  const kernel = createZfgKernel();
  elaborateModule(kernel, source("(backchain := 1, work := 100)"));
  assert.ok(kernel.theorems.has("contextual"));
});

test("contextual bindings preserve shared variables and require every remaining premise", () => {
  const source = (evidence: string) => `
    theorem consistent (x first second y : Set)
      requires firstMember : x ∈ first
      requires secondMember : x ∈ second
      ${evidence}
      requires classify : ∀ a, ∀ box, a ∈ box → box = y → a ∈ succ(0)
      requires rewrite : x ∈ succ(0) → succ(x) = y
      shows succ(x) = y
    proof
      simp (backchain := 1, work := 200) [rewrite, classify]
  `;
  assert.throws(() => elaborateModule(createZfgKernel(), source("")));
  assert.throws(() => elaborateModule(createZfgKernel(), source("requires unrelated : x = y")));
  const kernel = createZfgKernel();
  // The first contextual match cannot relieve its other premise; retry the second.
  elaborateModule(kernel, source("requires valid : second = y"));
  assert.ok(kernel.theorems.has("consistent"));
});

test("equivalence relief uses checked directions and does not export contextual assumptions", () => {
  const x = v("x"), box = v("box");
  const member = pred("in", a, b), target = pred("in", a, c);
  const classify = forall("x", forall("box", iff(pred("in", x, box), and(eq(x, x), pred("in", x, c)))));
  const rewrite = imp(target, eq(app("succ", a), d));
  const assumptions = [member, classify, rewrite];
  const goal = eq(app("succ", a), d);
  const options = { using: [assume(rewrite), assume(classify)], assumptions, backchain: { depth: 1, work: 100 } };
  const result = simplifyEqualityGoal(createZfgKernel(), goal, options);
  const proof = result.lift(refl(d));
  const kernel = createZfgKernel();
  assert.ok(formulaEquals(kernel.checkProof(proof, assumptions), goal));
  assert.throws(() => kernel.checkProof(proof, [classify, rewrite]));
  const backward = iff(target, member);
  const reversed = simplifyEqualityGoal(kernel, goal, { ...options, using: [assume(rewrite), assume(backward)], assumptions: [member, rewrite, backward] });
  assert.ok(formulaEquals(kernel.checkProof(reversed.lift(refl(d)), [member, rewrite, backward]), goal));
});
