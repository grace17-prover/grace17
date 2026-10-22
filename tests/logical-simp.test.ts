// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import {
  assume, createZfgKernel, eq, forall, formulaEquals, imp, not,
  simplifyFormulaGoal, v,
} from "../src/index.ts";

test("logical simp transports a residual negated goal through equality", () => {
  const kernel = createZfgKernel();
  const a = v("a"), b = v("b"), c = v("c");
  const equality = eq(a, b), original = not(eq(a, c)), residual = not(eq(b, c));
  const rewrite = simplifyFormulaGoal(kernel, original, {
    using: [assume(equality)], assumptions: [equality],
  });
  assert.ok(formulaEquals(rewrite.goal, residual));
  assert.ok(formulaEquals(kernel.checkProof(rewrite.lift(assume(residual)), [equality, residual]), original));
  assert.throws(() => kernel.checkProof(rewrite.lift(assume(residual)), [residual]));
});

test("conditional logical simp requires evidence and replays its discharge", () => {
  const kernel = createZfgKernel();
  const a = v("a"), b = v("b"), c = v("c"), d = v("d");
  const condition = eq(c, d), rule = imp(condition, eq(a, b));
  const original = not(eq(a, c)), residual = not(eq(b, c));
  assert.throws(() => simplifyFormulaGoal(kernel, original, {
    using: [assume(rule)], assumptions: [rule],
  }), /did not simplify/);
  const rewrite = simplifyFormulaGoal(kernel, original, {
    using: [assume(rule)], assumptions: [rule, condition], facts: [assume(condition)],
  });
  assert.ok(formulaEquals(rewrite.goal, residual));
  assert.ok(formulaEquals(kernel.checkProof(rewrite.lift(assume(residual)), [rule, condition, residual]), original));
  assert.throws(() => kernel.checkProof(rewrite.lift(assume(residual)), [rule, residual]));
});

test("logical simp does not cross quantifier scope or accept a no-op", () => {
  const kernel = createZfgKernel();
  const x = v("x"), y = v("y");
  const equality = eq(x, y);
  assert.throws(() => simplifyFormulaGoal(kernel, forall("x", not(eq(x, y))), {
    using: [assume(equality)], assumptions: [equality],
  }), /did not simplify/);
  assert.throws(() => simplifyFormulaGoal(kernel, not(equality), {
    using: [assume(eq(x, x))], assumptions: [eq(x, x)],
  }), /did not simplify/);
});

test("logical simp performs one productive step even with opposing rules", () => {
  const kernel = createZfgKernel();
  const x = v("x"), y = v("y"), z = v("z");
  const forward = eq(x, y), backward = eq(y, x);
  const rewrite = simplifyFormulaGoal(kernel, not(eq(x, z)), {
    using: [assume(forward), assume(backward)], assumptions: [forward, backward],
  });
  assert.ok(formulaEquals(rewrite.goal, not(eq(y, z))));
});

test("binder-independent simplification transports checked proofs without capture", async () => {
  const { exists, simplifyFormulaFact } = await import("../src/index.ts");
  const kernel = createZfgKernel();
  const a = v("a"), b = v("b"), x = v("x");
  const equality = eq(a, b);
  const source = exists("x", eq(x, a));
  const target = exists("x", eq(x, b));
  const options = { using: [assume(equality)], assumptions: [equality, source], underBinders: true };
  const simplified = simplifyFormulaFact(kernel, assume(source), options);
  assert.ok(formulaEquals(simplified.formula, target));
  assert.ok(formulaEquals(kernel.checkProof(simplified.proof, options.assumptions), target));
  assert.throws(() => kernel.checkProof(simplified.proof, [source]));
  // A rule mentioning the bound name rewrites under a renamed binder rather
  // than capturing: `a = x` turns `∃ x, x = a` into `∃ x_1, x_1 = x`, and the
  // transported proof checks.
  const renamed = simplifyFormulaGoal(kernel, source, {
    using: [assume(eq(a, x))], assumptions: [eq(a, x)], underBinders: true,
  });
  assert.equal(renamed.goal.tag, "exists");
  assert.notEqual((renamed.goal as { variable: string }).variable, "x");
  assert.ok(formulaEquals(renamed.goal, exists((renamed.goal as { variable: string }).variable, eq(v((renamed.goal as { variable: string }).variable), x))));
  assert.ok(formulaEquals(kernel.checkProof(renamed.lift(assume(renamed.goal)), [eq(a, x), renamed.goal]), source));
  // A rule whose left side is the bound name has nothing free to rewrite.
  assert.throws(() => simplifyFormulaGoal(kernel, source, {
    using: [assume(eq(x, b))], assumptions: [eq(x, b)], underBinders: true,
  }), /did not simplify/);
});
