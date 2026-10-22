// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import {
  app, assume, bottom, createZfgKernel, eq, formulaEquals, iff, imp, not, or, pred,
  proveCongruence, proveTautology, v, type Formula,
} from "../src/index.ts";
import { nat } from "../src/ast.ts";
import { proveLiteralDisequality } from "../src/type-system.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

test("tauto proves classical propositional consequences with checked proofs", () => {
  const kernel = createZfgKernel();
  kernel.declarePredicate("P", 0);
  kernel.declarePredicate("Q", 0);
  const p = pred("P");
  const q = pred("Q");
  const goals = [
    or(p, not(p)),
    imp(imp(imp(p, q), p), p),
    iff(imp(p, q), imp(not(q), not(p))),
    imp(imp(p, bottom), not(p)),
  ];
  for (const goal of goals) {
    const proof = proveTautology(kernel, goal);
    assert.equal(formulaEquals(kernel.checkProof(proof), goal), true);
  }
  assert.throws(() => proveTautology(kernel, p), /tauto found a counterexample/);
});

test("tauto prunes irrelevant propositional assumptions", { timeout: 5_000 }, () => {
  const kernel = createZfgKernel();
  kernel.declarePredicate("Target", 0);
  const target = pred("Target");
  const assumptions: Formula[] = [];
  for (let index = 0; index < 1_000; index += 1) {
    const name = `Noise${index}`;
    kernel.declarePredicate(name, 0);
    assumptions.push(pred(name));
  }
  const goal = or(target, not(target));
  const proof = proveTautology(kernel, goal, assumptions);
  assert.equal(formulaEquals(kernel.checkProof(proof, assumptions), goal), true);
});

test("cc closes transitive and nested functional equalities", () => {
  const kernel = createZfgKernel();
  kernel.declareFunction("f", 1);
  kernel.declareFunction("g", 2);
  const x = v("x");
  const y = v("y");
  const z = v("z");
  const assumptions = [eq(x, y), eq(y, z)];
  const goal = eq(app("g", app("f", x), x), app("g", app("f", z), z));
  const proof = proveCongruence(kernel, goal, assumptions);
  assert.equal(formulaEquals(kernel.checkProof(proof, assumptions), goal), true);
});

test("cc transports predicates and detects congruent contradictions", () => {
  const kernel = createZfgKernel();
  kernel.declareFunction("f", 1);
  kernel.declarePredicate("P", 1);
  kernel.declarePredicate("Q", 0);
  const x = v("x");
  const y = v("y");
  const equality = eq(x, y);
  const px = pred("P", app("f", x));
  const py = pred("P", app("f", y));
  const transported = proveCongruence(kernel, py, [equality, px]);
  assert.equal(formulaEquals(kernel.checkProof(transported, [equality, px]), py), true);

  const contradictionContext = [equality, px, not(py)];
  const arbitrary = pred("Q");
  const contradiction = proveCongruence(kernel, arbitrary, contradictionContext);
  assert.equal(formulaEquals(kernel.checkProof(contradiction, contradictionContext), arbitrary), true);
  assert.throws(() => proveCongruence(kernel, eq(x, y)), /cc found no congruence/);
});

test("cc scales across a long equality chain", { timeout: 5_000 }, () => {
  const kernel = createZfgKernel();
  kernel.declareFunction("f", 1);
  const terms = Array.from({ length: 251 }, (_, index) => v(`x${index}`));
  const assumptions = terms.slice(0, -1).map((term, index) => eq(term, terms[index + 1]!));
  const goal = eq(app("f", terms[0]!), app("f", terms.at(-1)!));
  const proof = proveCongruence(kernel, goal, assumptions, assumptions.map(assume));
  assert.equal(formulaEquals(kernel.checkProof(proof, assumptions), goal), true);
});

test("cc saturates deeply nested applications bottom-up", { timeout: 5_000 }, () => {
  const kernel = createZfgKernel();
  kernel.declareFunction("f", 1);
  const x = v("x");
  const y = v("y");
  let left = x;
  let right = y;
  for (let index = 0; index < 200; index += 1) {
    left = app("f", left);
    right = app("f", right);
  }
  const assumption = eq(x, y);
  const goal = eq(left, right);
  const proof = proveCongruence(kernel, goal, [assumption]);
  assert.equal(formulaEquals(kernel.checkProof(proof, [assumption]), goal), true);
});

test("distinct natural literals are distinct from the zero and successor laws alone", () => {
  const kernel = createZfgKernel();
  for (const [left, right] of [[1n, 0n], [0n, 1n], [3n, 7n], [7n, 3n], [2n, 5n]] as const) {
    const proof = proveLiteralDisequality(kernel, nat(left), nat(right));
    assert.ok(proof, `${left} ≠ ${right}`);
    assert.equal(formulaEquals(kernel.checkProof(proof), not(eq(nat(left), nat(right)))), true);
  }
  assert.equal(proveLiteralDisequality(kernel, nat(4n), nat(4n)), undefined);
  assert.equal(proveLiteralDisequality(kernel, v("x"), nat(4n)), undefined);
  // The successor form of a literal is the literal.
  const successor = proveLiteralDisequality(kernel, app("succ", nat(0n)), nat(0n));
  assert.ok(successor);
  assert.equal(formulaEquals(kernel.checkProof(successor), not(eq(nat(1n), nat(0n)))), true);
});

test("settle, typecheck, and arith close literal disequalities in a module importing only the core", () => {
  const source = `module Literals

theorem one.settle
  shows 1 ≠ 0
proof
  settle

theorem one.typecheck
  shows 1 ≠ 0
proof
  typecheck

theorem one.arith
  shows 1 ≠ 0
proof
  arith

theorem three.seven
  shows 3 ≠ 7
proof
  typecheck

theorem seven.three
  shows 7 ≠ 3
proof
  settle

theorem two.five
  shows ¬(2 = 5)
proof
  arith

theorem refute (x : Set)
  requires h : 4 = 9
  shows x = x ∪ x
proof
  settle
`;
  const result = checkWorkbenchFiles([{ name: "Literals.g17", source }], "ZFG");
  assert.equal(result.ok, true);
  assert.equal(result.theorems.length, 7);
  assert.deepEqual(result.theorems.flatMap(theorem => theorem.sorries), []);
});
