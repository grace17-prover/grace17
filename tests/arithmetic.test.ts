// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import {
  app, canonical, eq, formulaEquals, pred, settle, theorem, v,
} from "../src/index.ts";
import { buildArithmeticSuite } from "../examples/arithmetic-suite.ts";

test("checks commutativity, multiplication, and both distributive laws", () => {
  const { kernel, examples } = buildArithmeticSuite();
  for (const name of [
    "plus.commutative",
    "times.right_zero",
    "times.succ_right",
    "times.commutative",
    "times.distributes_right",
    "times.distributes_left",
    "times.distributes_three",
  ]) {
    const example = examples.find(item => item.name === name);
    assert.ok(example, `missing ${name}`);
    assert.equal(formulaEquals(kernel.checkProof(example.proof), example.statement), true);
  }
});

test("uses conditional commutativity safely as an ordered rewrite rule", () => {
  const { kernel } = buildArithmeticSuite();
  const natA = pred("Nat", v("a"));
  const natB = pred("Nat", v("b"));
  const goal = eq(app("plus", v("b"), v("a")), app("plus", v("a"), v("b")));
  const proof = settle(kernel, goal, {
    using: [theorem("plus.commutative")],
    assumptions: [natA, natB],
  });
  assert.equal(formulaEquals(kernel.checkProof(proof, [natA, natB]), goal), true);
  assert.throws(() => settle(kernel, goal, {
    using: [theorem("plus.commutative")],
  }), /did not close/);
});

test("efficiently computes a multiplication term with a checked proof", () => {
  const { kernel } = buildArithmeticSuite();
  const numeral = (value: number) => {
    let result = app("zero");
    for (let index = 0; index < value; index += 1) result = app("succ", result);
    return result;
  };
  const expression = app("times", numeral(7), numeral(8));
  const result = kernel.evaluateCertified(expression, 100_000);
  assert.equal(canonical(result.value), canonical(numeral(56)));
  assert.equal(formulaEquals(kernel.checkProof(result.proof), eq(expression, numeral(56))), true);
});
