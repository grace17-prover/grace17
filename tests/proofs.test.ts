// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { app, definition, eq, formulaEquals, settle } from "../src/index.ts";
import { buildProofSuite } from "../examples/proof-suite.ts";

test("checks the arithmetic, induction, and function-graph proof suite", () => {
  const { kernel, examples } = buildProofSuite();
  assert.deepEqual(examples.map(example => example.name), [
    "plus.right_unit",
    "plus.associative",
    "Doubleton.computes",
  ]);
  for (const example of examples) {
    assert.equal(formulaEquals(kernel.checkProof(example.proof), example.statement), true);
    assert.equal(formulaEquals(kernel.theorems.get(example.name)!, example.statement), true);
  }
});

test("rechecks representative proofs repeatedly", () => {
  const { kernel, examples } = buildProofSuite();
  for (let repetition = 0; repetition < 100; repetition += 1) {
    for (const example of examples) kernel.checkProof(example.proof);
  }
});

test("settle refuses an equality its rules cannot establish", () => {
  const { kernel } = buildProofSuite();
  assert.throws(() => settle(kernel, eq(app("zero"), app("succ", app("zero"))), {
    using: [definition("plus", "equation.0")],
  }), /did not close/);
});
