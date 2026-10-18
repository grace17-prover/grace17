// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { fromRationalCell, rational, reduceRationalMatrix, replayRationalRows, toRationalCell } from "../src/index.ts";

test("normalized rational cells preserve signed fraction values", () => {
  assert.deepEqual(fromRationalCell({ positive: 3n, negative: 7n, denominator: 6n }), rational(-2n, 3n));
  assert.deepEqual(toRationalCell(rational(-6n, 9n)),
    { positive: 0n, negative: 2n, denominator: 3n });
  assert.throws(() => fromRationalCell({ positive: 1n, negative: 0n, denominator: 0n }), /denominator/);
});

test("a three-variable system replays to the same exact reduced matrix", () => {
  const values = [[0, 1, 1, 5], [1, 1, 1, 6], [1, 2, 3, 14]].map(row => row.map(value => rational(BigInt(value))));
  const result = reduceRationalMatrix(values, 3);
  assert.equal(result.status, "unique");
  assert.deepEqual(result.rows, [[1, 0, 0, 1], [0, 1, 0, 2], [0, 0, 1, 3]].map(row =>
    row.map(value => rational(BigInt(value)))));
  assert.deepEqual(replayRationalRows(values, result.steps), result.rows);
  assert.ok(result.steps.some(step => step.kind === "swap"));
});

test("inconsistent and dependent exact systems report their distinct outcomes", () => {
  const input = (rows: number[][]) => rows.map(row => row.map(value => rational(BigInt(value))));
  assert.equal(reduceRationalMatrix(input([[1, 1, 2], [1, 1, 3]]), 2).status, "inconsistent");
  assert.equal(reduceRationalMatrix(input([[1, 1, 2], [2, 2, 4]]), 2).status, "underdetermined");
});

test("larger dense systems retain exact solutions and replayable row steps", () => {
  for (const n of [8, 16, 32]) {
    // Strict diagonal dominance makes this dense integer matrix nonsingular.
    const coefficients = Array.from({ length: n }, (_, i) =>
      Array.from({ length: n }, (_, j) => i === j ? n * 3 : (i + j) % 3 - 1));
    const expected = Array.from({ length: n }, (_, j) => BigInt(j + 1));
    const input = coefficients.map(row => [...row.map(value => rational(BigInt(value))),
      rational(row.reduce((sum, value, j) => sum + BigInt(value) * expected[j]!, 0n))]);
    const result = reduceRationalMatrix(input, n);
    assert.equal(result.status, "unique", `n=${n}`);
    assert.deepEqual(result.pivots, Array.from({ length: n }, (_, i) => i));
    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++) assert.deepEqual(result.rows[i]![j], rational(BigInt(i === j ? 1 : 0)));
      assert.deepEqual(result.rows[i]![n], rational(expected[i]!));
    }
    assert.deepEqual(replayRationalRows(input, result.steps), result.rows);
  }
});
