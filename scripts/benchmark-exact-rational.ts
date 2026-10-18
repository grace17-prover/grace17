#!/usr/bin/env node
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { performance } from "node:perf_hooks";
import { rational, reduceRationalMatrix } from "../src/rational-matrix.ts";

for (const n of (process.argv.length > 2 ? process.argv.slice(2).map(Number) : [8, 16, 32, 64, 128])) {
  const input = Array.from({ length: n }, (_, i) =>
    [...Array.from({ length: n }, (_, j) => rational(BigInt(i === j ? 2 : 1))), rational(BigInt(n + 1))]);
  const started = performance.now();
  const reduction = reduceRationalMatrix(input, n);
  const milliseconds = performance.now() - started;
  if (reduction.status !== "unique" || reduction.rows.some((row, i) =>
    row[n]?.numerator !== 1n || row[n]?.denominator !== 1n ||
    row.some((value, j) => j < n && (value.numerator !== BigInt(i === j ? 1 : 0) || value.denominator !== 1n))))
    throw new Error(`incorrect reduced form at dimension ${n}`);
  console.log(JSON.stringify({ n, milliseconds: +milliseconds.toFixed(1), steps: reduction.steps.length }));
}
