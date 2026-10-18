#!/usr/bin/env node
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Measure exact ground elimination separately from module loading and proof replay.
import { performance } from "node:perf_hooks";
import { fileURLToPath } from "node:url";
import { callNative, createZfgKernel, loadModuleGraph, type NativeValue } from "../src/index.ts";

const root = fileURLToPath(new URL("../lib", import.meta.url));
const entry = fileURLToPath(new URL("../lib/Grace/Cumulus/LinearAlgebra/Elimination.g17", import.meta.url));
const kernel = createZfgKernel();
const loading = performance.now();
loadModuleGraph(kernel, [entry], [root]);
console.log(`module load ${(performance.now() - loading).toFixed(1)} ms`);

const node = (fn: string, ...args: NativeValue[]): NativeValue => ({ tag: "app", fn, args });
const list = (items: readonly NativeValue[]): NativeValue =>
  items.reduceRight<NativeValue>((tail, head) => node("Grace.Core.Data.List.cons", head, tail),
    node("Grace.Core.Data.List.nil"));
const cell = (n: number): NativeValue => node("Grace.Cumulus.Rat.Computable.RationalCell.fraction",
  BigInt(n), 0n, 1n);

for (const n of (process.argv.length > 2 ? process.argv.slice(2).map(Number) : [2, 3, 4, 5])) {
  const rows = list(Array.from({ length: n }, (_, i) =>
    list([...Array.from({ length: n }, (_, j) => cell(i === j ? 2 : 1)), cell(n + 1)])));
  const started = performance.now();
  const result = callNative(kernel,
    "Grace.Cumulus.LinearAlgebra.Elimination.RationalMatrixOps.reducedEchelonChecked",
    [BigInt(n), rows], 100_000_000);
  const elapsed = performance.now() - started;
  const bitLengths = (value: NativeValue): number[] => typeof value === "bigint"
    ? [value.toString(2).length] : value.args.flatMap(bitLengths);
  const bits = bitLengths(result.value);
  console.log(JSON.stringify({ n, milliseconds: +elapsed.toFixed(1), ...result.stats,
    maxBits: Math.max(...bits), result: typeof result.value === "bigint" ? String(result.value) : result.value.fn }));
}
