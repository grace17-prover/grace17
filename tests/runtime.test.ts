// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import {
  app, callNative, callNativeNat, canonical, createZfgKernel, elaborateModule, evaluateNative, evaluateNativeNat,
  loadModuleGraph, type Term,
} from "../src/index.ts";

const numeral = (value: number): Term => {
  let result = app("zero");
  for (let index = 0; index < value; index += 1) result = app("succ", result);
  return result;
};

test("native bigint execution agrees with the general recursive evaluator", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, readFileSync(fileURLToPath(new URL("../examples/Arithmetic.g17", import.meta.url)), "utf8"));
  const term = app("times", numeral(40), numeral(25));
  assert.equal(evaluateNativeNat(kernel, term), 1_000n);
  assert.equal(canonical(kernel.evaluateFast(term)), canonical(numeral(1_000)));
});

test("native execution reports reductions and preserves uninterpreted set applications", () => {
  const kernel = createZfgKernel();
  const result = evaluateNative(kernel, app("pair", app("zero"), app("succ", app("zero"))));
  assert.deepEqual(result.value, { tag: "app", fn: "pair", args: [0n, 1n] });
  assert.equal(result.stats.calls, 4);
});

test("direct native calls execute large primitive recursions without a unary input tree", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, readFileSync(fileURLToPath(new URL("../examples/CoreNat.g17", import.meta.url)), "utf8"));
  elaborateModule(kernel, readFileSync(fileURLToPath(new URL("../examples/ModuleCompute.g17", import.meta.url)), "utf8"));
  assert.equal(callNativeNat(kernel, "Grace.Examples.Compute.Demo.double", [20_000n]), 40_000n);
});

test("native arithmetic specializations remain fuel bounded", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `
define plus (x y : Nat) -> Nat
  | zero, y => y
  | succ(x), y => succ(plus(x, y))
define times (x y : Nat) -> Nat
  | zero, y => zero
  | succ(x), y => plus(y, times(x, y))
define factorial (n : Nat) -> Nat
  | zero => 1
  | succ(n) => times(succ(n), factorial(n))
`);
  assert.throws(() => callNativeNat(kernel, "factorial", [1_000n], 10), /fuel/);
});

test("admitted natural decisions use BigInt and reject altered helper equations", () => {
  const kernel = createZfgKernel();
  loadModuleGraph(kernel, [fileURLToPath(new URL("../lib/Grace/Cumulus/Rat/Computable.g17", import.meta.url))],
    [fileURLToPath(new URL("../lib", import.meta.url))]);
  const prefix = "Grace.Cumulus.Rat.Computable.RationalCellOps.";
  const equal = callNative(kernel, "Grace.Cumulus.Nat.Mod.equalNat", [10n ** 60n, 10n ** 60n], 100);
  assert.deepEqual(equal.value, { tag: "app", fn: "Grace.Core.Data.Bool.true", args: [] });
  assert.equal(equal.stats.reductions, 1);
  assert.equal(callNativeNat(kernel, prefix + "minus", [10n ** 60n, 10n ** 60n - 7n], 100), 7n);
  assert.deepEqual(callNative(kernel, prefix + "less", [10n ** 60n - 1n, 10n ** 60n], 100).value,
    { tag: "app", fn: "Grace.Core.Data.Bool.true", args: [] });

  const helper = "Grace.Cumulus.Nat.Mod.isZero";
  const record = kernel.recursiveFunctions.get(helper)!;
  const changed = { ...record, equations: record.equations.map((item, index) => index === 0
    ? { ...item, body: app("Grace.Core.Data.Bool.false") } : item) };
  kernel.recursiveFunctions.set(helper, changed);
  const fallback = callNative(kernel, prefix + "less", [0n, 3n], 100);
  assert.deepEqual(fallback.value, { tag: "app", fn: "Grace.Core.Data.Bool.true", args: [] });
  assert.ok(fallback.stats.reductions > 1, "modified helper must disable the native shortcut");
});


test("changing-argument recursion reuses exact prefixes within one fresh evaluation", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `
def advance (n a : Nat) -> Nat
  | zero, a => a
  | succ(n), a => advance(n, succ(a))
`);
  const result = callNative(kernel, "advance", [120n, 3n], 100_000);
  assert.equal(result.value, 123n);
  assert.deepEqual(result.definitions, ["advance"]);
  assert.ok(result.stats.calls < 100_000);
  assert.equal(callNativeNat(kernel, "advance", [120n, 7n], 100_000), 127n);
  const mixed = evaluateNative(kernel, app("pair",
    app("advance", numeral(120), numeral(3)),
    app("advance", numeral(60), numeral(3))), 100_000);
  assert.deepEqual(mixed.value, { tag: "app", fn: "pair", args: [123n, 63n] });
  assert.deepEqual(mixed.definitions, ["advance"]);
  assert.throws(() => callNativeNat(kernel, "advance", [120n, 3n], 10), /fuel/);
});
