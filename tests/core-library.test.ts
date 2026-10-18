// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import {
  callNativeNat, compileProofModule, createZfgKernel, encodeProofMachineBinary,
  exportTheorem, loadModuleGraph, moduleReport, verifyProofMachineBinary,
} from "../src/index.ts";

const root = fileURLToPath(new URL("../lib", import.meta.url));
const core = fileURLToPath(new URL("../lib/Grace/Core.g17", import.meta.url));

test("loads the small bootstrapped computation core", () => {
  const kernel = createZfgKernel();
  const loaded = loadModuleGraph(kernel, [core], [root]);
  assert.deepEqual(loaded.map(item => item.module), [
    "Grace.Core.Nat", "Grace.Core.Nat.Algebra", "Grace.Core.Nat.Order", "Grace.Core.Data", "Grace.Core.List", "Grace.Core.Syntax",
    "Grace.Core",
  ]);
  assert.equal(callNativeNat(kernel, "Grace.Core.Nat.Rec.factorial", [5n]), 120n);
  assert.equal(callNativeNat(kernel, "Grace.Core.Nat.Rec.factorial", [20n]), 2_432_902_008_176_640_000n);
  assert.equal(exportTheorem(kernel, "Grace.Core.Nat.Rec.mul.six_seven").proof.nodes.length, 1);
  assert.equal(exportTheorem(kernel, "Grace.Core.Nat.Rec.factorial.five").proof.nodes.length, 1);
  assert.deepEqual(moduleReport(kernel).find(item => item.name === "Grace.Core")?.imports, [
    "Grace.Core.Nat.Order", "Grace.Core.List", "Grace.Core.Syntax",
  ]);
});

test("core computation proofs share one machine-checkable tape", () => {
  const kernel = createZfgKernel();
  const loaded = loadModuleGraph(kernel, [core], [root]);
  const names = loaded.flatMap(item => item.theorems);
  const tape = encodeProofMachineBinary(compileProofModule(names.map(name => exportTheorem(kernel, name))));
  const checked = verifyProofMachineBinary(kernel, tape);
  assert.equal(checked.theorems, names.length);
  assert.ok(checked.instructions > checked.theorems);
});
