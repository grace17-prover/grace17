// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import { spawnSync } from "node:child_process";
import { createZfgKernel, loadModuleGraph, moduleReport } from "../src/index.ts";

const root = fileURLToPath(new URL("../lib", import.meta.url));
const entry = fileURLToPath(new URL("../examples/Compute.g17", import.meta.url));

test("automatically resolves and topologically loads transitive module imports", () => {
  const kernel = createZfgKernel();
  const loaded = loadModuleGraph(kernel, [entry], [root]);
  assert.deepEqual(loaded.map(item => item.module), ["Grace.Core.Nat", "Grace.Examples.Compute"]);
  assert.deepEqual(moduleReport(kernel).map(item => item.name), ["Grace.Core.Nat", "Grace.Examples.Compute"]);
  assert.equal(kernel.theorems.has("Grace.Examples.Compute.Demo.imported_add"), true);
});

test("CLI loads imports automatically and runs a qualified function on native naturals", () => {
  const project = fileURLToPath(new URL("..", import.meta.url));
  const run = spawnSync(process.execPath, [
    "bin/g17.ts", "run", "--json", "--module-root", "lib",
    "examples/Compute.g17",
    "--function", "Grace.Examples.Compute.Demo.double", "--args", "100000",
  ], { cwd: project, encoding: "utf8" });
  assert.equal(run.status, 0, run.stderr);
  const result = JSON.parse(run.stdout);
  assert.equal(result.value, "200000");
  assert.equal(result.stats.reductions, 100001);
});
