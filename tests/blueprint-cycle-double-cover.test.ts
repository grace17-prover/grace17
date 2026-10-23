// The cycle double cover blueprint keeps elaborating as the library grows:
// every statement parses and checks, and only admissions stand in for proofs.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore
import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";

test("the cycle double cover blueprint checks with admissions only", () => {
  const run = spawnSync("node", ["--disable-warning=ExperimentalWarning", "bin/g17.ts", "check", "--json", "--continue", "--quiet",
    "--module-root", "blueprints", "--module-root", "lib",
    "blueprints/CycleDoubleCover/DoubleCover/Theorem.g17", "blueprints/CycleDoubleCover/TreePacking/Corollaries.g17"],
  { encoding: "utf8", maxBuffer: 1 << 28 });
  const report = JSON.parse(run.stdout) as {
    checked: { file: string; module: string; theorems: string[]; sorries: { theorem: string }[] }[];
    failed?: { file: string; error: string }[];
  };
  assert.deepEqual(report.failed ?? [], []);
  const blueprint = report.checked.filter(item => item.module.startsWith("CycleDoubleCover."));
  assert.equal(blueprint.length, 17, "every blueprint module is reached from the theorem and the corollaries");
  const theorems = blueprint.reduce((count, item) => count + item.theorems.length, 0);
  assert.ok(theorems >= 100, `the blueprint states ${theorems} theorems`);
  const main = blueprint.find(item => item.module === "CycleDoubleCover.DoubleCover.Theorem");
  assert.ok(main?.theorems.includes("CycleDoubleCover.DoubleCover.Theorem.cycleDoubleCover"));
  // Nothing outside the blueprint is admitted.
  for (const item of report.checked) {
    if (!item.module.startsWith("CycleDoubleCover.")) assert.deepEqual(item.sorries, [], item.module);
  }
});
