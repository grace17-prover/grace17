// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { createZfKernel, loadModuleSourceGraph, SurfaceError } from "../src/index.ts";

// A module checked past a failing theorem: the failure is reported, the
// next theorem is checked, and a failure outside a proof stops the module.
const source = `module Cont

theorem first (A : Set)
  shows A = A
proof
  exact nothing

theorem second (A : Set)
  shows A = A
proof
  rfl

theorem third (A : Set)
  shows A ⊆ A
proof
  exact first at A

def broken (A : Set) : Set := nonsense(A)

theorem fourth (A : Set)
  shows A = A
proof
  rfl
`;

test("the loader goes on to the next theorem after a failed proof and stops at a failed definition", () => {
  const kernel = createZfKernel();
  const failures: { line: number; message: string }[] = [];
  assert.throws(() => loadModuleSourceGraph(kernel, [{ file: "Cont.g17", source }], ["lib"], undefined, [], undefined,
    { onTheoremFailure: failure => failures.push({ line: failure.line, message: failure.error.message }) }),
  (error: unknown) => error instanceof SurfaceError && error.line === 18 && /nonsense/.test(error.message));
  assert.deepEqual(failures.map(item => item.line), [3, 13]);
  assert.match(failures[0]!.message, /unknown proof nothing/);
  assert.ok(kernel.theorems.has("Cont.second"));
  assert.ok(!kernel.theorems.has("Cont.first"));
  assert.ok(!kernel.theorems.has("Cont.third"));
});

test("check --continue reports every failed theorem of a module, counts the module once, and names the theorems skipped after a failure outside a proof", () => {
  const directory = mkdtempSync(join(tmpdir(), "g17-continue-"));
  const file = join(directory, "Cont.g17");
  writeFileSync(file, source);
  const projectRoot = resolve(import.meta.dirname, "..");
  const run = spawnSync(process.execPath, ["--disable-warning=ExperimentalWarning", join(projectRoot, "bin", "g17.ts"),
    "check", "--continue", "--json", "--module-root", join(projectRoot, "lib"), file], { cwd: projectRoot, encoding: "utf8" });
  const result = JSON.parse(run.stdout) as {
    ok: boolean; failures: { module: string; line: number }[]; skipped: unknown[];
    skippedAfterFailure: { module: string; line: number; theorems: string[] }[];
  };
  assert.equal(result.ok, false);
  assert.deepEqual(result.failures.map(item => [item.module, item.line]), [["Cont", 6], ["Cont", 14], ["Cont", 18]]);
  assert.deepEqual(result.skipped, []);
  assert.deepEqual(result.skippedAfterFailure, [{ module: "Cont", file, line: 18, theorems: ["fourth"] }]);
  const text = spawnSync(process.execPath, ["--disable-warning=ExperimentalWarning", join(projectRoot, "bin", "g17.ts"),
    "check", "--continue", "--quiet", "--module-root", join(projectRoot, "lib"), file], { cwd: projectRoot, encoding: "utf8" });
  assert.match(text.stdout, /skipped after failure .*Cont\.g17 \[Cont\]: fourth after line 18/);
  assert.match(text.stdout, /0 modules checked, 1 failed, 0 skipped/);
});
