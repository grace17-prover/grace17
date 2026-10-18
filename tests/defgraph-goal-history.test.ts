// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, exportTheoremForMachine, compileProofModule } from "../src/index.ts";
import { setSurfaceTraceCapture } from "../src/surface.ts";
import { checkWorkbenchFiles, workbenchFailure } from "../src/workbench.ts";
import { proofDeclarationContext, tacticStepAtCursor } from "../workbench/editor-utils.js";

const source = `module GraphHistory
namespace GraphHistory
import Grace.Cumulus.Set.Function

defgraph inclusion
  (A B : Set)
  (x ∈ A) : B := x
requires subset :
  A ⊆ B
proof
  unfold Subset at subset

  have included := subset with x, member
  exact included

theorem following (x : Set)
  shows x = x
proof
  rfl
end GraphHistory
`;
const lineOf = (s: string, text: string) => s.split("\n").findIndex(line => line.trim() === text) + 1;

test("bounded defgraph retains authored lines and intermediate goals on cold and cached checks", () => {
  for (let pass = 0; pass < 2; pass++) {
    const result = checkWorkbenchFiles([{ name: "GraphHistory.g17", source }], "ZF", ["GraphHistory.g17"]);
    const closed = result.theorems.find(t => t.name === "GraphHistory.inclusion.closed")!;
    assert.ok(closed.initial?.goals.length);
    assert.deepEqual(closed.steps.map(s => s.line), [11, 13, 14]);
    assert.deepEqual(closed.steps.map(s => s.command), ["unfold Subset at subset", "have included := subset with x, member", "exact included"]);
    const before = tacticStepAtCursor(closed.steps, 10, 1);
    const middle = tacticStepAtCursor(closed.steps, 13, 80);
    const end = tacticStepAtCursor(closed.steps, 14, 80);
    assert.equal(before, 0);
    assert.ok(closed.steps[middle - 1]!.after.goals.length);
    assert.equal(closed.steps[end - 1]!.after.goals.length, 0);
    for (const law of ["relates", "function", "value"]) {
      assert.deepEqual(result.theorems.find(t => t.name === `GraphHistory.inclusion.${law}`)!.steps, []);
    }
    assert.equal(result.theorems.find(t => t.name === "GraphHistory.following")!.steps[0]!.line, 19);
    assert.equal(result.theorems.find(t => 13 >= t.lineStart && 13 <= t.lineEnd)?.name, closed.name);
  }
});

test("the reported monomialWeights defgraph shows every authored proof step", () => {
  const name = "lib/Grace/Cumulus/Algebra/Polynomial/Assignment.g17";
  const text = readFileSync(name, "utf8");
  for (let pass = 0; pass < 2; pass++) {
    const result = checkWorkbenchFiles([{ name, source: text }], "ZF", [name]);
    const closed = result.theorems.find(t => t.name.endsWith(".monomialWeights.closed"))!;
    const first = lineOf(text, "unfold Subset at domain");
    assert.ok(closed.initial?.goals.length);
    assert.deepEqual(closed.steps.map(s => s.line), Array.from({ length: 7 }, (_, i) => first + i));
    assert.ok(closed.steps[0]!.after.goals.length);
    assert.equal(closed.steps.at(-1)!.after.goals.length, 0);
    assert.equal(result.theorems.find(t => first >= t.lineStart && first <= t.lineEnd)?.name, closed.name);
  }
});

test("a failing defgraph retains the actual error line and partial proof history", () => {
  const broken = source.replace("  exact included", "  exact member");
  let failure: ReturnType<typeof workbenchFailure> | undefined;
  try {
    checkWorkbenchFiles([{ name: "GraphHistory.g17", source: broken }], "ZF", ["GraphHistory.g17"]);
    assert.fail("invalid codomain proof accepted");
  } catch (error) { failure = workbenchFailure(error); }
  assert.equal(failure.line, 14);
  assert.match(failure.message, /checked codomain proof/);
  assert.ok(failure.trace?.initial.goals.length);
  assert.deepEqual(failure.trace?.steps.map(s => s.line), [11, 13, 14]);
  assert.equal(proofDeclarationContext(broken, 14)?.name, "inclusion");
  // Repairing the same editor buffer must restore all successful states.
  const repaired = checkWorkbenchFiles([{ name: "GraphHistory.g17", source }], "ZF", ["GraphHistory.g17"]);
  assert.equal(repaired.theorems.find(t => t.name.endsWith("inclusion.closed"))!.steps.length, 3);
});


test("defgraph editor traces do not change the checked proof program", () => {
  const programs = [false, true].map(capture => {
    const kernel = createZfKernel();
    setSurfaceTraceCapture(kernel, capture);
    loadModuleSourceGraph(kernel, [{ file: "GraphHistory.g17", source }], ["lib"]);
    const name = "GraphHistory.inclusion.closed";
    assert.equal(kernel.theoremTacticTraces.has(name), capture);
    return compileProofModule([exportTheoremForMachine(kernel, name)]);
  });
  assert.deepEqual(programs[0], programs[1]);
});
