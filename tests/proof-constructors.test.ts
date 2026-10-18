// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleSourceGraph, exportTheoremForMachine, compileProofModule, verifyProofMachine } from "../src/index.ts";

const header = `module Constructors
namespace Constructors
`;
test("local projections and nested partial constructors elaborate to existing checked rules", () => {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "Constructors.g17", source: header + `
theorem rebuild (x y : Set)
  requires h : x = x ∧ (y = y ∧ x = x)
  shows (y = y ∧ x = x) ∧ (∃ z, z = x ∧ x = x)
proof
  refine ⟨⟨h.right.left, ?_⟩, ?_⟩
  . exact h.left
  . refine ⟨x, rfl, h.right.right⟩

theorem apply_projection (x y : Set)
  requires h : x = x ∧ (∀ z, z = z → y = y)
  shows y = y
proof
  exact h.right at x with h.left

theorem whole_conjunction_hole (x : Set)
  requires h : x = x
  shows x = x ∧ (x = x ∧ x = x)
proof
  refine ⟨h, ?_⟩
  refine ⟨h, h⟩
theorem rewrite_projection (x y : Set)
  requires h : x = y ∧ y = y
  shows x = y
proof
  rw h.left
  rfl

theorem simplify_projection (x y : Set)
  requires h : x = y ∧ y = y
  shows x = y
proof
  simp [h.left]

theorem projected_iff (x y : Set)
  requires h : x = x ∧ (x = x ↔ y = y)
  shows y = y
proof
  exact h.right.forward with h.left

end Constructors
` }], ["lib"]);
  const trace = kernel.theoremTacticTraces.get("Constructors.rebuild")!;
  const refined = trace.steps.find(step => step.command.startsWith("refine"))!;
  assert.equal(refined.after.goals.length, 2);
  assert.equal(refined.after.goals[0]!.goal.tag, "eq");
  assert.equal(refined.after.goals[1]!.goal.tag, "exists");
  assert.equal(trace.steps.at(-1)!.after.goals.length, 0);
  for (const name of ["rebuild", "apply_projection", "whole_conjunction_hole", "rewrite_projection", "simplify_projection", "projected_iff"]) {
    const artifact = exportTheoremForMachine(kernel, `Constructors.${name}`);
    verifyProofMachine(kernel, compileProofModule([artifact]));
  }
});

test("invalid projections, unsolved holes, and extra nested entries fail", () => {
  for (const body of ["exact h.left", "refine ⟨h, ?_⟩", "refine ⟨⟨h, h, h⟩, h⟩"]) {
    const goal = body === "exact h.left" ? "x = x" : body.includes("⟨⟨") ? "(x = x ∧ x = x) ∧ x = x" : "x = x ∧ x = x";
    assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Bad.g17", source: `
module Bad
theorem invalid (x : Set)
  requires h : x = x
  shows ${goal}
proof
  ${body}
` }], ["lib"]), /conjunction|incomplete|unused|unsolved|goal/i);
  }
});

test("a final existential component accepts an existing proof without inventing a witness", () => {
  for (const body of ["refine ⟨diagonal, supplied⟩", "refine ⟨diagonal, ?_⟩\n  exact supplied"]) {
    const kernel = createZfKernel();
    loadModuleSourceGraph(kernel, [{ file: "Constructors.g17", source: header + `
theorem reuse (a : Set)
  requires diagonal : a = a
  requires supplied : ∃ x, x = a
  shows a = a ∧ (∃ x, x = a)
proof
  ${body}
end Constructors
` }], ["lib"]);
    verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, "Constructors.reuse")]));
  }
});

test("an existential component cannot reuse evidence for a different proposition", () => {
  const kernel = createZfKernel();
  assert.throws(() => loadModuleSourceGraph(kernel, [{ file: "Constructors.g17", source: header + `
theorem invalid (a b : Set)
  requires diagonal : a = a
  requires supplied : ∃ x, x = a
  shows a = a ∧ (∃ x, x = b)
proof
  refine ⟨diagonal, supplied⟩
end Constructors
` }], ["lib"]));
});
