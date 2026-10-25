// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { createZfKernel, loadModuleGraph, formatFormula, exportTheorem, verifyExportedProof } from "../src/index.ts";

const header = `module FiniteInductionTest
import Grace.Cumulus.Cardinal.Counting
`;

// A property closed under adding an element, inside an ambient set E.
const closed = `
theorem members_in_ambient (E F : Set)
  requires finite : Finite(F)
  requires bound : F ⊆ E
  shows ∀ y ∈ F, y ∈ E
proof
  induction finite with G a
  | empty =>
    intros y hy
    exfalso
    exact set.empty with hy
  | insert using ih =>
    intros y hy
    rw union2.membership at hy
    rw singleton.membership at hy
    rcases hy with inG | same
    . exact ih with y, inG
    . rw same
      exact aMember
`;

// A count of the elements of a finite set, by induction, without an ambient
// set in context: the induction runs inside F itself.
const count = `
theorem count_exists (F : Set)
  requires finite : Finite(F)
  shows ∃ n, Nat(n) ∧ cardinality(F) = n
proof
  induction finite with G a
  | empty =>
    refine ⟨zero, Naturals.constructor.zero, ?_⟩
    exact cardinality.empty
  | insert using ih =>
    obtain ⟨n, natural, size⟩ := ih
    have same : insert(a, G) = G ∪ {a}
      ext y
      simp
    have counted := cardinality.insert with GFinite, aFresh
    rw [same, size] at counted
    refine ⟨succ(n), Naturals.constructor.succ with natural, counted⟩
`;

// The two goals may also be taken with plain bullets.
const bullets = `
theorem count_exists_bullets (F : Set)
  requires finite : Finite(F)
  shows ∃ n, Nat(n) ∧ cardinality(F) = n
proof
  induction finite with G a
  . refine ⟨zero, Naturals.constructor.zero, ?_⟩
    exact cardinality.empty
  . intros G subset finiteG a member fresh ih
    obtain ⟨n, natural, size⟩ := ih
    have same : insert(a, G) = G ∪ {a}
      ext y
      simp
    have counted := cardinality.insert with finiteG, fresh
    rw [same, size] at counted
    refine ⟨succ(n), Naturals.constructor.succ with natural, counted⟩
`;

function load(body: string) {
  const directory = mkdtempSync(join(tmpdir(), "g17-finite-induction-"));
  const file = join(directory, "FiniteInductionTest.g17");
  writeFileSync(file, header + body);
  const kernel = createZfKernel();
  loadModuleGraph(kernel, [file], ["lib"]);
  return kernel;
}

test("induction over a finite set follows Finite.induction with the goal as the family", () => {
  const kernel = load(closed + count + bullets);
  for (const name of ["members_in_ambient", "count_exists", "count_exists_bullets"]) {
    const full = `FiniteInductionTest.${name}`;
    assert.ok(kernel.theorems.has(full), full);
    verifyExportedProof(kernel, exportTheorem(kernel, full));
    // The family { G ∈ 𝒫(E) | P(G) } is a hidden separation helper per use.
    assert.equal(kernel.definitions.get(`${full}.family`)?.kind, "separation", `${full}.family`);
  }
  const trace = kernel.theoremTacticTraces.get("FiniteInductionTest.members_in_ambient")!;
  const first = trace.steps[0]!;
  assert.equal(first.command, "induction finite with G a");
  assert.equal(first.after.goals.length, 2);
  assert.equal(formatFormula(first.after.goals[0]!.goal), "∀ y ∈ ∅, y ∈ E");
  assert.equal(formatFormula(first.after.goals[1]!.goal),
    "∀ G ⊆ E, Finite(G) → ∀ a ∈ E, a ∉ G → (∀ y ∈ G, y ∈ E) → ∀ y ∈ union2(G, {a}), y ∈ E");
  // The insert header introduces the step hypotheses by name.
  const insertHeader = trace.steps.find(step => step.command === "| insert using ih =>")!;
  const locals = insertHeader.after.goals[0]!.locals.map(item => item.name);
  assert.deepEqual(locals.filter(item => ["GSubset", "GFinite", "aMember", "aFresh", "ih"].includes(item)),
    ["GSubset", "GFinite", "aMember", "aFresh", "ih"]);
  assert.equal(formatFormula(insertHeader.after.goals[0]!.goal), "∀ y ∈ union2(G, {a}), y ∈ E");
  // Without an ambient subset hypothesis the induction runs inside F itself.
  const countTrace = kernel.theoremTacticTraces.get("FiniteInductionTest.count_exists")!;
  assert.match(formatFormula(countTrace.steps[0]!.after.goals[1]!.goal), /^∀ G ⊆ F, Finite\(G\) → ∀ a ∈ F, a ∉ G → /);
});

test("induction over a finite set reports a hypothesis that is not a finiteness fact", () => {
  assert.throws(() => load(`
theorem wrong (E F : Set)
  requires bound : F ⊆ E
  shows F ⊆ E
proof
  induction bound with G a
  | empty => simp
  | insert using ih => simp
`), /induction over a finite set expects a hypothesis Finite\(F\)/u);
});

test("the case headers must match the goals they open", () => {
  assert.throws(() => load(`
theorem swapped (F : Set)
  requires finite : Finite(F)
  shows F = F
proof
  induction finite with G a
  | insert using ih => rfl
  | empty => rfl
`), /expected the `\| empty =>` case/u);
});
