// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleSourceGraph, exportTheoremForMachine, compileProofModule, verifyProofMachine } from "../src/index.ts";

const header = `module NamedPremises
namespace NamedPremises
import Grace.Cumulus.Set.Function

theorem transport (A B x : Set)
  requires subset : A ⊆ B
  requires member : x ∈ A
  shows x ∈ B
proof
  unfold Subset at subset
  exact subset with x, member

theorem repeated (x : Set)
  requires first : x = x
  requires second : x = x
  shows x = x
proof
  exact first

theorem universal (a : Set)
  requires all : ∀ x, x = x ∧ a = a
  shows a = a
proof
  have one := all with a
  exact one.right

theorem iff_refl (x : Set)
  requires h : x = x
  shows x = x ↔ x = x
proof
  tauto
`;
function load(source: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "NamedPremises.g17", source: header + source + "\nend NamedPremises\n" }], ["lib"]);
  return kernel;
}

test("named premises infer all parameters, including projections, a trailing star, and equivalence directions", () => {
  const kernel = load(`
theorem use (A B x : Set)
  requires data : A ⊆ B ∧ x ∈ A
  shows x ∈ B
proof
  have image := transport with data.left, data.right
  exact image

theorem star (x : Set)
  requires hx : x = x
  shows x = x
proof
  exact repeated with hx, *

theorem direction (x : Set)
  requires hx : x = x
  shows x = x
proof
  exact iff_refl.forward with hx, hx

theorem alpha (a : Set)
  requires given : ∀ y, y = y ∧ a = a
  shows a = a
proof
  exact universal with given

theorem explicit (A B x : Set)
  requires subset : A ⊆ B
  requires hx : x ∈ A
  shows x ∈ B
proof
  exact transport at A, B, x with *
`);
  for (const name of ["use", "star", "direction", "alpha", "explicit"]) {
    verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, `NamedPremises.${name}`)]));
  }
});

test("named premises reject inconsistent carrier substitutions", () => {
  assert.throws(() => load(`
theorem conflict (A B C x : Set)
  requires subset : A ⊆ B
  requires hx : x ∈ C
  shows x ∈ B
proof
  exact transport with subset, hx
`), /named premise hx \(x ∈ C\) matches no requirement; requirement 2 is x ∈ A/);
});

test("a parameter absent from the named premises comes from the goal", () => {
  assert.throws(() => load(`
theorem missing (A B x : Set)
  requires subset : A ⊆ B
  shows x ∈ B
proof
  apply transport with subset
`), /1 goal remains; next is x ∈ A/);
});

test("a quantified variable cannot escape into an inferred theorem parameter", () => {
  assert.throws(() => load(`
theorem capture (a : Set)
  requires given : ∀ y, y = y ∧ y = y
  shows a = a
proof
  exact universal with given
`), /named premise given .* matches no requirement; requirement 1 is/);
});

test("inference is local to each application and does not reuse a prior carrier", () => {
  const kernel = load(`
theorem separate (A B C D x y : Set)
  requires first : A ⊆ B
  requires hx : x ∈ A
  requires second : C ⊆ D
  requires hy : y ∈ C
  shows x ∈ B ∧ y ∈ D
proof
  have left := transport with first, hx
  have right := transport with second, hy
  refine ⟨left, right⟩
`);
  verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, "NamedPremises.separate")]));
});

test("bare star reconstructs parameters from the goal and unique local premises", () => {
  const kernel = load(`
theorem goal_star (A B x : Set)
  requires subset : A ⊆ B
  requires hx : x ∈ A
  shows x ∈ B
proof
  exact transport with *

theorem goal_show (A B x : Set)
  requires subset : A ⊆ B
  requires hx : x ∈ A
  shows x ∈ B
proof
  show x ∈ B := transport with *
`);
  for (const name of ["goal_star", "goal_show"])
    verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, `NamedPremises.${name}`)]));
});

test("bare star rejects ambiguous parameters without selecting the first fact", () => {
  assert.throws(() => load(`
theorem ambiguous (A B C x : Set)
  requires first : A ⊆ B
  requires second : C ⊆ B
  requires left : x ∈ A
  requires right : x ∈ C
  shows x ∈ B
proof
  exact transport with *
`), /cannot uniquely infer parameters A.*explicit at list/);
});

test("later premises can resolve ambiguity without backtracking", () => {
  const kernel = load(`
theorem narrowed (A B C x : Set)
  requires first : A ⊆ B
  requires second : C ⊆ B
  requires member : x ∈ C
  shows x ∈ B
proof
  exact transport with *
`);
  verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, "NamedPremises.narrowed")]));
});

test("goal-directed inference never supplies a missing proof premise", () => {
  assert.throws(() => load(`
theorem missing_evidence (A B x : Set)
  requires subset : A ⊆ B
  shows x ∈ B
proof
  exact transport with *
`), /cannot find evidence/);
});

test("bare star infers an unstated have from unique local premises", () => {
  const kernel = load(`
theorem unstated (A B x : Set)
  requires subset : A ⊆ B
  requires member : x ∈ A
  shows x ∈ B
proof
  have result := transport with *
  exact result
`);
  verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, "NamedPremises.unstated")]));
});

test("bare star on a have still rejects ambiguous local premises", () => {
  assert.throws(() => load(`
theorem unstated_ambiguous (A B C x : Set)
  requires first : A ⊆ B
  requires second : A ⊆ C
  requires member : x ∈ A
  shows x ∈ B
proof
  have result := transport with *
  exact result
`), /cannot uniquely infer parameters/);
});

test("goal-directed inference rejects quantified-variable escape", () => {
  assert.throws(() => load(`
theorem capture_star (a : Set)
  requires given : ∀ y, y = y ∧ y = y
  shows a = a
proof
  exact universal with *
`), /cannot find evidence/);
});

test("goal-directed matching has a fixed work limit", () => {
  const facts = Array.from({ length: 2050 }, (_, i) => `  requires h${i} : A ⊆ B`).join("\n");
  assert.throws(() => load(`
theorem bounded_work (A B x : Set)
${facts}
  requires member : x ∈ A
  shows x ∈ B
proof
  exact transport with *
`), /2048-match limit.*explicit at list/);
});

test("goal-directed substitutions do not leak between sibling goals", () => {
  const kernel = load(`
theorem siblings (A B C D x y : Set)
  requires first : A ⊆ B
  requires hx : x ∈ A
  requires second : C ⊆ D
  requires hy : y ∈ C
  shows x ∈ B ∧ y ∈ D
proof
  constructor
  . exact transport with *
  . exact transport with *
`);
  verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, "NamedPremises.siblings")]));
});

test("a goal binder cannot become a free inferred parameter", () => {
  assert.throws(() => load(`
theorem quantified_conclusion (a : Set)
  requires h : a = a
  shows ∀ x, x = x ∧ a = a
proof
  intro x
  refine ⟨rfl, h⟩

theorem no_escape (a : Set)
  requires h : a = a
  shows ∀ y, y = y ∧ y = y
proof
  exact quantified_conclusion with *
`), /conclusion does not match the goal/);
});
