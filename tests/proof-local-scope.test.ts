// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, elaborateModule, exportTheorem, verifyExportedProof } from "../src/index.ts";

function check(source: string) {
  const kernel = createZfKernel();
  const result = elaborateModule(kernel, source);
  for (const name of result.theorems) verifyExportedProof(kernel, exportTheorem(kernel, name));
  return kernel;
}

test("sibling local lemmas can reuse existential witness names", () => {
  check(`module LocalScopes
theorem reusable (a : Set)
  requires existsA : ∃ x, x = a
  shows a = a
proof
  have first : a = a
    obtain ⟨x, hx⟩ := existsA
    rfl
  have second : a = a
    obtain ⟨x, hx⟩ := existsA
    exact first
  exact second
`);
});

test("sibling constructor goals can reuse witness and introduction names", () => {
  check(`module LocalScopes
theorem branches (a : Set)
  requires existsA : ∃ x, x = a
  shows (∀ y, y = y) ∧ (∀ y, y = y)
proof
  constructor
  . intro y
    obtain ⟨x, hx⟩ := existsA
    rfl
  . intro y
    obtain ⟨x, hx⟩ := existsA
    rfl
`);
});

test("a local existential witness is unavailable after its lemma closes", () => {
  assert.throws(() => check(`module LocalScopes
theorem leak (a : Set)
  requires existsA : ∃ x, x = a
  shows a = a
proof
  have first : a = a
    obtain ⟨x, hx⟩ := existsA
    rfl
  have leaked : x = x
    rfl
  rfl
`), /unknown.*x|unbound.*x|undeclared.*x|not.*scope/i);
});

test("an outer witness remains reserved inside nested lemmas", () => {
  assert.throws(() => check(`module LocalScopes
theorem collision (a : Set)
  requires existsA : ∃ x, x = a
  shows a = a
proof
  obtain ⟨x, hx⟩ := existsA
  have first : a = a
    obtain ⟨x, other⟩ := existsA
    rfl
  rfl
`), /witness x is already in scope/);
});
