// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { checkWorkbenchFiles } from "../src/workbench.ts";

for (const [kind, condition, witness, propertyProof] of [
  ["disjunction", "x = a ∨ x = b", "a", "left\n    rfl"],
  ["implication", "x = a → x = b", "b", "intro equal\n    rfl"],
]) {
  test(`defchoose preserves the complete ${kind} inside its membership conjunction`, () => {
    const source = `module ChoicePrecedence
import Grace.Cumulus.Set.Choice
defchoose pick (A a b : Set) (x ∈ A) := ${condition}
requires member : ${witness} ∈ A
proof
  witness ${witness}
  constructor
  . exact member
  . ${propertyProof}

theorem selected (A a b : Set)
  requires member : ${witness} ∈ A
  shows pick(A, a, b) ∈ A ∧ (${condition.replaceAll("x", "pick(A, a, b)")})
proof
  exact pick.selected at A, a, b with member
`;
    assert.equal(checkWorkbenchFiles([{ name: "ChoicePrecedence.g17", source }]).ok, true);
    assert.throws(() => checkWorkbenchFiles([{ name: "ChoicePrecedence.g17", source: source.replace(`  requires member : ${witness} ∈ A\n`, "").replace("with member", "with *") }]));
  });
}
