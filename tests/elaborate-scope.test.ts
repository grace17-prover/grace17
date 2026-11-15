// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { handleMachineRequest } from "../src/index.ts";

// `elaborate` at a line reads the text with the facts in force there: the
// section clauses up to and including the line, and inside a theorem its
// binders and premises.
const source = `module Scope
predicate Good (S : Set) := S = S

section Facts
variable (A : Set)
hypothesis good : Good(A)

def twice (x : Set) : Set :=
  pair(x, x)

theorem inside (B : Set)
  requires member : B ∈ A
  shows B ∈ A
proof
  exact member

end Facts
`;
const files = [{ name: "Scope.g17", source }];

function ok(response: ReturnType<typeof handleMachineRequest>): Record<string, unknown> {
  assert.equal((response as { ok: boolean }).ok, true, JSON.stringify(response));
  return (response as { result: Record<string, unknown> }).result;
}

test("a line on a section clause keeps the clause in force", () => {
  const result = ok(handleMachineRequest({ id: 1, method: "elaborate", params: { text: "Good(A)", files, line: 6 } }));
  assert.equal(result.line, 8);
  assert.equal(result.printed, "Good(A)");
});

test("a line inside a definition stands before it, with the section variables in scope", () => {
  const result = ok(handleMachineRequest({ id: 2, method: "elaborate", params: { text: "pair(A, A)", files, line: 9, kind: "term" } }));
  assert.equal(result.line, 8);
  assert.equal(result.printed, "{A, A}");
});

test("a line inside a theorem has its binders and premises in force and names the theorem", () => {
  const result = ok(handleMachineRequest({ id: 3, method: "elaborate", params: { text: "B ∈ A", files, line: 15 } }));
  assert.equal(result.theorem, "inside");
  assert.equal(result.line, 11);
  assert.equal(result.printed, "B ∈ A");
  assert.equal(result.kind, "formula");
});

test("a line after a theorem's proof is outside it", () => {
  const result = ok(handleMachineRequest({ id: 4, method: "elaborate", params: { text: "twice(A)", files, line: 16, kind: "term" } }));
  assert.equal(result.theorem, undefined);
  assert.equal(result.line, 16);
});
