// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { canonical, createZfgKernel, loadModuleSourceGraph } from "../src/index.ts";

// An overloaded arithmetic token on operands whose syntax fixes no sort is
// placed by the typing rules and instances of the functions they apply,
// their premises left as proof obligations, and an operand placed nowhere
// is an error rather than a natural reading.
const prefix = `module Placement
import Grace.Cumulus.Cardinal.Enumeration
import Grace.Cumulus.Real.Natural

def twice (n : Nat) : Set := n + n

instance twice.natural (n : Nat)
  shows Nat(twice(n))
proof
  unfold twice
  typecheck
`;

function load(source: string) {
  const kernel = createZfgKernel();
  loadModuleSourceGraph(kernel, [{ file: "Placement.g17", source }], ["lib"]);
  return kernel;
}

function failure(source: string): string {
  try {
    load(source);
  } catch (error) {
    return error instanceof Error ? error.message : String(error);
  }
  throw new Error("expected a failure");
}

test("operands placed by a typing rule and by an instance take the natural operation", () => {
  const kernel = load(prefix + `
theorem ruleAndInstance (S : Set) (n : Nat)
  requires finite : Finite(S)
  shows cardinality(S) + twice(n) = twice(n) + cardinality(S)
proof
  sorry

theorem ruleAlone (S T : Set)
  shows cardinality(S) + cardinality(T) = cardinality(T) + cardinality(S)
proof
  sorry

theorem instanceAndLiteral (n : Nat)
  shows twice(n) + 1 = 1 + twice(n)
proof
  sorry

theorem ruleOrder (S : Set) (n : Nat)
  shows cardinality(S) * twice(n) ≤ twice(n) * cardinality(S)
proof
  sorry
`);
  for (const name of ["ruleAndInstance", "ruleAlone", "instanceAndLiteral", "ruleOrder"]) {
    const statement = canonical(kernel.theorems.get(`Placement.${name}`)!);
    assert.doesNotMatch(statement, /real|rational/i, name);
    assert.match(statement, /Nat\.Rec\.(add|mul)"|LessEqual"/, name);
  }
});

test("an operand no rule, instance, or fact places is an error, not a natural reading", () => {
  assert.match(failure(prefix + `
theorem unplaced (S T : Set)
  shows cardinality(S) + T = T + cardinality(S)
proof
  sorry
`), /cannot resolve notation \+ for operand types/);
});

test("an operand whose rules place it in two sorts asks for an annotation", () => {
  assert.match(failure(prefix + `
def amb (x : Set) : Set := x

theorem amb.natural (n : Nat)
  shows Nat(amb(n))
proof
  unfold amb
  typecheck

theorem amb.real (X : Real)
  shows Real(amb(X))
proof
  unfold amb
  typecheck

theorem ambiguous (y z : Set)
  shows amb(y) + amb(z) = amb(z) + amb(y)
proof
  sorry
`), /cannot resolve notation \+ between amb\(y\) and amb\(z\): amb\(y\) could be the Nat one or the Real one; annotate it, as in \(amb\(y\):N\) or \(amb\(y\):R\)/);
});

test("a definition's declared result sort places its values, inside a recursion too", () => {
  const kernel = load(`module Placement
import Grace.Cumulus.Real.Natural

def indicator (P : Set) : Nat := 1

def count (xs : List(ℕ)) → Nat
  | List.nil => 0
  | List.cons(X, rest) => indicator(X) + count(rest)
  descends xs
`);
  assert.ok(kernel.definitions.has("Placement.count"));
});

test("a missing typed numeral names the declaring module when it is loaded, and says so when none is", () => {
  const unloaded = failure(`module Placement
import Grace.Cumulus.Real.Order

theorem zero (x : Real)
  shows x ≤ x ∨ (0:R) = (0:R)
proof
  sorry
`);
  assert.match(unloaded, /no Real numeral notation for 0 is in scope: no imported module declares one/);
  const kernel = createZfgKernel();
  assert.throws(() => loadModuleSourceGraph(kernel, [
    { file: "Numerals.g17", source: "module Numerals\nimport Grace.Cumulus.Real.Natural\n" },
    { file: "Placement.g17", source: `module Placement
import Grace.Cumulus.Real.Order

theorem zero (x : Real)
  shows x ≤ x ∨ (0:R) = (0:R)
proof
  sorry
` }], ["lib"]), /no Real numeral notation for 0 is in scope: it is declared in Grace\.Cumulus\.Real\.Addition and Grace\.Cumulus\.Real\.Natural; import one of them/);
});
