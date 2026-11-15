// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { canonical, createZfgKernel, loadModuleSourceGraph } from "../src/index.ts";

// The typing rule for cardinality lives in the module that defines it, so
// Finite(S) makes cardinality(S) a natural number for typecheck and for the
// placement of operands wherever cardinality is in scope.
test("typecheck types a finite set's cardinality as a natural from the home module", () => {
  const kernel = createZfgKernel();
  loadModuleSourceGraph(kernel, [{ file: "CardinalityType.g17", source: `module CardinalityType
import Grace.Cumulus.Cardinal.Enumeration

theorem natural (S : Set)
  requires finite : Finite(S)
  shows Nat(cardinality(S))
proof
  typecheck

theorem member (S : Set)
  requires finite : Finite(S)
  shows cardinality(S) ∈ ℕ
proof
  typecheck
` }], ["lib"]);
  assert.ok(kernel.theorems.has("CardinalityType.natural"));
  assert.ok(kernel.theorems.has("CardinalityType.member"));
});

test("a power of a finite cardinality inside a ring section is natural arithmetic", () => {
  const kernel = createZfgKernel();
  loadModuleSourceGraph(kernel, [{ file: "CardinalityPower.g17", source: `module CardinalityPower
import Grace.Cumulus.Algebra.Ring.Pow
import Grace.Cumulus.Cardinal.Enumeration

section Values
variable (R S : Set)
hypothesis ring : CommRing(R)
hypothesis finite : Finite(S)

theorem square
  shows cardinality(S) ^ 2 = cardinality(S) * cardinality(S)
proof
  arith

end Values
` }], ["lib"]);
  const statement = canonical(kernel.theorems.get("CardinalityPower.square")!);
  assert.match(statement, /Nat\.Pow\.pow"/);
  assert.doesNotMatch(statement, /Ring\.Pow\.Ring\.pow"/);
});
