// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfgKernel, formatFormula, loadModuleSourceGraph } from "../src/index.ts";

// Parameter inference for `with *`: a section hypothesis an instance can
// supply, such as CommRing(S), does not fix S from the one local fact of
// its shape while another hypothesis fixes S from the goal or the facts.
const prelude = `
predicate Good (S : Set) := S = S
predicate Links (f R S : Set) := f = f

instance pair.good (x : Set)
  shows Good(pair(x, x))
proof
  unfold Good
  rfl

section Hom
variable (R S f : Set)
hypothesis source : Good(R)
hypothesis target : Good(S)
hypothesis hom : Links(f, R, S)

theorem rule (a : Set)
  requires member : a ∈ R
  shows pair(f, a) = pair(a, f) ∨ pair(f, a) = pair(f, a)
proof
  right
  rfl

end Hom
`;

test("a with * application fixes a parameter from the hypothesis that mentions it, and the instance supplies the class hypothesis", () => {
  const kernel = createZfgKernel();
  loadModuleSourceGraph(kernel, [{ file: "Supplied.g17", source: `module Supplied
${prelude}
theorem use (A g a : Set)
  requires good : Good(A)
  requires link : Links(g, A, pair(A, A))
  requires aIn : a ∈ A
  shows pair(g, a) = pair(a, g) ∨ pair(g, a) = pair(g, a)
proof
  have applied := rule with *
  exact applied
` }], ["lib"]);
  assert.ok(kernel.theorems.has("Supplied.use"));
});

test("without an instance for the class, the lone local fact still fixes the parameter", () => {
  const kernel = createZfgKernel();
  loadModuleSourceGraph(kernel, [{ file: "Lone.g17", source: `module Lone
predicate Good (S : Set) := S = S

section Fact
variable (R : Set)
hypothesis source : Good(R)

theorem rule (a : Set)
  requires member : a ∈ R
  shows a ∈ R
proof
  exact member

end Fact

theorem use (A a : Set)
  requires good : Good(A)
  requires aIn : a ∈ A
  shows a ∈ A
proof
  have applied := rule with *
  exact applied
` }], ["lib"]);
  const statement = formatFormula(kernel.theorems.get("Lone.use")!);
  assert.match(statement, /Good\(A\)/);
});
