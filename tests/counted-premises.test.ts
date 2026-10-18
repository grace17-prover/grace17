// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfgKernel, elaborateModule } from "../src/index.ts";

const rules = `module Rules
namespace Rules
theorem guarded (x : Set)
  requires hx : x = x
  shows x = x
proof
  exact hx

theorem pair (x y : Set)
  requires hx : x = x
  requires hy : y = y
  shows x = x ∧ y = y
proof
  refine ⟨hx, hy⟩

theorem implication (x y : Set)
  requires hx : x = x
  requires hy : y = y
  shows x = y → x = y
proof
  intro same
  exact same
end Rules
`;
function check(body: string, requirements = "  requires hx : x = x\n  requires hy : y = y\n  requires same : x = y", goal = "x = y") {
  const kernel = createZfgKernel();
  elaborateModule(kernel, rules);
  elaborateModule(kernel, `module Client
import Rules
open Rules
theorem result (x y : Set)
${requirements}
  shows ${goal}
proof
${body}
`);
  kernel.checkProof(kernel.theoremProofs.get("Client.result")!);
}

test("counted premises preserve partial application and explicitly cross conclusion boundaries", () => {
  check("  have partial := implication at x, y with *{2}\n  exact partial with same");
  check("  exact implication at x, y with *{3}");
});

test("specialize shares counted and complete premise application", () => {
  check("  have partial := implication at x, y\n  specialize partial with *{2}\n  exact partial with same");
  check("  have partial := implication at x, y\n  specialize partial with *\n  exact partial");
  check("  have partial := implication\n  specialize partial with x, y, *{2}, same\n  exact partial");
});

test("counted premises expand before parsing nested proof applications", () => {
  check("  exact pair at x, y with guarded at x with *{2}", undefined, "x = x ∧ y = y");
});

test("counted premises reject invalid bounds, missing evidence and exhausted conclusions", () => {
  for (const n of ["0", "257", "9999999999999999999999999", "x", "-1", "1.5"])
    assert.throws(() => check(`  exact implication at x, y with *{${n}}`), /premise count from 1 to 256/);
  assert.throws(() => check("  exact implication at x, y with *{4}"), /no remaining argument/);
  assert.throws(() => check("  exact implication at x, y with *{2}", "  requires hx : x = x"), /no assumption matches/);
});


test("a premise wildcard ends a bullet tactic before its indented successor", () => {
  check(`  constructor
  . have first := guarded at x with *
    exact first
  . have second := pair at x, y with hx, *
    exact second`, undefined, "x = x ∧ (x = x ∧ y = y)");
});
