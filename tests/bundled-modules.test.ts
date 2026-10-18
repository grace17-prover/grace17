// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Bundled modules over a ring: `structure Module (R : Ring) extends
// AbelianGroup as additive (…)` is a structure M with projections
// M.carrier, M.add, M.zero, M.neg, M.smul and the additive group M.additive
// as a value; under hypotheses Ring(R) and Module(M, R) the operations are
// written v + w, -v, and r • v, a binder (v : M) is membership in the
// carrier, AbelianGroup(M.additive) is found by instance search, the first
// module laws are proved, and a ring is a module over itself.

import assert from "node:assert/strict";
import test from "node:test";
import { createZfKernel, formulaEquals, instanceReport, loadModuleSourceGraph, SurfaceError } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const header = "module BundledModules\nimport Grace.Cumulus.Algebra.Module.Basic\n";

const section = (body: string) => header + `
section S
variable (R M : Set)
hypothesis ring : Ring(R)
hypothesis module : Module(M, R)
${body}
end S
`;

function load(source: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "BundledModules.g17", source }], ["lib"]);
  return kernel;
}

function check(source: string) {
  const result = checkWorkbenchFiles([{ name: "BundledModules.g17", source }]);
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 800));
  return result;
}

const statement = (result: ReturnType<typeof check>, name: string): string =>
  result.theorems.find(item => item.name === name)!.statement;

const library = "Grace.Cumulus.Algebra.Module.Basic";

const compare = (kernel: ReturnType<typeof load>, restated: string, original: string): void => {
  assert.ok(kernel.theorems.has(`${library}.${original}`), original);
  assert.ok(formulaEquals(kernel.theorems.get(`BundledModules.${restated}`)!, kernel.theorems.get(`${library}.${original}`)!), original);
};

test("Module.mk takes the fields flat, and Module(M, R) is the ring, the typing, the additive group, and the laws", () => {
  const source = header + `
theorem intro_restated (R carrier add zero neg smul : Set)
  requires ring : Ring(R)
  requires addF : add : carrier × carrier → carrier
  requires zeroIn : zero ∈ carrier
  requires negF : neg : carrier → carrier
  requires smulF : smul : R.carrier × carrier → carrier
  requires additive : AbelianGroup(Group.mk(carrier, add, zero, neg))
  requires smulAdd : ∀ r ∈ R.carrier, ∀ v w ∈ carrier, smul(r, add(v, w)) = add(smul(r, v), smul(r, w))
  requires addSmul : ∀ r s ∈ R.carrier, ∀ v ∈ carrier, smul(r + s, v) = add(smul(r, v), smul(s, v))
  requires mulSmul : ∀ r s ∈ R.carrier, ∀ v ∈ carrier, smul(r * s, v) = smul(r, smul(s, v))
  requires oneSmul : ∀ v ∈ carrier, smul(R.one, v) = v
  shows Module(Module.mk(carrier, add, zero, neg, smul), R)
proof
  exact Module.intro with *

theorem value_restated (self : Set)
  shows Module.additive(self) = Group.mk(Module.carrier(self), Module.add(self), Module.zero(self), Module.neg(self))
proof
  exact Module.additive.value at self

theorem mul_restated (self : Set)
  shows Group.mul(Module.additive(self)) = Module.add(self)
proof
  exact Module.additive.mul at self

theorem abelian_restated (self R : Set)
  requires module : Module(self, R)
  shows AbelianGroup(Module.additive(self))
proof
  exact Module.additive.abelian_group with module

theorem opened (M R : Set)
  requires module : Module(M, R)
  shows Ring(R) ∧ AbelianGroup(M.additive)
proof
  obtain ⟨shape, ringR, addF, zeroIn, negF, smulF, additive, smulAdd, addSmul, mulSmul, oneSmul⟩ := module
  exact ⟨ringR, additive⟩
`;
  const result = check(source);
  const kernel = load(source);
  compare(kernel, "intro_restated", "Module.intro");
  compare(kernel, "value_restated", "Module.additive.value");
  compare(kernel, "mul_restated", "Module.additive.mul");
  compare(kernel, "abelian_restated", "Module.additive.abelian_group");
  assert.deepEqual(kernel.datatypes.get(`${library}.Module.inductive`)!.constructors.map(item => [item.name, item.arity]),
    [[`${library}.Module.mk`, 5]]);
  assert.equal(statement(result, "BundledModules.value_restated"),
    "∀ self, self.additive = Group.mk(self.carrier, self.add, self.zero, self.neg)");
  assert.equal(statement(result, "BundledModules.mul_restated"), "∀ self, self.additive.mul = self.add");
  assert.equal(statement(result, "BundledModules.abelian_restated"), "∀ self, ∀ R, Module(self, R) → AbelianGroup(self.additive)");
  assert.equal(statement(result, "BundledModules.opened"), "∀ M, ∀ R, Module(M, R) → Ring(R) ∧ AbelianGroup(M.additive)");
});

test("v + w, -v, r • v, and (v : M) are the projections applied, and the module's own + is distinct from the ring's", () => {
  const written = load(section(`
theorem spelled (r : R) (v w : M)
  shows r • (v + -w) + (r + r) • v = r • (v + -w) + (r + r) • v
proof
  rfl
`));
  const explicit = load(header + `
theorem spelled (R M r v w : Set)
  requires rIn : r ∈ Ring.carrier(R)
  requires vIn : v ∈ Module.carrier(M)
  requires wIn : w ∈ Module.carrier(M)
  requires ring : Ring(R)
  requires module : Module(M, R)
  shows call2(Module.add(M), call2(Module.smul(M), r, call2(Module.add(M), v, apply(Module.neg(M), w))),
      call2(Module.smul(M), call2(Ring.add(R), r, r), v)) =
    call2(Module.add(M), call2(Module.smul(M), r, call2(Module.add(M), v, apply(Module.neg(M), w))),
      call2(Module.smul(M), call2(Ring.add(R), r, r), v))
proof
  rfl
`);
  assert.ok(formulaEquals(written.theorems.get("BundledModules.spelled")!, explicit.theorems.get("BundledModules.spelled")!));
  const result = check(section(`
theorem printed (r : R) (v w : M)
  shows r • (v + w) = r • v + r • w
proof
  exact smul_add with *
`));
  assert.equal(statement(result, "BundledModules.printed"),
    "∀ R M, ∀ (r : R), ∀ (v w : M), Ring(R) → Module(M, R) → r • (v + w) = r • v + r • w");
});

test("the additive group of a module is an abelian group by instance search, and the group laws transport", () => {
  check(section(`
theorem abelian
  shows AbelianGroup(M.additive)
proof
  exact Module.additive.abelian_group with *

theorem commutes (v w : M)
  shows v + w = w + v
proof
  have abelian := Module.additive.abelian_group with module
  have swap := mul_comm at M.additive, v, w with abelian, *
  module_additive at swap
  exact swap

theorem cancels (v : M)
  requires doubled : v + v = v
  shows v = M.zero
proof
  exact Module.eq_zero_of_add_self with *
`));
});

test("the first module laws and the ring as a module over itself", () => {
  const source = section(`
theorem smul_add_restated (r : R) (v w : M)
  shows r • (v + w) = r • v + r • w
proof
  exact smul_add with *

theorem add_smul_restated (r s : R) (v : M)
  shows (r + s) • v = r • v + s • v
proof
  exact add_smul with *

theorem zero_smul_restated (v : M)
  shows R.zero • v = M.zero
proof
  exact zero_smul with *

theorem smul_zero_restated (r : R)
  shows r • M.zero = M.zero
proof
  exact smul_zero with *
`) + `
theorem to_module_restated (R : Set)
  requires ring : Ring(R)
  shows Module(selfModule(R), R)
proof
  exact Ring.to_module with ring

theorem self_module (R : Set)
  requires ring : Ring(R)
  shows AbelianGroup(Module.additive(selfModule(R)))
proof
  have module := Ring.to_module with ring
  exact Module.additive.abelian_group with module
`;
  const result = check(source);
  const kernel = load(source);
  const laws: Record<string, [string, string]> = {
    "smul_add": ["smul_add_restated", "∀ R M, ∀ (r : R), ∀ (v w : M), Ring(R) → Module(M, R) → r • (v + w) = r • v + r • w"],
    "add_smul": ["add_smul_restated", "∀ R M, ∀ (r s : R), ∀ (v : M), Ring(R) → Module(M, R) → (r + s) • v = r • v + s • v"],
    "zero_smul": ["zero_smul_restated", "∀ R M, ∀ (v : M), Ring(R) → Module(M, R) → R.zero • v = M.zero"],
    "smul_zero": ["smul_zero_restated", "∀ R M, ∀ (r : R), Ring(R) → Module(M, R) → r • M.zero = M.zero"],
    "Ring.to_module": ["to_module_restated", "∀ R, Ring(R) → Module(selfModule(R), R)"],
  };
  for (const [name, [restated, expected]] of Object.entries(laws)) {
    compare(kernel, restated, name);
    assert.equal(statement(result, `BundledModules.${restated}`), expected, name);
  }
  for (const name of ["Module.additive.abelian_group", "Module.additive.mem", "Module.smul_mem", "Module.add_mem", "Ring.to_module"]) {
    assert.ok(instanceReport(kernel).some(item => item.name === `${library}.${name}`), name);
  }
});

test("a module law written with the ring's operation on vectors is rejected", () => {
  assert.throws(() => load(section(`
theorem wrong (v w : M)
  shows v * w = w * v
proof
  rfl
`)), (error: unknown) => error instanceof SurfaceError);
});
