// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// `register simp` and `register ring`: the default rewrite set of `simp` and
// the ring scope forms `R ⧸ I`, `R ↾ T`, and `R[I]` are declared by the
// library modules that define the notions, inherited through imports,
// exported with the module interface, listed beside the notations, and
// absent from a module that does not import them; a wrong declaration is
// reported at its line.

import assert from "node:assert/strict";
import test from "node:test";
import { createZfKernel, formulaEquals, loadModuleSourceGraph } from "../src/index.ts";
import {
  captureSurfaceBaseline, decodeSurfaceEnvironmentDelta, decodeSurfaceEnvironmentIndex, elaborateModule,
  encodeSurfaceEnvironmentDelta, encodeSurfaceEnvironmentIndex, exportSurfaceEnvironmentDelta, exportSurfaceEnvironmentIndex,
  registrationReport,
} from "../src/surface.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

function load(files: readonly { readonly file: string; readonly source: string }[]) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, files, ["lib"]);
  return kernel;
}

// A set operation of the module's own, with a membership law proved as a
// theorem, so that nothing opens it unless the law is registered.
const header = "module Registered\nimport Grace.Cumulus.Set.Basic\n";
const law = `
def both (A B : Set) : Set := A ∩ B

theorem both.membership (x A B : Set)
  shows x ∈ both(A, B) ↔ x ∈ A ∧ x ∈ B
proof
  simp [both, intersection.membership]
`;
const registration = "register simp both.membership\n";
const opened = (tactic: string) => `
theorem opened (x A B : Set)
  requires h : x ∈ both(A, B)
  shows x ∈ A
proof
  ${tactic}
`;

test("the library registers the membership laws simp rewrites by default and the ring scope forms, and the listing shows them", () => {
  const result = checkWorkbenchFiles([{ name: "Registered.g17", source: "module Registered\nimport Grace.Cumulus.Algebra.Polynomial.Residue\n" }]);
  assert.equal(result.ok, true);
  const simp = result.registrations.filter(item => item.form === "simp");
  assert.deepEqual(simp.map(item => [item.predicate, item.module]).sort(), [
    ["Grace.Cumulus.Set.Algebra.symmetricDifference.membership", "Grace.Cumulus.Set.Algebra"],
    ["Grace.Cumulus.Set.Finite.FiniteSet.singleton.membership", "Grace.Cumulus.Set.Finite"],
    ["Grace.Cumulus.Set.Finite.FiniteSet.union2.membership", "Grace.Cumulus.Set.Finite"],
    ["Grace.Cumulus.Set.Powerset.difference.singleton_membership", "Grace.Cumulus.Set.Powerset"],
    ["pair.membership", undefined],
    ["set.empty", undefined],
  ]);
  assert.deepEqual(simp.find(item => item.predicate === "set.empty")!.rules, [{ rule: "axiom", name: "set.empty" }]);
  const rings = result.registrations.filter(item => item.form === "ring");
  assert.deepEqual(rings.map(item => [item.predicate, item.module, item.names]).sort(), [
    ["[]", "Grace.Cumulus.Algebra.Polynomial.Ring", ["A", "add", "zero", "neg", "mul", "one", "I"]],
    ["↾", "Grace.Cumulus.Algebra.Restriction", ["A", "add", "zero", "neg", "mul", "one", "B"]],
    ["⧸", "Grace.Cumulus.Algebra.Ring.QuotientCore", ["A", "add", "zero", "neg", "mul", "one", "I"]],
  ]);
  assert.equal(rings.find(item => item.predicate === "⧸")!.terms!.length, 6);
});

test("the defaults apply in order, the modules' laws before the bootstrap's, so a literal opens through the union, the singleton, and the pair", () => {
  const kernel = load([{ file: "Literal.g17", source: `module Literal
import Grace.Cumulus.Set.Finite

theorem alternatives (x a b c : Set)
  requires h : x ∈ {a, b, c}
  shows x = a ∨ x = b ∨ x = c
proof
  simp at h
  rcases h with ha | hb | hc
  . left
    exact ha
  . right
    left
    exact hb
  . right
    right
    exact hc
` }], ["lib"]);
  assert.ok(kernel.theorems.has("Literal.alternatives"));
});

test("a module's own simp registration makes simp at h and tauto open its membership, and a module without it gets no special treatment", () => {
  for (const tactic of ["simp at h\n  exact h.left", "tauto"]) {
    const registered = load([{ file: "Registered.g17", source: header + law + registration + opened(tactic) }]);
    assert.ok(registered.theorems.has("Registered.opened"));
    assert.throws(() => load([{ file: "Registered.g17", source: header + law + opened(tactic) }]),
      tactic === "tauto" ? /tauto found a counterexample/u : /\.left requires a conjunction, found x ∈ both\(A, B\)/u);
  }
  assert.ok(registrationReport(load([{ file: "Registered.g17", source: header + law + registration }]))
    .some(item => item.form === "simp" && item.predicate === "Registered.both.membership" && item.module === "Registered" &&
      item.rules!.length === 1 && item.rules![0]!.rule === "theorem"));
});

test("a simp registration is exported with the module interface, read by the modules that import it, and unseen elsewhere", () => {
  const library = { file: "Registered.g17", source: header + law + registration };
  const client = load([library, { file: "Client.g17", source: "module Client\nimport Registered\n" + opened("simp at h\n  exact h.left") }]);
  assert.ok(client.theorems.has("Client.opened"));
  // A module that proves the same law under its own name, without
  // importing the registration, opens nothing.
  const stranger = "module Stranger\nimport Grace.Cumulus.Set.Basic\n" + law + opened("simp at h\n  exact h.left");
  assert.throws(() => load([library, { file: "Stranger.g17", source: stranger }]), /\.left requires a conjunction/u);
  // The complete index and the per-module delta carry the record with its
  // rules, and decode again.
  const kernel = load([{ file: "Base.g17", source: "module Base\nimport Grace.Cumulus.Set.Basic\n" }]);
  const baseline = captureSurfaceBaseline(kernel);
  elaborateModule(kernel, header + law + registration);
  const digest = "0".repeat(64);
  const index = decodeSurfaceEnvironmentIndex(encodeSurfaceEnvironmentIndex(exportSurfaceEnvironmentIndex(kernel, "Registered", digest)));
  assert.ok(index.registrations!.some(item => item.form === "simp" && item.predicate === "set.empty" && item.module === undefined));
  assert.ok(index.registrations!.some(item => item.form === "simp" && item.predicate === "Registered.both.membership"));
  const delta = decodeSurfaceEnvironmentDelta(encodeSurfaceEnvironmentDelta(exportSurfaceEnvironmentDelta(kernel, baseline, "Registered", digest)));
  assert.deepEqual(delta.registrations!.map(item => [item.form, item.predicate, item.module, item.rules]),
    [["simp", "Registered.both.membership", "Registered", [{ rule: "theorem", name: "Registered.both.membership" }]]]);
});

// A ring scope form of the module's own: the scope `S := R ⊕ T` keeps the
// operations of `R` on the carrier `T`, declared over two lines.
const ringHeader = "module Forms\nimport Grace.Cumulus.Algebra.Ring.Defs\n";
const ringRegistration = `register ring (A, add, zero, neg, mul, one) ⊕ B :=
  (B, add, zero, neg, mul, one)
`;
const scoped = (form: string) => `
section Rings
variable (A add zero neg mul one T : Set)
notation ring R := (A, add, zero, neg, mul, one)
notation ring S := ${form}
theorem identity
  requires ring : IsCommRing(S)
  shows IsCommRing(S)
proof
  exact ring
end Rings
`;

test("a ring registration of the module's own defines a scope form, read as the registered terms at the pieces of the base scope", () => {
  const written = load([{ file: "Forms.g17", source: ringHeader + ringRegistration + scoped("R ⊕ T") }]);
  const spelled = load([{ file: "Forms.g17", source: ringHeader + ringRegistration + scoped("(T, add, zero, neg, mul, one)") }]);
  assert.ok(formulaEquals(written.theorems.get("Forms.identity")!, spelled.theorems.get("Forms.identity")!));
  assert.throws(() => load([{ file: "Forms.g17", source: ringHeader + scoped("R ⊕ T") }]),
    /expected notation ring R := \(A, add, zero, neg, mul, one\)(?:, or a registered form: Q := R ⧸ I)?; no ring form R ⊕ I is registered in scope/u);
  assert.throws(() => load([{ file: "Forms.g17", source: ringHeader + ringRegistration + scoped("Missing ⊕ T") }]),
    /unknown base ring notation Missing in Missing ⊕ T/u);
  const kernel = load([{ file: "Base.g17", source: ringHeader }]);
  const baseline = captureSurfaceBaseline(kernel);
  elaborateModule(kernel, ringHeader.replace("module Forms", "module Forms2") + ringRegistration);
  const delta = decodeSurfaceEnvironmentDelta(encodeSurfaceEnvironmentDelta(exportSurfaceEnvironmentDelta(kernel, baseline, "Forms2", "0".repeat(64))));
  assert.deepEqual(delta.registrations!.map(item => [item.form, item.predicate, item.module, item.names, item.terms!.length]),
    [["ring", "⊕", "Forms2", ["A", "add", "zero", "neg", "mul", "one", "B"], 6]]);
});

test("a wrong simp or ring registration is reported at its line", () => {
  const declare = (text: string) => load([{ file: "Registered.g17", source: header + law + text + "\n" }]);
  assert.throws(() => declare("register simp nope"),
    /line 10: a simp registration names a theorem, an axiom, a definition, or a definition property; unknown settle rule nope/u);
  assert.throws(() => declare(registration + registration), /register simp both.membership is already declared in this module/u);
  assert.throws(() => declare("register ring (A, add) ⧸ I := (A, add, zero, neg, mul, one)"),
    /a ring registration names the six pieces of the base scope and the operand as distinct pattern variables/u);
  assert.throws(() => declare("register ring (A, add, zero, neg, mul, one) ⧸ A := (A, add, zero, neg, mul, one)"),
    /distinct pattern variables/u);
  assert.throws(() => declare("register ring (A, add, zero, neg, mul, one) ⧸ I := (A, add)"),
    /the result of a ring registration lists the six pieces of the scope it defines, \(carrier, add, zero, neg, mul, one\), in parentheses/u);
  assert.throws(() => declare("register ring (A, add, zero, neg, mul, one) ⧸ I := (A, add, zero, neg, mul, q)"),
    /the result of a ring registration must be terms over its pattern variables: .*q/u);
  assert.throws(() => declare("register ring (A, add, zero, neg, mul, one) ⧸ I := (A, add, zero, neg, mul, one)\nregister ring (A, add, zero, neg, mul, one) ⧸ I := (A, add, zero, neg, mul, one)"),
    /register ring ⧸ is already declared in this module/u);
  assert.throws(() => declare("register simp both.membership\nregister kinds Nope"), /line 11: expected `register kinds/u);
});
