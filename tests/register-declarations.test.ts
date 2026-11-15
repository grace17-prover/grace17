// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// `register` declarations: the kinds of element a structure has, how a
// structure's values apply by their fields, and the facts a fact shape gives.
// They are parsed beside the notations, exported through the module
// interface, drive the dispatch of `F(x)` and its printing, report a wrong
// declaration, and give a module that lacks them no special treatment.

import assert from "node:assert/strict";
import test from "node:test";
import { createZfKernel, formulaEquals, loadModuleSourceGraph } from "../src/index.ts";
import {
  captureSurfaceBaseline, decodeSurfaceEnvironmentDelta, decodeSurfaceEnvironmentIndex, elaborateModule,
  encodeSurfaceEnvironmentDelta, encodeSurfaceEnvironmentIndex, exportSurfaceEnvironmentDelta, exportSurfaceEnvironmentIndex,
  registrationReport,
} from "../src/surface.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

// A structure of its own, applied by two fields over the kinds Category
// registers: the library's Functor is left aside so that the registration
// under test is the one the module declares.
const structure = `
structure Endo (C : Set)
  | obj map : Set
  where
    category : Category(C)
    objects : obj : C.obj → C.obj
    morphisms : map : C.mor → C.mor
`;
const registration = "register application Endo(E, C) over C object obj morphism map\n";
const header = "module Registered\nimport Grace.Cumulus.Category.Core\n";

function load(files: readonly { readonly file: string; readonly source: string }[]) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, files, ["lib"]);
  return kernel;
}

const applied = (conclusion: string) => `
theorem applied (E C a b f : Set)
  requires category : Category(C)
  requires endo : Endo(E, C)
  requires aIn : a ∈ obj(C)
  requires bIn : b ∈ obj(C)
  requires fHom : f : a ⟶ b
  shows ${conclusion}
proof
  constructor
  . rfl
  . rfl
`;

test("the library registers the kinds of a category, the application of a functor, and the facts of arrows, and the listing shows them", () => {
  const result = checkWorkbenchFiles([{ name: "Registered.g17", source: "module Registered\nimport Grace.Cumulus.Category.Natural\n" }]);
  assert.equal(result.ok, true);
  const registrations = result.registrations;
  const kinds = registrations.find(item => item.form === "kinds" && item.predicate.endsWith(".Category"));
  assert.ok(kinds, JSON.stringify(registrations));
  assert.equal(kinds.module, "Grace.Cumulus.Category.Core");
  assert.deepEqual(kinds.kinds!.map(item => [item.name, item.projection.split(".").at(-1)]), [["object", "obj"], ["morphism", "mor"]]);
  const application = registrations.find(item => item.form === "application" && item.predicate.endsWith(".Functor"));
  assert.ok(application);
  assert.equal(application.module, "Grace.Cumulus.Category.Functor");
  assert.deepEqual(application.names, ["F", "C", "D"]);
  assert.equal(application.over, 1);
  assert.deepEqual(application.kinds!.map(item => [item.name, item.projection.split(".").at(-1)]), [["object", "obj"], ["morphism", "map"]]);
  const facts = registrations.filter(item => item.form === "facts").map(item => item.predicate.split(".").at(-1));
  assert.deepEqual(facts.sort(), ["Morphism", "NaturalTransformation", "hom"]);
  const natural = registrations.find(item => item.form === "facts" && item.predicate.endsWith("NaturalTransformation"))!;
  assert.equal(natural.with!.length, 2);
  assert.equal(natural.gives!.length, 1);
  assert.deepEqual([...natural.variables!].sort(), ["C", "D", "F", "G", "η"]);
});

test("an application registration dispatches F(x) by the kind the facts give x, and the statement prints F applied", () => {
  const source = header + structure + registration;
  const written = load([{ file: "Registered.g17", source: source + applied("E(f) = E(f) ∧ E(a) = E(a)") }]);
  const spelled = load([{ file: "Registered.g17", source: source + applied("map(E)(f) = map(E)(f) ∧ obj(E)(a) = obj(E)(a)") }]);
  assert.ok(formulaEquals(written.theorems.get("Registered.applied")!, spelled.theorems.get("Registered.applied")!));
  const result = checkWorkbenchFiles([{ name: "Registered.g17", source: source + applied("E(f) = E(f) ∧ E(a) = E(a)") }]);
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 600));
  assert.match(result.theorems.find(item => item.name === "Registered.applied")!.statement, /E\(f\) = E\(f\) ∧ E\(a\) = E\(a\)$/u);
  assert.ok(registrationReport(written).some(item => item.form === "application" && item.predicate === "Registered.Endo" && item.module === "Registered"));
});

test("a module without the registration gets no special treatment: E(x) is the function applied, and it prints so", () => {
  const source = header + structure;
  const written = load([{ file: "Registered.g17", source: source + applied("E(a) = E(a) ∧ E(f) = E(f)") }]);
  const spelled = load([{ file: "Registered.g17", source: source + applied("apply(E, a) = apply(E, a) ∧ apply(E, f) = apply(E, f)") }]);
  assert.ok(formulaEquals(written.theorems.get("Registered.applied")!, spelled.theorems.get("Registered.applied")!));
  const result = checkWorkbenchFiles([{ name: "Registered.g17", source: source + applied("obj(E)(a) = obj(E)(a) ∧ map(E)(f) = map(E)(f)") }]);
  assert.equal(result.ok, true);
  assert.match(result.theorems.find(item => item.name === "Registered.applied")!.statement, /E\.obj\(a\) = E\.obj\(a\) ∧ E\.map\(f\) = E\.map\(f\)$/u);
});

test("an argument the facts place in no kind is an error naming the kinds and both spellings", () => {
  assert.throws(() => load([{ file: "Registered.g17", source: header + structure + registration + `
theorem loose (E C x : Set)
  requires category : Category(C)
  requires endo : Endo(E, C)
  shows E(x) = E(x)
proof
  rfl
` }]), /E is an endo, and x is not known to be an object or a morphism of C; add a binder such as \(x ∈ C\.obj\) or \(x ∈ C\.mor\), or write obj\(E\)\(x\) for an object and map\(E\)\(x\) for a morphism/u);
});

test("a registration is exported with the module interface and read by the modules that import it", () => {
  const client = `module Client
import Registered
` + applied("E(f) = E(f) ∧ E(a) = E(a)");
  const spelledClient = `module Client
import Registered
` + applied("map(E)(f) = map(E)(f) ∧ obj(E)(a) = obj(E)(a)");
  const library = { file: "Registered.g17", source: header + structure + registration };
  const written = load([library, { file: "Client.g17", source: client }]);
  const spelled = load([library, { file: "Client.g17", source: spelledClient }]);
  assert.ok(formulaEquals(written.theorems.get("Client.applied")!, spelled.theorems.get("Client.applied")!));
  // A module that does not import the declaring module reads E(a) as the
  // function applied, whatever the kernel holds.
  const stranger = `module Stranger
import Grace.Cumulus.Category.Core
` + structure.replace("Endo", "Endo2") + applied("E(a) = E(a) ∧ E(f) = E(f)").replace("Endo(E, C)", "Endo2(E, C)");
  const spelledStranger = stranger.replace("shows E(a) = E(a) ∧ E(f) = E(f)", "shows apply(E, a) = apply(E, a) ∧ apply(E, f) = apply(E, f)");
  const apart = load([library, { file: "Stranger.g17", source: stranger }]);
  const apartSpelled = load([library, { file: "Stranger.g17", source: spelledStranger }]);
  assert.ok(formulaEquals(apart.theorems.get("Stranger.applied")!, apartSpelled.theorems.get("Stranger.applied")!));
  // The complete index and the per-module delta both carry the records and
  // decode again, the delta holding only what the module added.
  const kernel = load([{ file: "Base.g17", source: "module Base\nimport Grace.Cumulus.Category.Core\n" }]);
  const baseline = captureSurfaceBaseline(kernel);
  elaborateModule(kernel, header + structure + registration);
  const digest = "0".repeat(64);
  const index = decodeSurfaceEnvironmentIndex(encodeSurfaceEnvironmentIndex(exportSurfaceEnvironmentIndex(kernel, "Registered", digest)));
  assert.ok(index.registrations!.some(item => item.form === "kinds" && item.module === "Grace.Cumulus.Category.Core"));
  assert.ok(index.registrations!.some(item => item.form === "application" && item.predicate === "Registered.Endo"));
  const delta = decodeSurfaceEnvironmentDelta(encodeSurfaceEnvironmentDelta(exportSurfaceEnvironmentDelta(kernel, baseline, "Registered", digest)));
  assert.deepEqual(delta.registrations!.map(item => [item.form, item.predicate, item.module]), [["application", "Registered.Endo", "Registered"]]);
});

test("a wrong registration is reported at its line", () => {
  const declare = (text: string) => load([{ file: "Registered.g17", source: header + structure + text + "\n" }]);
  assert.throws(() => declare("register kinds Category object nope morphism mor"),
    /line \d+: nope is not a field of Category; its fields are obj, mor, dom, cod, id, comp/u);
  assert.throws(() => declare("register application Endo(E, C) over C thing obj morphism map"),
    /no `register kinds` declaration in scope names the kind thing/u);
  assert.throws(() => declare("register application Endo(E, C) over X object obj morphism map"),
    /`over` names one of the pattern variables after the applied structure, C; found X/u);
  assert.throws(() => declare("register application Nope(E, C) over C object obj"),
    /unknown register application structure predicate Nope/u);
  assert.throws(() => declare("register facts Morphism(C, f, a, b) gives f ∈ C.mor ∧ q ∈ C.obj"),
    /the gives clause of a facts registration must be a formula over its variables: .*unknown variable or constant q/u);
  assert.throws(() => declare("register facts f = g gives f ∈ C.mor"),
    /the pattern of a facts registration is a predicate fact or a membership in a function value/u);
  assert.throws(() => declare("register nonsense Endo"), /expected `register kinds Category object obj morphism mor`/u);
  assert.throws(() => declare(registration + registration), /register application Endo is already declared in this module/u);
});
