// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// `register largecardinal`: a theorem relies on a registered hypothesis when
// it has it as a premise about something its conclusion does not mention (a
// sentence, or "if some κ is huge"), when a lemma it uses relies on it, or
// when it uses a lemma about it without a premise of its own that supplies
// it. A theorem with the premise about something its conclusion mentions is
// a fact about such objects and relies on nothing. The axiom audit reports
// this over the whole proof, the checked theorem and the Workbench badge from
// the statement. The registration is exported with the module and changes
// no statement and no proof.

import assert from "node:assert/strict";
import test from "node:test";
import { auditTheoremAxioms, createZfKernel, loadModuleSourceGraph } from "../src/index.ts";
import {
  captureSurfaceBaseline, decodeSurfaceEnvironmentDelta, decodeSurfaceEnvironmentIndex, elaborateModule,
  encodeSurfaceEnvironmentDelta, encodeSurfaceEnvironmentIndex, exportSurfaceEnvironmentDelta, exportSurfaceEnvironmentIndex,
} from "../src/surface.ts";
import { largeCardinalOccurrences, theoremLargeCardinals } from "../src/large-cardinals.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";
import { axiomAuditSummary, renderAxiomAudit, renderLargeCardinalBadge } from "../workbench/axiom-audit.js";

const hypotheses = `module Hypotheses
import Grace.Core

predicate Huge (κ : Set) := κ ∈ κ
register largecardinal Huge "a huge cardinal"
predicate Vast (κ : Set) := κ ∈ κ
register largecardinal Vast "a vast cardinal"
predicate Big := ∃ κ, κ ∈ κ
register largecardinal Big "a huge cardinal exists"

-- About huge cardinals: true whether or not one exists.
theorem huge.self (κ : Set)
  requires h : Huge(κ)
  shows κ ∈ κ
proof
  exact h

-- Relies on one existing: κ is not in the conclusion.
theorem huge.anything (κ x : Set)
  requires h : Huge(κ)
  shows x = x
proof
  rfl

theorem big.anything (x : Set)
  requires h : Big()
  shows x = x
proof
  rfl
`;

const uses = `module Uses
import Hypotheses

theorem through.about (κ : Set)
  requires h : Huge(κ)
  shows κ ∈ κ
proof
  exact huge.self with h

theorem through.relies (κ : Set)
  requires h : Huge(κ)
  shows κ ∈ κ ∧ κ = κ
proof
  constructor
  . exact h
  . exact huge.anything at κ, κ with h

theorem supplies (κ : Set)
  requires m : κ ∈ κ
  shows κ ∈ κ
proof
  have huge : Huge(κ) by exact m
  exact huge.self with huge

theorem relies.here (κ x : Set)
  requires h : Huge(κ)
  shows x = x
proof
  rfl

theorem proves.only (κ : Set)
  requires h : κ ∈ κ
  shows Vast(κ)
proof
  exact h

theorem under.negation (κ : Set)
  requires h : κ ∈ κ
  shows ¬Huge(κ) → κ ∈ κ
proof
  intro _
  exact h

theorem plain (x : Set)
  shows x = x
proof
  rfl
`;

function load() {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [
    { file: "Hypotheses.g17", source: hypotheses },
    { file: "Uses.g17", source: uses },
  ], ["lib"]);
  return kernel;
}

const names = (items: readonly { readonly predicate: string }[]) => items.map(item => item.predicate);

test("a statement relies on a hypothesis about what its conclusion does not mention, and is about one whose object it mentions", () => {
  const kernel = load();
  const of = (name: string) => theoremLargeCardinals(kernel, name);
  assert.deepEqual(names(of("Hypotheses.huge.anything").reliesOn), ["Hypotheses.Huge"]);
  assert.deepEqual(of("Hypotheses.huge.anything").reliesOn[0]!.label, "a huge cardinal");
  assert.deepEqual(names(of("Hypotheses.big.anything").reliesOn), ["Hypotheses.Big"]);
  assert.deepEqual(names(of("Hypotheses.huge.self").reliesOn), []);
  assert.deepEqual(names(of("Hypotheses.huge.self").about), ["Hypotheses.Huge"]);
  assert.deepEqual(names(of("Uses.proves.only").reliesOn), []);
  assert.deepEqual(names(of("Uses.proves.only").mentions), ["Hypotheses.Vast"]);
  // ¬Huge(κ) → … is (Huge(κ) → ⊥) → …: Huge occurs positively.
  assert.deepEqual(names(of("Uses.under.negation").reliesOn), []);
  assert.deepEqual(of("Uses.plain"), { reliesOn: [], about: [], mentions: [] });
  // A negated conclusion is a conclusion: Huge(κ) → ¬(κ = ∅) is about κ.
  const negated = largeCardinalOccurrences(kernel, { tag: "forall", variable: "k", body: { tag: "imp",
    left: { tag: "pred", pred: "Hypotheses.Huge", args: [{ tag: "var", name: "k" }] },
    right: { tag: "imp", left: { tag: "eq", left: { tag: "var", name: "k" }, right: { tag: "app", fn: "empty", args: [] } }, right: { tag: "bottom" } } } } as never);
  assert.deepEqual([names(negated.reliesOn), names(negated.about)], [[], ["Hypotheses.Huge"]]);
  // An equivalence rests on neither side.
  const huge = { tag: "pred", pred: "Hypotheses.Huge", args: [{ tag: "var", name: "x" }] } as const;
  const big = { tag: "pred", pred: "Hypotheses.Big", args: [] } as const;
  const equivalence = largeCardinalOccurrences(kernel, { tag: "forall", variable: "x", body: { tag: "iff", left: huge, right: big } } as never);
  assert.deepEqual([names(equivalence.reliesOn), names(equivalence.mentions)], [[], ["Hypotheses.Big", "Hypotheses.Huge"]]);
});

test("the axiom audit follows reliance through the proof, with where it starts", () => {
  const kernel = load();
  const audit = (name: string) => auditTheoremAxioms(kernel, name).largeCardinals;
  // About huge cardinals, through a lemma about them: relies on nothing.
  assert.deepEqual(audit("Uses.through.about"), {
    reliesOn: [], about: [{ predicate: "Hypotheses.Huge", label: "a huge cardinal", module: "Hypotheses" }], mentions: [],
  });
  // About huge cardinals by its statement, but a lemma it uses relies on one existing.
  assert.deepEqual(audit("Uses.through.relies").reliesOn, [{
    predicate: "Hypotheses.Huge", label: "a huge cardinal", module: "Hypotheses",
    via: "premise", path: ["Uses.through.relies", "Hypotheses.huge.anything"],
  }]);
  assert.deepEqual(audit("Uses.through.relies").about, []);
  // Uses a lemma about huge cardinals without a premise that supplies one.
  assert.deepEqual(audit("Uses.supplies").reliesOn, [{
    predicate: "Hypotheses.Huge", label: "a huge cardinal", module: "Hypotheses",
    via: "supplied", path: ["Uses.supplies"], lemma: "Hypotheses.huge.self",
  }]);
  assert.deepEqual(audit("Uses.relies.here").reliesOn.map(item => [item.via, item.path]), [["premise", ["Uses.relies.here"]]]);
  assert.deepEqual(audit("Uses.plain"), { reliesOn: [], about: [], mentions: [] });
});

test("the registration is exported with the module, in the index and in the delta", () => {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "Base.g17", source: "module Base\nimport Grace.Core\n" }], ["lib"]);
  const baseline = captureSurfaceBaseline(kernel);
  elaborateModule(kernel, hypotheses);
  const digest = "0".repeat(64);
  const index = decodeSurfaceEnvironmentIndex(encodeSurfaceEnvironmentIndex(exportSurfaceEnvironmentIndex(kernel, "Hypotheses", digest)));
  assert.ok(index.registrations!.some(item => item.form === "largecardinal" && item.predicate === "Hypotheses.Huge" && item.label === "a huge cardinal"));
  const delta = decodeSurfaceEnvironmentDelta(encodeSurfaceEnvironmentDelta(exportSurfaceEnvironmentDelta(kernel, baseline, "Hypotheses", digest)));
  assert.deepEqual(delta.registrations!.map(item => [item.form, item.predicate, item.label]),
    [["largecardinal", "Hypotheses.Huge", "a huge cardinal"], ["largecardinal", "Hypotheses.Vast", "a vast cardinal"],
      ["largecardinal", "Hypotheses.Big", "a huge cardinal exists"]]);
});

test("a wrong large cardinal registration is reported at its line", () => {
  const declare = (text: string) => loadModuleSourceGraph(createZfKernel(),
    [{ file: "Wrong.g17", source: `module Wrong\nimport Grace.Core\npredicate Huge (κ : Set) := κ ∈ κ\n${text}\n` }], ["lib"]);
  assert.throws(() => declare(`register largecardinal Nothing "no such predicate"`), /line 4:/u);
  assert.throws(() => declare(`register largecardinal Huge "a huge cardinal"\nregister largecardinal Huge "again"`),
    /line 5: register largecardinal Huge is already declared in this module/u);
  assert.throws(() => declare("register largecardinal Huge"), /line 4: expected/u);
});

test("a checked theorem carries the hypotheses its statement relies on, and the Workbench shows them", () => {
  const result = checkWorkbenchFiles([
    { name: "Hypotheses.g17", source: hypotheses },
    { name: "Uses.g17", source: uses },
  ], "ZF", ["Uses.g17"], { includeKernelDetails: false });
  assert.equal(result.ok, true);
  const theorem = (name: string) => result.theorems.find(item => item.name === name)!;
  assert.deepEqual(theorem("Uses.relies.here").largeCardinals, [{ predicate: "Hypotheses.Huge", label: "a huge cardinal" }]);
  for (const name of ["Uses.plain", "Uses.proves.only", "Uses.through.about"]) assert.equal(theorem(name).largeCardinals, undefined);
  assert.match(renderLargeCardinalBadge(theorem("Uses.relies.here")), /relies on a huge cardinal/u);
  assert.equal(renderLargeCardinalBadge(theorem("Uses.plain")), "");
  assert.match(renderLargeCardinalBadge({ largeCardinals: [{ predicate: "<b>", label: "<script>x</script>" }] }), /&lt;script&gt;/u);

  const kernel = load();
  const supplies = { ok: true, ...auditTheoremAxioms(kernel, "Uses.supplies") };
  assert.match(axiomAuditSummary(supplies), /relies on a huge cardinal$/u);
  const panel = renderAxiomAudit(supplies);
  assert.match(panel, /Relies on a large cardinal hypothesis: a huge cardinal/u);
  assert.match(panel, /This result relies on a large cardinal hypothesis/u);
  assert.match(panel, /Hypotheses\.huge\.self/u);
  const about = renderAxiomAudit({ ok: true, ...auditTheoremAxioms(kernel, "Uses.through.about") });
  assert.match(about, /holds whether or not they do/u);
  assert.doesNotMatch(about, /Relies on/u);
  const clean = { ok: true, ...auditTheoremAxioms(kernel, "Uses.plain") };
  assert.doesNotMatch(renderAxiomAudit(clean), /Large cardinal/u);
  // An audit from before large cardinal reports still renders.
  const { largeCardinals: _, ...older } = clean;
  assert.doesNotMatch(renderAxiomAudit(older), /Large cardinal/u);
});

test("the library's large cardinal hypotheses are registered and classified", () => {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "UsesAxioms.g17", source: "module UsesAxioms\nimport Grace.Cumulus.LargeCardinal.Axioms\n" }], ["lib"]);
  const area = "Grace.Cumulus.LargeCardinal";
  const audit = (name: string) => auditTheoremAxioms(kernel, `${area}.${name}`).largeCardinals;
  // Under TarskiGrothendieck an inaccessible exists: relies on the axiom.
  const exists = audit("Axioms.TarskiGrothendieck.existsInaccessible");
  assert.deepEqual(exists.reliesOn.map(item => [item.predicate, item.via, item.path]),
    [[`${area}.Axioms.TarskiGrothendieck`, "premise", [`${area}.Axioms.TarskiGrothendieck.existsInaccessible`]]]);
  assert.deepEqual(names(exists.mentions), [`${area}.Axioms.ExistsInaccessible`]);
  // Every set lies in V(κ) for an inaccessible κ: the universe it gives
  // Williamson's theorem comes from the axiom, whose definition mentions
  // universes, so the axiom is all it relies on.
  assert.deepEqual(names(audit("Axioms.TarskiGrothendieck.inaccessible_containing").reliesOn), [`${area}.Axioms.TarskiGrothendieck`]);
  // Williamson's theorem is a theorem of ZF about universes, and the
  // equivalence of the two existence statements rests on neither.
  assert.deepEqual(audit("Inaccessible.GrothendieckUniverse.eq_V").reliesOn, []);
  assert.deepEqual(names(audit("Inaccessible.GrothendieckUniverse.eq_V").about), [`${area}.Universe.GrothendieckUniverse`]);
  assert.deepEqual(audit("Axioms.ExistsInaccessible.iff_exists_universe").reliesOn, []);
  assert.equal(auditTheoremAxioms(kernel, `${area}.Axioms.TarskiGrothendieck.existsInaccessible`).hereditary.some(name => /choice/iu.test(name)), false);
});
