// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// `register largecardinal`: a predicate registered as a large cardinal
// hypothesis is reported, by the polarity of its occurrences, for every
// theorem that assumes it: in the axiom audit with the lemma that brought it
// in, in the checked theorem, and in the Workbench. The registration is
// exported with the module and changes no statement and no proof.

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

theorem huge.self (κ : Set)
  requires h : Huge(κ)
  shows κ ∈ κ
proof
  exact h
`;

const uses = `module Uses
import Hypotheses

theorem through.lemma (κ : Set)
  requires h : Huge(κ)
  shows κ ∈ κ
proof
  exact huge.self with h

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

test("a theorem assumes a large cardinal hypothesis in negative position and only mentions it in positive position", () => {
  const kernel = load();
  const names = (items: readonly { readonly predicate: string }[]) => items.map(item => item.predicate);
  assert.deepEqual(names(theoremLargeCardinals(kernel, "Uses.through.lemma").assumes), ["Hypotheses.Huge"]);
  assert.deepEqual(theoremLargeCardinals(kernel, "Uses.through.lemma").assumes[0]!.label, "a huge cardinal");
  const proves = theoremLargeCardinals(kernel, "Uses.proves.only");
  assert.deepEqual(names(proves.assumes), []);
  assert.deepEqual(names(proves.mentions), ["Hypotheses.Vast"]);
  // ¬Huge(κ) → … is (Huge(κ) → ⊥) → …: Huge occurs positively.
  assert.deepEqual(names(theoremLargeCardinals(kernel, "Uses.under.negation").assumes), []);
  assert.deepEqual(theoremLargeCardinals(kernel, "Uses.plain"), { assumes: [], mentions: [] });
  // An equivalence assumes both of its sides.
  const huge = { tag: "pred", pred: "Hypotheses.Huge", args: [{ tag: "var", name: "x" }] } as const;
  const vast = { tag: "pred", pred: "Hypotheses.Vast", args: [{ tag: "var", name: "x" }] } as const;
  assert.deepEqual(names(largeCardinalOccurrences(kernel, { tag: "iff", left: huge, right: vast } as never).assumes),
    ["Hypotheses.Huge", "Hypotheses.Vast"]);
});

test("the axiom audit names each hypothesis with the lemma that assumes it", () => {
  const kernel = load();
  const audit = auditTheoremAxioms(kernel, "Uses.through.lemma");
  assert.deepEqual(audit.largeCardinals.assumes, [{
    predicate: "Hypotheses.Huge", label: "a huge cardinal", module: "Hypotheses",
    path: ["Uses.through.lemma", "Hypotheses.huge.self"],
  }]);
  // A premise no lemma assumes is the theorem's own.
  assert.deepEqual(auditTheoremAxioms(kernel, "Hypotheses.huge.self").largeCardinals.assumes[0]!.path, ["Hypotheses.huge.self"]);
  assert.deepEqual(auditTheoremAxioms(kernel, "Uses.plain").largeCardinals, { assumes: [], mentions: [] });
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
    [["largecardinal", "Hypotheses.Huge", "a huge cardinal"], ["largecardinal", "Hypotheses.Vast", "a vast cardinal"]]);
});

test("a wrong large cardinal registration is reported at its line", () => {
  const declare = (text: string) => loadModuleSourceGraph(createZfKernel(),
    [{ file: "Wrong.g17", source: `module Wrong\nimport Grace.Core\npredicate Huge (κ : Set) := κ ∈ κ\n${text}\n` }], ["lib"]);
  assert.throws(() => declare(`register largecardinal Nothing "no such predicate"`), /line 4:/u);
  assert.throws(() => declare(`register largecardinal Huge "a huge cardinal"\nregister largecardinal Huge "again"`),
    /line 5: register largecardinal Huge is already declared in this module/u);
  assert.throws(() => declare("register largecardinal Huge"), /line 4: expected/u);
});

test("a checked theorem carries the hypotheses it assumes, and the Workbench shows them", () => {
  const result = checkWorkbenchFiles([
    { name: "Hypotheses.g17", source: hypotheses },
    { name: "Uses.g17", source: uses },
  ], "ZF", ["Uses.g17"], { includeKernelDetails: false });
  assert.equal(result.ok, true);
  const theorem = (name: string) => result.theorems.find(item => item.name === name)!;
  assert.deepEqual(theorem("Uses.through.lemma").largeCardinals, [{ predicate: "Hypotheses.Huge", label: "a huge cardinal" }]);
  assert.equal(theorem("Uses.plain").largeCardinals, undefined);
  assert.equal(theorem("Uses.proves.only").largeCardinals, undefined);
  assert.match(renderLargeCardinalBadge(theorem("Uses.through.lemma")), /assumes a huge cardinal/u);
  assert.equal(renderLargeCardinalBadge(theorem("Uses.plain")), "");
  assert.match(renderLargeCardinalBadge({ largeCardinals: [{ predicate: "<b>", label: "<script>x</script>" }] }), /&lt;script&gt;/u);

  const audit = { ok: true, ...auditTheoremAxioms(load(), "Uses.through.lemma") };
  assert.match(axiomAuditSummary(audit), /assumes a huge cardinal$/u);
  const panel = renderAxiomAudit(audit);
  assert.match(panel, /Large cardinal hypotheses/u);
  assert.match(panel, /Assumes a huge cardinal/u);
  assert.match(panel, /Hypotheses\.huge\.self/u);
  const clean = { ok: true, ...auditTheoremAxioms(load(), "Uses.plain") };
  assert.doesNotMatch(renderAxiomAudit(clean), /Large cardinal/u);
  // An audit from before large cardinal reports still renders.
  const { largeCardinals: _, ...older } = clean;
  assert.doesNotMatch(renderAxiomAudit(older), /Large cardinal/u);
});
