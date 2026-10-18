// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { axiomAuditSummary, renderAxiomAudit, createAxiomAuditLoader, renderAxiomAuditAction } from "../workbench/axiom-audit.js";
import { auditWorkbenchTheorem } from "../src/workbench.ts";

const clean = { ok: true, theorem: "example", complete: true, direct: [], hereditary: [], axioms: [], mechanisms: [], unavailable: [], classicalLogic: false };

test("audit component distinguishes clean, Choice, and incomplete proofs and escapes names", () => {
  assert.match(renderAxiomAudit(clean), /No Choice axiom used/);
  assert.match(axiomAuditSummary(clean), /0 direct · 0 inherited/);
  const choice = { ...clean, hereditary: ["set.globalChoice"], axioms: [{ name: "set.globalChoice", statement: "<script>bad()</script>", direct: false, path: ["<img src=x>", "axiom set.globalChoice"] }] };
  assert.match(renderAxiomAudit(choice), /Choice is used/);
  assert.match(renderAxiomAudit(choice), /Inherited/);
  assert.doesNotMatch(renderAxiomAudit(choice), /<script>|<img/);
  assert.match(renderAxiomAudit({ ...clean, complete: false }), /Choice usage is undetermined/);
  assert.doesNotMatch(renderAxiomAudit({ ...clean, complete: false }), /No Choice axiom used/);
});

test("hover loader coalesces requests but invalidates on any workspace edit and retries failures", async () => {
  let calls = 0;
  let fail = false;
  const load = createAxiomAuditLoader(async () => { calls++; if (fail) throw new Error("failed"); return clean; });
  const payload = { files: [{ name: "a.g17", source: "old" }], activeFile: "a.g17" };
  await Promise.all([load("t", payload), load("t", payload)]);
  assert.equal(calls, 1);
  payload.files[0].source = "new";
  await load("t", payload);
  assert.equal(calls, 2);
  fail = true;
  await assert.rejects(load("another", payload));
  fail = false;
  await load("another", payload);
  assert.equal(calls, 4);
});

test("Workbench audits follow changed proof dependencies after editing", () => {
  const header = "module HoverAudit\nnamespace HoverAudit\ntheorem result\n  shows empty = empty\nproof\n";
  const file = { name: "HoverAudit.g17", source: header + "  rfl\nend HoverAudit\n" };
  const first = auditWorkbenchTheorem([file], "HoverAudit.result", "ZF", [file.name]);
  assert.equal(first.complete, true);
  assert.deepEqual(first.hereditary, []);
  file.source = header + "  sorry\nend HoverAudit\n";
  const edited = auditWorkbenchTheorem([file], "HoverAudit.result", "ZF", [file.name]);
  assert.ok(edited.hereditary.some(name => name.includes("sorry")));
});

test("browser audit follows a precompiled rational theorem without source replay", async () => {
  const browser = await import("../workbench/generated/src/workbench.js");
  const files = [{ name: "CompiledAudit.g17", source: "module CompiledAudit\nimport Grace.Cumulus.Rat.Operations\n" }];
  browser.prepareWorkbenchFiles(files, "ZFG", files[0].name);
  const audit = browser.auditWorkbenchTheorem(files,
    "Grace.Cumulus.Rat.Operations.rationalClass.eq", "ZFG", [files[0].name]);
  assert.equal(audit.complete, true, JSON.stringify(audit.unavailable));
  assert.ok(!audit.hereditary.some((name: string) => /choice/i.test(name)));
  assert.ok(audit.visited > 1);
});

test("the quiet audit action appears only at current QED, including sorries", () => {
  const theorem = { name: 'Example.<theorem>"', sorries: [] };
  assert.equal(renderAxiomAuditAction({ goals: [{}] }, theorem), "");
  assert.equal(renderAxiomAuditAction(undefined, theorem), "");
  assert.equal(renderAxiomAuditAction({ goals: [] }, undefined), "");
  assert.equal(renderAxiomAuditAction({ goals: [] }, theorem, false), "");
  const action = renderAxiomAuditAction({ goals: [] }, theorem);
  assert.match(action, />Axioms<\/button>/);
  assert.match(action, /data-axiom-audit="Example.&lt;theorem&gt;&quot;"/);
  assert.equal(renderAxiomAuditAction({ goals: [] }, { ...theorem, sorries: [{}] }), action);
});
