// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { mkdtempSync, writeFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { auditTheoremAxioms, createZfKernel, createZfgKernel, loadModuleGraph,
  induction, compileProofModule, exportTheoremForMachine, axiom, theorem, definition, refl, app, v, eq, exists, forall, and, imp } from "../src/index.ts";

 test("audit separates local axioms from hereditary uses and ignores unused assumptions", () => {
  const k = createZfKernel();
  const statement = eq(app("empty"), app("empty"));
  k.addAxiom("custom.used", statement);
  k.addAxiom("custom.unused", statement);
  k.addTheorem("leaf", statement, axiom("custom.used"));
  k.addTheorem("middle", statement, theorem("leaf"));
  k.addTheorem("root", statement, theorem("middle"));
  assert.deepEqual(auditTheoremAxioms(k, "leaf").direct, ["custom.used"]);
  const audit = auditTheoremAxioms(k, "root");
  assert.equal(audit.complete, true);
  assert.deepEqual(audit.direct, []);
  assert.deepEqual(audit.hereditary, ["custom.used"]);
  assert.deepEqual(audit.axioms[0].path, ["root", "middle", "leaf", "axiom custom.used"]);
  k.addTheorem("reflexive", statement, refl(app("empty")));
  assert.deepEqual(auditTheoremAxioms(k, "reflexive").hereditary, []);
});

test("audit follows definition admission certificates, not only named theorem references", () => {
  const k = createZfKernel();
  const relation = eq(v("x"), app("empty"));
  const unique = exists("x", and(relation,
    forall("y", imp(eq(v("y"), app("empty")), eq(v("y"), v("x"))))));
  k.addAxiom("custom.existence", unique);
  k.defineUniqueFunction({ name: "described", parameters: [], value: "x", relation,
    existsUnique: axiom("custom.existence") });
  k.addTheorem("descriptionLaw", k.definitions.get("described")!.properties.get("characterization")!,
    definition("described", "characterization"));
  const audit = auditTheoremAxioms(k, "descriptionLaw");
  assert.equal(audit.complete, true);
  assert.deepEqual(audit.direct, []);
  assert.deepEqual(audit.hereditary, ["custom.existence"]);
  assert.deepEqual(audit.axioms[0].path, ["descriptionLaw", "definition described", "axiom custom.existence"]);
  assert.equal(audit.mechanisms[0].kind, "unique-description");
});

test("missing retained proofs produce an incomplete audit, never a clean result", () => {
  const k = createZfKernel();
  const statement = eq(app("empty"), app("empty"));
  k.addTheorem("lost", statement, refl(app("empty")));
  k.addTheorem("caller", statement, theorem("lost"));
  k.theoremProofs.delete("lost");
  const audit = auditTheoremAxioms(k, "caller");
  assert.equal(audit.complete, false);
  assert.deepEqual(audit.unavailable, [{ name: "lost", path: ["caller", "lost"] }]);
});

test("Choice is visible directly and through ordinary library theorems", () => {
  const k = createZfgKernel();
  loadModuleGraph(k, ["lib/Grace/Cumulus/Set/Choice.g17"], ["lib"]);
  const name = "Grace.Cumulus.Set.Choice.choose.member";
  const selected = auditTheoremAxioms(k, name);
  assert.equal(selected.complete, true);
  assert.ok(selected.direct.includes("set.globalChoice"));
  k.addTheorem("useChoice", k.theorems.get(name)!, theorem(name));
  const inherited = auditTheoremAxioms(k, "useChoice");
  assert.deepEqual(inherited.direct, []);
  assert.ok(inherited.hereditary.includes("set.globalChoice"));
});

test("CLI emits a machine-readable audit and reports admitted sorry axioms", () => {
  const directory = mkdtempSync(join(tmpdir(), "grace-audit-"));
  try {
    const file = join(directory, "Audit.g17");
    writeFileSync(file, "module Audit\nnamespace Audit\ntheorem admitted\n  shows empty = empty\nproof\n  sorry\ntheorem inherited\n  shows empty = empty\nproof\n  exact admitted\nend Audit\n");
    const result = JSON.parse(execFileSync(process.execPath, ["--disable-warning=ExperimentalWarning", "bin/g17.ts", "axiom-audit", "--json", file, "--theorem", "Audit.inherited"], { encoding: "utf8" }));
    assert.equal(result.complete, true);
    assert.deepEqual(result.direct, []);
    assert.equal(result.hereditary.length, 1);
    assert.match(result.hereditary[0], /sorry/);
    assert.throws(() => execFileSync(process.execPath, ["--disable-warning=ExperimentalWarning", "bin/g17.ts", "axiom-audit", "--json", file, "--theorem", "missing"], { stdio: "pipe" }));
  } finally { rmSync(directory, { recursive: true, force: true }); }
});

test("machine-replayed proofs retain complete local and hereditary audits across forks", () => {
  const base = createZfKernel();
  const statement = eq(app("empty"), app("empty"));
  base.addAxiom("machine.used", statement);
  const source = base.fork();
  source.addTheorem("machineLeaf", statement, axiom("machine.used"));
  source.addTheorem("machineCaller", statement, theorem("machineLeaf"));
  const names = ["machineLeaf", "machineCaller"];
  const program = compileProofModule(names.map(name => ({ ...exportTheoremForMachine(source, name), environment: base.digest() })));
  base.addTheoremMachineBatch(names.map(name => ({ name, statement })), program);
  assert.equal(base.theoremProofs.has("machineCaller"), false);
  const audit = auditTheoremAxioms(base.fork(), "machineCaller");
  assert.equal(audit.complete, true);
  assert.deepEqual(audit.direct, []);
  assert.deepEqual(audit.hereditary, ["machine.used"]);
  assert.deepEqual(audit.axioms[0].path, ["machineCaller", "machineLeaf", "axiom machine.used"]);
  assert.equal(Object.isFrozen(program.code), true);
});

test("natural induction reports its implicit least-inductive-set axiom", () => {
  const k = createZfKernel();
  const proof = induction("Naturals", "n", eq(v("n"), v("n")), [
    { constructor: "zero", fields: [], proof: refl(app("zero")) },
    { constructor: "succ", fields: ["k"], proof: refl(app("succ", v("k"))) },
  ]);
  k.addTheorem("byInduction", k.checkProof(proof), proof);
  const audit = auditTheoremAxioms(k, "byInduction");
  assert.equal(audit.complete, true);
  assert.deepEqual(audit.direct, []);
  assert.ok(audit.hereditary.includes("set.infinity.minimal"));
  assert.ok(audit.mechanisms.some(item => item.kind === "natural-induction"));
});
