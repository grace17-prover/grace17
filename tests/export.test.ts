// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, readFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import {
  createZfgKernel, elaborateModule, exportTheorem, formulaEquals, renderProofHtml,
  verifyExportedProof,
} from "../src/index.ts";

const project = fileURLToPath(new URL("..", import.meta.url));
const sets = readFileSync(fileURLToPath(new URL("../examples/Sets.g17", import.meta.url)), "utf8");

test("retains, exports, and independently verifies theorem proof DAGs", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, sets);
  const exported = exportTheorem(kernel, "pair.left");
  assert.equal(exported.format, "grace17.proof");
  assert.equal(exported.version, 4);
  assert.deepEqual(exported.dependencies.axioms, ["set.pairing"]);
  assert.deepEqual(exported.dependencies.theorems, ["pair.membership"]);
  assert.ok(exported.proof.nodes.length > 1);
  assert.equal(exported.trace.nodes[exported.trace.root]!.proofNode, exported.proof.root);
  assert.equal(formulaEquals(exported.trace.nodes[exported.trace.root]!.conclusion, exported.statement), true);
  assert.deepEqual(exported.tactics?.steps.map(step => step.command), [
    "have membership := pair.membership at x, y, x",
    "apply membership.backward",
    "left",
    "reflexivity",
  ]);
  assert.equal(exported.tactics?.steps.at(-1)?.after.goals.length, 0);
  assert.equal(formulaEquals(verifyExportedProof(kernel, exported), exported.statement), true);
  const roundTrip = JSON.parse(JSON.stringify(exported));
  assert.equal(formulaEquals(verifyExportedProof(kernel, roundTrip), exported.statement), true);
  assert.throws(() => verifyExportedProof(kernel, { ...exported, digest: "forged" }), /corrupted/);
  assert.throws(() => verifyExportedProof(kernel, { ...exported, environment: "forged" }), /corrupted|environment/);
});

test("renders a self-contained, inspectable proof tree", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, sets);
  const html = renderProofHtml(exportTheorem(kernel, "pair.left"));
  assert.match(html, /GRACE17 proof/);
  assert.match(html, /∀ x, ∀ y, x ∈ \{x, y\}/);
  assert.match(html, /pair\.membership/);
  assert.match(html, /↔ backward/);
  assert.match(html, /Goal \/ result/);
  assert.match(html, /Context Γ/);
  assert.match(html, /no remaining premises/);
  assert.match(html, /Tactic proof/);
  assert.match(html, /have membership := pair\.membership at x, y, x/);
  assert.match(html, /⊢ x = x ∨ x = y/);
  assert.match(html, /<details class="kernel-proof">/);
  assert.ok(html.indexOf("Tactic proof") < html.indexOf("Drill into kernel proof"));
});

test("records local assumptions in context-sensitive goal states", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, sets);
  const exported = exportTheorem(kernel, "membership.identity");
  const contextual = exported.trace.nodes.find(node => node.assumptions.length > 0);
  assert.ok(contextual);
  assert.equal(contextual.assumptions[0]!.tag, "pred");
  assert.match(renderProofHtml(exported), /Context Γ/);
  assert.match(renderProofHtml(exported), /x ∈ y/);
});

test("exports JSON and HTML through the CLI", () => {
  const directory = mkdtempSync(join(tmpdir(), "grace17-export-"));
  const jsonPath = join(directory, "pair-left.g17proof.json");
  const htmlPath = join(directory, "pair-left.html");
  for (const [command, output] of [["export", jsonPath], ["view", htmlPath]] as const) {
    const run = spawnSync(process.execPath, ["bin/g17.ts", command, "examples/Sets.g17", "--theorem", "pair.left", "--out", output, "--json"], {
      cwd: project,
      encoding: "utf8",
    });
    assert.equal(run.status, 0, run.stderr);
    assert.equal(JSON.parse(run.stdout).ok, true);
  }
  assert.equal(JSON.parse(readFileSync(jsonPath, "utf8")).theorem, "pair.left");
  assert.match(readFileSync(htmlPath, "utf8"), /proof-node/);
});
