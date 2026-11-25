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
  canonical, canonicalDigest, createZfgKernel, decodeExportedProof, elaborateModule, encodeExportedProof, exportedProofText,
  exportTheorem, forall, formulaEquals, parseExportedProof, pred, renderProofHtml, v, verifyExportedProof,
  type ExportedProof,
} from "../src/index.ts";

const project = fileURLToPath(new URL("..", import.meta.url));
const sets = readFileSync(fileURLToPath(new URL("../examples/Sets.g17", import.meta.url)), "utf8");

test("retains, exports, and independently verifies theorem proof DAGs", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, sets);
  const exported = exportTheorem(kernel, "pair.left");
  assert.equal(exported.format, "grace17.proof");
  assert.equal(exported.version, 5);
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
  const file = readFileSync(jsonPath, "utf8");
  assert.equal(JSON.parse(file).theorem, "pair.left");
  assert.equal(JSON.parse(file).version, 5);
  assert.match(readFileSync(htmlPath, "utf8"), /proof-node/);
});

test("a version 5 file writes each formula once and reads back to a proof that verifies", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, sets);
  for (const name of ["pair.left", "membership.identity"]) {
    const exported = exportTheorem(kernel, name);
    const text = [...exportedProofText(exported)].join("");
    const encoded = JSON.parse(text);
    assert.equal(encoded.version, 5);
    const written = encoded.formulas.map((formula: unknown) => canonical(formula));
    assert.equal(new Set(written).size, written.length, "no formula is written twice");
    assert.ok(!/"tag":"(forall|imp|pred|eq|and|or|iff|exists|bottom)"/.test(JSON.stringify(encoded.trace)), "the trace refers to formulas by index");
    const read = parseExportedProof(text);
    assert.equal(read.digest, exported.digest);
    assert.equal(formulaEquals(verifyExportedProof(kernel, read), exported.statement), true);
    assert.equal(canonical(read.trace), canonical(exported.trace));
    assert.equal(canonical(read.tactics), canonical(exported.tactics));
  }
});

test("a version 5 file with a changed formula, context, or reference is rejected", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, sets);
  const text = [...exportedProofText(exportTheorem(kernel, "pair.left"))].join("");
  const forgeries = [
    text.replace('"pred":"in"', '"pred":"subset"'),
    text.replace(/"assumptions":\[\]/, '"assumptions":[{"$":0}]'),
    text.replace(/\{"\$":0\}/, '{"$":99999}'),
  ];
  for (const forged of forgeries) {
    assert.notEqual(forged, text);
    assert.throws(() => verifyExportedProof(kernel, parseExportedProof(forged)), /corrupted|missing formula|does not match/);
  }
});

test("formulas that differ only in their bound names are written separately", () => {
  const first = forall("x", pred("p", v("x")));
  const second = forall("y", pred("p", v("y")));
  const body = {
    format: "grace17.proof", version: 5, theorem: "t", environment: "e", statement: first,
    dependencies: { axioms: [], theorems: [], definitions: [] }, proof: { root: 0, nodes: [], digest: "" },
    trace: { root: 0, nodes: [{ proofNode: 0, assumptions: [first, second], conclusion: second, children: [] }] },
  } as unknown as Omit<ExportedProof, "digest">;
  const encoded = encodeExportedProof(body);
  assert.equal(encoded.formulas.length, 2);
  const decoded = decodeExportedProof({ ...encoded, digest: "" });
  assert.equal(canonical(decoded.trace), canonical(body.trace));
});

test("a version 4 export still verifies", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, sets);
  const { digest: _digest, ...body } = exportTheorem(kernel, "pair.left");
  const legacy = { ...body, version: 4 as const };
  const exported = JSON.parse(JSON.stringify({ ...legacy, digest: canonicalDigest(legacy) }));
  assert.equal(formulaEquals(verifyExportedProof(kernel, parseExportedProof(JSON.stringify(exported))), body.statement), true);
  assert.throws(() => verifyExportedProof(kernel, { ...exported, digest: canonicalDigest(body) }), /corrupted/);
});

test("a proof too large to write out is rendered from each formula written once", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, sets);
  const exported = exportTheorem(kernel, "pair.left");
  assert.doesNotMatch(renderProofHtml(exported), /kernel-data/);
  const html = renderProofHtml(exported, { staticKernelLimit: 0 });
  const data = JSON.parse(html.match(/<script type="application\/json" id="kernel-data">([^<]*)<\/script>/)![1]!);
  assert.equal(data.nodes.length, exported.trace.nodes.length);
  assert.equal(data.root, exported.trace.root);
  assert.equal(new Set(data.formulas).size, data.formulas.length);
  assert.ok(data.formulas.includes("∀ x, ∀ y, x ∈ {x, y}"));
  // Every judgment is reached from the root once; the others are links.
  const reached = data.nodes.flatMap((node: number[][]) => (node[3] as number[]).filter(child => child >= 0));
  assert.equal(new Set(reached).size, reached.length);
  assert.equal(reached.length + 1, exported.trace.nodes.length);
  const scripts = [...html.matchAll(/<script>([\s\S]*?)<\/script>/g)].map(match => match[1]!);
  assert.ok(scripts.length >= 1);
  for (const script of scripts) assert.doesNotThrow(() => new Function(script));
  assert.match(html, /Tactic proof/);
  assert.match(html, /have membership := pair\.membership at x, y, x/);
});
