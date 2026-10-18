// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import assert from "node:assert/strict";
import { mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { spawnSync } from "node:child_process";
import test from "node:test";
import { fileURLToPath } from "node:url";
import {
  canonical, compileSeparateKernelModule, createZfgFoundationKernel, describeFoundation, exportKernelEnvironment,
  installSetTheoryBootstrap, loadModuleGraph, replaySeparateKernelModuleExact,
  type SeparateCompiledKernelModule,
} from "../src/index.ts";
import { sha256Hex } from "../src/hash.ts";

// The Python checker is the reference implementation and the slowest of the
// three, so its replay of the complete library is a local and release check
// (npm run check:g17c:python). Continuous integration replays the library
// with the Rust checker and keeps the Python tests that finish quickly.
const fullReplay = process.env.CI && !process.env.GRACE17_PYTHON_FULL
  ? "the complete Cumulus replay with the Python checker runs locally and before a release"
  : false;

const root = fileURLToPath(new URL("..", import.meta.url));
const library = fileURLToPath(new URL("../lib", import.meta.url));
const cumulus = fileURLToPath(new URL("../lib/Grace/Cumulus.g17", import.meta.url));
const checker = fileURLToPath(new URL("../checkers/python/g17c_check.py", import.meta.url));

let fixture: { directory: string; receipt: string; legacy: string; bootstrap: string; artifact: string;
  compiledBootstrap: SeparateCompiledKernelModule; compiled: SeparateCompiledKernelModule } | undefined;
function files() {
  if (fixture) return fixture;
  const foundationKernel = createZfgFoundationKernel();
  const bootstrapCompleted = foundationKernel.fork();
  const bootstrapCheckpoint = bootstrapCompleted.admissionCheckpoint();
  installSetTheoryBootstrap(bootstrapCompleted);
  const compiledBootstrap = compileSeparateKernelModule(
    foundationKernel, foundationKernel, bootstrapCompleted, bootstrapCheckpoint, { module: "Grace.Bootstrap" },
  );
  const base = replaySeparateKernelModuleExact(foundationKernel, compiledBootstrap);
  const completed = base.fork();
  const checkpoint = completed.admissionCheckpoint();
  loadModuleGraph(completed, [cumulus], [library]);
  const compiled = compileSeparateKernelModule(foundationKernel, base, completed, checkpoint, {
    module: "Grace.Cumulus",
    dependencies: [{ module: compiledBootstrap.module, digest: compiledBootstrap.digest }],
  });
  const directory = mkdtempSync(join(tmpdir(), "grace17-g17c-python-"));
  const receipt = join(directory, "ZFG.g17f");
  const legacy = join(directory, "ZFG.g17env");
  const bootstrap = join(directory, "Bootstrap.g17c");
  const artifact = join(directory, "Cumulus.g17c");
  writeFileSync(receipt, JSON.stringify(describeFoundation("ZFG")));
  writeFileSync(legacy, JSON.stringify(exportKernelEnvironment(foundationKernel)));
  writeFileSync(bootstrap, JSON.stringify(compiledBootstrap));
  writeFileSync(artifact, JSON.stringify(compiled));
  return fixture = { directory, receipt, legacy, bootstrap, artifact, compiledBootstrap, compiled };
}

const command = (artifact: string, bootstrap: string, foundation: string) =>
  [checker, artifact, "--foundation", foundation, "--dependency", bootstrap, "--json"];

test("independent Python G17C checker constructs ZFG and reconstructs complete Cumulus", { skip: fullReplay }, () => {
  const { artifact, bootstrap, compiled } = files();
  const run = spawnSync("python3", command(artifact, bootstrap, "ZFG"), {
    cwd: root, encoding: "utf8", timeout: 600_000,
  });
  assert.equal(run.status, 0, run.stderr);
  const result = JSON.parse(run.stdout);
  assert.equal(result.ok, true);
  assert.equal(result.module, "Grace.Cumulus");
  assert.equal(result.environment, compiled.resultEnvironment);
});

test("Cumulus cannot bypass its checked bootstrap dependency", () => {
  const { artifact } = files();
  const run = spawnSync("python3", [checker, artifact, "--foundation", "ZFG", "--json"], {
    cwd: root, encoding: "utf8", timeout: 600_000,
  });
  assert.notEqual(run.status, 0);
  assert.match(run.stderr, /missing dependency artifact Grace\.Bootstrap/i);
});

test("tiny foundation receipts authenticate checker construction rather than kernel maps", { skip: fullReplay }, () => {
  const { receipt, bootstrap, artifact, compiled } = files();
  const run = spawnSync("python3", command(artifact, bootstrap, receipt), {
    cwd: root, encoding: "utf8", timeout: 600_000,
  });
  assert.equal(run.status, 0, run.stderr);
  assert.equal(JSON.parse(run.stdout).environment, compiled.resultEnvironment);
});

test("full G17C checker rejects trusted foundation snapshots", () => {
  const { legacy, bootstrap, artifact } = files();
  const run = spawnSync("python3", command(artifact, bootstrap, legacy), {
    cwd: root, encoding: "utf8", timeout: 600_000,
  });
  assert.notEqual(run.status, 0);
  assert.match(run.stderr, /checker-constructed|snapshots are not accepted/i);
});

test("Python checker rejects a forged tiny foundation receipt", () => {
  const { directory, bootstrap, artifact } = files();
  const forged = join(directory, "forged.g17f");
  writeFileSync(forged, JSON.stringify({ ...describeFoundation("ZFG"), environment: "0".repeat(64) }));
  const run = spawnSync("python3", command(artifact, bootstrap, forged), {
    cwd: root, encoding: "utf8", timeout: 600_000,
  });
  assert.notEqual(run.status, 0);
  assert.match(run.stderr, /wrong environment/i);
});

test("independent Python checker rejects a redigested false Bootstrap theorem", () => {
  const { directory, compiledBootstrap } = files();
  const events = structuredClone(compiledBootstrap.events);
  const batch = [...events].reverse().find(item => item.kind === "theoremBatch");
  assert.ok(batch && batch.kind === "theoremBatch");
  const epsilon = batch.statements.find(item => item.name === "epsilon0.less.membership");
  assert.ok(epsilon);
  (epsilon as { statement: unknown }).statement = {
    tag: "eq", left: { tag: "app", fn: "empty", args: [] }, right: { tag: "app", fn: "omega", args: [] },
  };
  const { digest: _digest, ...oldBody } = compiledBootstrap;
  const body = { ...oldBody, events };
  const forged = { ...body, digest: sha256Hex(canonical(body)) };
  const path = join(directory, "false-bootstrap.g17c");
  writeFileSync(path, JSON.stringify(forged));
  const run = spawnSync("python3", [checker, path, "--foundation", "ZFG", "--json"], {
    cwd: root, encoding: "utf8", timeout: 600_000,
  });
  assert.notEqual(run.status, 0);
  assert.match(run.stderr, /boundary|wrong formula/i);
});

test("independent Python G17C checker rejects corruption and redigested recursion forgeries", () => {
  const { directory, bootstrap, compiled } = files();
  const eventIndex = compiled.events.findIndex(item => item.kind === "admission" &&
    item.event.operation === "defineTransfiniteFunction");
  assert.notEqual(eventIndex, -1);
  const events = structuredClone(compiled.events);
  const item = events[eventIndex]!;
  assert.equal(item.kind, "admission");
  const payload = item.event.payload as { options: { successor: { args: unknown[] } } };
  const successor = payload.options.successor;
  successor.args = [{ tag: "app", fn: "Grace.Cumulus.Set.Hierarchy.V", args: [{ tag: "var", name: "alpha" }] }];
  const { digest: _digest, ...oldBody } = compiled;
  const body = { ...oldBody, events };
  const forged = { ...body, digest: sha256Hex(canonical(body)) };
  const path = join(directory, "forged.g17c");
  writeFileSync(path, JSON.stringify(forged));
  const run = spawnSync("python3", command(path, bootstrap, "ZFG"), {
    cwd: root, encoding: "utf8", timeout: 600_000,
  });
  assert.notEqual(run.status, 0);
  assert.match(run.stderr, /transfinite|successor|clause|recursive/i);
});

test("independent Python G17C checker rejects a redigested false theorem statement", { skip: fullReplay }, () => {
  const { directory, bootstrap, compiled } = files();
  const events = structuredClone(compiled.events);
  const batch = events.find(item => item.kind === "theoremBatch");
  assert.ok(batch && batch.kind === "theoremBatch");
  (batch.statements[0] as { statement: unknown }).statement = {
    tag: "eq", left: { tag: "app", fn: "empty", args: [] }, right: { tag: "app", fn: "omega", args: [] },
  };
  const { digest: _digest, ...oldBody } = compiled;
  const body = { ...oldBody, events };
  const forged = { ...body, digest: sha256Hex(canonical(body)) };
  const path = join(directory, "false-theorem.g17c");
  writeFileSync(path, JSON.stringify(forged));
  const run = spawnSync("python3", command(path, bootstrap, "ZFG"), {
    cwd: root, encoding: "utf8", timeout: 600_000,
  });
  assert.notEqual(run.status, 0);
  assert.match(run.stderr, /boundary|wrong formula/i);
});
