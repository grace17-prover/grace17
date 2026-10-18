// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// The independent Rust checkers: built from source when a Rust toolchain is
// present, then run over the conformance corpus, freshly compiled proof
// tapes, and a compiled module replayed from the bare ZFG axioms.

import assert from "node:assert/strict";
import { existsSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { spawnSync } from "node:child_process";
import test from "node:test";
import { fileURLToPath } from "node:url";
import {
  compileSeparateKernelModule, createZfgFoundationKernel, describeFoundation, installSetTheoryBootstrap,
  loadModuleGraph, replaySeparateKernelModuleExact,
} from "../src/index.ts";

const root = fileURLToPath(new URL("..", import.meta.url));
const library = join(root, "lib");
const cargo = spawnSync("cargo", ["--version"], { encoding: "utf8" });
const available = cargo.status === 0;
const tape = join(root, "build/rust/g17check");
const modules = join(root, "build/rust/g17c_check");

function ensureBuilt(): void {
  if (existsSync(tape) && existsSync(modules)) return;
  const build = spawnSync("bash", ["checkers/rust/build.sh"], { cwd: root, encoding: "utf8", timeout: 900_000 });
  assert.equal(build.status, 0, build.stderr);
}

test("the Rust checkers build and pass the conformance corpus", { skip: !available && "cargo is not installed" }, () => {
  ensureBuilt();
  const corpus = spawnSync("python3", ["checkers/rust/check_conformance.py"], { cwd: root, encoding: "utf8", timeout: 300_000 });
  assert.equal(corpus.status, 0, corpus.stderr);
  assert.match(corpus.stdout, /30 accepted, 36 rejected, 0 unsupported/);
});

test("the Rust tape checker accepts freshly compiled modules and rejects mutations", { skip: !available && "cargo is not installed" }, () => {
  ensureBuilt();
  for (const source of ["examples/Arithmetic.g17", "examples/Sets.g17", "lib/Grace/Core/Data.g17"]) {
    const directory = mkdtempSync(join(tmpdir(), "g17-rust-"));
    const machine = join(directory, "module.g17m");
    const environment = join(directory, "module.g17env");
    const compile = spawnSync(process.execPath, ["bin/g17.ts", "compile", source,
      "--out", machine, "--environment", environment, "--module-root", "lib"],
    { cwd: root, encoding: "utf8" });
    assert.equal(compile.status, 0, compile.stderr);
    const checked = spawnSync(tape, [machine, "--environment", environment, "--json"], { cwd: root, encoding: "utf8" });
    assert.equal(checked.status, 0, checked.stderr);
    const result = JSON.parse(checked.stdout);
    assert.equal(result.ok, true);
    assert.equal(result.checker, "grace17-rust");
    const bytes = readFileSync(machine);
    const damaged = Buffer.from(bytes);
    damaged[damaged.length - 1] ^= 1;
    writeFileSync(machine, damaged);
    const rejected = spawnSync(tape, [machine, "--environment", environment, "--json"], { cwd: root, encoding: "utf8" });
    assert.equal(rejected.status, 1);
    assert.match(rejected.stderr, /"ok":false/);
  }
});

test("the Rust module checker constructs ZFG and replays a compiled module with its bootstrap", { skip: !available && "cargo is not installed" }, () => {
  ensureBuilt();
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
  loadModuleGraph(completed, [join(root, "lib/Grace/Cumulus/Relation/QuotientMap.g17")], [library]);
  const compiled = compileSeparateKernelModule(foundationKernel, base, completed, checkpoint, {
    module: "Grace.Cumulus.Relation.QuotientMap",
    dependencies: [{ module: compiledBootstrap.module, digest: compiledBootstrap.digest }],
  });
  const directory = mkdtempSync(join(tmpdir(), "g17-rust-g17c-"));
  const receipt = join(directory, "ZFG.g17f");
  const bootstrap = join(directory, "Bootstrap.g17c");
  const artifact = join(directory, "Module.g17c");
  writeFileSync(receipt, JSON.stringify(describeFoundation("ZFG")));
  writeFileSync(bootstrap, JSON.stringify(compiledBootstrap));
  writeFileSync(artifact, JSON.stringify(compiled));
  for (const foundation of ["ZFG", receipt]) {
    const run = spawnSync(modules, [artifact, "--foundation", foundation, "--dependency", bootstrap, "--json"],
      { cwd: root, encoding: "utf8", timeout: 600_000 });
    assert.equal(run.status, 0, run.stderr);
    const result = JSON.parse(run.stdout);
    assert.equal(result.ok, true);
    assert.equal(result.module, "Grace.Cumulus.Relation.QuotientMap");
    assert.equal(result.environment, compiled.resultEnvironment);
  }
  const bypass = spawnSync(modules, [artifact, "--foundation", "ZFG", "--json"], { cwd: root, encoding: "utf8", timeout: 600_000 });
  assert.notEqual(bypass.status, 0);
  assert.match(bypass.stderr, /missing dependency artifact Grace\.Bootstrap/);
  const wrongProfile = spawnSync(modules, [artifact, "--foundation", "ZF", "--dependency", bootstrap, "--json"],
    { cwd: root, encoding: "utf8", timeout: 600_000 });
  assert.notEqual(wrongProfile.status, 0);
});

test("the Rust module checker replays the complete Cumulus from the ZFG axioms", { skip: !available && "cargo is not installed" }, () => {
  ensureBuilt();
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
  loadModuleGraph(completed, [join(root, "lib/Grace/Cumulus.g17")], [library]);
  const compiled = compileSeparateKernelModule(foundationKernel, base, completed, checkpoint, {
    module: "Grace.Cumulus",
    dependencies: [{ module: compiledBootstrap.module, digest: compiledBootstrap.digest }],
  });
  const directory = mkdtempSync(join(tmpdir(), "g17-rust-cumulus-"));
  const bootstrap = join(directory, "Bootstrap.g17c");
  const artifact = join(directory, "Cumulus.g17c");
  writeFileSync(bootstrap, JSON.stringify(compiledBootstrap));
  writeFileSync(artifact, JSON.stringify(compiled));
  const run = spawnSync(modules, [artifact, "--foundation", "ZFG", "--dependency", bootstrap, "--json"],
    { cwd: root, encoding: "utf8", timeout: 900_000, maxBuffer: 64 * 1024 * 1024 });
  assert.equal(run.status, 0, run.stderr);
  const result = JSON.parse(run.stdout);
  assert.equal(result.ok, true);
  assert.equal(result.module, "Grace.Cumulus");
  assert.equal(result.environment, compiled.resultEnvironment);
});
