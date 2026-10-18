// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { auditTheoremAxioms, createSetTheoryKernel, loadModuleGraph, loadModuleSourceGraph } from "../src/index.ts";
import { artifactPath, buildModuleStore, createStoreKernel, foundationArtifactPath, loadModuleStore } from "../src/module-store.ts";

const library = fileURLToPath(new URL("../lib", import.meta.url));

// A diamond over a small library prefix: D imports B and C, both of which
// import A, which imports the core natural-number algebra.
function diamond(root: string, cBody: string): void {
  const write = (name: string, source: string): void => {
    const file = join(root, ...name.split("."));
    mkdirSync(join(file, ".."), { recursive: true });
    writeFileSync(`${file}.g17`, source);
  };
  write("Store.A", `module Store.A
import Grace.Core.Nat.Algebra

def twice (n : Nat) : Nat := add(n, n)

theorem twice.zero
  shows twice(0) = 0
proof
  compute
`);
  write("Store.B", `module Store.B
import Store.A

theorem twice.one
  shows twice(1) = 2
proof
  compute
`);
  write("Store.C", `module Store.C
import Store.A

${cBody}
`);
  write("Store.D", `module Store.D
import Store.B
import Store.C

theorem both
  shows twice(1) = 2 ∧ twice(2) = 4
proof
  constructor
  . exact twice.one
  . exact twice.two
`);
}

const cTwo = `theorem twice.two
  shows twice(2) = 4
proof
  compute`;

test("module artifacts replay to the digest of a source check and are reused when current", t => {
  const directory = mkdtempSync(join(tmpdir(), "g17-store-"));
  t.after(() => rmSync(directory, { recursive: true, force: true }));
  const root = join(directory, "src");
  const store = join(directory, "modules");
  diamond(root, cTwo);
  const roots = [root, library];

  const first = buildModuleStore(["Store.D"], { roots, store, verify: true });
  assert.deepEqual(first.reused, []);
  assert.deepEqual(first.built.slice(-4), ["Store.A", "Store.B", "Store.C", "Store.D"]);
  assert.ok(first.built.includes("Grace.Core.Nat.Algebra"));

  const direct = createSetTheoryKernel({ profile: "ZFG" });
  loadModuleGraph(direct, [join(root, "Store", "D.g17")], roots);
  const replayed = loadModuleStore(createSetTheoryKernel({ profile: "ZFG" }), ["Store.D"], store);
  assert.equal(replayed.kernel.digest(), direct.digest());
  assert.equal(replayed.kernel.theorems.size, direct.theorems.size);
  assert.deepEqual(replayed.loaded.at(-1)?.theorems, ["Store.D.both"]);
  const artifact = JSON.parse(readFileSync(artifactPath(store, "Store.D"), "utf8"));
  assert.deepEqual(artifact.imports, ["Store.B", "Store.C"]);
  assert.deepEqual(artifact.closure.slice(-3).map((item: { module: string }) => item.module), ["Store.A", "Store.B", "Store.C"]);

  const second = buildModuleStore(["Store.D"], { roots, store });
  assert.deepEqual(second.built, []);
  assert.equal(second.reused.length, first.built.length);
});

test("editing one module rebuilds it and its dependents only", t => {
  const directory = mkdtempSync(join(tmpdir(), "g17-store-"));
  t.after(() => rmSync(directory, { recursive: true, force: true }));
  const root = join(directory, "src");
  const store = join(directory, "modules");
  diamond(root, cTwo);
  const roots = [root, library];
  buildModuleStore(["Store.D"], { roots, store });

  diamond(root, `theorem twice.two
  shows twice(2) = 4
proof
  compute

theorem twice.three
  shows twice(3) = 6
proof
  compute`);
  const rebuilt = buildModuleStore(["Store.D"], { roots, store });
  assert.deepEqual(rebuilt.built, ["Store.C", "Store.D"]);
  assert.ok(rebuilt.reused.includes("Store.A") && rebuilt.reused.includes("Store.B"));

  const direct = createSetTheoryKernel({ profile: "ZFG" });
  loadModuleGraph(direct, [join(root, "Store", "D.g17")], roots);
  const replayed = loadModuleStore(createSetTheoryKernel({ profile: "ZFG" }), ["Store.D"], store);
  assert.equal(replayed.kernel.digest(), direct.digest());
  assert.ok(replayed.kernel.theorems.has("Store.C.twice.three"));
});

test("a workspace file elaborates over the store with its imports' notation and names", t => {
  const directory = mkdtempSync(join(tmpdir(), "g17-store-"));
  t.after(() => rmSync(directory, { recursive: true, force: true }));
  const root = join(directory, "src");
  const store = join(directory, "modules");
  diamond(root, cTwo);
  const roots = [root, library];
  buildModuleStore(["Store.D"], { roots, store });
  const loaded = loadModuleStore(createSetTheoryKernel({ profile: "ZFG" }), ["Store.D"], store);
  const modules = loadModuleSourceGraph(loaded.kernel, [{ file: "Probe.g17", source: `module Probe
import Store.D

theorem probe (n : Nat)
  shows twice(n) + 0 = n + n
proof
  have h : twice(n) = n + n
    unfold twice
    rfl
  rw h
  exact add.right_unit at n + n with *
` }], roots);
  assert.deepEqual(modules.map(item => item.module), ["Probe"]);
  assert.ok(loaded.kernel.theorems.has("Probe.probe"));
});

test("a corrupted or inconsistent artifact is refused", t => {
  const directory = mkdtempSync(join(tmpdir(), "g17-store-"));
  t.after(() => rmSync(directory, { recursive: true, force: true }));
  const root = join(directory, "src");
  const store = join(directory, "modules");
  diamond(root, cTwo);
  const roots = [root, library];
  buildModuleStore(["Store.D"], { roots, store });

  const path = artifactPath(store, "Store.C");
  const original = readFileSync(path, "utf8");
  const artifact = JSON.parse(original);
  artifact.loaded.theorems = [...artifact.loaded.theorems, "Store.C.forged"];
  writeFileSync(path, JSON.stringify(artifact));
  assert.throws(() => loadModuleStore(createSetTheoryKernel({ profile: "ZFG" }), ["Store.D"], store), /Corrupted module artifact/);

  // A rebuilt dependency whose dependents were not rebuilt is detected by
  // the dependents' recorded closure digests.
  writeFileSync(path, original);
  diamond(root, `theorem twice.two
  shows twice(2) = 4
proof
  compute

theorem extra
  shows twice(0) = 0
proof
  compute`);
  buildModuleStore(["Store.C"], { roots, store });
  assert.throws(() => loadModuleStore(createSetTheoryKernel({ profile: "ZFG" }), ["Store.D"], store), /different Store.C/);
  buildModuleStore(["Store.D"], { roots, store });
  assert.ok(loadModuleStore(createSetTheoryKernel({ profile: "ZFG" }), ["Store.D"], store).kernel.theorems.has("Store.C.extra"));
});

// A store-loaded kernel keeps only loaders for the verified machine proofs;
// an audit reloads them from the artifacts and agrees with a source check.
test("an axiom audit over the store reloads machine proofs on demand", t => {
  const directory = mkdtempSync(join(tmpdir(), "g17-store-"));
  t.after(() => rmSync(directory, { recursive: true, force: true }));
  const root = join(directory, "src");
  const store = join(directory, "modules");
  diamond(root, cTwo);
  const roots = [root, library];
  buildModuleStore(["Store.D"], { roots, store });
  const direct = createSetTheoryKernel({ profile: "ZFG" });
  loadModuleGraph(direct, [join(root, "Store", "D.g17")], roots);
  const replayed = loadModuleStore(createSetTheoryKernel({ profile: "ZFG" }), ["Store.D"], store);
  assert.deepEqual(auditTheoremAxioms(replayed.kernel, "Store.D.both"), auditTheoremAxioms(direct, "Store.D.both"));
  const entry = replayed.kernel.theoremMachineProofs.get("Store.B.twice.one")!;
  assert.equal(typeof entry.program.version, "number");
  // A rewritten artifact no longer backs proofs that were not reloaded yet.
  writeFileSync(artifactPath(store, "Store.A"), JSON.stringify({ format: "grace17.module-artifact" }));
  assert.throws(() => replayed.kernel.theoremMachineProofs.get("Store.A.twice.zero")!.program, /no longer holds|Corrupted/);
});

// The store's foundation image replays to the elaborated foundation exactly,
// and a store built with it loads to the digest of a source check.
test("the foundation image replays to the elaborated foundation", t => {
  const directory = mkdtempSync(join(tmpdir(), "g17-store-"));
  t.after(() => rmSync(directory, { recursive: true, force: true }));
  const root = join(directory, "src");
  const store = join(directory, "modules");
  diamond(root, cTwo);
  buildModuleStore(["Store.D"], { roots: [root, library], store });
  assert.ok(readFileSync(foundationArtifactPath(store, "ZFG"), "utf8").startsWith('{"digest":"'));
  const elaborated = createSetTheoryKernel({ profile: "ZFG" });
  const imaged = createStoreKernel(store, "ZFG");
  assert.equal(imaged.digest(), elaborated.digest());
  assert.equal(imaged.foundationDigest(), elaborated.foundationDigest());
  const direct = createSetTheoryKernel({ profile: "ZFG" });
  loadModuleGraph(direct, [join(root, "Store", "D.g17")], [root, library]);
  assert.equal(loadModuleStore(imaged, ["Store.D"], store).kernel.digest(), direct.digest());
  // A stale image falls back to elaboration; corrupted bytes are refused.
  writeFileSync(foundationArtifactPath(store, "ZFG"), readFileSync(foundationArtifactPath(store, "ZFG"), "utf8").replace(/"sourceDigest":"[0-9a-f]{8}/, '"sourceDigest":"00000000'));
  assert.throws(() => createStoreKernel(store, "ZFG"), /Corrupted foundation artifact/);
  writeFileSync(foundationArtifactPath(store, "ZFG"), "{}");
  assert.throws(() => createStoreKernel(store, "ZFG"), /Corrupted foundation artifact/);
  rmSync(foundationArtifactPath(store, "ZFG"));
  assert.equal(createStoreKernel(store, "ZFG").digest(), elaborated.digest());
});
