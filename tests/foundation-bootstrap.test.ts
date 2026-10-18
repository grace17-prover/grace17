// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { readdirSync, readFileSync } from "node:fs";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import test from "node:test";
import {
  compileSeparateKernelModule, createZfgFoundationKernel, createZfgKernel,
  decodeFoundationBootstrap, describeFoundation, encodeFoundationBootstrap,
  installSetTheoryBootstrap, replayFoundation, replaySeparateKernelModuleExact,
  SET_THEORY_BOOTSTRAP_FILES,
} from "../src/index.ts";

const root = fileURLToPath(new URL("..", import.meta.url));

test("the bootstrap is visible Grace source and Kernel contains no user-land proofs", () => {
  assert.deepEqual([...SET_THEORY_BOOTSTRAP_FILES], [
    "Grace/Bootstrap/Aliases.g17",
    "Grace/Bootstrap/Nat.g17",
    "Grace/Bootstrap/OrderedPair.g17",
    "Grace/Bootstrap/Epsilon0.g17",
  ]);
  const source = SET_THEORY_BOOTSTRAP_FILES
    .map(name => readFileSync(join(root, "lib", name), "utf8"))
    .join("\n");
  for (const declaration of [
    "empty.membership", "bootstrap.membership.asymmetric", "nat.zero",
    "Naturals.injective.succ", "bootstrap.orderedPair.injective", "epsilon0.less.membership",
  ]) assert.match(source, new RegExp(`(?:theorem|def) ${declaration.replaceAll(".", "\\.")}`));

  const host = readFileSync(join(root, "src", "zfg.ts"), "utf8");
  assert.doesNotMatch(host, /String\.raw|theorem\s+nat\.zero|def\s+epsilon0\.less/);

  for (const name of readdirSync(join(root, "lib", "Grace", "Kernel"), { recursive: true })) {
    if (!String(name).endsWith(".g17")) continue;
    const kernelDocument = readFileSync(join(root, "lib", "Grace", "Kernel", String(name)), "utf8");
    assert.doesNotMatch(kernelDocument, /^(?:axiom|theorem|lemma|proof|def|define|predicate)\b/m);
  }
});

test("foundation bootstrap reconstructs and authenticates the exact ZFG environment", () => {
  const description = describeFoundation("ZFG");
  const encoded = encodeFoundationBootstrap(description);
  assert.ok(encoded.byteLength < 256);
  assert.doesNotMatch(new TextDecoder().decode(encoded), /kernel|axioms|theorems|definitions/);
  const decoded = decodeFoundationBootstrap(encoded);
  const kernel = replayFoundation(decoded);
  assert.equal(kernel.digest(), description.environment);
  assert.equal(kernel.foundationDigest(), description.environment);
  assert.equal(kernel.capabilities.setTheory, "ZFG");
});

test("foundation bootstrap rejects a changed expected environment", () => {
  const description = describeFoundation("ZFG");
  assert.throws(() => replayFoundation({ ...description, environment: "0".repeat(64) }),
    /wrong environment/);
});

test("foundation bootstrap profiles have distinct authenticated results", () => {
  const zf = describeFoundation("ZF");
  const zfc = describeFoundation("ZFC");
  const zfg = describeFoundation("ZFG");
  assert.notEqual(zf.environment, zfc.environment);
  assert.notEqual(zfc.environment, zfg.environment);
});

test("TypeScript and Python independently construct identical foundation profiles", () => {
  const program = [
    "from g17c_check import construct_foundation",
    "print('\\n'.join(construct_foundation(p).digest for p in ('ZF','ZFC','ZFG')))",
  ].join(";");
  const run = spawnSync("python3", ["-c", program], {
    cwd: root,
    encoding: "utf8",
    env: { ...process.env, PYTHONPATH: fileURLToPath(new URL("../checkers/python", import.meta.url)) },
  });
  assert.equal(run.status, 0, run.stderr);
  assert.deepEqual(run.stdout.trim().split("\n"),
    (["ZF", "ZFC", "ZFG"] as const).map(profile => describeFoundation(profile).environment));
});

test("Grace.Bootstrap replays aliases as proofs and reaches the direct convenience environment", () => {
  const foundation = createZfgFoundationKernel();
  assert.equal(foundation.functions.has("epsilon0.less"), false);
  assert.equal(foundation.axioms.has("foundation.epsilon0.less.membership"), false);
  const completed = foundation.fork();
  const checkpoint = completed.admissionCheckpoint();
  installSetTheoryBootstrap(completed);
  const compiled = compileSeparateKernelModule(
    foundation, foundation, completed, checkpoint, { module: "Grace.Bootstrap" },
  );
  assert.deepEqual(compiled.events.map(item => item.kind), ["theoremBatch", "admission", "theoremBatch"]);
  assert.equal(compiled.events[1]?.kind === "admission" && compiled.events[1].event.operation, "defineSubset");
  const replayed = replaySeparateKernelModuleExact(foundation, compiled);
  assert.equal(replayed.digest(), createZfgKernel().digest());
  assert.equal(replayed.axioms.has("pair.membership"), false);
  assert.equal(replayed.theorems.has("pair.membership"), true);
  assert.equal(replayed.axioms.has("foundation.epsilon0.less.membership"), false);
  assert.equal(replayed.functions.has("epsilon0.less"), true);
  assert.equal(replayed.definitions.has("epsilon0.less"), true);
  assert.equal(replayed.theorems.has("epsilon0.less.membership"), true);
});
