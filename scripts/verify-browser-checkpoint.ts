// Expose a bundled checkpoint to the independent G17C checkers.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore
import assert from "node:assert/strict";
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname } from "node:path";
import {
  canonical, compileSeparateKernelModule, createZfgFoundationKernel,
  installSetTheoryBootstrap, replaySeparateKernelModuleExact,
} from "../src/index.ts";
import { sha256Hex } from "../src/hash.ts";
import { standardDependencyCheckpoints } from "../workbench/generated/src/standard-checkpoints.js";
const name = process.argv[2] ?? "Grace.Cumulus.Real.Squares";
const output = process.argv[3] ?? "build/browser-checkpoint";
mkdirSync(dirname(output), { recursive: true });
const entry = standardDependencyCheckpoints.get(name);
if (!entry) throw Error(`No bundled checkpoint for ${name}`);
const checkpoint = { ...entry, ...JSON.parse(readFileSync(new URL(`../workbench/generated/${entry.file}`, import.meta.url), "utf8")) };
// Browser prefixes start above the proof-checked bootstrap. Independent G17C
// checkers start from primitive ZFG, so make that bootstrap an explicit checked
// dependency. The bundled admission events and theorem programs are unchanged.
const foundation = createZfgFoundationKernel();
const boot = foundation.fork();
const start = boot.admissionCheckpoint();
installSetTheoryBootstrap(boot);
const bootstrap = compileSeparateKernelModule(foundation, foundation, boot, start, { module: "Grace.Bootstrap" });
const base = replaySeparateKernelModuleExact(foundation, bootstrap);
assert.equal(base.digest(), checkpoint.compiled.baseEnvironment);
assert.equal(checkpoint.compiled.dependencies.length, 0);
const { digest: _digest, ...original } = checkpoint.compiled;
const body = { ...original,
  foundation: { profile: "ZFG" as const, environment: foundation.digest() },
  dependencies: [{ module: bootstrap.module, digest: bootstrap.digest }],
};
const artifact = { ...body, digest: sha256Hex(canonical(body)) };
assert.equal(artifact.events, checkpoint.compiled.events);
const checked = replaySeparateKernelModuleExact(base, artifact);
assert.equal(checked.digest(), checkpoint.compiled.resultEnvironment);
writeFileSync(`${output}-bootstrap.g17c`, canonical(bootstrap) + "\n");
writeFileSync(`${output}.g17c`, canonical(artifact) + "\n");
console.log(JSON.stringify({ checkpoint: name, sourceModules: checkpoint.sources.length,
  theorems: checkpoint.loaded.reduce((count, module) => count + module.theorems.length, 0),
  events: artifact.events.length, environment: checked.digest() }));
