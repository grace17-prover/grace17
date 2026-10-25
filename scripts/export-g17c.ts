#!/usr/bin/env node
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Export one library module and its import closure as a strict G17C
// certificate: a Bootstrap.g17c dependency and a Module.g17c artifact that
// the independent checkers replay from the bare ZFG axioms.
//
//   node scripts/export-g17c.ts <module.g17> [output-dir]
//
// The module name is read from the file's header; the output directory
// defaults to build/compiled-<last name segment>.

import { existsSync, mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { basename, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import {
  canonical, compileSeparateKernelModule, createZfgFoundationKernel, describeFoundation,
  installSetTheoryBootstrap, loadModuleGraph, replaySeparateKernelModuleExact,
} from "../src/index.ts";

const project = fileURLToPath(new URL("..", import.meta.url));
const file = process.argv[2];
if (!file || file.startsWith("-") || !existsSync(file)) {
  console.error("usage: node scripts/export-g17c.ts <module.g17> [output-dir]");
  process.exit(2);
}
const source = resolve(file);
const header = readFileSync(source, "utf8").match(/^module\s+([\w.]+)/m);
if (!header) {
  console.error(`${file}: no module header`);
  process.exit(2);
}
const name = header[1];
const output = resolve(process.argv[3] ?? join(project, "build", `compiled-${basename(source, ".g17")}`));

const started = Date.now();
const foundation = createZfgFoundationKernel();
const bootstrapCompleted = foundation.fork();
const bootstrapCheckpoint = bootstrapCompleted.admissionCheckpoint();
installSetTheoryBootstrap(bootstrapCompleted);
const bootstrap = compileSeparateKernelModule(
  foundation, foundation, bootstrapCompleted, bootstrapCheckpoint, { module: "Grace.Bootstrap" },
);
const base = replaySeparateKernelModuleExact(foundation, bootstrap);
const completed = base.fork();
const checkpoint = completed.admissionCheckpoint();
loadModuleGraph(completed, [source], [join(project, "lib")]);
const artifact = compileSeparateKernelModule(foundation, base, completed, checkpoint, {
  module: name,
  dependencies: [{ module: bootstrap.module, digest: bootstrap.digest }],
});
mkdirSync(output, { recursive: true });
writeFileSync(join(output, "ZFG.g17f"), `${canonical(describeFoundation("ZFG"))}\n`);
writeFileSync(join(output, "Bootstrap.g17c"), `${canonical(bootstrap)}\n`);
writeFileSync(join(output, "Module.g17c"), `${canonical(artifact)}\n`);
console.log(`${name}: ${output} (${((Date.now() - started) / 1000).toFixed(0)} s)`);
