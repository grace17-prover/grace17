#!/usr/bin/env node
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { mkdirSync, rmSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import {
  canonical, compileSeparateKernelModule, createZfgFoundationKernel, describeFoundation,
  installSetTheoryBootstrap, loadModuleGraph, replaySeparateKernelModuleExact,
} from "../src/index.ts";

const project = fileURLToPath(new URL("..", import.meta.url));
const output = resolve(process.argv[2] ?? join(project, "build", "compiled"));
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
loadModuleGraph(completed, [join(project, "lib", "Grace", "Cumulus.g17")], [join(project, "lib")]);
const artifact = compileSeparateKernelModule(foundation, base, completed, checkpoint, {
  module: "Grace.Cumulus",
  dependencies: [{ module: bootstrap.module, digest: bootstrap.digest }],
});
mkdirSync(output, { recursive: true });
rmSync(join(output, "ZFG.g17env"), { force: true });
writeFileSync(join(output, "ZFG.g17f"), `${canonical(describeFoundation("ZFG"))}\n`);
writeFileSync(join(output, "Bootstrap.g17c"), `${canonical(bootstrap)}\n`);
writeFileSync(join(output, "Cumulus.g17c"), `${canonical(artifact)}\n`);
console.log(output);
