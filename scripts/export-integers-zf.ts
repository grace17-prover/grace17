#!/usr/bin/env node
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { mkdirSync, rmSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import {
  canonical, compileSeparateKernelModule, createZfFoundationKernel, describeFoundation,
  installSetTheoryBootstrap, loadModuleGraph, replaySeparateKernelModuleExact, theoremDependencies,
} from "../src/index.ts";

const project = fileURLToPath(new URL("..", import.meta.url));
const output = resolve(process.argv[2] ?? join(project, "build", "integers-zf"));
const foundation = createZfFoundationKernel();
const bootstrapCompleted = foundation.fork();
const bootstrapCheckpoint = bootstrapCompleted.admissionCheckpoint();
installSetTheoryBootstrap(bootstrapCompleted);
const bootstrap = compileSeparateKernelModule(
  foundation, foundation, bootstrapCompleted, bootstrapCheckpoint, { module: "Grace.Bootstrap" },
);
const base = replaySeparateKernelModuleExact(foundation, bootstrap);
const completed = base.fork();
const checkpoint = completed.admissionCheckpoint();
loadModuleGraph(completed, [join(project, "lib", "Grace", "Cumulus", "Int.g17"), join(project, "lib", "Grace", "Cumulus", "NumberTheory.g17")], [join(project, "lib")]);
for (const name of completed.theorems.keys()) {
  if (!/\.Int\.|\.NumberTheory\./.test(name)) continue;
  const choices = theoremDependencies(completed, name).axioms.filter(axiom => /choice/i.test(axiom));
  if (choices.length) throw new Error(`${name} unexpectedly depends on ${choices.join(", ")}`);
}
const artifact = compileSeparateKernelModule(foundation, base, completed, checkpoint, {
  module: "Grace.IntegersZF",
  dependencies: [{ module: bootstrap.module, digest: bootstrap.digest }],
});
mkdirSync(output, { recursive: true });
rmSync(join(output, "ZF.g17env"), { force: true });
writeFileSync(join(output, "ZF.g17f"), `${canonical(describeFoundation("ZF"))}\n`);
writeFileSync(join(output, "Bootstrap.g17c"), `${canonical(bootstrap)}\n`);
writeFileSync(join(output, "Integers.g17c"), `${canonical(artifact)}\n`);
const replayed = replaySeparateKernelModuleExact(base, artifact);
console.log(JSON.stringify({ output, events: artifact.events.length, digest: replayed.digest() }));
