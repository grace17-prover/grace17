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
const output = resolve(process.argv[2] ?? join(project, "build", "zf-library"));
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
loadModuleGraph(completed, ["Int", "NumberTheory", "Cardinal", "Geometry", "LinearAlgebra", "GraphTheory"].map(name => join(project, "lib", "Grace", "Cumulus", `${name}.g17`)), [join(project, "lib")]);
// Bootstrap was already replayed under ZF; replay does not retain its proof trees.
// Audit each newly elaborated library theorem, then replay the full artifact.
for (const name of completed.theorems.keys()) {
  if (base.theorems.has(name)) continue;
  const choices = theoremDependencies(completed, name).axioms.filter(axiom => /choice/i.test(axiom));
  if (choices.length) throw new Error(`${name} unexpectedly depends on ${choices.join(", ")}`);
}
const artifact = compileSeparateKernelModule(foundation, base, completed, checkpoint, {
  module: "Grace.Cumulus.ZFAudit",
  dependencies: [{ module: bootstrap.module, digest: bootstrap.digest }],
});
mkdirSync(output, { recursive: true });
rmSync(join(output, "ZF.g17env"), { force: true });
writeFileSync(join(output, "ZF.g17f"), `${canonical(describeFoundation("ZF"))}\n`);
writeFileSync(join(output, "Bootstrap.g17c"), `${canonical(bootstrap)}\n`);
writeFileSync(join(output, "CumulusZF.g17c"), `${canonical(artifact)}\n`);
const replayed = replaySeparateKernelModuleExact(base, artifact);
console.log(JSON.stringify({ output, events: artifact.events.length, theorems: replayed.theorems.size, digest: replayed.digest() }));
