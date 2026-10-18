#!/usr/bin/env node
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { performance } from "node:perf_hooks";
import { fileURLToPath } from "node:url";
import {
  compileDenseKernelModule, compileKernelModule, compileProofModule, compileSeparateKernelModule,
  createZfgFoundationKernel, createZfgKernel,
  decodeCompiledKernelModule, decodeDenseKernelModule, decodeProofMachineBinary, decodeSeparateKernelModule,
  encodeCompiledKernelModule, encodeDenseKernelModule, encodeProofMachineBinary, encodeSeparateKernelModule,
  encodeSurfaceEnvironmentIndex, exportSurfaceEnvironmentIndex, exportTheoremForMachine,
  installSetTheoryBootstrap, loadModuleGraph,
  replayCompiledKernelModule, replayDenseKernelModule, replaySeparateKernelModuleExact, verifyProofMachine,
} from "../src/index.ts";

const library = fileURLToPath(new URL("../lib", import.meta.url));
const cumulus = fileURLToPath(new URL("../lib/Grace/Cumulus.g17", import.meta.url));
const measure = <T>(operation: () => T): { readonly value: T; readonly milliseconds: number } => {
  const started = performance.now();
  const value = operation();
  return { value, milliseconds: performance.now() - started };
};

const base = createZfgKernel();
const kernel = base.fork();
const checkpoint = kernel.admissionCheckpoint();
const source = measure(() => loadModuleGraph(kernel, [cumulus], [library]));
const theoremNames = source.value.flatMap(module => module.theorems);
const exports = measure(() => theoremNames.map(name => exportTheoremForMachine(kernel, name)));
const compiled = measure(() => compileProofModule(exports.value));
const binary = encodeProofMachineBinary(compiled.value);
const decoded = measure(() => decodeProofMachineBinary(binary));
const replay = measure(() => verifyProofMachine(kernel, decoded.value));
const warmReplay = measure(() => verifyProofMachine(kernel, decoded.value));
const rate = replay.value.stats.instructions / (replay.milliseconds / 1_000);
const warmRate = warmReplay.value.stats.instructions / (warmReplay.milliseconds / 1_000);
const eventCompile = measure(() => compileKernelModule(kernel, checkpoint, { module: "Grace.Cumulus" }));
const eventBinary = encodeCompiledKernelModule(eventCompile.value);
const eventDecode = measure(() => decodeCompiledKernelModule(eventBinary));
const eventReplay = measure(() => replayCompiledKernelModule(createZfgKernel(), eventDecode.value));
const denseCompile = measure(() => compileDenseKernelModule(base, kernel, checkpoint, { module: "Grace.Cumulus" }));
const denseBinary = encodeDenseKernelModule(denseCompile.value);
const denseDecode = measure(() => decodeDenseKernelModule(denseBinary));
const denseReplay = measure(() => replayDenseKernelModule(createZfgKernel(), denseDecode.value));
const foundation = createZfgFoundationKernel();
const bootstrapCompleted = foundation.fork();
const bootstrapCheckpoint = bootstrapCompleted.admissionCheckpoint();
installSetTheoryBootstrap(bootstrapCompleted);
const bootstrapCompile = measure(() => compileSeparateKernelModule(
  foundation, foundation, bootstrapCompleted, bootstrapCheckpoint, { module: "Grace.Bootstrap" },
));
const bootstrapBinary = encodeSeparateKernelModule(bootstrapCompile.value);
const bootstrapDecode = measure(() => decodeSeparateKernelModule(bootstrapBinary));
const bootstrapReplay = measure(() => replaySeparateKernelModuleExact(foundation, bootstrapDecode.value));
const separateKernel = bootstrapReplay.value.fork();
const separateCheckpoint = separateKernel.admissionCheckpoint();
measure(() => loadModuleGraph(separateKernel, [cumulus], [library]));
const bootstrapDependency = [{ module: bootstrapCompile.value.module, digest: bootstrapCompile.value.digest }];
const separateCompile = measure(() => compileSeparateKernelModule(
  foundation, bootstrapReplay.value, separateKernel, separateCheckpoint,
  { module: "Grace.Cumulus", dependencies: bootstrapDependency },
));
const separateBinary = encodeSeparateKernelModule(separateCompile.value);
const separateDecode = measure(() => decodeSeparateKernelModule(separateBinary));
const separateReplay = measure(() => replaySeparateKernelModuleExact(bootstrapReplay.value, separateDecode.value));
const surfaceIndex = encodeSurfaceEnvironmentIndex(exportSurfaceEnvironmentIndex(
  kernel, separateCompile.value.module, separateCompile.value.digest,
));

console.log(`Cumulus: ${theoremNames.length.toLocaleString()} theorems, ${replay.value.stats.instructions.toLocaleString()} instructions`);
console.log(`source elaboration + kernel admission  ${source.milliseconds.toFixed(1).padStart(8)} ms`);
console.log(`G17M judgment export               ${exports.milliseconds.toFixed(1).padStart(8)} ms`);
console.log(`G17M arena compilation             ${compiled.milliseconds.toFixed(1).padStart(8)} ms`);
console.log(`G17M binary decode                 ${decoded.milliseconds.toFixed(1).padStart(8)} ms`);
console.log(`G17M cold replay                   ${replay.milliseconds.toFixed(1).padStart(8)} ms  (${Math.round(rate).toLocaleString()} instructions/s)`);
console.log(`G17M warm replay                   ${warmReplay.milliseconds.toFixed(1).padStart(8)} ms  (${Math.round(warmRate).toLocaleString()} instructions/s)`);
console.log(`G17M size                          ${(binary.length / 1024).toFixed(1).padStart(8)} KiB`);
console.log(`G17C event compilation             ${eventCompile.milliseconds.toFixed(1).padStart(8)} ms`);
console.log(`G17C canonical decode              ${eventDecode.milliseconds.toFixed(1).padStart(8)} ms`);
console.log(`G17C checked admission replay      ${eventReplay.milliseconds.toFixed(1).padStart(8)} ms`);
console.log(`G17C size                          ${(eventBinary.length / 1024).toFixed(1).padStart(8)} KiB`);
if (eventReplay.value.digest() !== kernel.digest()) throw new Error("G17C replay digest mismatch");
console.log(`dense G17C compilation              ${denseCompile.milliseconds.toFixed(1).padStart(8)} ms`);
console.log(`dense G17C canonical decode         ${denseDecode.milliseconds.toFixed(1).padStart(8)} ms`);
console.log(`dense G17C checked replay            ${denseReplay.milliseconds.toFixed(1).padStart(8)} ms`);
console.log(`dense G17C size                      ${(denseBinary.length / 1024).toFixed(1).padStart(8)} KiB`);
if (denseReplay.value.digest() !== kernel.digest()) throw new Error("Dense G17C replay digest mismatch");
console.log(`bootstrap G17C compilation          ${bootstrapCompile.milliseconds.toFixed(1).padStart(8)} ms`);
console.log(`bootstrap G17C canonical decode     ${bootstrapDecode.milliseconds.toFixed(1).padStart(8)} ms`);
console.log(`bootstrap G17C checked replay       ${bootstrapReplay.milliseconds.toFixed(1).padStart(8)} ms`);
console.log(`bootstrap G17C size                 ${(bootstrapBinary.length / 1024).toFixed(1).padStart(8)} KiB`);
console.log(`separate G17C compilation           ${separateCompile.milliseconds.toFixed(1).padStart(8)} ms`);
console.log(`separate G17C canonical decode      ${separateDecode.milliseconds.toFixed(1).padStart(8)} ms`);
console.log(`separate G17C exact replay          ${separateReplay.milliseconds.toFixed(1).padStart(8)} ms`);
console.log(`separate G17C size                  ${(separateBinary.length / 1024).toFixed(1).padStart(8)} KiB`);
console.log(`surface-index sidecar size          ${(surfaceIndex.length / 1024).toFixed(1).padStart(8)} KiB`);
if (separateReplay.value.digest() !== kernel.digest() || separateKernel.digest() !== kernel.digest()) {
  throw new Error("Separate G17C replay digest mismatch");
}
