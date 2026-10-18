// Isolated source/checking measurement for the centroid and median extension.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore
import { readFileSync } from "node:fs";
import { createZfgKernel, loadModuleGraph, elaborateModule,
  exportTheoremForMachine, compileProofModule } from "../src/index.ts";

const kernel = createZfgKernel();
const start = performance.now();
loadModuleGraph(kernel, ["lib/Grace/Cumulus/Geometry/Parallelogram.g17"], ["lib"]);
const prepared = performance.now();
const checked = elaborateModule(kernel,
  readFileSync("lib/Grace/Cumulus/Geometry/Centroid.g17", "utf8"));
const done = performance.now();
const name = "Euclidean.centroid.concurrency";
const replayStart = performance.now();
const replay = kernel.checkProofWithStats(kernel.theoremProofs.get(name)!);
const replayDone = performance.now();
const machine = compileProofModule([exportTheoremForMachine(kernel, name)]);
console.log(JSON.stringify({ version: JSON.parse(readFileSync("package.json", "utf8")).version, node: process.version,
  methodology: "One fresh process; imports prepared outside leaf timer; no Workbench; fresh proof-result cache for replay; certificate uses checked library references.",
  preparationMilliseconds: prepared - start,
  leafMilliseconds: done - prepared, theorems: checked.theorems.length,
  concurrencyReplayMilliseconds: replayDone - replayStart,
  concurrencyStats: replay.stats, concurrencyInstructions: machine.code.length }, null, 2));
