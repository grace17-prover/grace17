#!/usr/bin/env node
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { readdirSync, readFileSync } from "node:fs";
import { join, relative } from "node:path";
import { performance } from "node:perf_hooks";
import { fileURLToPath } from "node:url";
import { checkWorkbenchFiles, prepareWorkbenchFiles } from "../src/workbench.ts";

const project = fileURLToPath(new URL("..", import.meta.url));
const cumulus = join(project, "lib", "Grace", "Cumulus");
const requestedFile = process.env.GRACE_BENCH_FILE;
const files = readdirSync(cumulus, { recursive: true, withFileTypes: true })
  .filter(entry => entry.isFile() && entry.name.endsWith(".g17"))
  .map(entry => join(entry.parentPath, entry.name))
  .filter(path => relative(cumulus, path).includes("/"))
  .filter(path => !requestedFile || relative(cumulus, path) === requestedFile)
  .sort();

interface Measurement {
  readonly name: string;
  readonly dependencies: number;
  readonly leaf: number;
  readonly edited: number;
  readonly cached: number;
  readonly theorems: number;
}

const measurements: Measurement[] = [];
const started = performance.now();
for (const path of files) {
  const name = relative(cumulus, path);
  const opened = [{ name, source: readFileSync(path, "utf8") }];
  const dependencies = prepareWorkbenchFiles(opened, "ZFG", name);
  const leaf = checkWorkbenchFiles(opened, "ZFG", [name], { includeKernelDetails: false });
  if (!leaf.ok) throw new Error(`${name}: ${leaf.error}`);
  const editedFiles = [{ name, source: `${opened[0]!.source}\n-- performance-audit edit\n` }];
  const edited = checkWorkbenchFiles(editedFiles, "ZFG", [name], { includeKernelDetails: false });
  if (!edited.ok) throw new Error(`${name}: ${edited.error}`);
  const cached = checkWorkbenchFiles(editedFiles, "ZFG", [name], { includeKernelDetails: false });
  if (!cached.ok) throw new Error(`${name}: ${cached.error}`);
  measurements.push({
    name,
    dependencies: dependencies.milliseconds,
    leaf: leaf.milliseconds,
    edited: edited.milliseconds,
    cached: cached.milliseconds,
    theorems: cached.theorems.length,
  });
}

measurements.sort((left, right) => right.edited - left.edited);
console.log(
  "file".padEnd(38), "dependencies".padStart(13), "leaf".padStart(10),
  "edited".padStart(10), "cached".padStart(10), "theorems".padStart(10),
);
for (const item of measurements) {
  console.log(
    item.name.padEnd(38),
    `${item.dependencies.toFixed(1)} ms`.padStart(13),
    `${item.leaf.toFixed(1)} ms`.padStart(10),
    `${item.edited.toFixed(1)} ms`.padStart(10),
    `${item.cached.toFixed(1)} ms`.padStart(10),
    String(item.theorems).padStart(10),
  );
}
const coldOver = measurements.filter(item => item.leaf >= 100);
const editedOver = measurements.filter(item => item.edited >= 100);
console.log(`\n${measurements.length} files · ${coldOver.length} cold leaves at or above 100 ms · ${editedOver.length} edited leaves at or above 100 ms · ${(performance.now() - started).toFixed(1)} ms audit`);
if (coldOver.length > 0 || editedOver.length > 0) process.exitCode = 1;
