// Phase-separated Workbench performance audit.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore
// Usage: node scripts/profile-file-check.ts [--no-profile] Geometry/Circumcenter.g17
// Run comparisons sequentially, with no concurrent builds/checks.
import { readFileSync, mkdirSync, writeFileSync } from "node:fs";
import { Session } from "node:inspector";
const { checkWorkbenchFiles, prepareWorkbenchFiles } = await import(process.argv.includes("--browser")
  ? "../workbench/generated/src/workbench.js" : "../src/workbench.ts");
const out = process.env.GRACE_AUDIT_OUT ?? "build/file-audit";
const profiling = !process.argv.includes("--no-profile");
const cachedRepeats = Number(process.argv.find(argument => argument.startsWith("--cached-repeats="))?.split("=")[1] ?? 1);
if (!Number.isInteger(cachedRepeats) || cachedRepeats < 1 || cachedRepeats > 100)
  throw Error("--cached-repeats must be an integer from 1 to 100");
mkdirSync(out, { recursive: true });
const inspector = new Session();
inspector.connect();
const post = (method: string) => new Promise<any>((resolve, reject) =>
  inspector.post(method as any, (error, result) => error ? reject(error) : resolve(result)));
const rows: { file: string; phase: string; wallMs: number; reportedMs: number }[] = [];
try {
  if (profiling) await post("Profiler.enable");
  for (const file of process.argv.slice(2).filter(argument => !argument.startsWith("--"))) {
    const source = readFileSync(`lib/Grace/Cumulus/${file}`, "utf8");
    let current = source;
    for (const phase of ["dependencies", "first", "comment-edit", ...Array.from({ length: cachedRepeats }, () => "cached")]) {
      // A comment-only edit measures cache reuse, not fresh proof execution.
      if (phase === "comment-edit") current = source + "\n-- Audit comment edit.\n";
      const files = [{ name: file, source: current }];
      if (profiling) await post("Profiler.start");
      const start = performance.now();
      const result = phase === "dependencies"
        ? prepareWorkbenchFiles(files, "ZFG", file)
        : checkWorkbenchFiles(files, "ZFG", [file], { includeKernelDetails: false, includeEnvironmentDigest: !process.argv.includes("--live") });
      const wall = performance.now() - start;
      if (profiling) {
        const { profile } = await post("Profiler.stop");
        writeFileSync(`${out}/${file.replaceAll("/", "_")}-${phase}.cpuprofile`, JSON.stringify(profile));
      }
      if (!result.ok) throw Error(JSON.stringify(result));
      const row = { file, phase, wallMs: +wall.toFixed(2), reportedMs: result.milliseconds };
      rows.push(row);
      console.log(JSON.stringify(row));
      writeFileSync(`${out}/measurements.json`, JSON.stringify(rows, null, 2) + "\n");
    }
  }
} finally { inspector.disconnect(); }
