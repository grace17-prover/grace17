#!/usr/bin/env node
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Run each test file in its own process with a bounded heap. The built-in
// parallel runner keeps every file's kernel in one process group and exhausts
// memory on a 16 GB machine; one process per file keeps the peak at the
// largest single file. `--shard i/n` takes every n-th file starting at i, for
// CI jobs that split the suite; `--concurrency k` runs k files at once.

import { spawn } from "node:child_process";
import { readdirSync } from "node:fs";
import { cpus } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

const args = process.argv.slice(2);
const option = (name: string): string | undefined => {
  const index = args.indexOf(name);
  return index >= 0 ? args[index + 1] : undefined;
};
const shard = /^(\d+)\/(\d+)$/.exec(option("--shard") ?? "1/1");
if (!shard) { console.error("--shard expects i/n"); process.exit(2); }
const shardIndex = Number(shard[1]) - 1;
const shardCount = Number(shard[2]);
const concurrency = Number(option("--concurrency") ?? Math.max(1, Math.min(2, cpus().length >> 1)));
const heap = option("--heap") ?? "8192";
// `--exclude a,b` leaves out every test file whose name contains one of the
// pieces, before sharding, so a heavy file can run in its own job.
const excluded = (option("--exclude") ?? "").split(",").map(item => item.trim()).filter(Boolean);
const filters = args.filter((item, index) => !item.startsWith("--") && !["--shard", "--concurrency", "--heap", "--exclude"].includes(args[index - 1] ?? ""));
// Library imports come from a module store unless --from-source is given.
const preload = args.includes("--from-source") ? [] : ["--import", fileURLToPath(new URL("../tests/helpers/library-store.ts", import.meta.url))];

const tests = fileURLToPath(new URL("../tests", import.meta.url));
const files = readdirSync(tests).filter(name => name.endsWith(".test.ts")).sort()
  .filter(name => filters.length === 0 || filters.some(filter => name.includes(filter)))
  .filter(name => !excluded.some(piece => name.includes(piece)))
  .filter((_, index) => index % shardCount === shardIndex);

const failures: string[] = [];
let next = 0;
let passed = 0;
const started = performance.now();

function runOne(name: string): Promise<void> {
  return new Promise(resolveRun => {
    const fileStarted = performance.now();
    const child = spawn(process.execPath, [
      `--max-old-space-size=${heap}`, "--disable-warning=ExperimentalWarning", ...preload, "--test", join(tests, name),
    ], {
      stdio: ["ignore", "pipe", "pipe"],
      // The processes a test spawns (a compile of the library, a checker) get
      // the same heap as the test itself, as they do under the CI workflow.
      env: { ...process.env, NODE_OPTIONS: `--max-old-space-size=${heap}` },
    });
    let output = "";
    child.stdout.on("data", chunk => { output += chunk; });
    child.stderr.on("data", chunk => { output += chunk; });
    child.on("close", (code, signal) => {
      const seconds = ((performance.now() - fileStarted) / 1000).toFixed(1);
      if (code === 0) { passed += 1; console.log(`ok   ${name} (${seconds}s)`); }
      else {
        failures.push(name);
        console.log(`FAIL ${name} (${seconds}s${signal ? `, ${signal}` : `, exit ${code}`})`);
        console.log(output.split("\n").filter(line => !/^ℹ |^# /.test(line)).join("\n"));
      }
      resolveRun();
    });
  });
}

async function worker(): Promise<void> {
  while (next < files.length) await runOne(files[next++]!);
}

await Promise.all(Array.from({ length: Math.min(concurrency, files.length) }, worker));
const seconds = ((performance.now() - started) / 1000).toFixed(1);
console.log(`${passed} of ${files.length} test files passed in ${seconds}s${failures.length ? `; failed: ${failures.join(", ")}` : ""}`);
process.exitCode = failures.length ? 1 : 0;
