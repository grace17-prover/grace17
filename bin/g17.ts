#!/usr/bin/env node
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Launcher: the command line lives in src/cli.ts. The sources are run from a
// prebuilt JavaScript copy under build/cli when it is current, so a run does
// not strip and compile every source file; a stale or missing copy is rebuilt
// first (scripts/build-cli.ts), which is also what makes it current again
// after the sources change. The launcher also gives the run the heap the
// settings ask for: when the runtime's limit is below it, the command is run
// again in a child with that limit, and this process reports its result.

import { enableCompileCache } from "node:module";
import { spawnSync } from "node:child_process";
import { existsSync, readFileSync, readdirSync, statSync } from "node:fs";
import { join } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { getHeapStatistics } from "node:v8";

try { enableCompileCache(); } catch { /* an unsupported runtime runs without the cache */ }

const project = fileURLToPath(new URL("..", import.meta.url));
const sources = join(project, "src");
const built = join(project, "build", "cli");
const stampPath = join(built, "stamp.json");

function currentStamp(): string {
  return JSON.stringify(readdirSync(sources).filter(name => name.endsWith(".ts")).sort()
    .map(name => [name, statSync(join(sources, name)).mtimeMs]));
}

const stamp = currentStamp();
if (!existsSync(stampPath) || readFileSync(stampPath, "utf8") !== stamp) {
  const { buildCli } = await import("../scripts/build-cli.ts");
  buildCli(project, stamp);
}
const args = process.argv.slice(2);
const { loadCliSettings } = await import(pathToFileURL(join(built, "src", "cli-settings.js")).href) as typeof import("../src/cli-settings.ts");

// A megabyte or two of slack: the limit the runtime reports is a little
// above the flag that set it.
const HEAP_SLACK_MB = 64;
let wanted: number | undefined;
try { wanted = loadCliSettings(args).heap; } catch { /* the command reports the settings error itself */ }
const limit = Math.floor(getHeapStatistics().heap_size_limit / 2 ** 20);
if (wanted !== undefined && process.env.G17_LAUNCHED !== "1" && limit + HEAP_SLACK_MB < wanted) {
  const execArgv = process.execArgv.filter(item => !item.startsWith("--max-old-space-size"));
  const child = spawnSync(process.execPath,
    [`--max-old-space-size=${wanted}`, "--disable-warning=ExperimentalWarning", ...execArgv, fileURLToPath(import.meta.url), ...args],
    { stdio: "inherit", env: { ...process.env, G17_LAUNCHED: "1" } });
  if (child.error) throw child.error;
  if (child.signal) process.kill(process.pid, child.signal);
  process.exit(child.status ?? 1);
}
const { runCli } = await import(pathToFileURL(join(built, "src", "cli.js")).href) as typeof import("../src/cli.ts");
runCli(args);
