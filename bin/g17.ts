#!/usr/bin/env node
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Launcher: the command line lives in src/cli.ts. The sources are run from a
// prebuilt JavaScript copy under build/cli when it is current, so a run does
// not strip and compile every source file; a stale or missing copy is rebuilt
// first (scripts/build-cli.ts), which is also what makes it current again
// after the sources change.

import { enableCompileCache } from "node:module";
import { existsSync, readFileSync, readdirSync, statSync } from "node:fs";
import { join } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

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
const { runCli } = await import(pathToFileURL(join(built, "src", "cli.js")).href) as typeof import("../src/cli.ts");
runCli(process.argv.slice(2));
