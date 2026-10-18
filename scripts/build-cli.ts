#!/usr/bin/env node
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Write a plain JavaScript copy of src/ to build/cli/src for the command
// line, so a run loads JavaScript instead of stripping every TypeScript file.
// The stamp records the source modification times the copy was made from.
//
//   node scripts/build-cli.ts

import { mkdirSync, readdirSync, readFileSync, renameSync, writeFileSync } from "node:fs";
import { stripTypeScriptTypes } from "node:module";
import { basename, join } from "node:path";
import { fileURLToPath } from "node:url";

export function buildCli(project: string, stamp: string): void {
  const sources = join(project, "src");
  const output = join(project, "build", "cli", "src");
  mkdirSync(output, { recursive: true });
  for (const name of readdirSync(sources)) {
    if (!name.endsWith(".ts")) continue;
    let javascript = stripTypeScriptTypes(readFileSync(join(sources, name), "utf8"), { mode: "strip" })
      .replaceAll(/(from\s+["'][^"']+)\.ts(["'])/g, "$1.js$2")
      .replaceAll(/(import\(\s*["'][^"']+)\.ts(["']\s*\))/g, "$1.js$2");
    // The copy sits three directories below the project root instead of one.
    if (name === "project-root.ts") javascript = javascript.replace('new URL("..", import.meta.url)', 'new URL("../../..", import.meta.url)');
    const target = join(output, `${basename(name, ".ts")}.js`);
    writeFileSync(`${target}.${process.pid}.tmp`, javascript);
    renameSync(`${target}.${process.pid}.tmp`, target);
  }
  const stampPath = join(project, "build", "cli", "stamp.json");
  writeFileSync(`${stampPath}.${process.pid}.tmp`, stamp);
  renameSync(`${stampPath}.${process.pid}.tmp`, stampPath);
}

if (process.argv[1] && fileURLToPath(import.meta.url) === process.argv[1]) {
  const project = fileURLToPath(new URL("..", import.meta.url));
  const sources = join(project, "src");
  const { statSync } = await import("node:fs");
  const stamp = JSON.stringify(readdirSync(sources).filter(name => name.endsWith(".ts")).sort()
    .map(name => [name, statSync(join(sources, name)).mtimeMs]));
  buildCli(project, stamp);
  console.log("Built build/cli");
}
