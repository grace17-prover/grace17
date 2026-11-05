// The Abhyankar–Sathaye blueprint elaborates as it stands: every module
// checks with its admissions, the README's module table names a planned
// home for each module, and the showcase statement is in the theorem module.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore
import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { readdirSync, readFileSync } from "node:fs";
import { join } from "node:path";

const root = "blueprints/AbhyankarSathaye";

function g17Files(directory: string): string[] {
  return readdirSync(directory, { withFileTypes: true }).flatMap(entry => {
    const path = join(directory, entry.name);
    return entry.isDirectory() ? g17Files(path) : entry.name.endsWith(".g17") ? [path] : [];
  }).sort();
}

test("the Abhyankar–Sathaye blueprint elaborates with its admissions", () => {
  const files = g17Files(root);
  assert.ok(files.length >= 16, `the blueprint has ${files.length} modules`);
  const run = spawnSync("node", ["--max-old-space-size=8192", "--disable-warning=ExperimentalWarning", "bin/g17.ts", "check",
    "--json", "--continue", "--quiet", "--module-root", "blueprints", "--module-root", "lib", ...files],
    { encoding: "utf8", maxBuffer: 1 << 28 });
  const report = JSON.parse(run.stdout) as { checked?: { file: string; theorems: string[] }[]; failed?: { file: string; error: string }[] };
  const failed = (report.failed ?? []).filter(item => item.file.includes(root));
  assert.deepEqual(failed.map(item => `${item.file}: ${item.error.slice(0, 120)}`), []);
  const checked = (report.checked ?? []).filter(item => item.file.includes(root));
  assert.equal(checked.length, files.length);
  const theorem = checked.find(item => item.file.endsWith("Theorem.g17"));
  assert.ok(theorem?.theorems.some(name => name.endsWith(".counterexample")), "the theorem module states counterexample");
  const readme = readFileSync(join(root, "README.md"), "utf8");
  const rows = readme.match(/^\| [A-Z][\w.]* \| \d \| [^|]+ \|$/gmu) ?? [];
  assert.equal(rows.length, files.length, "every module has a row in the module table");
});
