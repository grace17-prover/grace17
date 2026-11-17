// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// The checks of the complete Cumulus that run in their own processes: the
// command line over the whole library, and the compile of its machine module
// replayed by the independent Python checker. They live apart from the
// in-process replay of cumulus.test.ts so that no test process holds the
// whole library while a child does the same.

import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

const project = fileURLToPath(new URL("..", import.meta.url));

test("the CLI accepts multiple module roots for Cumulus", () => {
  const run = spawnSync(process.execPath, ["bin/g17.ts", "check", "--json",
    "--module-root", "lib", "lib/Grace/Cumulus.g17"], {
    cwd: project, encoding: "utf8", maxBuffer: 16 * 1024 * 1024,
  });
  assert.equal(run.status, 0, run.stderr);
  const report = JSON.parse(run.stdout);
  assert.equal(report.ok, true);
  assert.ok(report.checked.some((item: { file: string }) => item.file.endsWith("lib/Grace/Cumulus/Order.g17")));
});

test("the independent Python checker replays the complete Cumulus machine module", () => {
  const directory = mkdtempSync(join(tmpdir(), "g17-cumulus-python-"));
  const machine = join(directory, "Cumulus.g17m");
  const environment = join(directory, "Cumulus.g17env");
  const compile = spawnSync(process.execPath, ["bin/g17.ts", "compile",
    "--module-root", "lib", "lib/Grace/Cumulus.g17",
    "--out", machine, "--environment", environment], { cwd: project, encoding: "utf8" });
  assert.equal(compile.status, 0, compile.stderr);
  const checked = spawnSync("python3", ["checkers/python/g17check.py", machine,
    "--environment", environment, "--json"], { cwd: project, encoding: "utf8" });
  assert.equal(checked.status, 0, checked.stderr);
  const report = JSON.parse(checked.stdout);
  assert.equal(report.ok, true);
  const compiled = compile.stdout.match(/compiled (\d+) theorems.*\((\d+) instructions,/);
  assert.ok(compiled, compile.stdout);
  assert.equal(report.theorems, Number(compiled[1]));
  assert.equal(report.instructions, Number(compiled[2]));
});
