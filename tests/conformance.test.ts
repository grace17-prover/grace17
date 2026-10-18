// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { spawnSync } from "node:child_process";

const project = fileURLToPath(new URL("..", import.meta.url));
const manifest = JSON.parse(readFileSync(join(project, "conformance/manifest.json"), "utf8"));

test("checked-in conformance corpus covers every G17M opcode positively and negatively", () => {
  assert.equal(manifest.format, "grace17.conformance");
  assert.equal(manifest.version, 1);
  assert.equal(manifest.g17m_version, 4);
  assert.deepEqual(manifest.coverage.opcodes, Array.from({ length: 30 }, (_, index) => index));
  const accepts = new Set<number>(manifest.vectors.filter((item: any) => item.expected === "accept").map((item: any) => item.opcode));
  const rejects = new Set<number>(manifest.vectors.filter((item: any) => item.expected === "reject").map((item: any) => item.opcode));
  assert.deepEqual([...accepts].sort((a, b) => a - b), manifest.coverage.opcodes);
  assert.deepEqual([...rejects].sort((a, b) => a - b), manifest.coverage.opcodes);
});

test("TypeScript and independent Python checkers agree with every conformance expectation", () => {
  const typescript = spawnSync(process.execPath, ["scripts/check-conformance.ts"], {
    cwd: project, encoding: "utf8",
  });
  assert.equal(typescript.status, 0, typescript.stderr);
  assert.match(typescript.stdout, new RegExp(`passed ${manifest.vectors.length} conformance vectors`));

  const python = spawnSync("python3", ["checkers/python/check_conformance.py"], {
    cwd: project, encoding: "utf8",
  });
  assert.equal(python.status, 0, python.stderr);
  assert.match(python.stdout, new RegExp(`passed ${manifest.vectors.length} conformance vectors`));
});
