// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Profile the original expanded midsegment calculation after preparing imports.
// Usage: node --disable-warning=ExperimentalWarning scripts/profile-polynomial.ts [output.cpuprofile]
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname } from "node:path";
import { Session } from "node:inspector";
import { checkWorkbenchFiles, prepareWorkbenchFiles } from "../src/workbench.ts";

const file = { name: "PolynomialRegression.g17",
  source: readFileSync("tests/fixtures/polynomial-midsegment.g17", "utf8") };
const preparationStart = performance.now();
prepareWorkbenchFiles([file], "ZFG", file.name);
const preparationMilliseconds = performance.now() - preparationStart;
const session = new Session();
session.connect();
const post = (method: string, params = {}): Promise<any> => new Promise((resolve, reject) =>
  session.post(method as any, params, (error, result) => error ? reject(error) : resolve(result)));
try {
  await post("Profiler.enable");
  await post("Profiler.start");
  const start = performance.now();
  const result = checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false });
  const milliseconds = performance.now() - start;
  const { profile } = await post("Profiler.stop");
  const output = process.argv[2] ?? "build/polynomial.cpuprofile";
  mkdirSync(dirname(output), { recursive: true });
  writeFileSync(output, JSON.stringify(profile));
  console.log(JSON.stringify({ ok: result.ok, milliseconds, preparationMilliseconds, profile: output }));
  if (!result.ok) process.exitCode = 1;
} finally {
  session.disconnect();
}
