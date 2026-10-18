// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Cold proof execution without the Workbench or its environment hashing.
// Usage: node --disable-warning=ExperimentalWarning scripts/profile-proof-execution.ts [output-prefix] [--no-profile] [--suite | --library] [--timing-only]
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname } from "node:path";
import { Session } from "node:inspector";
import { createZfgKernel, loadModuleGraph, elaborateModule,
  exportTheoremForMachine, compileProofModule } from "../src/index.ts";

const kernel = createZfgKernel();
const preparationStart = performance.now();
const libraryMode = process.argv.includes("--library");
const modules = loadModuleGraph(kernel, [libraryMode ? "lib/Grace/Cumulus.g17" : "lib/Grace/Cumulus/Geometry.g17"], ["lib"]);
const preparationMilliseconds = performance.now() - preparationStart;
if (libraryMode) {
  console.log(JSON.stringify({ sourceMilliseconds: preparationMilliseconds,
    theorems: modules.reduce((count, module) => count + module.theorems.length, 0),
    environment: kernel.digest() }));
  process.exit(0);
}
const source = readFileSync("tests/fixtures/polynomial-midsegment.g17", "utf8");
const prefix = process.argv[2] ?? "build/proof-execution";
const timingOnly = process.argv.includes("--timing-only");
const profiling = !process.argv.includes("--no-profile");
mkdirSync(dirname(prefix), { recursive: true });
const session = new Session();
session.connect();
const post = (method: string, params = {}): Promise<any> => new Promise((resolve, reject) =>
  session.post(method as any, params, (error, result) => error ? reject(error) : resolve(result)));
const profile = async <T>(name: string, operation: () => T) => {
  if (profiling) await post("Profiler.start");
  const start = performance.now();
  const result = operation();
  const milliseconds = performance.now() - start;
  if (profiling) {
    const { profile } = await post("Profiler.stop");
    writeFileSync(`${prefix}-${name}.cpuprofile`, JSON.stringify(profile));
  }
  return { result, milliseconds };
};
try {
  if (profiling) await post("Profiler.enable");
  const elaboration = await profile("elaboration", () => elaborateModule(kernel, source));
  const name = "PolynomialRegression.original_midsegment_length";
  const proof = kernel.theoremProofs.get(name)!;
  // checkProofWithStats uses a fresh proof-result cache; it does not take a
  // theorem-cache hit from the elaboration just measured.
  const replay = await profile("replay", () => kernel.checkProofWithStats(proof));
  const machine = timingOnly ? undefined : compileProofModule([exportTheoremForMachine(kernel, name)]);
  const cases = [{ name: "polynomial", elaborationMilliseconds: elaboration.milliseconds,
    freshProofCacheReplayMilliseconds: replay.milliseconds, instructions: machine?.code.length }];
  if (process.argv.includes("--suite")) {
    for (const [label, path, target] of [
      ["induction", "examples/Arithmetic.g17", createZfgKernel()],
      ["sets", "examples/Sets.g17", createZfgKernel()],
      ["geometry", "examples/GeometryStarter.g17", kernel],
    ] as const) {
      const text = readFileSync(path, "utf8");
      const checked = await profile(label, () => elaborateModule(target, text));
      const replayed = await profile(`${label}-replay`, () => {
        for (const theorem of checked.result.theorems)
          target.checkProofWithStats(target.theoremProofs.get(theorem)!);
      });
      cases.push({ name: label, elaborationMilliseconds: checked.milliseconds,
        freshProofCacheReplayMilliseconds: replayed.milliseconds,
        instructions: timingOnly ? undefined : compileProofModule(checked.result.theorems.map(name => exportTheoremForMachine(target, name))).code.length });
    }
  }
  console.log(JSON.stringify({ preparationMilliseconds, cases, replay: replay.result.stats,
    rssBytes: process.memoryUsage().rss }));
} finally {
  session.disconnect();
}
