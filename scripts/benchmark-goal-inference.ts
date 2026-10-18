// Compare explicit and goal-directed applications of the quadratic-integrality lemma.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore
import assert from "node:assert/strict";
import { createZfKernel, loadModuleGraph, elaborateModule, exportTheoremForMachine, compileProofModule } from "../src/index.ts";

const count = 100;
const header = `module InferenceBenchmark
namespace InferenceBenchmark
import Grace.Cumulus.Algebra.MonicRelations
section Algebras
variable (A add zero neg mul one B plus z minus times unit f x a : Set)
notation ring R := (A, add, zero, neg, mul, one)
notation ring S := (B, plus, z, minus, times, unit)
hypothesis source : CommRing(R)
hypothesis target : CommRing(S)
hypothesis hom : RingHom(f, R, S)
hypothesis element : x ∈ S
hypothesis coefficient : a ∈ R
hypothesis quadratic : S[x * x] = f(a)
`;
const source = (explicit: boolean) => header + Array.from({ length: count }, (_, i) => `
theorem t${i}
  shows IntegralOver(f, R, S, x)
proof
  exact IntegralOver.of_square${explicit ? " at A, add, zero, neg, mul, one, B, plus, z, minus, times, unit, f, x, a" : ""} with *
`).join("\n") + "end Algebras\nend InferenceBenchmark\n";
const timings: Record<string, number[]> = { explicit: [], inferred: [] };
let expected: unknown;
for (let sample = 0; sample < 4; sample++) {
  for (const explicit of sample % 2 ? [false, true] : [true, false]) {
    const kernel = createZfKernel();
    loadModuleGraph(kernel, ["lib/Grace/Cumulus/Algebra/MonicRelations.g17"], ["lib"]);
    const input = source(explicit);
    const start = performance.now();
    elaborateModule(kernel, input);
    const elapsed = performance.now() - start;
    if (sample > 0) timings[explicit ? "explicit" : "inferred"]!.push(elapsed);
    const program = compileProofModule([exportTheoremForMachine(kernel, "InferenceBenchmark.t0")]);
    if (expected === undefined) expected = program;
    else assert.deepEqual(program, expected, "inference must emit exactly the explicit proof program");
  }
}
const median = (values: number[]) => [...values].sort((a, b) => a - b)[1];
console.log(JSON.stringify({ node: process.version, count,
  methodology: "100 applications of IntegralOver.of_square; dependencies loaded outside timer; one warmup pair, three measured alternating-order pairs; includes parsing, elaboration and kernel checking; exact emitted proof-program equality asserted.",
  milliseconds: timings, medianMilliseconds: { explicit: median(timings.explicit!), inferred: median(timings.inferred!) } }, null, 2));
