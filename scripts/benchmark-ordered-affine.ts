#!/usr/bin/env node
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Measure checked abstract ordered-ring certificates without import startup.
import { performance } from "node:perf_hooks";
import { fileURLToPath } from "node:url";
import { createZfgKernel, loadModuleGraph, loadModuleSourceGraph } from "../src/index.ts";

const library = fileURLToPath(new URL("../lib", import.meta.url));
const ordered = fileURLToPath(new URL("../lib/Grace/Cumulus/Algebra/OrderedAdditive.g17", import.meta.url));
const base = createZfgKernel();
loadModuleGraph(base, [ordered], [library]);
const add = (items: readonly string[]): string => items.length === 1 ? items[0]! :
  `call2(add, ${items[0]}, ${add(items.slice(1))})`;

function source(n: number, cancellation: boolean, irrelevant: number): string {
  const xs = Array.from({ length: n }, (_, index) => `x${index}`);
  const ys = Array.from({ length: n }, (_, index) => `y${index}`);
  const zs = Array.from({ length: irrelevant }, (_, index) => `z${index}`);
  const target = cancellation ? add([...xs, "call1(neg, y0)"]) : add(xs);
  const bound = cancellation ? add(ys.slice(1).reverse()) : add(ys.reverse());
  return `module User.AffineBenchmark
namespace User.AffineBenchmark
import Grace.Cumulus.Algebra.OrderedAdditive

theorem combined (A add zero neg mul one le ${[...xs, ...ys, ...zs].join(" ")} : Set)
  requires ring : OrderedRing(A, add, zero, neg, mul, one, le)
${[...xs, ...ys, ...zs].map(name =>

end User.AffineBenchmark
`  requires h${name} : ${name} ∈ A`).join("\n")}
${xs.map((name, index) => `  requires bound${index} : relates(le, ${name}, ${ys[index]})`).join("\n")}
${zs.map(name => `  requires unused${name} : relates(le, ${name}, ${name})`).join("\n")}
  shows relates(le, ${target}, ${bound})
proof
  linarith
`;
}

for (const [n, cancellation, irrelevant] of [
  [2, 0, 0], [4, 0, 0], [8, 0, 0], [8, 1, 0], [12, 0, 0], [16, 0, 0],
  [24, 0, 0], [32, 0, 0], [2, 0, 8], [2, 0, 32], [2, 0, 400],
] as const) {
  const name = `User.AffineBenchmark${n}_${cancellation}_${irrelevant}`;
  const started = performance.now();
  loadModuleSourceGraph(base, [{ file: `${name}.g17`, source: source(n, !!cancellation, irrelevant)
    .replace("User.AffineBenchmark\n", `${name}\n`) }], [library]);
  console.log(`${n} bounds, ${irrelevant} unused, cancellation ${!!cancellation}: ${(performance.now() - started).toFixed(1)} ms`);
}
