import { readFileSync } from "node:fs";
import { performance } from "node:perf_hooks";
import { app, callNative, createZfgKernel, elaborateModule, type Term } from "../src/index.ts";

const kernel = createZfgKernel();
elaborateModule(kernel, readFileSync(new URL("CoreNat.g17", import.meta.url), "utf8"));
elaborateModule(kernel, readFileSync(new URL("ModuleCompute.g17", import.meta.url), "utf8"));

const numeral = (value: number): Term => {
  let result = app("zero");
  for (let index = 0; index < value; index += 1) result = app("succ", result);
  return result;
};

const started = performance.now();
const result = kernel.evaluateFastWithStats(
  app("Grace.Examples.Compute.Demo.double", numeral(500)),
  10_000_000,
);
const elapsed = performance.now() - started;
const nativeStarted = performance.now();
const native = callNative(kernel, "Grace.Examples.Compute.Demo.double", [100_000n]);
const nativeElapsed = performance.now() - nativeStarted;

let value = 0;
let cursor = result.value;
while (cursor.tag === "app" && cursor.fn === "succ" && cursor.args.length === 1) {
  value += 1;
  cursor = cursor.args[0]!;
}
if (cursor.tag !== "app" || cursor.fn !== "zero") throw new Error("result is not a natural numeral");

console.log(`double(500) = ${value}`);
console.log(`${result.stats.reductions.toLocaleString()} equation reductions in ${elapsed.toFixed(1)} ms; ${result.stats.cacheHits.toLocaleString()} DAG cache hits`);
console.log(`native double(100000) = ${native.value} in ${nativeElapsed.toFixed(3)} ms (no unary input tree)`);
