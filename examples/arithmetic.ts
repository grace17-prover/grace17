import { performance } from "node:perf_hooks";
import { app, canonical, definition, eq, settle } from "../src/index.ts";
import { buildArithmeticSuite } from "./arithmetic-suite.ts";

const suite = buildArithmeticSuite();
const arithmetic = suite.examples.filter(example =>
  example.name.startsWith("plus.") || example.name.startsWith("times."));

console.log("GRACE17 arithmetic suite");
for (const example of arithmetic) {
  const repetitions = 2_000;
  const start = performance.now();
  for (let index = 0; index < repetitions; index += 1) suite.kernel.checkProof(example.proof);
  const elapsed = performance.now() - start;
  console.log(`  ${example.name.padEnd(26)} admitted ${example.checkMilliseconds.toFixed(3)} ms; ${Math.round(repetitions / (elapsed / 1_000)).toLocaleString()} checks/s`);
}

const numeral = (value: number) => {
  let result = app("zero");
  for (let index = 0; index < value; index += 1) result = app("succ", result);
  return result;
};
const computation = app("times", app("plus", numeral(2), numeral(3)), numeral(4));
const twenty = numeral(20);
const checked = suite.kernel.evaluateCertified(computation);
suite.kernel.checkProof(checked.proof);
if (canonical(checked.value) !== canonical(twenty)) throw new Error("Certified evaluator returned the wrong numeral");
const rewriteStart = performance.now();
const rewriteProof = settle(suite.kernel, eq(computation, twenty), {
  using: [
    definition("plus", "equation.0"),
    definition("plus", "equation.1"),
    definition("times", "equation.0"),
    definition("times", "equation.1"),
  ],
});
suite.kernel.checkProof(rewriteProof);
console.log(`  certified computation      (2 + 3) * 4 = 20; rewrite proof ${(performance.now() - rewriteStart).toFixed(3)} ms`);
console.log(`  environment digest         ${suite.kernel.digest()}`);
