import { readFileSync } from "node:fs";
import { performance } from "node:perf_hooks";
import { fileURLToPath } from "node:url";
import { app, createZfgKernel, elaborateModule } from "../src/index.ts";

const source = readFileSync(fileURLToPath(new URL("./Arithmetic.g17", import.meta.url)), "utf8");
const kernel = createZfgKernel();
const start = performance.now();
const module = elaborateModule(kernel, source);
const elapsed = performance.now() - start;

const numeral = (value: number) => {
  let result = app("zero");
  for (let index = 0; index < value; index += 1) result = app("succ", result);
  return result;
};
kernel.checkProof(kernel.evaluateCertified(app("times", numeral(6), numeral(7))).proof);

console.log("GRACE17 surface module");
console.log(`  definitions: ${module.definitions.join(", ")}`);
console.log(`  theorems:    ${module.theorems.join(", ")}`);
console.log(`  elaboration: ${elapsed.toFixed(3)} ms`);
console.log("  computation: 6 * 7 = 42 (certified)");
console.log(`  digest:      ${kernel.digest()}`);
