import { performance } from "node:perf_hooks";
import { buildProofSuite } from "./proof-suite.ts";

const suite = buildProofSuite();
const coldRepetitions = 20_000;
const incrementalRepetitions = 1_000_000;

console.log("GRACE17 reference AST proof ergonomics suite");
for (const example of suite.examples) {
  const nodes = proofNodes(example.proof);
  let start = performance.now();
  for (let index = 0; index < coldRepetitions; index += 1) {
    suite.kernel.checkProofWithStats(example.proof);
  }
  const coldElapsed = performance.now() - start;
  const coldRate = Math.round(coldRepetitions / (coldElapsed / 1_000));
  start = performance.now();
  for (let index = 0; index < incrementalRepetitions; index += 1) {
    suite.kernel.checkProof(example.proof);
  }
  const incrementalElapsed = performance.now() - start;
  const incrementalRate = Math.round(incrementalRepetitions / (incrementalElapsed / 1_000));
  console.log(`  ${example.name.padEnd(24)} ${nodes.toString().padStart(3)} nodes; admitted ${example.checkMilliseconds.toFixed(3)} ms`);
  console.log(`    cold ${coldRate.toLocaleString()} proofs/s (${Math.round(coldRate * nodes).toLocaleString()} nodes/s); incremental ${incrementalRate.toLocaleString()} hits/s`);
}
console.log(`  environment digest       ${suite.kernel.digest()}`);

function proofNodes(value: unknown): number {
  if (value === null || typeof value !== "object") return 0;
  const record = value as Record<string, unknown>;
  let count = typeof record.rule === "string" ? 1 : 0;
  for (const child of Object.values(record)) {
    if (Array.isArray(child)) count += child.reduce((sum, item) => sum + proofNodes(item), 0);
    else count += proofNodes(child);
  }
  return count;
}
