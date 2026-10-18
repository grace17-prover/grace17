import { performance } from "node:perf_hooks";
import {
  app, checkProofDag, congr, definition, encodeProofDag, eq, prepareRewrites,
  refl, settle, v, type Proof, type SettleStats,
} from "../src/index.ts";
import { buildArithmeticSuite } from "./arithmetic-suite.ts";

const { kernel } = buildArithmeticSuite();
const rules: Proof[] = [definition("plus", "equation.0"), definition("plus", "equation.1")];
for (let index = 0; index < 2_000; index += 1) {
  const name = `irrelevant${index}`;
  kernel.defineFunction(name, ["x"], v("x"));
  rules.push(definition(name));
}
const prepareStart = performance.now();
const prepared = prepareRewrites(kernel, rules);
const prepareMs = performance.now() - prepareStart;
const numeral = (value: number) => {
  let result = app("zero");
  for (let index = 0; index < value; index += 1) result = app("succ", result);
  return result;
};
const stats: SettleStats = { rules: 0, termsVisited: 0, candidatesConsidered: 0, rewrites: 0 };
const settleStart = performance.now();
settle(kernel, eq(app("plus", numeral(8), numeral(9)), numeral(17)), { using: prepared, stats });
const settleMs = performance.now() - settleStart;

let shared: Proof = refl(app("zero"));
for (let depth = 0; depth < 18; depth += 1) shared = congr("pair", shared, shared);
const dag = encodeProofDag(shared);
const dagStart = performance.now();
const checked = checkProofDag(kernel, dag);
const dagMs = performance.now() - dagStart;
const replayCount = 5_000;
const replayStart = performance.now();
for (let index = 0; index < replayCount; index += 1) checkProofDag(kernel, dag);
const replayMs = performance.now() - replayStart;

console.log("GRACE17 scaling suite");
console.log(`  rewrite rules             ${stats.rules.toLocaleString()}`);
console.log(`  index preparation         ${prepareMs.toFixed(3)} ms`);
console.log(`  8 + 9 rewrite proof       ${settleMs.toFixed(3)} ms`);
console.log(`  candidate rules examined  ${stats.candidatesConsidered}`);
console.log(`  proof tree nodes          ${checked.treeNodes.toLocaleString()}`);
console.log(`  proof DAG nodes           ${checked.dagNodes.toLocaleString()}`);
console.log(`  DAG checker visits/hits   ${checked.stats.nodesVisited}/${checked.stats.cacheHits}`);
console.log(`  authenticated tape replay ${dagMs.toFixed(3)} ms`);
console.log(`  sustained replay          ${Math.round(replayCount / (replayMs / 1_000)).toLocaleString()} proofs/s`);
