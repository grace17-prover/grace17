import { performance } from "node:perf_hooks";
import {
  compileProofModule, encodeProofMachineBinary, exportTheorem, verifyProofMachineBinary,
} from "../src/index.ts";
import { buildProofSuite } from "./proof-suite.ts";

const start = performance.now();
const suite = buildProofSuite();
const module = compileProofModule(suite.examples.map(example => exportTheorem(suite.kernel, example.name)));
const binary = encodeProofMachineBinary(module);
const checked = verifyProofMachineBinary(suite.kernel, binary);

const elapsed = performance.now() - start;
console.log(`checked ${checked.theorems} proofs (${checked.instructions} instructions, ${binary.length} binary bytes) in ${elapsed.toFixed(1)} ms`);
