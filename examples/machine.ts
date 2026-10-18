import { performance } from "node:perf_hooks";
import { compileProofMachine, createZfgKernel, exportTheorem, MachineOp, verifyProofMachine, type ProofMachineProgram } from "../src/index.ts";
import { buildProofSuite } from "./proof-suite.ts";

const suite = buildProofSuite();
const repetitions = 20_000;

console.log("GRACE17 numeric proof-machine suite");
for (const example of suite.examples) {
  const program = compileProofMachine(exportTheorem(suite.kernel, example.name));
  verifyProofMachine(suite.kernel, program);
  let start = performance.now();
  for (let index = 0; index < repetitions; index += 1) suite.kernel.checkProofWithStats(example.proof);
  const referenceElapsed = performance.now() - start;
  const referenceRate = repetitions / (referenceElapsed / 1_000);
  start = performance.now();
  for (let index = 0; index < repetitions; index += 1) verifyProofMachine(suite.kernel, program);
  const elapsed = performance.now() - start;
  const proofsPerSecond = repetitions / (elapsed / 1_000);
  console.log(`  ${example.name.padEnd(24)} ${program.code.length.toString().padStart(3)} instructions`);
  console.log(`    reference ${Math.round(referenceRate).toLocaleString()} proofs/s; machine ${Math.round(proofsPerSecond).toLocaleString()} proofs/s; ${Math.round(proofsPerSecond * program.code.length).toLocaleString()} instructions/s`);
  console.log(`    ${program.terms.length} term nodes; ${program.formulas.length} formula nodes; ${program.symbols.length} symbols`);
}
console.log("  reference AST kernel and numeric machine agree on every result");

// Long tapes model release/module checking and amortize per-certificate setup.
const bulkInstructions = 250_000;
const bulkKernel = createZfgKernel();
const bulk: ProofMachineProgram = Object.freeze({
  version: 3,
  environment: bulkKernel.digest(),
  symbols: Object.freeze(["zero"]),
  terms: Object.freeze([Object.freeze([2, 0])]),
  formulas: Object.freeze([Object.freeze([1, 0, 0])]),
  contexts: Object.freeze([Object.freeze([])]),
  code: Object.freeze(Array.from({ length: bulkInstructions }, () => Object.freeze([MachineOp.refl, 0, 0, 0, 0]))),
  root: bulkInstructions - 1,
});
verifyProofMachine(bulkKernel, bulk);
const bulkStart = performance.now();
verifyProofMachine(bulkKernel, bulk);
const bulkElapsed = performance.now() - bulkStart;
console.log(`  bulk tape                  ${bulkInstructions.toLocaleString()} instructions; ${(bulkElapsed).toFixed(3)} ms; ${Math.round(bulkInstructions / (bulkElapsed / 1_000)).toLocaleString()} instructions/s`);
