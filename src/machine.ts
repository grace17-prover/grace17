// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { naturalValue, type Formula, type Term } from "./ast.ts";
import { decodeProofDag } from "./dag.ts";
import type { MachineProofExport } from "./export.ts";
import { KernelError } from "./errors.ts";
import { deepFreeze as freezeCertificate } from "./freeze.ts";
import type { Kernel } from "./kernel.ts";
import type { Proof } from "./proof.ts";

/** Dense opcodes for the first GRACE17 proof machine. */
export const MachineOp = Object.freeze({
  assumption: 0, axiom: 1, theorem: 2, definition: 3, refl: 4,
  symm: 5, trans: 6, congr: 7, impIntro: 8, impElim: 9,
  forallIntro: 10, forallElim: 11, induction: 12, eqElim: 13,
  andIntro: 14, andElimLeft: 15, andElimRight: 16,
  orIntroLeft: 17, orIntroRight: 18, orElim: 19,
  iffIntro: 20, iffElimLeft: 21, iffElimRight: 22,
  existsIntro: 23, existsElim: 24, falseElim: 25, dne: 26,
  wellFoundedInduction: 27,
  compute: 28,
  rationalClassCompute: 29,
} as const);

export interface ProofMachineProgram {
  readonly version: 4;
  /** SHA-256 digest of the canonical trusted environment snapshot. */
  readonly environment: string;
  readonly symbols: readonly string[];
  /** term: free-var(0,sym), bound-var(1,index), app(2,fn,...args), nat(3,decimal-sym) */
  readonly terms: readonly (readonly number[])[];
  /** formula: bottom=0, eq=1, pred=2, imp=3, forall=4, and/or/iff=5/6/7, exists=8 */
  readonly formulas: readonly (readonly number[])[];
  readonly contexts: readonly (readonly number[])[];
  /** instruction: op, conclusion, context, premise-count, premises..., data... */
  readonly code: readonly (readonly number[])[];
  readonly root: number;
}

export interface ProofMachineModuleProgram extends ProofMachineProgram {
  /** theorem-name symbol id, root instruction id */
  readonly theorems: readonly (readonly [number, number])[];
}

export interface MachineCheckStats {
  readonly instructions: number;
  readonly formulaNodes: number;
  readonly termNodes: number;
}

/** Compile the checked proof/trace pair into a dense, alpha-normalized program. */
export function compileProofMachine(exported: MachineProofExport): ProofMachineProgram {
  const arena = new Arena();
  const code: number[][] = [];
  const root = appendProof(arena, code, exported);
  const program: ProofMachineProgram = {
    version: 4,
    environment: exported.environment,
    symbols: arena.symbols,
    terms: arena.terms,
    formulas: arena.formulas,
    contexts: arena.contexts,
    code,
    root,
  };
  deepFreeze(program);
  return program;
}

/** Link many theorem certificates into one shared-arena, single-pass module tape. */
export function compileProofModule(exports: Iterable<MachineProofExport>): ProofMachineModuleProgram {
  const arena = new Arena();
  const code: number[][] = [];
  const theorems: [number, number][] = [];
  let environment: string | undefined;
  // Exports are consumed as they come, so a caller may produce them one
  // theorem at a time and let each go once it is on the tape.
  for (const exported of exports) {
    environment ??= exported.environment;
    if (exported.environment !== environment) throw new KernelError("Cannot link proofs from different environments");
    theorems.push([arena.symbolId(exported.theorem), appendProof(arena, code, exported)]);
  }
  if (environment === undefined) throw new KernelError("Cannot compile an empty proof module");
  const program: ProofMachineModuleProgram = {
    version: 4,
    environment,
    symbols: arena.symbols,
    terms: arena.terms,
    formulas: arena.formulas,
    contexts: arena.contexts,
    code,
    root: theorems.at(-1)![1],
    theorems,
  };
  deepFreeze(program);
  return program;
}

function appendProof(arena: Arena, code: number[][], exported: MachineProofExport): number {
  const proofs = decodeProofDag(exported.proof);
  const contextIds = exported.trace.nodes.map(node => arena.internContext(node.assumptions));
  const traceToInstruction = new Map<number, number>();

  const visit = (traceId: number): number => {
    const previous = traceToInstruction.get(traceId);
    if (previous !== undefined) return previous;
    const trace = exported.trace.nodes[traceId];
    if (!trace) throw new KernelError(`Machine compiler cannot find judgment ${traceId}`);
    const premises = trace.children.map(visit);
    const proof = proofs[trace.proofNode];
    if (!proof) throw new KernelError(`Machine compiler cannot find proof node ${trace.proofNode}`);
    const op = opcode(proof.rule);
    const data = instructionData(arena, proof);
    const instruction = [
      op, arena.internFormula(trace.conclusion), contextIds[traceId]!,
      premises.length, ...premises, ...data,
    ];
    const id = code.length;
    code.push(instruction);
    traceToInstruction.set(traceId, id);
    return id;
  };

  return visit(exported.trace.root);
}

/** Replay every numeric instruction. No tactics, rewriting, or proof search occur here. */
export function verifyProofMachine(kernel: Kernel, program: ProofMachineProgram): {
  readonly formula: Formula;
  readonly formulaId: number;
  readonly stats: MachineCheckStats;
} {
  return verifyProofMachineCurrent(kernel, program, true);
}

/**
 * Replay in the supplied live environment. G17C already authenticates its
 * ordered environment chain, so embedded batches need not re-hash the entire
 * growing kernel only to compare the standalone G17M binding field.
 */
export function verifyProofMachineCurrent(
  kernel: Kernel,
  program: ProofMachineProgram,
  requireEnvironmentDigest = false,
): {
  readonly formula: Formula;
  readonly formulaId: number;
  readonly stats: MachineCheckStats;
} {
  const { formula, formulaId, stats } = verifyProofMachineWithArena(kernel, program, requireEnvironmentDigest);
  return { formula, formulaId, stats };
}

/** The verification together with the arena it ran in, for a statement check on an unfrozen program. */
function verifyProofMachineWithArena(
  kernel: Kernel,
  program: ProofMachineProgram,
  requireEnvironmentDigest = false,
): {
  readonly formula: Formula;
  readonly formulaId: number;
  readonly stats: MachineCheckStats;
  readonly arena: Arena;
} {
  if (program.version !== 4 || (requireEnvironmentDigest && program.environment !== kernel.digest()) ||
      program.root < 0 || program.root >= program.code.length) {
    throw new KernelError("Malformed proof-machine program");
  }
  const arena = runtimeFor(program);
  arena.validateSignature(kernel, program.terms.length, program.formulas.length);
  const results = arena.results;
  const requireClosedRoot = (root: number): void => {
    const instruction = program.code[root];
    if (!instruction || arena.context(instruction[2]).length !== 0) {
      throw new KernelError("Machine proof roots and theorem boundaries must have empty contexts");
    }
  };
  requireClosedRoot(program.root);
  const boundaryRoots = new Map<string, number>();
  if ("theorems" in program) {
    for (const [nameId, root] of program.theorems) {
      const name = arena.symbol(nameId);
      requireClosedRoot(root);
      if (boundaryRoots.has(name)) throw new KernelError(`Duplicate machine theorem boundary: ${name}`);
      boundaryRoots.set(name, root);
    }
  }

  for (let pc = 0; pc < program.code.length; pc += 1) {
    const instruction = program.code[pc]!;
    if (instruction.length < 4) throw new KernelError(`Malformed machine instruction ${pc}`);
    const op = instruction[0]!;
    const claimed = instruction[1]!;
    const contextId = instruction[2]!;
    const premiseCount = instruction[3]!;
    if (!Number.isSafeInteger(premiseCount) || premiseCount! < 0 || instruction.length < 4 + premiseCount!) {
      throw new KernelError(`Malformed premise list at instruction ${pc}`);
    }
    for (let index = 0; index < premiseCount; index += 1) {
      const premise = instruction[4 + index]!;
      if (!Number.isSafeInteger(premise) || premise < 0 || premise >= pc) {
        throw new KernelError(`Machine instruction ${pc} has a forward or invalid premise`);
      }
    }
    const dataStart = 4 + premiseCount;
    const fixedData = FIXED_DATA_WORDS[op];
    if (fixedData !== undefined && instruction.length !== dataStart + fixedData) {
      throw new KernelError(`Malformed data for machine instruction ${pc}`);
    }
    const context = arena.context(contextId!);
    const claim = arena.formulaId(claimed);
    let derived: number;

    switch (op) {
      case MachineOp.assumption: {
        requireCount(premiseCount, 0, op, pc);
        const formula = arena.formulaId(instruction[dataStart]);
        if (!context.includes(formula)) throw new KernelError(`Inactive machine assumption at instruction ${pc}`);
        derived = formula;
        break;
      }
      case MachineOp.axiom:
      case MachineOp.theorem:
      case MachineOp.definition: {
        requireCount(premiseCount, 0, op, pc);
        const name = arena.symbol(instruction[dataStart]);
        let formula: Formula | undefined;
        if (op === MachineOp.axiom) formula = kernel.axioms.get(name);
        else if (op === MachineOp.theorem) {
          const boundary = boundaryRoots.get(name);
          if (boundary !== undefined) {
            if (boundary >= pc) {
              throw new KernelError(`Machine theorem dependency is not yet proved: ${name}`);
            }
            derived = results[boundary]!;
            break;
          }
          formula = kernel.theorems.get(name);
        }
        else formula = kernel.definitions.get(name)?.properties.get(arena.symbol(instruction[dataStart + 1]));
        if (!formula) throw new KernelError(`Unknown machine dependency ${name}`);
        derived = arena.internFormula(formula);
        break;
      }
      case MachineOp.refl: {
        requireCount(premiseCount, 0, op, pc);
        const term = arena.termId(instruction[dataStart]);
        const conclusion = arena.expectFormula(claim, 1, "reflexivity");
        if (conclusion[1] !== term || conclusion[2] !== term) throw new KernelError(`Bad reflexivity at instruction ${pc}`);
        derived = claim;
        break;
      }
      case MachineOp.compute: {
        requireCount(premiseCount, 0, op, pc);
        const dependencyCount = instruction[dataStart];
        if (!Number.isSafeInteger(dependencyCount) || dependencyCount! < 0 ||
            instruction.length !== dataStart + 1 + dependencyCount!) {
          throw new KernelError(`Malformed computation dependencies at instruction ${pc}`);
        }
        const conclusion = arena.reifyFormula(claim);
        if (conclusion.tag !== "eq") throw new KernelError(`Kernel computation requires an equality at instruction ${pc}`);
        const definitions = instruction.slice(dataStart + 1).map(id => arena.symbol(id));
        kernel.checkComputationalEquality(conclusion.left, conclusion.right, definitions);
        derived = claim;
        break;
      }
      case MachineOp.rationalClassCompute: {
        requireCount(premiseCount, 0, op, pc);
        const conclusion = arena.reifyFormula(claim);
        if (conclusion.tag !== "eq") throw new KernelError(`Rational computation needs equality at ${pc}`);
        kernel.checkRationalClassEquality(conclusion.left, conclusion.right);
        derived = claim;
        break;
      }
      case MachineOp.symm: {
        requireCount(premiseCount, 1, op, pc); requireSameContexts(program, instruction, pc, contextId, premiseCount);
        const equality = arena.expectFormula(results[instruction[4]!]!, 1, "symmetry");
        const conclusion = arena.expectFormula(claim, 1, "symmetry");
        if (conclusion[1] !== equality[2] || conclusion[2] !== equality[1]) throw new KernelError(`Bad symmetry at instruction ${pc}`);
        derived = claim;
        break;
      }
      case MachineOp.trans: {
        requireCount(premiseCount, 2, op, pc); requireSameContexts(program, instruction, pc, contextId, premiseCount);
        const left = arena.expectFormula(results[instruction[4]!]!, 1, "transitivity");
        const right = arena.expectFormula(results[instruction[5]!]!, 1, "transitivity");
        if (left[2] !== right[1]) throw new KernelError(`Transitivity mismatch at instruction ${pc}`);
        const conclusion = arena.expectFormula(claim, 1, "transitivity");
        if (conclusion[1] !== left[1] || conclusion[2] !== right[2]) throw new KernelError(`Bad transitivity conclusion at ${pc}`);
        derived = claim;
        break;
      }
      case MachineOp.congr: {
        requireSameContexts(program, instruction, pc, contextId, premiseCount);
        const fnSymbol = instruction[dataStart]!;
        const fn = arena.symbol(fnSymbol);
        if (kernel.functions.get(fn) !== premiseCount) throw new KernelError(`Bad machine congruence arity for ${fn}`);
        const conclusion = arena.expectFormula(claim, 1, "congruence");
        const equalities = Array.from({ length: premiseCount }, (_, index) =>
          arena.expectFormula(results[instruction[4 + index]!]!, 1, "congruence"));
        const expectedLeft = arena.internApplication(fn, equalities.map(equality => equality[1]!));
        const expectedRight = arena.internApplication(fn, equalities.map(equality => equality[2]!));
        if (conclusion[1] !== expectedLeft || conclusion[2] !== expectedRight) {
          throw new KernelError(`Bad congruence conclusion at instruction ${pc}`);
        }
        derived = claim;
        break;
      }
      case MachineOp.impIntro: {
        requireCount(premiseCount, 1, op, pc);
        const premise = instruction[4]!;
        const assumption = arena.formulaId(instruction[dataStart]);
        arena.requireExtendedContext(context, program.code[premise]![2]!, assumption, pc);
        const conclusion = arena.expectFormula(claim, 3, "implication introduction");
        if (conclusion[1] !== assumption || conclusion[2] !== results[premise]) throw new KernelError(`Bad implication introduction at ${pc}`);
        derived = claim;
        break;
      }
      case MachineOp.impElim: {
        requireCount(premiseCount, 2, op, pc); requireSameContexts(program, instruction, pc, contextId, premiseCount);
        const implication = arena.expectFormula(results[instruction[4]!]!, 3, "implication elimination");
        if (implication[1] !== results[instruction[5]!]) throw new KernelError(`Implication argument mismatch at instruction ${pc}`);
        if (claim !== implication[2]) throw new KernelError(`Bad implication conclusion at instruction ${pc}`);
        derived = claim;
        break;
      }
      case MachineOp.forallIntro: {
        requireCount(premiseCount, 1, op, pc); requireSameContexts(program, instruction, pc, contextId, premiseCount);
        const variable = instruction[dataStart]!;
        if (context.some(formula => arena.hasFreeFormula(formula, variable))) {
          throw new KernelError(`Generalized variable is free in the machine context at ${pc}`);
        }
        const conclusion = arena.expectFormula(claim, 4, "universal introduction");
        if (!arena.matchesAbstraction(conclusion[1]!, results[instruction[4]!]!, variable)) {
          throw new KernelError(`Bad universal introduction at instruction ${pc}`);
        }
        derived = claim;
        break;
      }
      case MachineOp.forallElim: {
        requireCount(premiseCount, 1, op, pc); requireSameContexts(program, instruction, pc, contextId, premiseCount);
        const universal = arena.expectFormula(results[instruction[4]!]!, 4, "universal elimination");
        if (!arena.matchesInstantiation(claim, universal[1]!, arena.termId(instruction[dataStart]))) {
          throw new KernelError(`Bad universal elimination at instruction ${pc}`);
        }
        derived = claim;
        break;
      }
      case MachineOp.eqElim: {
        requireCount(premiseCount, 2, op, pc); requireSameContexts(program, instruction, pc, contextId, premiseCount);
        const equality = arena.expectFormula(results[instruction[4]!]!, 1, "equality elimination");
        const variable = instruction[dataStart]!;
        const motive = arena.formulaId(instruction[dataStart + 1]);
        const reverse = instruction[dataStart + 2] === 1;
        const source = equality[reverse ? 2 : 1]!;
        const target = equality[reverse ? 1 : 2]!;
        if (results[instruction[5]!] !== arena.substituteFreeFormula(motive, variable, source) ||
            claim !== arena.substituteFreeFormula(motive, variable, target)) {
          throw new KernelError(`Bad equality elimination at instruction ${pc}`);
        }
        derived = claim;
        break;
      }
      case MachineOp.andIntro: {
        requireCount(premiseCount, 2, op, pc); requireSameContexts(program, instruction, pc, contextId, premiseCount);
        const conclusion = arena.expectFormula(claim, 5, "conjunction introduction");
        if (conclusion[1] !== results[instruction[4]!] || conclusion[2] !== results[instruction[5]!]) throw new KernelError(`Bad conjunction introduction at ${pc}`);
        derived = claim;
        break;
      }
      case MachineOp.andElimLeft:
      case MachineOp.andElimRight: {
        requireCount(premiseCount, 1, op, pc); requireSameContexts(program, instruction, pc, contextId, premiseCount);
        const conjunction = arena.expectFormula(results[instruction[4]!]!, 5, "conjunction elimination");
        const expected = conjunction[op === MachineOp.andElimLeft ? 1 : 2]!;
        if (claim !== expected) throw new KernelError(`Bad conjunction elimination at ${pc}`);
        derived = claim;
        break;
      }
      case MachineOp.orIntroLeft:
      case MachineOp.orIntroRight: {
        requireCount(premiseCount, 1, op, pc); requireSameContexts(program, instruction, pc, contextId, premiseCount);
        const conclusion = arena.expectFormula(claim, 6, "disjunction introduction");
        const side = arena.formulaId(instruction[dataStart]);
        const expectedLeft = op === MachineOp.orIntroLeft ? results[instruction[4]!]! : side;
        const expectedRight = op === MachineOp.orIntroLeft ? side : results[instruction[4]!]!;
        if (conclusion[1] !== expectedLeft || conclusion[2] !== expectedRight) throw new KernelError(`Bad disjunction introduction at ${pc}`);
        derived = claim;
        break;
      }
      case MachineOp.orElim: {
        requireCount(premiseCount, 3, op, pc);
        const disjunctionPremise = instruction[4]!;
        if (program.code[disjunctionPremise]![2] !== contextId) throw new KernelError(`Context mismatch at instruction ${pc}`);
        const disjunction = arena.expectFormula(results[disjunctionPremise]!, 6, "disjunction elimination");
        arena.requireExtendedContext(context, program.code[instruction[5]!]![2]!, disjunction[1]!, pc);
        arena.requireExtendedContext(context, program.code[instruction[6]!]![2]!, disjunction[2]!, pc);
        if (results[instruction[5]!] !== results[instruction[6]!] || claim !== results[instruction[5]!]) {
          throw new KernelError(`Bad disjunction elimination at ${pc}`);
        }
        derived = claim;
        break;
      }
      case MachineOp.iffIntro: {
        requireCount(premiseCount, 2, op, pc); requireSameContexts(program, instruction, pc, contextId, premiseCount);
        const forward = arena.expectFormula(results[instruction[4]!]!, 3, "equivalence introduction");
        const backward = arena.expectFormula(results[instruction[5]!]!, 3, "equivalence introduction");
        const conclusion = arena.expectFormula(claim, 7, "equivalence introduction");
        if (forward[1] !== backward[2] || forward[2] !== backward[1] || conclusion[1] !== forward[1] || conclusion[2] !== forward[2]) {
          throw new KernelError(`Bad equivalence introduction at ${pc}`);
        }
        derived = claim;
        break;
      }
      case MachineOp.iffElimLeft:
      case MachineOp.iffElimRight: {
        requireCount(premiseCount, 1, op, pc); requireSameContexts(program, instruction, pc, contextId, premiseCount);
        const equivalence = arena.expectFormula(results[instruction[4]!]!, 7, "equivalence elimination");
        const conclusion = arena.expectFormula(claim, 3, "equivalence elimination");
        const reverse = op === MachineOp.iffElimRight;
        if (conclusion[1] !== equivalence[reverse ? 2 : 1] || conclusion[2] !== equivalence[reverse ? 1 : 2]) {
          throw new KernelError(`Bad equivalence elimination at ${pc}`);
        }
        derived = claim;
        break;
      }
      case MachineOp.existsIntro: {
        requireCount(premiseCount, 1, op, pc); requireSameContexts(program, instruction, pc, contextId, premiseCount);
        const variable = instruction[dataStart]!;
        const body = arena.formulaId(instruction[dataStart + 1]);
        const witness = arena.termId(instruction[dataStart + 2]);
        const conclusion = arena.expectFormula(claim, 8, "existential introduction");
        if (!arena.matchesAbstraction(conclusion[1]!, body, variable) ||
            results[instruction[4]!] !== arena.substituteFreeFormula(body, variable, witness)) {
          throw new KernelError(`Bad existential introduction at ${pc}`);
        }
        derived = claim;
        break;
      }
      case MachineOp.existsElim: {
        requireCount(premiseCount, 2, op, pc);
        const existentialPremise = instruction[4]!;
        if (program.code[existentialPremise]![2] !== contextId) throw new KernelError(`Context mismatch at instruction ${pc}`);
        const existential = arena.expectFormula(results[existentialPremise]!, 8, "existential elimination");
        const witness = instruction[dataStart]!;
        if (context.some(formula => arena.hasFreeFormula(formula, witness)) || arena.hasFreeFormula(results[existentialPremise]!, witness)) {
          throw new KernelError(`Existential witness is not fresh at ${pc}`);
        }
        const witnessTerm = arena.internTermNode([0, witness]);
        const instance = arena.instantiateFormula(existential[1]!, witnessTerm);
        const bodyPremise = instruction[5]!;
        arena.requireExtendedContext(context, program.code[bodyPremise]![2]!, instance, pc);
        if (arena.hasFreeFormula(results[bodyPremise]!, witness) || claim !== results[bodyPremise]) {
          throw new KernelError(`Existential witness escapes at ${pc}`);
        }
        derived = claim;
        break;
      }
      case MachineOp.falseElim: {
        requireCount(premiseCount, 1, op, pc); requireSameContexts(program, instruction, pc, contextId, premiseCount);
        arena.expectFormula(results[instruction[4]!]!, 0, "false elimination");
        if (claim !== arena.formulaId(instruction[dataStart])) throw new KernelError(`Bad false elimination at ${pc}`);
        derived = claim;
        break;
      }
      case MachineOp.dne: {
        requireCount(premiseCount, 1, op, pc); requireSameContexts(program, instruction, pc, contextId, premiseCount);
        const proposition = arena.formulaId(instruction[dataStart]);
        const bottom = arena.internFormulaNode([0]);
        const negated = arena.internFormulaNode([3, proposition, bottom]);
        const doubleNegated = arena.internFormulaNode([3, negated, bottom]);
        if (results[instruction[4]!] !== doubleNegated || claim !== proposition) throw new KernelError(`Bad double-negation elimination at ${pc}`);
        derived = claim;
        break;
      }
      case MachineOp.induction: {
        const datatype = kernel.datatypes.get(arena.symbol(instruction[dataStart]));
        const variable = instruction[dataStart + 1]!;
        const motive = arena.formulaId(instruction[dataStart + 2]);
        const parameterCount = instruction[dataStart + 3]!;
        const parameters = instruction.slice(dataStart + 4, dataStart + 4 + parameterCount).map(id => arena.termId(id));
        const caseCount = instruction[dataStart + 4 + parameterCount]!;
        if (!datatype || parameterCount !== (datatype.parameters?.length ?? 0) ||
            caseCount !== datatype.constructors.length || premiseCount !== caseCount) {
          throw new KernelError(`Malformed machine induction at instruction ${pc}`);
        }
        if (parameters.some(parameter => arena.hasFreeTerm(parameter, variable))) {
          throw new KernelError(`Induction variable occurs in a datatype parameter at ${pc}`);
        }
        if (context.some(formula => arena.hasFreeFormula(formula, variable))) {
          throw new KernelError(`Induction variable is free in the machine context at ${pc}`);
        }
        let cursor = dataStart + 5 + parameterCount;
        const seen = new Set<string>();
        for (let index = 0; index < caseCount; index += 1) {
          const constructorName = arena.symbol(instruction[cursor++]!);
          const fieldCount = instruction[cursor++]!;
          const fields = instruction.slice(cursor, cursor + fieldCount);
          cursor += fieldCount;
          const constructor = datatype.constructors.find(item => item.name === constructorName);
          if (!constructor || constructor.arity !== fieldCount || seen.has(constructorName) || new Set(fields).size !== fields.length) {
            throw new KernelError(`Malformed machine induction case ${constructorName}`);
          }
          seen.add(constructorName);
          if (fields.some(field => field === variable || arena.hasFreeFormula(motive, field) ||
              parameters.some(parameter => arena.hasFreeTerm(parameter, field)) ||
              context.some(formula => arena.hasFreeFormula(formula, field)))) {
            throw new KernelError(`Machine induction field is not fresh at instruction ${pc}`);
          }
          const fieldTerms = fields.map(field => arena.internTermNode([0, field]));
          const expectedContext = [...context];
          for (let fieldIndex = 0; fieldIndex < constructor.arity; fieldIndex += 1) {
            if (constructor.recursiveFields.includes(fieldIndex)) {
              expectedContext.push(arena.internPredicate(datatype.predicate, [...parameters, fieldTerms[fieldIndex]!]));
              expectedContext.push(arena.substituteFreeFormula(motive, variable, fieldTerms[fieldIndex]!));
            } else {
              const parameterField = constructor.parameterFields?.find(item => item.field === fieldIndex);
              if (parameterField) expectedContext.push(arena.internPredicate("in", [fieldTerms[fieldIndex]!, parameters[parameterField.parameter]!]));
            }
          }
          const premise = instruction[4 + index]!;
          arena.requireContext(expectedContext, program.code[premise]![2]!, pc);
          const constructorTerm = arena.internApplication(constructorName, fieldTerms);
          const expected = arena.substituteFreeFormula(motive, variable, constructorTerm);
          if (results[premise] !== expected) throw new KernelError(`Wrong machine induction case ${constructorName}`);
        }
        if (cursor !== instruction.length) throw new KernelError(`Malformed machine induction data at instruction ${pc}`);
        const variableTerm = arena.internTermNode([0, variable]);
        const membership = arena.internPredicate(datatype.predicate, [...parameters, variableTerm]);
        const body = arena.internFormulaNode([3, membership, motive]);
        derived = arena.internFormulaNode([4, arena.abstractFormula(body, variable)]);
        break;
      }
      case MachineOp.wellFoundedInduction: {
        requireCount(premiseCount, 2, op, pc); requireSameContexts(program, instruction, pc, contextId, premiseCount);
        const relation = arena.termId(instruction[dataStart]);
        const domain = arena.termId(instruction[dataStart + 1]);
        const variable = instruction[dataStart + 2]!;
        const predecessor = instruction[dataStart + 3]!;
        const motive = arena.formulaId(instruction[dataStart + 4]);
        if (variable === predecessor || arena.hasFreeTerm(relation, variable) || arena.hasFreeTerm(relation, predecessor) ||
            arena.hasFreeTerm(domain, variable) || arena.hasFreeTerm(domain, predecessor) ||
            arena.hasFreeFormula(motive, predecessor) ||
            context.some(formula => arena.hasFreeFormula(formula, variable) || arena.hasFreeFormula(formula, predecessor))) {
          throw new KernelError(`Malformed well-founded induction variables at ${pc}`);
        }
        const expectedWellFounded = arena.internPredicate("wellFoundedOn", [relation, domain]);
        if (results[instruction[4]!] !== expectedWellFounded) throw new KernelError(`Wrong well-foundedness certificate at ${pc}`);
        const x = arena.internTermNode([0, variable]);
        const y = arena.internTermNode([0, predecessor]);
        const predecessorMotive = arena.substituteFreeFormula(motive, variable, y);
        const inDomainY = arena.internPredicate("in", [y, domain]);
        const relates = arena.internPredicate("relates", [relation, y, x]);
        const conjunction = arena.internFormulaNode([5, inDomainY, relates]);
        const ihBody = arena.internFormulaNode([3, conjunction, predecessorMotive]);
        const ih = arena.internFormulaNode([4, arena.abstractFormula(ihBody, predecessor)]);
        const inDomainX = arena.internPredicate("in", [x, domain]);
        const stepBody = arena.internFormulaNode([3, inDomainX, arena.internFormulaNode([3, ih, motive])]);
        const expectedStep = arena.internFormulaNode([4, arena.abstractFormula(stepBody, variable)]);
        if (results[instruction[5]!] !== expectedStep) throw new KernelError(`Wrong well-founded induction step at ${pc}`);
        const resultBody = arena.internFormulaNode([3, inDomainX, motive]);
        derived = arena.internFormulaNode([4, arena.abstractFormula(resultBody, variable)]);
        break;
      }
      default: throw new KernelError(`Unsupported proof-machine opcode ${op} at instruction ${pc}`);
    }
    if (derived !== claimed) throw new KernelError(`Machine instruction ${pc} derives the wrong formula`);
    results[pc] = derived;
  }
  const formulaId = results[program.root]!;
  const cacheable = immutablePrograms.has(program);
  let formula = cacheable ? reifiedResults.get(program) : undefined;
  if (!formula) {
    formula = arena.reifyFormula(formulaId);
    deepFreeze(formula);
    if (cacheable) reifiedResults.set(program, formula);
  }
  return {
    formula, formulaId, arena,
    stats: { instructions: program.code.length, formulaNodes: arena.formulas.length, termNodes: arena.terms.length },
  };
}

/** Exact number of rule-specific words after the premise ids; -dynamic rules are omitted. */
const FIXED_DATA_WORDS: Readonly<Record<number, number>> = Object.freeze({
  [MachineOp.assumption]: 1, [MachineOp.axiom]: 1, [MachineOp.theorem]: 1,
  [MachineOp.definition]: 2, [MachineOp.refl]: 1,
  [MachineOp.symm]: 0, [MachineOp.trans]: 0, [MachineOp.congr]: 1,
  [MachineOp.impIntro]: 1, [MachineOp.impElim]: 0,
  [MachineOp.forallIntro]: 1, [MachineOp.forallElim]: 1,
  [MachineOp.eqElim]: 3, [MachineOp.andIntro]: 0,
  [MachineOp.andElimLeft]: 0, [MachineOp.andElimRight]: 0,
  [MachineOp.orIntroLeft]: 1, [MachineOp.orIntroRight]: 1,
  [MachineOp.orElim]: 0, [MachineOp.iffIntro]: 0,
  [MachineOp.iffElimLeft]: 0, [MachineOp.iffElimRight]: 0,
  [MachineOp.existsIntro]: 3, [MachineOp.existsElim]: 1,
  [MachineOp.falseElim]: 1, [MachineOp.dne]: 1,
  [MachineOp.wellFoundedInduction]: 5,
  [MachineOp.rationalClassCompute]: 0,
});

/** Check a linked module in one pass and validate every named theorem boundary. */
export function verifyProofModule(kernel: Kernel, program: ProofMachineModuleProgram): {
  readonly theorems: number;
  readonly instructions: number;
} {
  verifyProofMachine(kernel, program);
  const arena = runtimeFor(program);
  const seen = new Set<string>();
  for (const entry of program.theorems) {
    if (!Array.isArray(entry) || entry.length !== 2) throw new KernelError("Malformed theorem boundary");
    const name = arena.symbol(entry[0]);
    if (seen.has(name)) throw new KernelError(`Duplicate machine theorem boundary: ${name}`);
    seen.add(name);
    const statement = kernel.theorems.get(name);
    const instruction = program.code[entry[1]];
    if (!statement || !instruction || arena.results[entry[1]] !== arena.internFormula(statement)) {
      throw new KernelError(`Machine theorem boundary mismatch: ${name}`);
    }
  }
  return { theorems: program.theorems.length, instructions: program.code.length };
}

/** Check a theorem batch before its statements have been installed. */
export function verifyProofModuleStatements(
  kernel: Kernel,
  program: ProofMachineModuleProgram,
  statements: readonly { readonly name: string; readonly statement: Formula }[],
): { readonly theorems: number; readonly instructions: number } {
  const { arena } = verifyProofMachineWithArena(kernel, program);
  if (statements.length !== program.theorems.length) throw new KernelError("Machine theorem statement count mismatch");
  const seen = new Set<string>();
  statements.forEach((entry, index) => {
    const boundary = program.theorems[index];
    if (!boundary || arena.symbol(boundary[0]) !== entry.name || seen.has(entry.name) ||
        arena.results[boundary[1]] !== arena.internFormula(entry.statement)) {
      throw new KernelError(`Machine theorem boundary mismatch: ${entry.name}`);
    }
    seen.add(entry.name);
  });
  return { theorems: statements.length, instructions: program.code.length };
}

function opcode(rule: Proof["rule"]): number {
  const value = (MachineOp as Record<string, number>)[rule];
  if (value === undefined) throw new KernelError(`Proof machine does not yet support ${rule}`);
  return value;
}

function instructionData(arena: Arena, proof: Proof): number[] {
  switch (proof.rule) {
    case "assumption": return [arena.internFormula(proof.formula)];
    case "axiom": case "theorem": return [arena.symbolId(proof.name)];
    case "definition": return [arena.symbolId(proof.name), arena.symbolId(proof.property ?? "equation")];
    case "refl": return [arena.internTerm(proof.term)];
    case "compute": return [proof.definitions.length, ...proof.definitions.map(name => arena.symbolId(name))];
    case "rationalClassCompute": return [];
    case "symm": case "trans": case "impElim": case "andIntro": case "andElimLeft": case "andElimRight":
    case "orElim": case "iffIntro": case "iffElimLeft": case "iffElimRight": return [];
    case "congr": return [arena.symbolId(proof.fn)];
    case "eqElim": return [arena.symbolId(proof.variable), arena.internFormula(proof.motive), proof.reverse ? 1 : 0];
    case "impIntro": return [arena.internFormula(proof.assumption)];
    case "forallIntro": return [arena.symbolId(proof.variable)];
    case "forallElim": return [arena.internTerm(proof.term)];
    case "orIntroLeft": return [arena.internFormula(proof.right)];
    case "orIntroRight": return [arena.internFormula(proof.left)];
    case "existsIntro": return [arena.symbolId(proof.variable), arena.internFormula(proof.body), arena.internTerm(proof.witness)];
    case "existsElim": return [arena.symbolId(proof.witness)];
    case "falseElim": return [arena.internFormula(proof.conclusion)];
    case "dne": return [arena.internFormula(proof.proposition)];
    case "induction": return [
      arena.symbolId(proof.datatype), arena.symbolId(proof.variable), arena.internFormula(proof.motive),
      proof.parameters.length, ...proof.parameters.map(parameter => arena.internTerm(parameter)), proof.cases.length,
      ...proof.cases.flatMap(branch => [
        arena.symbolId(branch.constructor), branch.fields.length, ...branch.fields.map(field => arena.symbolId(field)),
      ]),
    ];
    case "wellFoundedInduction": return [
      arena.internTerm(proof.relation), arena.internTerm(proof.domain), arena.symbolId(proof.variable),
      arena.symbolId(proof.predecessor), arena.internFormula(proof.motive),
    ];
  }
}

function requireCount(actual: number, expected: number, op: number, pc: number): void {
  if (actual !== expected) throw new KernelError(`Opcode ${op} at ${pc} expects ${expected} premises`);
}

function requireSameContexts(
  program: ProofMachineProgram,
  instruction: readonly number[],
  pc: number,
  contextId: number,
  premiseCount: number,
): void {
  for (let index = 0; index < premiseCount; index += 1) {
    if (program.code[instruction[4 + index]!]![2] !== contextId) {
      throw new KernelError(`Context mismatch at instruction ${pc}`);
    }
  }
}

/**
 * Open-addressing table from a node's numbers to its id, so interning a
 * program's nodes hashes integers rather than building a string per node.
 */
class NodeTable {
  private slots = new Int32Array(1024).fill(-1);
  private count = 0;
  private readonly nodes: readonly (readonly number[])[];
  constructor(nodes: readonly (readonly number[])[]) { this.nodes = nodes; }
  private static hash(node: readonly number[]): number {
    let hash = 2166136261;
    for (let index = 0; index < node.length; index += 1) hash = Math.imul(hash ^ node[index]!, 16777619);
    return hash >>> 0;
  }
  private static same(left: readonly number[], right: readonly number[]): boolean {
    if (left.length !== right.length) return false;
    for (let index = 0; index < left.length; index += 1) if (left[index] !== right[index]) return false;
    return true;
  }
  find(node: readonly number[]): number | undefined {
    const mask = this.slots.length - 1;
    for (let slot = NodeTable.hash(node) & mask; ; slot = (slot + 1) & mask) {
      const id = this.slots[slot]!;
      if (id === -1) return undefined;
      if (NodeTable.same(this.nodes[id]!, node)) return id;
    }
  }
  /** Record `id` for a node known to be absent. */
  insert(node: readonly number[], id: number): void {
    if ((this.count + 1) * 2 > this.slots.length) {
      const previous = this.slots;
      this.slots = new Int32Array(previous.length * 2).fill(-1);
      for (const existing of previous) if (existing !== -1) this.place(this.nodes[existing]!, existing);
    }
    this.place(node, id);
    this.count += 1;
  }
  private place(node: readonly number[], id: number): void {
    const mask = this.slots.length - 1;
    let slot = NodeTable.hash(node) & mask;
    while (this.slots[slot] !== -1) slot = (slot + 1) & mask;
    this.slots[slot] = id;
  }
}

/** A cache key from three small non-negative integers, falling back to text when they are not small. */
function tripleKey(first: number, second: number, third: number): number | string {
  return first < 2_097_152 && second < 1_048_576 && third < 4_096
    ? (first * 1_048_576 + second) * 4_096 + third
    : `${first}/${second}/${third}`;
}

class Arena {
  readonly symbols: string[] = [];
  readonly terms: number[][] = [];
  readonly formulas: number[][] = [];
  readonly contexts: number[][] = [];
  readonly results: Int32Array;
  private readonly symbolMap = new Map<string, number>();
  private readonly termMap = new NodeTable(this.terms);
  private readonly formulaMap = new NodeTable(this.formulas);
  private readonly contextMap = new NodeTable(this.contexts);
  private readonly abstractCache = new Map<number | string, number>();
  private readonly substitutionCache = new Map<number | string, number>();
  private readonly instantiateCache = new Map<number | string, number>();
  private readonly formulaObjects = new WeakMap<object, number>();
  private readonly termObjects = new WeakMap<object, number>();

  constructor(program?: ProofMachineProgram) {
    this.results = new Int32Array(program?.code.length ?? 0);
    if (!program) return;
    program.symbols.forEach(value => { this.symbolMap.set(value, this.symbols.length); this.symbols.push(value); });
    program.terms.forEach(node => this.internTermNode([...node]));
    program.formulas.forEach(node => this.internFormulaNode([...node]));
    program.contexts.forEach(node => this.internContextIds([...node]));
  }
  validateSignature(kernel: Kernel, termCount: number, formulaCount: number): void {
    for (let index = 0; index < termCount; index += 1) {
      const node = this.terms[index]!;
      if (node[0] === 2) {
        const name = this.symbol(node[1]);
        if (kernel.functions.get(name) !== node.length - 2) throw new KernelError(`Unknown or malformed machine function ${name}`);
      }
    }
    for (let index = 0; index < formulaCount; index += 1) {
      const node = this.formulas[index]!;
      if (node[0] === 2) {
        const name = this.symbol(node[1]);
        if (kernel.predicates.get(name) !== node.length - 2) throw new KernelError(`Unknown or malformed machine predicate ${name}`);
      }
    }
  }

  symbolId(value: string): number {
    const previous = this.symbolMap.get(value);
    if (previous !== undefined) return previous;
    const id = this.symbols.length;
    this.symbols.push(value); this.symbolMap.set(value, id); return id;
  }
  symbol(id: number | undefined): string {
    const value = id === undefined ? undefined : this.symbols[id];
    if (value === undefined) throw new KernelError(`Invalid machine symbol ${id}`);
    return value;
  }
  termId(id: number | undefined): number {
    if (id === undefined || !this.terms[id]) throw new KernelError(`Invalid machine term ${id}`);
    return id;
  }
  formulaId(id: number | undefined): number {
    if (id === undefined || !this.formulas[id]) throw new KernelError(`Invalid machine formula ${id}`);
    return id;
  }
  context(id: number | undefined): readonly number[] {
    const value = id === undefined ? undefined : this.contexts[id];
    if (!value) throw new KernelError(`Invalid machine context ${id}`);
    return value;
  }
  internTerm(term: Term, binders: readonly string[] = []): number {
    if (binders.length === 0) {
      const previous = this.termObjects.get(term);
      if (previous !== undefined) return previous;
    }
    let result: number;
    const numeral = naturalValue(term);
    if (numeral !== undefined) {
      result = this.internTermNode([3, this.symbolId(numeral.toString())]);
    } else if (term.tag === "var") {
      for (let index = binders.length - 1; index >= 0; index -= 1) {
        if (binders[index] === term.name) return this.internTermNode([1, binders.length - index - 1]);
      }
      result = this.internTermNode([0, this.symbolId(term.name)]);
    } else if (term.tag === "nat") {
      throw new KernelError(`Malformed natural literal ${term.value}`);
    } else {
      result = this.internTermNode([2, this.symbolId(term.fn), ...term.args.map(arg => this.internTerm(arg, binders))]);
    }
    if (binders.length === 0) this.termObjects.set(term, result);
    return result;
  }
  internFormula(formula: Formula, binders: readonly string[] = []): number {
    if (binders.length === 0) {
      const previous = this.formulaObjects.get(formula);
      if (previous !== undefined) return previous;
    }
    let result: number;
    switch (formula.tag) {
      case "bottom": result = this.internFormulaNode([0]); break;
      case "eq": result = this.internFormulaNode([1, this.internTerm(formula.left, binders), this.internTerm(formula.right, binders)]); break;
      case "pred": result = this.internFormulaNode([2, this.symbolId(formula.pred), ...formula.args.map(arg => this.internTerm(arg, binders))]); break;
      case "imp": result = this.internFormulaNode([3, this.internFormula(formula.left, binders), this.internFormula(formula.right, binders)]); break;
      case "forall": result = this.internFormulaNode([4, this.internFormula(formula.body, [...binders, formula.variable])]); break;
      case "and": result = this.internFormulaNode([5, this.internFormula(formula.left, binders), this.internFormula(formula.right, binders)]); break;
      case "or": result = this.internFormulaNode([6, this.internFormula(formula.left, binders), this.internFormula(formula.right, binders)]); break;
      case "iff": result = this.internFormulaNode([7, this.internFormula(formula.left, binders), this.internFormula(formula.right, binders)]); break;
      case "exists": result = this.internFormulaNode([8, this.internFormula(formula.body, [...binders, formula.variable])]); break;
    }
    if (binders.length === 0) this.formulaObjects.set(formula, result);
    return result;
  }
  internTermNode(node: number[]): number { return this.internNode(node, this.terms, this.termMap); }
  internFormulaNode(node: number[]): number { return this.internNode(node, this.formulas, this.formulaMap); }
  private internNode(node: number[], nodes: number[][], map: NodeTable): number {
    const previous = map.find(node); if (previous !== undefined) return previous;
    const id = nodes.length; nodes.push(node); map.insert(node, id); return id;
  }
  internContext(formulas: readonly Formula[]): number { return this.internContextIds(formulas.map(item => this.internFormula(item))); }
  private internContextIds(ids: number[]): number {
    const previous = this.contextMap.find(ids); if (previous !== undefined) return previous;
    const id = this.contexts.length; this.contexts.push(ids); this.contextMap.insert(ids, id); return id;
  }
  expectFormula(id: number, tag: number, operation: string): readonly number[] {
    const node = this.formulas[id]; if (!node || node[0] !== tag) throw new KernelError(`Machine ${operation} received the wrong formula`); return node;
  }
  expectApplication(id: number, fn: number, operation: string): readonly number[] {
    const node = this.terms[id];
    if (!node || node[0] !== 2 || node[1] !== fn) throw new KernelError(`Machine ${operation} received the wrong term`);
    return node;
  }
  matchesAbstraction(target: number, source: number, symbol: number, depth = 0): boolean {
    const left = this.formulas[target]; const right = this.formulas[source];
    if (!left || !right || left[0] !== right[0] || left.length !== right.length) return false;
    if (left[0] === 0) return true;
    if (left[0] === 1) return this.termMatchesAbstraction(left[1]!, right[1]!, symbol, depth) && this.termMatchesAbstraction(left[2]!, right[2]!, symbol, depth);
    if (left[0] === 2) return left[1] === right[1] && left.slice(2).every((term, index) => this.termMatchesAbstraction(term, right[index + 2]!, symbol, depth));
    if (left[0] === 3 || (left[0]! >= 5 && left[0]! <= 7)) return this.matchesAbstraction(left[1]!, right[1]!, symbol, depth) && this.matchesAbstraction(left[2]!, right[2]!, symbol, depth);
    return this.matchesAbstraction(left[1]!, right[1]!, symbol, depth + 1);
  }
  private termMatchesAbstraction(target: number, source: number, symbol: number, depth: number): boolean {
    const left = this.terms[target]; const right = this.terms[source];
    if (!left || !right) return false;
    if (right[0] === 0 && right[1] === symbol) return left[0] === 1 && left[1] === depth;
    if (left[0] !== right[0] || left.length !== right.length) return false;
    if (left[0] !== 2) return left[1] === right[1];
    return left[1] === right[1] && left.slice(2).every((term, index) => this.termMatchesAbstraction(term, right[index + 2]!, symbol, depth));
  }
  matchesInstantiation(target: number, source: number, replacement: number, depth = 0): boolean {
    // Constructing the instantiated arena node also performs canonical
    // zero/succ -> compact-natural folding. A structural zipper would reject
    // the definitionally identical `succ(2)` and `3` representations.
    return target === this.instantiateFormula(source, replacement, depth);
  }
  internApplication(fn: string, args: readonly number[]): number {
    return this.internApplicationSymbol(this.symbolId(fn), args);
  }
  private internApplicationSymbol(fn: number, args: readonly number[]): number {
    const name = this.symbol(fn);
    if (name === "zero" && args.length === 0) return this.internTermNode([3, this.symbolId("0")]);
    if (name === "succ" && args.length === 1) {
      const argument = this.terms[args[0]!]!;
      if (argument?.[0] === 3) return this.internTermNode([3, this.symbolId((BigInt(this.symbol(argument[1])) + 1n).toString())]);
    }
    return this.internTermNode([2, fn, ...args]);
  }
  internPredicate(pred: string, args: readonly number[]): number { return this.internFormulaNode([2, this.symbolId(pred), ...args]); }
  requireContext(expected: readonly number[], actualId: number, pc: number): void {
    const actual = this.context(actualId);
    if (actual.length !== expected.length || actual.some((item, index) => item !== expected[index])) {
      throw new KernelError(`Branch context mismatch at instruction ${pc}`);
    }
  }
  requireExtendedContext(parent: readonly number[], actualId: number, extra: number, pc: number): void {
    this.requireContext([...parent, extra], actualId, pc);
  }
  hasFreeFormula(formula: number, symbol: number): boolean {
    const node = this.formulas[formula]!;
    if (node[0] === 1) return this.hasFreeTerm(node[1]!, symbol) || this.hasFreeTerm(node[2]!, symbol);
    if (node[0] === 2) return node.slice(2).some(term => this.hasFreeTerm(term, symbol));
    if (node[0] === 3 || (node[0]! >= 5 && node[0]! <= 7)) return this.hasFreeFormula(node[1]!, symbol) || this.hasFreeFormula(node[2]!, symbol);
    if (node[0] === 4 || node[0] === 8) return this.hasFreeFormula(node[1]!, symbol);
    return false;
  }
  hasFreeTerm(term: number, symbol: number): boolean {
    const node = this.terms[term]!;
    return node[0] === 0 ? node[1] === symbol : node[0] === 2 && node.slice(2).some(child => this.hasFreeTerm(child, symbol));
  }
  abstractFormula(formula: number, symbol: number, depth = 0): number {
    const key = tripleKey(formula, symbol, depth); const hit = this.abstractCache.get(key); if (hit !== undefined) return hit;
    const node = this.formulas[formula]!;
    let result: number;
    if (node[0] === 0) result = formula;
    else if (node[0] === 1) result = this.internFormulaNode([1, this.abstractTerm(node[1]!, symbol, depth), this.abstractTerm(node[2]!, symbol, depth)]);
    else if (node[0] === 2) result = this.internFormulaNode([2, node[1]!, ...node.slice(2).map(term => this.abstractTerm(term, symbol, depth))]);
    else if (node[0] === 3 || (node[0]! >= 5 && node[0]! <= 7)) result = this.internFormulaNode([node[0]!, this.abstractFormula(node[1]!, symbol, depth), this.abstractFormula(node[2]!, symbol, depth)]);
    else result = this.internFormulaNode([node[0]!, this.abstractFormula(node[1]!, symbol, depth + 1)]);
    this.abstractCache.set(key, result); return result;
  }
  private abstractTerm(term: number, symbol: number, depth: number): number {
    const node = this.terms[term]!;
    if (node[0] === 0 && node[1] === symbol) return this.internTermNode([1, depth]);
    if (node[0] !== 2) return term;
    return this.internApplicationSymbol(node[1]!, node.slice(2).map(child => this.abstractTerm(child, symbol, depth)));
  }
  substituteFreeFormula(formula: number, symbol: number, replacement: number): number {
    const key = tripleKey(formula, symbol, replacement); const hit = this.substitutionCache.get(key); if (hit !== undefined) return hit;
    const node = this.formulas[formula]!;
    let result: number;
    if (node[0] === 0) result = formula;
    else if (node[0] === 1) result = this.internFormulaNode([1, this.substituteFreeTerm(node[1]!, symbol, replacement), this.substituteFreeTerm(node[2]!, symbol, replacement)]);
    else if (node[0] === 2) result = this.internFormulaNode([2, node[1]!, ...node.slice(2).map(term => this.substituteFreeTerm(term, symbol, replacement))]);
    else if (node[0] === 3 || (node[0]! >= 5 && node[0]! <= 7)) result = this.internFormulaNode([node[0]!, this.substituteFreeFormula(node[1]!, symbol, replacement), this.substituteFreeFormula(node[2]!, symbol, replacement)]);
    else result = this.internFormulaNode([node[0]!, this.substituteFreeFormula(node[1]!, symbol, replacement)]);
    this.substitutionCache.set(key, result); return result;
  }
  private substituteFreeTerm(term: number, symbol: number, replacement: number): number {
    const node = this.terms[term]!;
    if (node[0] === 0 && node[1] === symbol) return replacement;
    if (node[0] !== 2) return term;
    return this.internApplicationSymbol(node[1]!, node.slice(2).map(child => this.substituteFreeTerm(child, symbol, replacement)));
  }
  instantiateFormula(formula: number, replacement: number, depth = 0): number {
    const key = tripleKey(formula, replacement, depth); const hit = this.instantiateCache.get(key); if (hit !== undefined) return hit;
    const node = this.formulas[formula]!;
    let result: number;
    if (node[0] === 0) result = formula;
    else if (node[0] === 1) result = this.internFormulaNode([1, this.instantiateTerm(node[1]!, replacement, depth), this.instantiateTerm(node[2]!, replacement, depth)]);
    else if (node[0] === 2) result = this.internFormulaNode([2, node[1]!, ...node.slice(2).map(term => this.instantiateTerm(term, replacement, depth))]);
    else if (node[0] === 3 || (node[0]! >= 5 && node[0]! <= 7)) result = this.internFormulaNode([node[0]!, this.instantiateFormula(node[1]!, replacement, depth), this.instantiateFormula(node[2]!, replacement, depth)]);
    else result = this.internFormulaNode([node[0]!, this.instantiateFormula(node[1]!, replacement, depth + 1)]);
    this.instantiateCache.set(key, result); return result;
  }
  private instantiateTerm(term: number, replacement: number, depth: number): number {
    const node = this.terms[term]!;
    if (node[0] === 1) {
      if (node[1] === depth) return this.shiftTerm(replacement, depth);
      return node[1]! > depth ? this.internTermNode([1, node[1]! - 1]) : term;
    }
    if (node[0] !== 2) return term;
    return this.internApplicationSymbol(node[1]!, node.slice(2).map(child => this.instantiateTerm(child, replacement, depth)));
  }
  private shiftTerm(term: number, amount: number): number {
    if (amount === 0) return term;
    const node = this.terms[term]!;
    if (node[0] === 1) return this.internTermNode([1, node[1]! + amount]);
    if (node[0] !== 2) return term;
    return this.internApplicationSymbol(node[1]!, node.slice(2).map(child => this.shiftTerm(child, amount)));
  }
  reifyFormula(id: number, binders: readonly string[] = []): Formula {
    const node = this.formulas[id]!;
    const term = (termId: number): Term => {
      const item = this.terms[termId]!;
      if (item[0] === 0) return { tag: "var", name: this.symbol(item[1]) };
      if (item[0] === 1) return { tag: "var", name: binders[binders.length - item[1]! - 1] ?? `#${item[1]}` };
      if (item[0] === 3) return { tag: "nat", value: this.symbol(item[1]) };
      return { tag: "app", fn: this.symbol(item[1]), args: item.slice(2).map(term) };
    };
    switch (node[0]) {
      case 0: return { tag: "bottom" };
      case 1: return { tag: "eq", left: term(node[1]!), right: term(node[2]!) };
      case 2: return { tag: "pred", pred: this.symbol(node[1]), args: node.slice(2).map(term) };
      case 3: return { tag: "imp", left: this.reifyFormula(node[1]!, binders), right: this.reifyFormula(node[2]!, binders) };
      case 4: { const name = `x${binders.length}`; return { tag: "forall", variable: name, body: this.reifyFormula(node[1]!, [...binders, name]) }; }
      case 5: return { tag: "and", left: this.reifyFormula(node[1]!, binders), right: this.reifyFormula(node[2]!, binders) };
      case 6: return { tag: "or", left: this.reifyFormula(node[1]!, binders), right: this.reifyFormula(node[2]!, binders) };
      case 7: return { tag: "iff", left: this.reifyFormula(node[1]!, binders), right: this.reifyFormula(node[2]!, binders) };
      case 8: { const name = `x${binders.length}`; return { tag: "exists", variable: name, body: this.reifyFormula(node[1]!, [...binders, name]) }; }
      default: throw new KernelError(`Invalid machine formula opcode ${node[0]}`);
    }
  }
}

const immutablePrograms = new WeakSet<object>();
const runtimes = new WeakMap<object, Arena>();
const reifiedResults = new WeakMap<object, Formula>();
function runtimeFor(program: ProofMachineProgram): Arena {
  if (Object.isFrozen(program)) {
    // A shallow freeze is not evidence that nested arenas are immutable.
    if (!immutablePrograms.has(program)) { deepFreeze(program); immutablePrograms.add(program); }
    const previous = runtimes.get(program); if (previous) return previous;
    const arena = new Arena(program); runtimes.set(program, arena); return arena;
  }
  return new Arena(program);
}

function deepFreeze(value: unknown): void {
  freezeCertificate(value);
}
