// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { sha256Hex } from "./hash.ts";
import {
  and, canonical, formulaEquals, formulaCanonical, pred, substituteFormula, v, type Formula,
} from "./ast.ts";
import { checkProofDag, decodeProofDag, encodeProofDagWithIndex, type ProofDag } from "./dag.ts";
import { KernelError, type Kernel } from "./kernel.ts";
import type { Proof } from "./proof.ts";
import type { TacticTrace } from "./tactic-trace.ts";

export interface ProofDependencies {
  readonly axioms: readonly string[];
  readonly theorems: readonly string[];
  readonly definitions: readonly string[];
}

export interface ExportedProof {
  readonly format: "grace17.proof";
  readonly version: 4;
  readonly theorem: string;
  readonly environment: string;
  readonly statement: Formula;
  readonly dependencies: ProofDependencies;
  readonly proof: ProofDag;
  readonly trace: ProofTrace;
  readonly tactics?: TacticTrace;
  readonly digest: string;
}

/** Minimal checked certificate input used by the dense G17M compiler. */
export interface MachineProofExport {
  readonly theorem: string;
  readonly environment: string;
  readonly proof: ProofDag;
  readonly trace: ProofTrace;
}

/** A context-sensitive kernel judgment: assumptions ⊢ conclusion. */
export interface ProofTraceNode {
  readonly proofNode: number;
  readonly assumptions: readonly Formula[];
  readonly conclusion: Formula;
  readonly children: readonly number[];
}

export interface ProofTrace {
  readonly root: number;
  readonly nodes: readonly ProofTraceNode[];
}

export function exportTheorem(kernel: Kernel, name: string): ExportedProof {
  const statement = kernel.theorems.get(name);
  const proof = kernel.theoremProofs.get(name);
  if (!statement || !proof) throw new KernelError(`Theorem has no retained proof: ${name}`);
  const encoded = encodeProofDagWithIndex(proof);
  const tactics = kernel.theoremTacticTraces.get(name);
  const body = {
    format: "grace17.proof" as const,
    version: 4 as const,
    theorem: name,
    environment: kernel.digest(),
    statement,
    dependencies: proofDependencies(kernel, proof, name),
    proof: encoded.dag,
    trace: buildProofTrace(kernel, proof, encoded.nodeIds),
    ...(tactics ? { tactics } : {}),
  };
  return Object.freeze({ ...body, digest: digestExport(body) });
}

/**
 * Build only the authenticated proof DAG and contextual judgments needed by
 * G17M. Human-facing dependency, tactic, and presentation digests
 * stay in `exportTheorem`; compiling a library must not construct them hundreds
 * of times.
 */
export function exportTheoremForMachine(kernel: Kernel, name: string): MachineProofExport {
  const proof = kernel.theoremProofs.get(name);
  if (!kernel.theorems.has(name) || !proof) throw new KernelError(`Theorem has no retained proof: ${name}`);
  const encoded = encodeProofDagWithIndex(proof);
  return Object.freeze({
    theorem: name,
    environment: kernel.digest(),
    proof: encoded.dag,
    trace: buildProofTrace(kernel, proof, encoded.nodeIds),
  });
}

/** Compile-time certificate input for a theorem not yet installed in `kernel`. */
export function exportProofForMachine(
  kernel: Kernel,
  name: string,
  proof: Proof,
  environment = kernel.digest(),
): MachineProofExport {
  const encoded = encodeProofDagWithIndex(proof);
  return Object.freeze({
    theorem: name,
    environment,
    proof: encoded.dag,
    trace: buildProofTrace(kernel, proof, encoded.nodeIds),
  });
}

export function verifyExportedProof(kernel: Kernel, exported: ExportedProof): Formula {
  const { digest, ...body } = exported;
  if (exported.format !== "grace17.proof" || exported.version !== 4 || digest !== digestExport(body)) {
    throw new KernelError("Malformed or corrupted exported proof");
  }
  if (exported.environment !== kernel.digest()) throw new KernelError("Exported proof belongs to a different environment");
  const registered = kernel.theorems.get(exported.theorem);
  if (!registered || !formulaEquals(registered, exported.statement)) throw new KernelError("Exported theorem statement mismatch");
  const checked = checkProofDag(kernel, exported.proof).formula;
  if (!formulaEquals(checked, exported.statement)) throw new KernelError("Exported proof derives the wrong statement");
  validateTrace(exported);
  const decoded = decodeProofDag(exported.proof);
  const nodeIds = new Map(decoded.map((proof, index) => [proof, index]));
  const expectedTrace = buildProofTrace(kernel, decoded[exported.proof.root]!, nodeIds);
  if (canonical(expectedTrace) !== canonical(exported.trace)) {
    throw new KernelError("Exported proof judgment trace does not match the checked proof");
  }
  if (exported.tactics) validateTacticTrace(exported.tactics);
  return checked;
}

function validateTacticTrace(trace: TacticTrace): void {
  if (!trace.initial || !Array.isArray(trace.initial.goals) || !Array.isArray(trace.steps)) {
    throw new KernelError("Malformed tactic trace");
  }
  let state = trace.initial;
  trace.steps.forEach((step, index) => {
    if (!Number.isSafeInteger(step.line) || step.line < 1 || typeof step.command !== "string" || !step.command ||
        !step.before || !Array.isArray(step.before.goals) || !step.after || !Array.isArray(step.after.goals) ||
        canonical(step.before) !== canonical(state)) {
      throw new KernelError(`Malformed tactic trace step #${index}`);
    }
    state = step.after;
  });
  if (trace.steps.length === 0 || state.goals.length !== 0) {
    throw new KernelError("Tactic trace does not finish the proof");
  }
  trace.narrative?.forEach((entry, index) => {
    if (!Number.isSafeInteger(entry.line) || entry.line < 1 || !Number.isSafeInteger(entry.indent) || entry.indent < 0 ||
        (entry.kind !== "heading" && entry.kind !== "note") || typeof entry.text !== "string" || !entry.text) {
      throw new KernelError(`Malformed proof narrative entry #${index}`);
    }
  });
}

function buildProofTrace(kernel: Kernel, root: Proof, nodeIds: ReadonlyMap<Proof, number>): ProofTrace {
  const nodes: ProofTraceNode[] = [];
  const interned = new Map<string, number>();

  const visit = (proof: Proof, assumptions: readonly Formula[]): number => {
    const proofNode = nodeIds.get(proof);
    if (proofNode === undefined) throw new KernelError("Proof trace refers to an unencoded proof node");
    const key = `${proofNode}\u001e${assumptions.map(formulaCanonical).join("\u001f")}`;
    const previous = interned.get(key);
    if (previous !== undefined) return previous;

    const id = nodes.length;
    interned.set(key, id);
    nodes.push(undefined as unknown as ProofTraceNode);
    const conclusion = kernel.checkProof(proof, assumptions);
    const children = contextualChildren(kernel, proof, assumptions).map(item => visit(item.proof, item.assumptions));
    nodes[id] = Object.freeze({
      proofNode,
      assumptions: Object.freeze([...assumptions]),
      conclusion,
      children: Object.freeze(children),
    });
    return id;
  };

  const traceRoot = visit(root, []);
  return Object.freeze({ root: traceRoot, nodes: Object.freeze(nodes) });
}

function contextualChildren(
  kernel: Kernel,
  proof: Proof,
  assumptions: readonly Formula[],
): { readonly proof: Proof; readonly assumptions: readonly Formula[] }[] {
  const same = (child: Proof) => ({ proof: child, assumptions });
  switch (proof.rule) {
    case "assumption": case "axiom": case "theorem": case "definition": case "refl": case "compute": case "rationalClassCompute": return [];
    case "impIntro": return [{ proof: proof.body, assumptions: [...assumptions, proof.assumption] }];
    case "orElim": {
      const disjunction = kernel.checkProof(proof.disjunction, assumptions);
      if (disjunction.tag !== "or") throw new KernelError("Disjunction trace expected an or-formula");
      return [same(proof.disjunction), { proof: proof.left, assumptions: [...assumptions, disjunction.left] },
        { proof: proof.right, assumptions: [...assumptions, disjunction.right] }];
    }
    case "existsElim": {
      const existential = kernel.checkProof(proof.existential, assumptions);
      if (existential.tag !== "exists") throw new KernelError("Existential trace expected an existential formula");
      const instance = substituteFormula(existential.body, existential.variable, v(proof.witness));
      return [same(proof.existential), { proof: proof.body, assumptions: [...assumptions, instance] }];
    }
    case "induction": {
      const datatype = kernel.datatypes.get(proof.datatype);
      if (!datatype) throw new KernelError(`Unknown induction datatype: ${proof.datatype}`);
      return proof.cases.map(branch => {
        const constructor = datatype.constructors.find(item => item.name === branch.constructor)!;
        const branchAssumptions: Formula[] = [...assumptions];
        for (let index = 0; index < constructor.arity; index += 1) {
          const field = v(branch.fields[index]!);
          if (constructor.recursiveFields.includes(index)) {
            branchAssumptions.push(pred(datatype.predicate, ...proof.parameters, field));
            branchAssumptions.push(substituteFormula(proof.motive, proof.variable, field));
          } else {
            const parameterField = constructor.parameterFields?.find(item => item.field === index);
            if (parameterField) branchAssumptions.push(pred("in", field, proof.parameters[parameterField.parameter]!));
          }
        }
        return { proof: branch.proof, assumptions: branchAssumptions };
      });
    }
    case "symm": return [same(proof.proof)];
    case "trans": case "andIntro": return [same(proof.left), same(proof.right)];
    case "congr": return proof.proofs.map(same);
    case "eqElim": return [same(proof.equality), same(proof.evidence)];
    case "impElim": return [same(proof.implication), same(proof.argument)];
    case "forallIntro": return [same(proof.body)];
    case "forallElim": return [same(proof.universal)];
    case "andElimLeft": case "andElimRight": return [same(proof.conjunction)];
    case "orIntroLeft": case "orIntroRight": return [same(proof.proof)];
    case "iffIntro": return [same(proof.forward), same(proof.backward)];
    case "iffElimLeft": case "iffElimRight": return [same(proof.equivalence)];
    case "existsIntro": return [same(proof.evidence)];
    case "falseElim": return [same(proof.absurdity)];
    case "dne": return [same(proof.proof)];
    case "wellFoundedInduction": return [same(proof.wellFounded), same(proof.step)];
  }
}

function validateTrace(exported: ExportedProof): void {
  const { trace } = exported;
  if (!trace || !Number.isSafeInteger(trace.root) || trace.root < 0 || trace.root >= trace.nodes.length) {
    throw new KernelError("Exported proof has an invalid judgment trace");
  }
  trace.nodes.forEach((node, index) => {
    if (!Number.isSafeInteger(node.proofNode) || node.proofNode < 0 || node.proofNode >= exported.proof.nodes.length ||
        !Array.isArray(node.assumptions) || !Array.isArray(node.children) ||
        node.children.some(child => !Number.isSafeInteger(child) || child < 0 || child >= trace.nodes.length)) {
      throw new KernelError(`Malformed proof judgment #${index}`);
    }
  });
  const root = trace.nodes[trace.root]!;
  if (root.assumptions.length !== 0 || root.proofNode !== exported.proof.root ||
      !formulaEquals(root.conclusion, exported.statement)) {
    throw new KernelError("Exported proof judgment trace has the wrong root");
  }
}

const proofDependencyCache = new WeakMap<Proof, ProofDependencies>();

function proofDependencies(kernel: Kernel, root: Proof, rootName: string): ProofDependencies {
  const known = proofDependencyCache.get(root);
  if (known) return known;
  const axioms = new Set<string>();
  const theorems = new Set<string>();
  const definitions = new Set<string>();
  const merge = (dependencies: ProofDependencies): void => {
    dependencies.axioms.forEach(name => axioms.add(name));
    dependencies.theorems.forEach(name => theorems.add(name));
    dependencies.definitions.forEach(name => definitions.add(name));
  };
  const visit = (value: unknown): void => {
    if (isProof(value)) {
      if (value.rule === "axiom") axioms.add(value.name);
      if (value.rule === "definition") definitions.add(`${value.name}.${value.property ?? "equation"}`);
      if (value.rule === "compute") value.definitions.forEach(name => definitions.add(`${name}.equation`));
      if (value.rule === "rationalClassCompute") {
        theorems.add("Grace.Cumulus.Rat.Operations.rationalClass.eq");
        definitions.add("Grace.Core.Nat.Rec.add.equation");
        definitions.add("Grace.Core.Nat.Rec.mul.equation");
      }
      if (value.rule === "theorem") {
        if (value.name !== rootName) theorems.add(value.name);
        const dependency = kernel.theoremProofs.get(value.name);
        if (dependency) merge(proofDependencies(kernel, dependency, value.name));
      }
      Object.entries(value).forEach(([key, child]) => { if (key !== "rule") visit(child); });
    } else if (Array.isArray(value)) {
      value.forEach(visit);
    } else if (value !== null && typeof value === "object") {
      Object.values(value).forEach(visit);
    }
  };
  visit(root);
  const result = Object.freeze({
    axioms: Object.freeze([...axioms].sort()),
    theorems: Object.freeze([...theorems].sort()),
    definitions: Object.freeze([...definitions].sort()),
  });
  proofDependencyCache.set(root, result);
  return result;
}

/** Collect transitive theorem dependencies without constructing a proof DAG or judgment trace. */
export function theoremDependencies(kernel: Kernel, name: string): ProofDependencies {
  const proof = kernel.theoremProofs.get(name);
  if (!kernel.theorems.has(name) || !proof) throw new KernelError(`Theorem has no retained proof: ${name}`);
  return proofDependencies(kernel, proof, name);
}

function isProof(value: unknown): value is Proof {
  return value !== null && typeof value === "object" && typeof (value as { rule?: unknown }).rule === "string";
}

function digestExport(body: object): string {
  return sha256Hex(canonical(body));
}
