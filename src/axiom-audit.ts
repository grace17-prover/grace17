// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { MachineOp, type ProofMachineModuleProgram } from "./machine.ts";
import { KernelError, type Kernel, type KernelAdmissionEvent } from "./kernel.ts";
import { formatFormula } from "./pretty.ts";
import type { Proof } from "./proof.ts";
import { largeCardinalOccurrences, throughDefinitions, type LargeCardinalHypothesis } from "./large-cardinals.ts";

export interface AxiomAudit {
  readonly theorem: string;
  readonly complete: boolean;
  readonly direct: readonly string[];
  /** All named axioms, including direct uses. */
  readonly hereditary: readonly string[];
  readonly axioms: readonly { name: string; statement: string; direct: boolean; path: readonly string[] }[];
  /** Built-in schema/definition mechanisms are separate from named axioms. */
  readonly mechanisms: readonly { name: string; kind: string; path: readonly string[] }[];
  readonly unavailable: readonly { name: string; path: readonly string[] }[];
  readonly classicalLogic: boolean;
  readonly visited: number;
  /** The registered large cardinal hypotheses (`register largecardinal`) of the theorem, over its whole proof. */
  readonly largeCardinals: LargeCardinalAudit;
}

/**
 * `reliesOn`: the hypotheses the theorem relies on, through its statement or
 * any lemma or definition its proof uses, each with where the reliance
 * starts: `path` runs to the declaration whose statement relies on it
 * (`via: "premise"`), or to the one that uses a lemma about it, `lemma`,
 * without a premise of its own that supplies it (`via: "supplied"`).
 * `about`: those the statement is about and the proof relies on nowhere,
 * as in a theorem about every inaccessible κ. `mentions`: those that occur
 * only as what the theorem proves.
 */
export interface LargeCardinalAudit {
  readonly reliesOn: readonly (LargeCardinalHypothesis & {
    readonly via: "premise" | "supplied";
    readonly path: readonly string[];
    readonly lemma?: string;
  })[];
  readonly about: readonly LargeCardinalHypothesis[];
  readonly mentions: readonly LargeCardinalHypothesis[];
}

type Ref = { kind: "theorem" | "definition"; name: string };
const key = (ref: Ref): string => `${ref.kind}:${ref.name}`;
const label = (ref: Ref): string => ref.kind === "definition" ? `definition ${ref.name}` : ref.name;

/** Read-only proof dependency audit. No proof checking authority or global cache. */
export function auditTheoremAxioms(kernel: Kernel, theorem: string): AxiomAudit {
  if (!kernel.theorems.has(theorem)) throw new KernelError(`Unknown theorem: ${theorem}`);
  const admissions = new Map<string, KernelAdmissionEvent>();
  let naturalRegistration = false;
  for (const event of kernel.admissionEventsSince({ eventCount: 0, environment: "" })) {
    if (event.operation === "registerNaturalDatatype") naturalRegistration = true;
    const payload = event.payload;
    const options = (payload.options ?? payload.spec ?? payload) as Record<string, unknown>;
    if (typeof options.name === "string" && event.operation !== "addTheorem" && event.operation !== "addAxiom" &&
        event.operation !== "declareFunction" && event.operation !== "declarePredicate") {
      admissions.set(options.name, event);
    }
  }
  const root: Ref = { kind: "theorem", name: theorem };
  const queue: Ref[] = [root];
  const parents = new Map<string, Ref | undefined>([[key(root), undefined]]);
  const axioms = new Map<string, Ref>();
  const direct = new Set<string>();
  const mechanisms: { name: string; kind: string; path: readonly string[] }[] = [];
  const unavailable: { name: string; path: readonly string[] }[] = [];
  let classicalLogic = false;
  const path = (ref: Ref): string[] => {
    const result: string[] = [];
    for (let cursor: Ref | undefined = ref; cursor; cursor = parents.get(key(cursor))) result.push(label(cursor));
    return result.reverse();
  };
  // Every theorem and definition a declaration's proof refers to, for
  // closing the large cardinal classification over the proof.
  const uses = new Map<string, Ref[]>();
  const enqueue = (ref: Ref, parent: Ref): void => {
    const edges = uses.get(key(parent));
    if (edges) edges.push(ref); else uses.set(key(parent), [ref]);
    if (parents.has(key(ref))) return;
    parents.set(key(ref), parent);
    queue.push(ref);
  };
  // Each shared proof object is traversed once per declaration. Breadth-first
  // declaration traversal supplies one shortest dependency path per axiom.
  const scan = (value: unknown, owner: Ref): void => {
    const pending: unknown[] = [value];
    const seen = new WeakSet<object>();
    while (pending.length) {
      const item = pending.pop();
      if (!item || typeof item !== "object" || seen.has(item)) continue;
      seen.add(item);
      // Terms and formulas contain no proof certificates. Avoid traversing
      // their often-large shared syntax trees during a hover audit.
      if ("tag" in item) continue;
      const proof = item as Proof;
      if (proof.rule === "axiom") {
        if (!axioms.has(proof.name)) axioms.set(proof.name, owner);
        if (owner.kind === "theorem" && owner.name === theorem) direct.add(proof.name);
      } else if (proof.rule === "theorem") enqueue({ kind: "theorem", name: proof.name }, owner);
      else if (proof.rule === "definition") enqueue({ kind: "definition", name: proof.name }, owner);
      else if (proof.rule === "compute") {
        for (const name of proof.definitions) enqueue({ kind: "definition", name }, owner);
      } else if (proof.rule === "induction") enqueue({ kind: "definition", name: proof.datatype }, owner);
      else if (proof.rule === "rationalClassCompute") {
        enqueue({ kind: "theorem", name: "Grace.Cumulus.Rat.Operations.rationalClass.eq" }, owner);
        for (const name of ["Grace.Core.Nat.Rec.add", "Grace.Core.Nat.Rec.mul"])
          enqueue({ kind: "definition", name }, owner);
      } else if (proof.rule === "dne") classicalLogic = true;
      for (const child of Object.values(item)) if (child && typeof child === "object") pending.push(child);
    }
  };
  const scanMachine = (program: ProofMachineModuleProgram, root: number, owner: Ref): void => {
    const pending = [root];
    const seen = new Set<number>();
    while (pending.length) {
      const index = pending.pop()!;
      if (seen.has(index)) continue;
      seen.add(index);
      const instruction = program.code[index]!;
      const op = instruction[0], count = instruction[3]!;
      const data = 4 + count;
      const symbol = (offset = 0): string => program.symbols[instruction[data + offset]!]!;
      if (op === MachineOp.axiom) {
        const name = symbol();
        if (!axioms.has(name)) axioms.set(name, owner);
        if (owner.name === theorem) direct.add(name);
      } else if (op === MachineOp.theorem) enqueue({ kind: "theorem", name: symbol() }, owner);
      else if (op === MachineOp.definition || op === MachineOp.induction)
        enqueue({ kind: "definition", name: symbol() }, owner);
      else if (op === MachineOp.compute) {
        for (let i = 1; i <= instruction[data]!; i++) enqueue({ kind: "definition", name: symbol(i) }, owner);
      } else if (op === MachineOp.rationalClassCompute) {
        enqueue({ kind: "theorem", name: "Grace.Cumulus.Rat.Operations.rationalClass.eq" }, owner);
        for (const name of ["Grace.Core.Nat.Rec.add", "Grace.Core.Nat.Rec.mul"])
          enqueue({ kind: "definition", name }, owner);
      } else if (op === MachineOp.dne) classicalLogic = true;
      for (let i = 0; i < count; i++) pending.push(instruction[4 + i]!);
    }
  };
  for (let cursor = 0; cursor < queue.length; cursor++) {
    const ref = queue[cursor]!;
    if (ref.kind === "theorem") {
      const proof = kernel.theoremProofs.get(ref.name);
      const machine = kernel.theoremMachineProofs.get(ref.name);
      if (proof) scan(proof, ref);
      else if (machine) scanMachine(machine.program, machine.root, ref);
      else unavailable.push({ name: ref.name, path: path(ref) });
    } else {
      const record = kernel.definitions.get(ref.name);
      const event = admissions.get(ref.name);
      if (!record && ref.name === "Naturals" && naturalRegistration && kernel.datatypes.has("Naturals")) {
        // The canonical natural induction rule is enabled by this named
        // least-inductive-set axiom and the transparent Nat/zero/succ interface.
        mechanisms.push({ name: "Naturals", kind: "natural-induction", path: path(ref) });
        if (kernel.axioms.has("set.infinity.minimal")) {
          if (!axioms.has("set.infinity.minimal")) axioms.set("set.infinity.minimal", ref);
        } else unavailable.push({ name: "set.infinity.minimal", path: path(ref) });
        for (const name of ["Nat", "zero", "succ"]) enqueue({ kind: "definition", name }, ref);
        continue;
      }
      if (!record || !event) {
        unavailable.push({ name: label(ref), path: path(ref) });
        continue;
      }
      if (!["function", "predicate"].includes(record.kind)) {
        mechanisms.push({ name: ref.name, kind: record.kind === "unique-choice" ? "unique-description" : record.kind, path: path(ref) });
      }
      // Existence, functionality, well-foundedness, closure and decrease
      // certificates reside in admission payloads, not DefinitionRecord.
      scan(event.payload, ref);
      const recursive = kernel.recursiveFunctions.get(ref.name);
      if (recursive) enqueue({ kind: "definition", name: recursive.datatype }, ref);
    }
  }
  const names = [...axioms.keys()].sort();
  return {
    theorem, complete: unavailable.length === 0,
    direct: [...direct].sort(), hereditary: names,
    axioms: names.map(name => ({ name, statement: kernel.axioms.has(name)
      ? formatFormula(kernel.axioms.get(name)!, { symbol: n => n }) : "Unavailable axiom statement",
      direct: direct.has(name), path: [...path(axioms.get(name)!), `axiom ${name}`] })),
    mechanisms: mechanisms.sort((a, b) => a.name.localeCompare(b.name)),
    unavailable, classicalLogic, visited: queue.length,
    largeCardinals: largeCardinalAudit(kernel, root, queue, uses, path),
  };
}

/**
 * The large cardinal hypotheses a theorem relies on over its whole proof.
 * A declaration relies on what its statement relies on, on what the
 * declarations it uses rely on, and on what they are about that its own
 * statement does not mention: it supplied that premise from elsewhere.
 */
function largeCardinalAudit(
  kernel: Kernel, root: Ref, order: readonly Ref[], uses: ReadonlyMap<string, readonly Ref[]>, path: (ref: Ref) => string[],
): LargeCardinalAudit {
  const own = largeCardinalOccurrences(kernel, kernel.theorems.get(root.name)!);
  const hypotheses = new Map<string, LargeCardinalHypothesis>();
  const statements = new Map<string, { readonly relies: ReadonlySet<string>; readonly about: ReadonlySet<string>; readonly mentions: ReadonlySet<string> }>();
  const statement = (ref: Ref) => {
    let known = statements.get(key(ref));
    if (!known) {
      const formula = ref.kind === "theorem" ? kernel.theorems.get(ref.name) : undefined;
      const found = formula ? largeCardinalOccurrences(kernel, formula) : undefined;
      for (const item of [...found?.reliesOn ?? [], ...found?.about ?? []]) hypotheses.set(item.predicate, item);
      known = {
        relies: new Set(found?.reliesOn.map(item => item.predicate)),
        about: new Set(found?.about.map(item => item.predicate)),
        mentions: throughDefinitions(kernel, [found?.reliesOn ?? [], found?.about ?? [], found?.mentions ?? []].flat().map(item => item.predicate)),
      };
      statements.set(key(ref), known);
    }
    return known;
  };
  // Children before parents: a depth-first post-order over the uses. Proofs
  // form no cycles; were one met, the declaration on the stack counts as
  // relying on nothing yet.
  const postorder: Ref[] = [];
  const entered = new Set<string>();
  const stack: { readonly ref: Ref; next: number }[] = [{ ref: root, next: 0 }];
  entered.add(key(root));
  while (stack.length) {
    const top = stack[stack.length - 1]!;
    const children = uses.get(key(top.ref)) ?? [];
    if (top.next < children.length) {
      const child = children[top.next++]!;
      if (!entered.has(key(child))) { entered.add(key(child)); stack.push({ ref: child, next: 0 }); }
    } else { stack.pop(); postorder.push(top.ref); }
  }
  const relies = new Map<string, Set<string>>();
  const about = new Map<string, Set<string>>();
  const supplied = new Map<string, Map<string, Ref>>();
  for (const ref of postorder) {
    const own = statement(ref);
    const result = new Set(own.relies);
    const lemmas = new Map<string, Ref>();
    for (const child of uses.get(key(ref)) ?? []) {
      for (const name of relies.get(key(child)) ?? []) result.add(name);
      for (const name of about.get(key(child)) ?? []) {
        // A statement that mentions the hypothesis anywhere can supply it
        // from its own premises or quantifiers; one that never mentions it
        // obtained it elsewhere.
        if (own.about.has(name) || own.relies.has(name) || own.mentions.has(name)) continue;
        result.add(name);
        if (!lemmas.has(name)) lemmas.set(name, child);
      }
    }
    relies.set(key(ref), result);
    about.set(key(ref), new Set([...own.about].filter(name => !result.has(name))));
    supplied.set(key(ref), lemmas);
  }
  const reliesOn = [...relies.get(key(root)) ?? []].sort().map(name => {
    // The nearest declaration where the reliance starts.
    for (const ref of order) {
      if (statement(ref).relies.has(name)) return { ...hypotheses.get(name)!, via: "premise" as const, path: path(ref) };
      const lemma = supplied.get(key(ref))?.get(name);
      if (lemma) return { ...hypotheses.get(name)!, via: "supplied" as const, path: path(ref), lemma: label(lemma) };
    }
    return { ...hypotheses.get(name)!, via: "premise" as const, path: [root.name] };
  });
  return {
    reliesOn,
    about: own.about.filter(item => !relies.get(key(root))?.has(item.predicate)),
    mentions: own.mentions.filter(item => !relies.get(key(root))?.has(item.predicate)),
  };
}
