// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { sha256Hex } from "./hash.ts";
import {
  and, app, canonical, eq, exists, forall, foralls, formulaCanonical, formulaContainsSymbol, formulaEquals,
  freeFormulaVariables, freeTermVariables, iff, imp, nat, naturalValue, not, or, pred, substituteFormula, termEquals, v,
  type Formula, type Term,
} from "./ast.ts";
import { compute, congr, definition as definitionProof, forallElim, refl, trans, type Proof } from "./proof.ts";
import { formatTerm } from "./pretty.ts";
import { evaluateNative, nativeValueEquals, nativeValueToTerm, type NativeValue } from "./runtime.ts";
import { KernelError } from "./errors.ts";
import type { TacticTrace } from "./tactic-trace.ts";
import { deepFreeze, isDeeplyFrozen } from "./freeze.ts";
import { verifyProofModuleStatements, type ProofMachineModuleProgram } from "./machine.ts";

export { KernelError } from "./errors.ts";

export type DefinitionKind = "function" | "predicate" | "separation" | "replacement" | "unique-choice" |
  "datatype" | "recursive" | "well-founded-recursive" | "well-founded-set-recursive" |
  "membership-recursive" | "transfinite-recursive";
export type SetTheoryProfile = "none" | "ZF" | "ZFC" | "ZFG";

export interface DefinitionRecord {
  readonly name: string;
  readonly kind: DefinitionKind;
  readonly parameters: readonly string[];
  readonly properties: ReadonlyMap<string, Formula>;
}

export interface FoundationCapabilities {
  readonly separation: boolean;
  readonly replacement: boolean;
  readonly inductiveDefinitions?: boolean;
  readonly setTheory?: SetTheoryProfile;
}

export interface ProofCheckStats {
  nodesVisited: number;
  cacheHits: number;
}

export interface EvaluationStats {
  readonly calls: number;
  readonly reductions: number;
  readonly cacheHits: number;
}

export interface FoundationReport {
  readonly profile: SetTheoryProfile;
  readonly axioms: readonly string[];
  readonly schemaInstances: Readonly<Record<
    "separation" | "replacement" | "uniqueChoice" | "datatype" | "wellFoundedRecursion" |
    "membershipRecursion" | "transfiniteRecursion",
    readonly string[]
  >>;
}

/**
 * An untrusted transcript of a successful public kernel admission.  It is not
 * part of the logical state and is never consulted while checking proofs.  A
 * compiled-module writer turns these values into authenticated certificates;
 * a loader must replay the named public operation rather than restoring maps.
 */
export interface KernelAdmissionEvent {
  readonly operation: KernelAdmissionOperation;
  readonly payload: Readonly<Record<string, unknown>>;
}

export type KernelAdmissionOperation =
  | "declareFunction" | "declarePredicate" | "addAxiom" | "addTheorem"
  | "defineFunction" | "definePredicate" | "declareDatatype" | "registerNaturalDatatype"
  | "defineStructuralFunction" | "defineWellFoundedFunction" | "defineSubset"
  | "reifyUnaryOperation" | "defineReplacement" | "defineUniqueFunction"
  | "defineWellFoundedSetFunction" | "defineMembershipRecursiveFunction"
  | "defineTransfiniteFunction";

export interface KernelAdmissionCheckpoint {
  readonly eventCount: number;
  readonly environment: string;
}

interface ContextTrieNode { readonly children: Map<number, ContextTrieNode>; token?: object }

interface CachedCheck {
  /** The cache the result belongs to, by its token; a replaced cache leaves every result behind. */
  readonly token: object;
  readonly context: object;
  readonly formula: Formula;
  others?: WeakMap<object, Formula>;
}

// A checked proof node carries its cached result in a private field: the
// result is found by the node's identity exactly as it was in a weak map keyed
// by the node, and the field, named only in this module, can be neither read
// nor forged outside it. The weak map it replaces was an ephemeron table
// holding millions of nodes, and probing it was most of the cost of a check.
// An exotic node that refuses the field keeps its result in the table.
class ProofNodeTarget { constructor(target: object) { return target; } }
class CheckedProofNode extends ProofNodeTarget {
  #checked: CachedCheck;
  constructor(target: object, checked: CachedCheck) { super(target); this.#checked = checked; }
  static of(target: object): CachedCheck | undefined { return #checked in target ? target.#checked : undefined; }
  static install(target: object, checked: CachedCheck): boolean {
    if (#checked in target) { target.#checked = checked; return true; }
    try { new CheckedProofNode(target, checked); return true; } catch { return false; }
  }
}

interface ProofCache {
  /** Identity of this cache, held by every result it owns. */
  readonly token: object;
  /**
   * Proof identity -> canonical assumption-context identity -> derived formula,
   * for nodes that cannot carry the result themselves.
   *
   * Equivalent contexts receive one interned token, so final theorem
   * admission can reuse subproofs already checked by the elaborator even though
   * implication introduction reconstructs the assumption arrays.
   */
  readonly results: WeakMap<object, CachedCheck>;
  readonly contextTokens: WeakMap<object, object>;
  /**
   * Canonical formula text -> small id, and the same id by formula identity
   * so an interned formula is never re-serialized. A context is identified
   * by its sorted id set, walked through a trie, so finding the token of a
   * fresh assumption array allocates nothing.
   */
  readonly formulaIds: Map<string, number>;
  readonly formulaIdsByObject: WeakMap<Formula, number>;
  readonly contextTrie: ContextTrieNode;
  /** Canonical context identity -> alpha-canonical active formulas. */
  readonly activeAssumptions: WeakMap<object, ReadonlySet<string>>;
}

// A closed check must never reuse a caller-owned array's previous open-context
// token: that array may have been emptied since its last check.
const closedAssumptions: readonly Formula[] = Object.freeze([]);

function emptyProofCache(): ProofCache {
  return {
    token: {}, results: new WeakMap(), contextTokens: new WeakMap(), activeAssumptions: new WeakMap(),
    formulaIds: new Map(), formulaIdsByObject: new WeakMap(), contextTrie: { children: new Map() },
  };
}

export interface ConstructorSpec {
  readonly name: string;
  readonly recursiveFields: readonly number[];
  readonly arity: number;
  /** Nonrecursive fields constrained to a datatype Set parameter. */
  readonly parameterFields?: readonly { readonly field: number; readonly parameter: number }[];
}

export interface DatatypeRecord {
  readonly name: string;
  readonly predicate: string;
  readonly parameters?: readonly string[];
  readonly constructors: readonly ConstructorSpec[];
  /** Give surface ADT constructors a canonical tagged Kuratowski denotation. */
  readonly setTheoreticEncoding?: boolean;
}

export type Pattern =
  | { readonly tag: "bind"; readonly name: string }
  | { readonly tag: "ctor"; readonly name: string; readonly args: readonly Pattern[] };

export const bind = (name: string): Pattern => ({ tag: "bind", name });
export const ctor = (name: string, ...args: Pattern[]): Pattern => ({ tag: "ctor", name, args });

function freshLogicalVariable(base: string, term: Term, extra: readonly string[] = []): string {
  const forbidden = new Set([...freeTermVariables(term), ...extra]);
  if (!forbidden.has(base)) return base;
  for (let index = 1; ; index += 1) if (!forbidden.has(`${base}_${index}`)) return `${base}_${index}`;
}

/** Canonical formulas used to validate pleasant userland ordinal interfaces. */
export function vonNeumannTransitive(set: Term): Formula {
  const member = freshLogicalVariable("member", set);
  const element = freshLogicalVariable("element", set, [member]);
  return forall(member, imp(pred("in", v(member), set), forall(element,
    imp(pred("in", v(element), v(member)), pred("in", v(element), set)))));
}

export function vonNeumannOrdinal(term: Term): Formula {
  const member = freshLogicalVariable("ordinalMember", term);
  return and(vonNeumannTransitive(term), forall(member,
    imp(pred("in", v(member), term), vonNeumannTransitive(v(member)))));
}

export function vonNeumannLimit(term: Term, successor: (value: Term) => Term = value =>
  app("union2", value, app("singleton", value))): Formula {
  const member = freshLogicalVariable("limitMember", term);
  return and(vonNeumannOrdinal(term), and(not(eq(term, app("empty"))), forall(member,
    imp(pred("in", v(member), term), pred("in", successor(v(member)), term)))));
}

export interface RecursiveEquation {
  readonly patterns: readonly Pattern[];
  readonly body: Term;
}

export interface RecursiveFunctionRecord {
  readonly name: string;
  readonly parameters: readonly string[];
  readonly datatype: string;
  readonly decreasingParameter: number;
  readonly equations: readonly RecursiveEquation[];
  readonly admission: "structural" | "well-founded";
  readonly termination?: {
    readonly relation: Term;
    readonly domain: Term;
    readonly measure: Term;
  };
}

export class Kernel {
  readonly functions = new Map<string, number>();
  readonly predicates = new Map<string, number>();
  readonly axioms = new Map<string, Formula>();
  readonly theorems = new Map<string, Formula>();
  readonly theoremProofs = new Map<string, Proof>();
  /** Verified certificate provenance for on-demand audits; never consulted by proof checking. */
  readonly theoremMachineProofs = new Map<string, { readonly program: ProofMachineModuleProgram; readonly root: number }>();
  readonly theoremTacticTraces = new Map<string, TacticTrace>();
  readonly definitions = new Map<string, DefinitionRecord>();
  readonly datatypes = new Map<string, DatatypeRecord>();
  readonly recursiveFunctions = new Map<string, RecursiveFunctionRecord>();
  readonly functionBodies = new Map<string, { readonly parameters: readonly string[]; readonly body: Term }>();
  readonly capabilities: FoundationCapabilities;
  /** Successful closed checks survive incremental rechecks in this monotone environment. */
  private readonly closedProofCache = new WeakMap<object, Formula>();
  /** Successful open subproofs are reused while tactics grow a proof in one context. */
  private contextualProofCache: ProofCache = emptyProofCache();
  private contextualAssumptionSnapshots = new WeakMap<object, readonly Formula[]>();
  private readonly admissions: KernelAdmissionEvent[] = [];
  /**
   * Content receipts for modules replayed successfully in this process.
   * Receipts are loader provenance, never logical state: proof checking and
   * environment digests do not consult them.
   */
  private readonly checkedModules = new Map<string, string>();
  private readonly checkedModuleResults = new Map<string, string>();
  private foundationBoundary?: string;
  private cachedDigest?: string;

  constructor(capabilities: FoundationCapabilities = { separation: false, replacement: false }) {
    deepFreeze(capabilities);
    this.capabilities = capabilities;
  }

  /**
   * Cheap monotone checkpoint for incremental elaboration.  Every declaration
   * in the source kernel has already passed this kernel's checks; copying the
   * maps introduces no new trusted proposition and lets an editor discard only
   * the module currently being edited.
   */
  fork(): Kernel {
    const result = new Kernel({ ...this.capabilities });
    for (const [name, value] of this.functions) result.functions.set(name, value);
    for (const [name, value] of this.predicates) result.predicates.set(name, value);
    for (const [name, value] of this.axioms) result.axioms.set(name, value);
    for (const [name, value] of this.theorems) result.theorems.set(name, value);
    for (const [name, value] of this.theoremProofs) result.theoremProofs.set(name, value);
    for (const [name, value] of this.theoremMachineProofs) result.theoremMachineProofs.set(name, value);
    for (const [name, value] of this.theoremTacticTraces) result.theoremTacticTraces.set(name, value);
    for (const [name, value] of this.definitions) result.definitions.set(name, value);
    for (const [name, value] of this.datatypes) result.datatypes.set(name, value);
    for (const [name, value] of this.recursiveFunctions) result.recursiveFunctions.set(name, value);
    for (const [name, value] of this.functionBodies) result.functionBodies.set(name, value);
    result.admissions.push(...this.admissions);
    for (const [name, digest] of this.checkedModules) result.checkedModules.set(name, digest);
    for (const [name, digest] of this.checkedModuleResults) result.checkedModuleResults.set(name, digest);
    result.foundationBoundary = this.foundationBoundary;
    result.cachedDigest = this.cachedDigest;
    return result;
  }

  /** Return the content digest of an already replayed compiled module. */
  checkedModuleReceipt(name: string): string | undefined {
    return this.checkedModules.get(name);
  }

  /** Strict standalone result committed to by the checked artifact. */
  checkedModuleResultEnvironment(name: string): string | undefined {
    return this.checkedModuleResults.get(name);
  }

  /** A deterministic report for cache loaders and editor infrastructure. */
  checkedModuleReceipts(): readonly { readonly module: string; readonly digest: string }[] {
    return [...this.checkedModules].map(([module, digest]) => ({ module, digest }))
      .sort((left, right) => left.module.localeCompare(right.module));
  }

  /**
   * Record successful checked replay. This cannot add or authorize a logical
   * declaration; only compiled-module replay should normally call it.
   */
  recordCheckedModule(module: string, digest: string, resultEnvironment = this.digest()): void {
    if (!module || !/^[0-9a-f]{64}$/.test(digest) || !/^[0-9a-f]{64}$/.test(resultEnvironment)) {
      throw new KernelError("Malformed checked module receipt");
    }
    const previous = this.checkedModules.get(module);
    const previousResult = this.checkedModuleResults.get(module);
    if ((previous !== undefined && previous !== digest) ||
        (previousResult !== undefined && previousResult !== resultEnvironment)) {
      throw new KernelError(`Conflicting checked module receipt: ${module}`);
    }
    this.checkedModules.set(module, digest);
    this.checkedModuleResults.set(module, resultEnvironment);
  }

  /** Identify the completed foundation prefix for portable module loading. */
  recordFoundationBoundary(): string {
    const digest = this.digest();
    if (this.foundationBoundary !== undefined && this.foundationBoundary !== digest) {
      throw new KernelError("Foundation boundary is already fixed");
    }
    this.foundationBoundary = digest;
    return digest;
  }

  /** Foundation identity is loader metadata and is not consulted by proofs. */
  foundationDigest(): string | undefined {
    return this.foundationBoundary;
  }

  /** Mark an exact environment boundary from which a compiled module starts. */
  admissionCheckpoint(): KernelAdmissionCheckpoint {
    return Object.freeze({ eventCount: this.admissions.length, environment: this.digest() });
  }

  /** Untrusted compiler input; replay never grants these records authority. */
  admissionEventsSince(checkpoint: KernelAdmissionCheckpoint): readonly KernelAdmissionEvent[] {
    if (!Number.isSafeInteger(checkpoint.eventCount) || checkpoint.eventCount < 0 ||
        checkpoint.eventCount > this.admissions.length) throw new KernelError("Invalid kernel admission checkpoint");
    return this.admissions.slice(checkpoint.eventCount);
  }

  declareFunction(name: string, arity: number): void {
    this.ensureFresh(name);
    this.ensureArity(arity);
    this.functions.set(name, arity);
    this.cachedDigest = undefined;
    this.recordAdmission("declareFunction", { name, arity });
  }

  declarePredicate(name: string, arity: number): void {
    this.ensureFresh(name);
    this.ensureArity(arity);
    this.predicates.set(name, arity);
    this.cachedDigest = undefined;
    this.recordAdmission("declarePredicate", { name, arity });
  }

  addAxiom(name: string, formula: Formula): void {
    if (this.axioms.has(name) || this.theorems.has(name)) throw new KernelError(`Duplicate proposition name: ${name}`);
    this.checkFormula(formula);
    this.ensureClosed(formula, `Axiom ${name}`);
    deepFreeze(formula);
    this.axioms.set(name, formula);
    this.cachedDigest = undefined;
    this.recordAdmission("addAxiom", { name, formula });
  }

  addTheorem(name: string, statement: Formula, proof: Proof): void {
    if (this.axioms.has(name) || this.theorems.has(name)) throw new KernelError(`Duplicate proposition name: ${name}`);
    this.checkFormula(statement);
    this.ensureClosed(statement, `Theorem ${name}`);
    const actual = this.checkProof(proof);
    if (!formulaEquals(actual, statement)) {
      throw new KernelError(`Proof of ${name} derives ${canonical(actual)}, expected ${canonical(statement)}`);
    }
    deepFreeze(statement);
    this.theorems.set(name, statement);
    this.theoremProofs.set(name, proof);
    this.cachedDigest = undefined;
    this.recordAdmission("addTheorem", { name, statement, proof });
  }

  /** Atomically admit a dense theorem batch only after complete machine replay. */
  addTheoremMachineBatch(
    entries: readonly { readonly name: string; readonly statement: Formula }[],
    program: ProofMachineModuleProgram,
    reload?: (name: string) => ProofMachineModuleProgram,
  ): void {
    if (entries.length === 0) throw new KernelError("Cannot admit an empty theorem batch");
    const names = new Set<string>();
    for (const entry of entries) {
      if (!entry.name || names.has(entry.name) || this.axioms.has(entry.name) || this.theorems.has(entry.name)) {
        throw new KernelError(`Duplicate proposition name: ${entry.name}`);
      }
      names.add(entry.name);
      this.checkFormula(entry.statement);
      this.ensureClosed(entry.statement, `Theorem ${entry.name}`);
    }
    verifyProofModuleStatements(this, program, entries);
    // With a loader, the verified program is not retained: an audit reloads
    // it through `reload`, which must return the program admitted here.
    // Retained programs are most of a loaded library's memory.
    if (!reload) deepFreeze(program);
    for (const [name, root] of program.theorems) {
      const theorem = program.symbols[name]!;
      this.theoremMachineProofs.set(theorem, reload
        ? Object.freeze({ get program() { return reload(theorem); }, root })
        : Object.freeze({ program, root }));
    }
    for (const entry of entries) {
      deepFreeze(entry.statement);
      this.theorems.set(entry.name, entry.statement);
    }
    this.cachedDigest = undefined;
  }

  /** Attach untrusted source-level provenance after the theorem is admitted. */
  setTheoremTacticTrace(name: string, trace: TacticTrace): void {
    if (!this.theorems.has(name)) throw new KernelError(`Cannot attach tactics to unknown theorem: ${name}`);
    this.theoremTacticTraces.set(name, trace);
  }

  defineFunction(name: string, parameters: readonly string[], body: Term): DefinitionRecord {
    this.validateParameters(parameters);
    this.ensureFresh(name);
    if (this.termContainsFunction(body, name)) throw new KernelError(`Recursive definition ${name} requires a well-founded recursion certificate`);
    this.checkTerm(body);
    this.ensureVariablesWithin(freeTermVariables(body), parameters, `Definition ${name}`);
    this.functions.set(name, parameters.length);
    deepFreeze(body);
    const storedBody = { parameters: [...parameters], body };
    deepFreeze(storedBody);
    this.functionBodies.set(name, storedBody);
    const lhs = app(name, ...parameters.map(v));
    const equation = foralls(parameters, eq(lhs, body));
    const record = this.recordDefinition(name, "function", parameters, new Map([["equation", equation]]));
    this.recordAdmission("defineFunction", { name, parameters: [...parameters], body });
    return record;
  }

  definePredicate(name: string, parameters: readonly string[], body: Formula): DefinitionRecord {
    this.validateParameters(parameters);
    this.ensureFresh(name);
    if (formulaContainsSymbol(body, name)) throw new KernelError(`Recursive predicate definition: ${name}`);
    this.checkFormula(body);
    this.ensureVariablesWithin(freeFormulaVariables(body), parameters, `Definition ${name}`);
    this.predicates.set(name, parameters.length);
    const equation = foralls(parameters, iff(pred(name, ...parameters.map(v)), body));
    const record = this.recordDefinition(name, "predicate", parameters, new Map([["equation", equation]]));
    this.recordAdmission("definePredicate", { name, parameters: [...parameters], body });
    return record;
  }

  declareDatatype(spec: DatatypeRecord): DefinitionRecord {
    if (!this.capabilities.inductiveDefinitions) throw new KernelError("The foundation does not enable inductive set definitions");
    if (!spec.name || !spec.predicate || spec.constructors.length === 0) throw new KernelError("Malformed datatype declaration");
    if (spec.setTheoreticEncoding &&
        (this.functions.get("orderedPair") !== 2 || this.functions.get("empty") !== 0 || !this.datatypes.has("Naturals"))) {
      throw new KernelError("Set-theoretic datatype encoding requires ordered pairs, empty, and von Neumann naturals");
    }
    if (this.datatypes.has(spec.name)) throw new KernelError(`Datatype already declared: ${spec.name}`);
    this.ensureFresh(spec.name);
    this.ensureFresh(spec.predicate);
    const parameters = spec.parameters ?? [];
    this.validateParameters(parameters);
    const constructorNames = new Set<string>();
    for (const ctor of spec.constructors) {
      this.ensureFresh(ctor.name);
      this.ensureArity(ctor.arity);
      if (constructorNames.has(ctor.name)) throw new KernelError(`Duplicate constructor: ${ctor.name}`);
      constructorNames.add(ctor.name);
      if (new Set(ctor.recursiveFields).size !== ctor.recursiveFields.length ||
          ctor.recursiveFields.some(index => !Number.isSafeInteger(index) || index < 0 || index >= ctor.arity)) {
        throw new KernelError(`Bad recursive-field specification for ${ctor.name}`);
      }
      const parameterFields = ctor.parameterFields ?? [];
      if (new Set(parameterFields.map(item => item.field)).size !== parameterFields.length ||
          parameterFields.some(item => !Number.isSafeInteger(item.field) || item.field < 0 || item.field >= ctor.arity ||
            !Number.isSafeInteger(item.parameter) || item.parameter < 0 || item.parameter >= parameters.length ||
            ctor.recursiveFields.includes(item.field))) {
        throw new KernelError(`Bad parameter-field specification for ${ctor.name}`);
      }
    }

    this.predicates.set(spec.predicate, parameters.length + 1);
    for (const ctor of spec.constructors) this.functions.set(ctor.name, ctor.arity);

    const properties = new Map<string, Formula>();
    const freshNames = (prefix: string, count: number): string[] => {
      const used = new Set(parameters);
      return Array.from({ length: count }, (_, index) => {
        let candidate = `${prefix}${index}`;
        while (used.has(candidate)) candidate = `_${candidate}`;
        used.add(candidate);
        return candidate;
      });
    };
    const conjoin = (items: readonly Formula[]): Formula => {
      if (items.length === 0) throw new KernelError("Internal empty datatype conjunction");
      return items.slice(1).reduce<Formula>((result, item) => and(result, item), items[0]!);
    };
    const disjoin = (items: readonly Formula[]): Formula => {
      if (items.length === 0) throw new KernelError("Internal empty datatype disjunction");
      return items.slice(1).reduce<Formula>((result, item) => or(result, item), items[0]!);
    };
    for (const ctor of spec.constructors) {
      const localConstructorName = ctor.name.slice(ctor.name.lastIndexOf(".") + 1);
      const fields = Array.from({ length: ctor.arity }, (_, index) => `field${index}`);
      const parameterTerms = parameters.map(v);
      let closure = pred(spec.predicate, ...parameterTerms, app(ctor.name, ...fields.map(v)));
      for (let index = fields.length - 1; index >= 0; index -= 1) {
        if (ctor.recursiveFields.includes(index)) {
          closure = imp(pred(spec.predicate, ...parameterTerms, v(fields[index]!)), closure);
        } else {
          const parameterField = ctor.parameterFields?.find(item => item.field === index);
          if (parameterField) closure = imp(pred("in", v(fields[index]!), v(parameters[parameterField.parameter]!)), closure);
        }
      }
      properties.set(`constructor.${localConstructorName}`, foralls([...parameters, ...fields], closure));
      // Constructors execute as compact tagged nodes, but their mathematical
      // denotation is a hereditarily finite Kuratowski encoding.
      // Encoding the fully qualified names makes tags stable across load order.
      if (spec.setTheoreticEncoding && this.functions.get("orderedPair") === 2 && this.functions.get("empty") === 0) {
        const encodeSequence = (items: readonly Term[]): Term => items.reduceRight<Term>(
          (tail, item) => app("orderedPair", item, tail), app("empty"),
        );
        const tag = encodeSequence([...`${spec.name}.${ctor.name}`].map(character => nat(character.codePointAt(0)!)));
        const payload = encodeSequence(fields.map(v));
        properties.set(`representation.${localConstructorName}`, foralls([...parameters, ...fields],
          eq(app(ctor.name, ...fields.map(v)), app("orderedPair", tag, payload))));
      }
    }
    // The inductive declaration also exposes its standard elimination-facing
    // shape facts. They are schema products, checked by every replay checker,
    // and avoid expanding tagged Kuratowski encodings in proofs.
    for (const ctorSpec of spec.constructors) {
      if (ctorSpec.arity === 0) continue;
      const local = ctorSpec.name.slice(ctorSpec.name.lastIndexOf(".") + 1);
      const leftFields = freshNames("left", ctorSpec.arity);
      const rightFields = freshNames("right", ctorSpec.arity);
      const equalFields = leftFields.map((field, index) => eq(v(field), v(rightFields[index]!)));
      properties.set(`injective.${local}`, foralls([...leftFields, ...rightFields], imp(
        eq(app(ctorSpec.name, ...leftFields.map(v)), app(ctorSpec.name, ...rightFields.map(v))),
        conjoin(equalFields),
      )));
    }
    for (let leftIndex = 0; leftIndex < spec.constructors.length; leftIndex += 1) {
      for (let rightIndex = leftIndex + 1; rightIndex < spec.constructors.length; rightIndex += 1) {
        const leftCtor = spec.constructors[leftIndex]!;
        const rightCtor = spec.constructors[rightIndex]!;
        const leftFields = freshNames("left", leftCtor.arity);
        const rightFields = freshNames("right", rightCtor.arity);
        const leftLocal = leftCtor.name.slice(leftCtor.name.lastIndexOf(".") + 1);
        const rightLocal = rightCtor.name.slice(rightCtor.name.lastIndexOf(".") + 1);
        properties.set(`disjoint.${leftLocal}.${rightLocal}`,
          foralls([...leftFields, ...rightFields], not(eq(
            app(leftCtor.name, ...leftFields.map(v)), app(rightCtor.name, ...rightFields.map(v)),
          ))));
      }
    }
    const caseElement = parameters.includes("value") ? "_value" : "value";
    const alternatives = spec.constructors.map((ctorSpec, ctorIndex) => {
      const fields = freshNames(`case${ctorIndex}_field`, ctorSpec.arity);
      const guards: Formula[] = [];
      fields.forEach((field, fieldIndex) => {
        if (ctorSpec.recursiveFields.includes(fieldIndex)) {
          guards.push(pred(spec.predicate, ...parameters.map(v), v(field)));
        } else {
          const parameterField = ctorSpec.parameterFields?.find(item => item.field === fieldIndex);
          if (parameterField) guards.push(pred("in", v(field), v(parameters[parameterField.parameter]!)));
        }
      });
      guards.push(eq(v(caseElement), app(ctorSpec.name, ...fields.map(v))));
      return fields.reduceRight<Formula>((body, field) => exists(field, body), conjoin(guards));
    });
    properties.set("cases", foralls([...parameters, caseElement], imp(
      pred(spec.predicate, ...parameters.map(v), v(caseElement)), disjoin(alternatives),
    )));
    const stored: DatatypeRecord = {
      name: spec.name,
      predicate: spec.predicate,
      parameters: [...parameters],
      constructors: spec.constructors.map(ctor => ({ ...ctor, recursiveFields: [...ctor.recursiveFields],
        parameterFields: [...(ctor.parameterFields ?? [])] })),
      setTheoreticEncoding: spec.setTheoreticEncoding ?? false,
    };
    deepFreeze(stored);
    this.datatypes.set(spec.name, stored);
    const record = this.recordDefinition(spec.name, "datatype", [], properties);
    this.recordAdmission("declareDatatype", { spec: stored });
    return record;
  }

  /**
   * Register the already-defined von Neumann naturals as the datatype used by
   * induction, pattern coverage, and compact execution.
   *
   * This operation adds no proposition.  It accepts only the exact transparent
   * definitions zero=empty, succ(n)=n union {n}, Nat(n)<->n in omega, together
   * with the least-inductive-set law.  The resulting datatype record is
   * computational metadata justified by those set-theoretic declarations.
   */
  registerNaturalDatatype(): void {
    if (this.datatypes.has("Naturals")) throw new KernelError("Naturals datatype is already registered");
    const zero = this.functionBodies.get("zero");
    const successor = this.functionBodies.get("succ");
    const natural = this.definitions.get("Nat")?.properties.get("equation");
    const expectedSuccessor = app("union", app("pair", v("n"), app("pair", v("n"), v("n"))));
    const expectedNatural = forall("n", iff(pred("Nat", v("n")), pred("in", v("n"), app("omega"))));
    const minimality = forall("A", imp(and(
      pred("in", app("empty"), v("A")),
      forall("n", imp(pred("in", v("n"), v("A")), pred("in", expectedSuccessor, v("A")))),
    ), forall("n", imp(pred("in", v("n"), app("omega")), pred("in", v("n"), v("A"))))));
    const installedMinimality = this.axioms.get("set.infinity.minimal");
    if (!zero || zero.parameters.length !== 0 || !termEquals(zero.body, app("empty")) ||
        !successor || successor.parameters.length !== 1 || successor.parameters[0] !== "n" ||
        !termEquals(successor.body, expectedSuccessor) || !natural || !formulaEquals(natural, expectedNatural) ||
        !installedMinimality || !formulaEquals(installedMinimality, minimality)) {
      throw new KernelError("Natural datatype registration requires the canonical von Neumann interface");
    }
    this.datatypes.set("Naturals", {
      name: "Naturals", predicate: "Nat", constructors: [
        { name: "zero", arity: 0, recursiveFields: [] },
        { name: "succ", arity: 1, recursiveFields: [0] },
      ],
    });
    this.recordAdmission("registerNaturalDatatype", {});
  }

  defineStructuralFunction(options: {
    readonly name: string;
    readonly parameters: readonly string[];
    readonly datatype: string;
    readonly decreasingParameter: number;
    readonly equations: readonly RecursiveEquation[];
  }): DefinitionRecord {
    const { name, parameters, datatype, decreasingParameter, equations } = options;
    this.ensureFresh(name);
    this.validateParameters(parameters);
    const data = this.datatypes.get(datatype);
    if (!data) throw new KernelError(`Unknown datatype: ${datatype}`);
    if (!Number.isSafeInteger(decreasingParameter) || decreasingParameter < 0 || decreasingParameter >= parameters.length) {
      throw new KernelError(`Bad decreasing parameter for ${name}`);
    }
    if (equations.length !== data.constructors.length) throw new KernelError(`${name} must have one equation for each ${datatype} constructor`);

    const seenRoots = new Set<string>();
    const properties = new Map<string, Formula>();
    equations.forEach((equation, equationIndex) => {
      if (equation.patterns.length !== parameters.length) throw new KernelError(`Equation ${equationIndex} of ${name} has the wrong arity`);
      equation.patterns.forEach((pattern, index) => {
        if (index !== decreasingParameter && pattern.tag !== "bind") {
          throw new KernelError(`Only the decreasing parameter may be structurally matched in ${name}`);
        }
      });
      const root = equation.patterns[decreasingParameter]!;
      if (root.tag !== "ctor") throw new KernelError(`Equation ${equationIndex} of ${name} must match a ${datatype} constructor`);
      const ctor = data.constructors.find(item => item.name === root.name);
      if (!ctor || root.args.length !== ctor.arity) throw new KernelError(`Bad constructor pattern ${root.name} in ${name}`);
      equation.patterns.forEach(pattern => this.validatePattern(pattern));
      if (seenRoots.has(root.name)) throw new KernelError(`Duplicate ${root.name} equation in ${name}`);
      seenRoots.add(root.name);

      const bindings = this.patternBindings(equation.patterns);
      if (new Set(bindings).size !== bindings.length) throw new KernelError(`Nonlinear pattern in equation ${equationIndex} of ${name}`);
      this.ensureVariablesWithin(freeTermVariables(equation.body), bindings, `Body of ${name} equation ${equationIndex}`);
      this.checkRecursiveBody(
        equation.body,
        name,
        parameters.length,
        decreasingParameter,
        new Set(this.recursiveSubterms(root, ctor)),
      );

      const lhs = app(name, ...equation.patterns.map(pattern => this.patternTerm(pattern)));
      properties.set(`equation.${equationIndex}`, foralls(bindings, eq(lhs, equation.body)));
    });
    if (seenRoots.size !== data.constructors.length) throw new KernelError(`Equations of ${name} are not exhaustive`);

    this.functions.set(name, parameters.length);
    const storedEquations = equations.map(equation => ({ patterns: [...equation.patterns], body: equation.body }));
    deepFreeze(storedEquations);
    this.recursiveFunctions.set(name, {
      name, parameters: [...parameters], datatype, decreasingParameter,
      equations: storedEquations, admission: "structural",
    });
    const record = this.recordDefinition(name, "recursive", parameters, properties);
    this.recordAdmission("defineStructuralFunction", { options: {
      name, parameters: [...parameters], datatype, decreasingParameter, equations: storedEquations,
    } });
    return record;
  }

  /**
   * Admit recursion through a kernel-checked, set-sized well-founded relation.
   * The relation is represented by a set-theoretic graph; `relates`
   * connects that graph to its ordered pairs.
   */
  defineWellFoundedFunction(options: {
    readonly name: string;
    readonly parameters: readonly string[];
    readonly coverageDatatype: string;
    readonly coverageParameter: number;
    readonly equations: readonly RecursiveEquation[];
    readonly relation: Term;
    readonly domain: Term;
    readonly measure: Term;
    readonly wellFounded: Proof;
    readonly measureInDomain: Proof;
    readonly decreases: readonly Proof[];
  }): DefinitionRecord {
    const {
      name, parameters, coverageDatatype, coverageParameter, equations,
      relation, domain, measure, wellFounded, measureInDomain, decreases,
    } = options;
    this.ensureFresh(name);
    this.validateParameters(parameters);
    this.checkTerm(relation);
    this.checkTerm(domain);
    this.ensureVariablesWithin(freeTermVariables(relation), [], `Relation of ${name}`);
    this.ensureVariablesWithin(freeTermVariables(domain), [], `Termination domain of ${name}`);
    this.checkTerm(measure);
    this.ensureVariablesWithin(freeTermVariables(measure), parameters, `Measure of ${name}`);

    const data = this.datatypes.get(coverageDatatype);
    if (!data) throw new KernelError(`Unknown coverage datatype: ${coverageDatatype}`);
    if (!Number.isSafeInteger(coverageParameter) || coverageParameter < 0 || coverageParameter >= parameters.length) {
      throw new KernelError(`Bad coverage parameter for ${name}`);
    }
    if (equations.length !== data.constructors.length) {
      throw new KernelError(`${name} must have one equation for each ${coverageDatatype} constructor`);
    }

    const expectedWellFounded = pred("wellFoundedOn", relation, domain);
    if (!formulaEquals(this.checkProof(wellFounded), expectedWellFounded)) {
      throw new KernelError(`Well-foundedness proof for ${name} has the wrong conclusion`);
    }
    const expectedMeasure = foralls(parameters, pred("in", measure, domain));
    if (!formulaEquals(this.checkProof(measureInDomain), expectedMeasure)) {
      throw new KernelError(`Measure-domain proof for ${name} has the wrong conclusion`);
    }

    const seenRoots = new Set<string>();
    const properties = new Map<string, Formula>();
    const obligations: Formula[] = [];
    equations.forEach((equation, equationIndex) => {
      if (equation.patterns.length !== parameters.length) throw new KernelError(`Equation ${equationIndex} of ${name} has the wrong arity`);
      equation.patterns.forEach((pattern, index) => {
        if (index !== coverageParameter && pattern.tag !== "bind") {
          throw new KernelError(`Only the coverage parameter may be matched in ${name}`);
        }
      });
      const root = equation.patterns[coverageParameter]!;
      if (root.tag !== "ctor") throw new KernelError(`Equation ${equationIndex} of ${name} must match a ${coverageDatatype} constructor`);
      const constructor = data.constructors.find(item => item.name === root.name);
      if (!constructor || root.args.length !== constructor.arity) throw new KernelError(`Bad constructor pattern ${root.name} in ${name}`);
      equation.patterns.forEach(pattern => this.validatePattern(pattern));
      if (seenRoots.has(root.name)) throw new KernelError(`Duplicate ${root.name} equation in ${name}`);
      seenRoots.add(root.name);

      const bindings = this.patternBindings(equation.patterns);
      if (new Set(bindings).size !== bindings.length) throw new KernelError(`Nonlinear pattern in equation ${equationIndex} of ${name}`);
      this.ensureVariablesWithin(freeTermVariables(equation.body), bindings, `Body of ${name} equation ${equationIndex}`);
      const calls = this.collectRecursiveCalls(equation.body, name, parameters.length);
      const currentArguments = equation.patterns.map(pattern => this.patternTerm(pattern));
      const currentSubstitution = new Map(parameters.map((parameter, index) => [parameter, currentArguments[index]!]));
      const currentMeasure = this.substituteMany(measure, currentSubstitution);
      for (const call of calls) {
        const callSubstitution = new Map(parameters.map((parameter, index) => [parameter, call.args[index]!]));
        const nextMeasure = this.substituteMany(measure, callSubstitution);
        obligations.push(foralls(bindings, pred("relates", relation, nextMeasure, currentMeasure)));
      }

      const lhs = app(name, ...currentArguments);
      properties.set(`equation.${equationIndex}`, foralls(bindings, eq(lhs, equation.body)));
    });
    if (seenRoots.size !== data.constructors.length) throw new KernelError(`Equations of ${name} are not exhaustive`);
    if (decreases.length !== obligations.length) {
      throw new KernelError(`${name} has ${obligations.length} recursive calls but ${decreases.length} decrease proofs`);
    }
    obligations.forEach((expected, index) => {
      if (!formulaEquals(this.checkProof(decreases[index]!), expected)) {
        throw new KernelError(`Decrease proof ${index} for ${name} has the wrong conclusion`);
      }
    });

    this.functions.set(name, parameters.length);
    const storedEquations = equations.map(equation => ({ patterns: [...equation.patterns], body: equation.body }));
    deepFreeze(storedEquations);
    this.recursiveFunctions.set(name, {
      name,
      parameters: [...parameters],
      datatype: coverageDatatype,
      decreasingParameter: coverageParameter,
      equations: storedEquations,
      admission: "well-founded",
      termination: { relation, domain, measure },
    });
    properties.set("termination.wellFounded", expectedWellFounded);
    properties.set("termination.measure", expectedMeasure);
    obligations.forEach((obligation, index) => properties.set(`termination.decrease.${index}`, obligation));
    const record = this.recordDefinition(name, "well-founded-recursive", parameters, properties);
    this.recordAdmission("defineWellFoundedFunction", { options: {
      name, parameters: [...parameters], coverageDatatype, coverageParameter, equations: storedEquations,
      relation, domain, measure, wellFounded, measureInDomain, decreases: [...decreases],
    } });
    return record;
  }

  evaluate(term: Term, fuel = 1_000_000): Term {
    return this.evaluateFast(term, fuel);
  }

  /**
   * Execute admitted equations without constructing a proof object at every
   * reduction. This is the ACL2-style runtime path; `evaluateCertified` is the
   * independently checkable logical replay path.
   */
  evaluateFast(term: Term, fuel = 1_000_000): Term {
    return this.evaluateFastWithStats(term, fuel).value;
  }

  evaluateFastWithStats(term: Term, fuel = 1_000_000): { readonly value: Term; readonly stats: EvaluationStats } {
    if (!Number.isSafeInteger(fuel) || fuel < 1) throw new KernelError("Evaluation fuel must be positive");
    const state = { remaining: fuel, calls: 0, reductions: 0, cacheHits: 0, memo: new WeakMap<object, Term>() };
    const value = this.evaluateFastInternal(term, state);
    return { value, stats: { calls: state.calls, reductions: state.reductions, cacheHits: state.cacheHits } };
  }

  evaluateCertified(term: Term, fuel = 10_000): { readonly value: Term; readonly proof: Proof } {
    if (!Number.isSafeInteger(fuel) || fuel < 1) throw new KernelError("Evaluation fuel must be positive");
    return this.evaluateCertifiedWithFuel(term, { remaining: fuel });
  }

  /**
   * Build the compact certificate for a closed definitional equality.
   *
   * This is proof assembly only; checkProof independently replays the computation using only the recorded definition allow-list.
   */
  proveComputation(left: Term, right: Term, fuel = 1_000_000): Proof {
    const result = this.normalizeComputationalEquality(left, right, undefined, fuel);
    if (!nativeValueEquals(result.left, result.right)) {
      throw new KernelError(`Closed terms have different normal forms: ${formatTerm(nativeValueToTerm(result.left))} and ${formatTerm(nativeValueToTerm(result.right))}`);
    }
    return compute(left, right, [...result.used].sort());
  }

  /** Trusted replay entry point shared by the AST and numeric kernel checkers. */
  checkComputationalEquality(
    left: Term,
    right: Term,
    definitions: readonly string[],
    fuel = 1_000_000,
  ): void {
    if (!Array.isArray(definitions)) throw new KernelError("Malformed computation dependency list");
    if (new Set(definitions).size !== definitions.length ||
        definitions.some((name, index) => index > 0 && definitions[index - 1]! >= name)) {
      throw new KernelError("Computation dependencies must be unique and sorted");
    }
    for (const name of definitions) {
      if (!this.functionBodies.has(name) && !this.recursiveFunctions.has(name)) {
        throw new KernelError(`Unknown computational definition: ${name}`);
      }
    }
    const result = this.normalizeComputationalEquality(left, right, new Set(definitions), fuel);
    const used = [...result.used].sort();
    if (used.length !== definitions.length || used.some((name, index) => name !== definitions[index])) {
      throw new KernelError("Computation certificate has an inexact definition dependency list");
    }
    if (!nativeValueEquals(result.left, result.right)) {
      throw new KernelError(`Closed terms have different normal forms: ${formatTerm(nativeValueToTerm(result.left))} and ${formatTerm(nativeValueToTerm(result.right))}`);
    }
  }

  /** Ground quotient equality justified by the already proved rationalClass.eq theorem. */
  checkRationalClassEquality(left: Term, right: Term): void {
    this.checkTerm(left); this.checkTerm(right);
    const className = "Grace.Cumulus.Rat.Operations.rationalClass";
    const theoremName = "Grace.Cumulus.Rat.Operations.rationalClass.eq";
    const addName = "Grace.Core.Nat.Rec.add";
    const mulName = "Grace.Core.Nat.Rec.mul";
    if (!this.datatypes.has("Naturals") || left.tag !== "app" || right.tag !== "app" ||
        left.fn !== className || right.fn !== className || left.args.length !== 3 || right.args.length !== 3 ||
        [...left.args, ...right.args].some(value => naturalValue(value) === undefined) ||
        naturalValue(left.args[2]!) === 0n || naturalValue(right.args[2]!) === 0n) {
      throw new KernelError("Rational computation needs two ground classes with positive denominators");
    }
    const [a, b, m, c, d, n] = ["a", "b", "m", "c", "d", "n"].map(v);
    const mul = (x: Term, y: Term) => app(mulName, x, y);
    const add = (x: Term, y: Term) => app(addName, x, y);
    const cross = (first: readonly Term[], second: readonly Term[]) =>
      eq(add(mul(second[2]!, first[0]!), mul(first[2]!, second[1]!)),
         add(mul(first[2]!, second[0]!), mul(second[2]!, first[1]!)));
    const variables = [a, b, m, c, d, n];
    const conclusion = eq(app(className, a, b, m), app(className, c, d, n));
    const premises = [...variables.map(value => pred("Nat", value)), not(eq(m, nat(0))),
      not(eq(n, nat(0))), cross([a, b, m], [c, d, n])];
    const schema = foralls(["a", "b", "m", "c", "d", "n"],
      premises.reduceRight<Formula>((body, premise) => imp(premise, body), conclusion));
    const theorem = this.theorems.get(theoremName);
    if (!theorem || !formulaEquals(theorem, schema))
      throw new KernelError("Rational computation requires the proved quotient equality criterion");
    const concrete = cross(left.args, right.args);
    if (concrete.tag !== "eq") throw new KernelError("Malformed rational cross-product");
    this.checkComputationalEquality(concrete.left, concrete.right, [addName, mulName]);
  }

  defineSubset(
    name: string,
    parameters: readonly string[],
    element: string,
    bound: Term,
    condition: Formula,
  ): DefinitionRecord {
    if (!this.capabilities.separation) throw new KernelError("The foundation does not enable Separation");
    this.validateParameters(parameters);
    if (parameters.includes(element)) throw new KernelError(`Bound element ${element} also occurs as a parameter`);
    this.ensureFresh(name);
    if (formulaContainsSymbol(condition, name) || this.termContainsFunction(bound, name)) {
      throw new KernelError(`Impredicative self-reference in Separation definition ${name}`);
    }
    this.checkTerm(bound);
    this.checkFormula(condition);
    this.ensureVariablesWithin(freeTermVariables(bound), parameters, `Bound of ${name}`);
    this.ensureVariablesWithin(freeFormulaVariables(condition), [...parameters, element], `Condition of ${name}`);
    this.functions.set(name, parameters.length);
    const member = pred("in", v(element), app(name, ...parameters.map(v)));
    const characterization = foralls([...parameters, element], iff(member, and(pred("in", v(element), bound), condition)));
    const record = this.recordDefinition(name, "separation", parameters, new Map([["membership", characterization]]));
    this.recordAdmission("defineSubset", { name, parameters: [...parameters], element, bound, condition });
    return record;
  }

  reifyUnaryOperation(options: {
    readonly name: string;
    readonly operation: string;
    readonly domain: Term;
    readonly codomain: Term;
    readonly variable: string;
    readonly closure: Proof;
  }): DefinitionRecord {
    if (!this.capabilities.replacement) throw new KernelError("The foundation does not enable Replacement");
    const { name, operation, domain, codomain, variable, closure } = options;
    this.ensureFresh(name);
    if (this.functions.get(operation) !== 1) throw new KernelError(`Operation ${operation} is not a declared unary function`);
    this.checkTerm(domain);
    this.checkTerm(codomain);
    this.ensureVariablesWithin(freeTermVariables(domain), [], `Domain of ${name}`);
    this.ensureVariablesWithin(freeTermVariables(codomain), [], `Codomain of ${name}`);
    const expectedClosure = forall(variable, imp(
      pred("in", v(variable), domain),
      pred("in", app(operation, v(variable)), codomain),
    ));
    const actualClosure = this.checkProof(closure);
    if (!formulaEquals(actualClosure, expectedClosure)) {
      throw new KernelError(`Closure proof for ${name} has the wrong conclusion`);
    }
    this.functions.set(name, 0);
    const graph = app(name);
    const pairVariable = variable === "p" ? "pair_" : "p";
    const membership = forall(pairVariable, iff(
      pred("in", v(pairVariable), graph),
      exists(variable, and(
        pred("in", v(variable), domain),
        eq(v(pairVariable), app("orderedPair", v(variable), app(operation, v(variable)))),
      )),
    ));
    const functionOn = pred("functionOn", graph, domain, codomain);
    const application = forall(variable, imp(
      pred("in", v(variable), domain),
      eq(app("apply", graph, v(variable)), app(operation, v(variable))),
    ));
    const record = this.recordDefinition(name, "replacement", [], new Map([
      ["membership", membership],
      ["functionOn", functionOn],
      ["application", application],
    ]));
    this.recordAdmission("reifyUnaryOperation", { options: {
      name, operation, domain, codomain, variable, closure,
    } });
    return record;
  }

  /**
   * Admit one instance of the Replacement schema.
   *
   * `relation(input, output, parameters...)` must be single-valued on
   * `domain`.  The certificate is explicit because, unlike a
   * definition, this event invokes a set-existence principle.
   */
  defineReplacement(options: {
    readonly name: string;
    readonly parameters: readonly string[];
    readonly domain: Term;
    readonly input: string;
    readonly output: string;
    readonly relation: Formula;
    readonly functionality: Proof;
  }): DefinitionRecord {
    if (!this.capabilities.replacement) throw new KernelError("The foundation does not enable Replacement");
    const { name, parameters, domain, input, output, relation, functionality } = options;
    this.validateParameters(parameters);
    if (input === output || parameters.includes(input) || parameters.includes(output)) {
      throw new KernelError(`Replacement variables for ${name} must be distinct from its parameters`);
    }
    this.ensureFresh(name);
    if (formulaContainsSymbol(relation, name) || this.termContainsFunction(domain, name)) {
      throw new KernelError(`Impredicative self-reference in Replacement definition ${name}`);
    }
    this.checkTerm(domain);
    this.checkFormula(relation);
    this.ensureVariablesWithin(freeTermVariables(domain), parameters, `Domain of ${name}`);
    this.ensureVariablesWithin(freeFormulaVariables(relation), [...parameters, input, output], `Relation of ${name}`);

    const unique = this.freshVariable(`${output}_other`, new Set([...parameters, input, output, ...freeFormulaVariables(relation)]));
    const relationAtUnique = substituteFormula(relation, output, v(unique));
    const expectedFunctionality = foralls(parameters, forall(input, imp(
      pred("in", v(input), domain),
      exists(output, and(
        relation,
        forall(unique, imp(relationAtUnique, eq(v(unique), v(output)))),
      )),
    )));
    const actualFunctionality = this.checkProof(functionality);
    if (!formulaEquals(actualFunctionality, expectedFunctionality)) {
      throw new KernelError(`Functionality proof for ${name} has the wrong conclusion`);
    }

    this.functions.set(name, parameters.length);
    const member = this.freshVariable("member", new Set([...parameters, input, output, ...freeFormulaVariables(relation)]));
    const relationAtMember = substituteFormula(relation, output, v(member));
    const membership = foralls([...parameters, member], iff(
      pred("in", v(member), app(name, ...parameters.map(v))),
      exists(input, and(pred("in", v(input), domain), relationAtMember)),
    ));
    const record = this.recordDefinition(name, "replacement", parameters, new Map([
      ["functionality", expectedFunctionality],
      ["membership", membership],
    ]));
    this.recordAdmission("defineReplacement", { options: {
      name, parameters: [...parameters], domain, input, output, relation, functionality,
    } });
    return record;
  }

  /**
   * Conservative description-by-unique-existence.  The supplied proof must
   * establish existence and uniqueness before the fresh function symbol is
   * installed.  This is the set-theoretic analogue of a definite
   * description; no choice axiom is involved.
   */
  defineUniqueFunction(options: {
    readonly name: string;
    readonly parameters: readonly string[];
    readonly value: string;
    readonly relation: Formula;
    readonly existsUnique: Proof;
  }): DefinitionRecord {
    const { name, parameters, value, relation, existsUnique } = options;
    this.ensureFresh(name);
    this.validateParameters(parameters);
    if (!value || parameters.includes(value)) throw new KernelError(`Bad unique value variable for ${name}`);
    this.ensureVariablesWithin(freeFormulaVariables(relation), [...parameters, value], `Unique relation of ${name}`);
    const other = this.freshVariable(`${value}_other`, new Set([...parameters, value, ...freeFormulaVariables(relation)]));
    const otherRelation = substituteFormula(relation, value, v(other));
    const expected = foralls(parameters, exists(value, and(
      relation,
      forall(other, imp(otherRelation, eq(v(other), v(value)))),
    )));
    if (!formulaEquals(this.checkProof(existsUnique), expected)) {
      throw new KernelError(`Unique-existence proof for ${name} has the wrong conclusion`);
    }
    this.functions.set(name, parameters.length);
    const characterization = foralls(parameters,
      substituteFormula(relation, value, app(name, ...parameters.map(v))));
    const record = this.recordDefinition(name, "unique-choice", parameters, new Map([
      ["existsUnique", expected],
      ["characterization", characterization],
    ]));
    this.recordAdmission("defineUniqueFunction", { options: {
      name, parameters: [...parameters], value, relation, existsUnique,
    } });
    return record;
  }

  /**
   * Replacement-backed recursion over an arbitrary formula-defined,
   * set-well-founded relation.  This event is non-executable:
   * it constructs a unique set graph and a value function, but installs no
   * evaluator body.  Its schema is a theorem of ZF Foundation + Replacement.
   */
  defineWellFoundedSetFunction(options: {
    readonly name: string;
    readonly parameters: readonly string[];
    readonly variable: string;
    readonly predecessor: string;
    readonly history: string;
    readonly successorIndex?: string;
    readonly ordinalCondition?: Formula;
    readonly limitCondition?: Formula;
    readonly domain: Term;
    readonly precedes: Formula;
    readonly step: Term;
    readonly wellFounded: Proof;
  }): DefinitionRecord {
    const { name, parameters, variable, predecessor, history, domain, precedes, step, wellFounded } = options;
    if (!this.capabilities.separation || !this.capabilities.replacement ||
        (this.capabilities.setTheory ?? "none") === "none" || !this.axioms.has("set.foundation")) {
      throw new KernelError("Set recursion requires Separation, Replacement, and Foundation");
    }
    this.ensureFresh(name);
    const solutionName = `${name}.Solution`;
    this.ensureFresh(solutionName);
    const historyName = `${name}.history`;
    this.ensureFresh(historyName);
    this.validateParameters(parameters);
    if (!variable || !predecessor || !history || new Set([...parameters, variable, predecessor, history]).size !== parameters.length + 3) {
      throw new KernelError(`Recursion variables for ${name} must be distinct`);
    }
    this.checkTerm(domain);
    this.ensureVariablesWithin(freeTermVariables(domain), parameters, `Recursion domain of ${name}`);
    this.ensureVariablesWithin(freeFormulaVariables(precedes), [...parameters, predecessor, variable], `Predecessor relation of ${name}`);
    this.checkTerm(step);
    this.ensureVariablesWithin(freeTermVariables(step), [...parameters, variable, history], `Recursion step of ${name}`);

    const forbidden = new Set([...parameters, variable, predecessor, history,
      ...freeTermVariables(domain), ...freeFormulaVariables(precedes), ...freeTermVariables(step)]);
    const subset = this.freshVariable("subset", forbidden); forbidden.add(subset);
    const minimum = this.freshVariable("minimum", forbidden); forbidden.add(minimum);
    const member = this.freshVariable("member", forbidden); forbidden.add(member);
    const graph = this.freshVariable("graph", forbidden); forbidden.add(graph);
    const otherGraph = this.freshVariable("otherGraph", forbidden); forbidden.add(otherGraph);
    const output = this.freshVariable("output", forbidden); forbidden.add(output);
    const otherOutput = this.freshVariable("otherOutput", forbidden); forbidden.add(otherOutput);

    const atRelation = (earlier: Term, later: Term): Formula =>
      substituteFormula(substituteFormula(precedes, predecessor, earlier), variable, later);
    const domainSubset = forall(member, imp(pred("in", v(member), v(subset)), pred("in", v(member), domain)));
    const minimal = exists(minimum, and(
      pred("in", v(minimum), v(subset)),
      forall(predecessor, imp(atRelation(v(predecessor), v(minimum)), not(pred("in", v(predecessor), v(subset))))),
    ));
    const expectedWellFounded = foralls(parameters, forall(subset, imp(
      domainSubset, imp(not(eq(v(subset), app("empty"))), minimal),
    )));
    if (!formulaEquals(this.checkProof(wellFounded), expectedWellFounded)) {
      throw new KernelError(`Set-well-foundedness proof for ${name} has the wrong conclusion`);
    }

    const historyFormula = (graphTerm: Term, point: Term, historyTerm: Term): Formula => {
      const pairValue = this.freshVariable("pairValue", forbidden);
      const earlier = this.freshVariable("earlier", new Set([...forbidden, pairValue]));
      const earlierValue = this.freshVariable("earlierValue", new Set([...forbidden, pairValue, earlier]));
      const priorPair = exists(earlier, exists(earlierValue, and(
        pred("in", v(earlier), domain),
        and(atRelation(v(earlier), point), eq(v(pairValue), app("orderedPair", v(earlier), v(earlierValue)))),
      )));
      return forall(pairValue, iff(
        pred("in", v(pairValue), historyTerm),
        and(pred("in", v(pairValue), graphTerm), priorPair),
      ));
    };
    const graphShape = and(
      forall(member, imp(pred("in", v(member), v(graph)), exists(variable, exists(output, and(
        pred("in", v(variable), domain), eq(v(member), app("orderedPair", v(variable), v(output))),
      ))))),
      and(
        forall(variable, imp(pred("in", v(variable), domain), exists(output,
          pred("in", app("orderedPair", v(variable), v(output)), v(graph))))),
        forall(variable, imp(pred("in", v(variable), domain), forall(output, forall(otherOutput, imp(and(
          pred("in", app("orderedPair", v(variable), v(output)), v(graph)),
          pred("in", app("orderedPair", v(variable), v(otherOutput)), v(graph)),
        ), eq(v(output), v(otherOutput))))))),
      ),
    );
    const instantiatedStep = this.substituteMany(step, new Map([
      [variable, v(variable)], [history, v(history)],
    ]));
    const solutionBody = and(graphShape, forall(variable, imp(pred("in", v(variable), domain),
      exists(history, exists(output, and(
        historyFormula(v(graph), v(variable), v(history)),
        and(pred("in", app("orderedPair", v(variable), v(output)), v(graph)), eq(v(output), instantiatedStep)),
      ))))));

    this.predicates.set(solutionName, parameters.length + 1);
    const solutionEquation = foralls([...parameters, graph], iff(
      pred(solutionName, ...parameters.map(v), v(graph)), solutionBody,
    ));
    this.recordDefinition(solutionName, "predicate", [...parameters, graph], new Map([["equation", solutionEquation]]));

    const solutionAt = (graphTerm: Term): Formula => pred(solutionName, ...parameters.map(v), graphTerm);
    const existenceUnique = foralls(parameters, exists(graph, and(
      solutionAt(v(graph)), forall(otherGraph, imp(solutionAt(v(otherGraph)), eq(v(otherGraph), v(graph)))),
    )));
    this.functions.set(name, parameters.length + 1);
    this.functions.set(historyName, parameters.length + 1);
    const valueTerm = app(name, ...parameters.map(v), v(variable));
    const historyTerm = app(historyName, ...parameters.map(v), v(variable));
    const valueAtPredecessor = app(name, ...parameters.map(v), v(predecessor));
    const historyMember = this.freshVariable("historyMember", forbidden);
    const historyMembership = foralls([...parameters, variable, historyMember], iff(
      pred("in", v(historyMember), historyTerm),
      exists(predecessor, and(pred("in", v(predecessor), domain), and(
        atRelation(v(predecessor), v(variable)),
        eq(v(historyMember), app("orderedPair", v(predecessor), valueAtPredecessor)),
      ))),
    ));
    const valueProperty = foralls([...parameters, variable], imp(pred("in", v(variable), domain), exists(graph, and(
      solutionAt(v(graph)), pred("in", app("orderedPair", v(variable), valueTerm), v(graph)),
    ))));
    const equationProperty = foralls([...parameters, variable], imp(pred("in", v(variable), domain),
      exists(graph, exists(history, and(solutionAt(v(graph)), and(
        historyFormula(v(graph), v(variable), v(history)),
        eq(valueTerm, instantiatedStep),
      ))))));
    const directStep = this.substituteMany(step, new Map([
      [variable, v(variable)], [history, historyTerm],
    ]));
    const directEquation = foralls([...parameters, variable], imp(
      pred("in", v(variable), domain), eq(valueTerm, directStep),
    ));
    const outsideProperty = foralls([...parameters, variable], imp(
      not(pred("in", v(variable), domain)), eq(valueTerm, app("empty")),
    ));
    const record = this.recordDefinition(name, "well-founded-set-recursive", [...parameters, variable], new Map([
      ["wellFounded", expectedWellFounded],
      ["solution.existsUnique", existenceUnique],
      ["history.membership", historyMembership],
      ["value", valueProperty],
      ["equation", equationProperty],
      ["equation.direct", directEquation],
      ["outside", outsideProperty],
    ]));
    this.recordAdmission("defineWellFoundedSetFunction", { options: {
      name, parameters: [...parameters], variable, predecessor, history,
      ...(options.successorIndex ? { successorIndex: options.successorIndex } : {}),
      ...(options.ordinalCondition ? { ordinalCondition: options.ordinalCondition } : {}),
      ...(options.limitCondition ? { limitCondition: options.limitCondition } : {}),
      domain, precedes, step, wellFounded,
    } });
    return record;
  }

  /**
   * Class-wide recursion along set membership. Foundation makes membership
   * well-founded, and Replacement makes the graph of earlier values over the
   * member set of each input a set. The event is non-executable and
   * exposes only its history characterization and defining equation.
   */
  defineMembershipRecursiveFunction(options: {
    readonly name: string;
    readonly parameters: readonly string[];
    readonly variable: string;
    readonly predecessor: string;
    readonly history: string;
    readonly step: Term;
  }): DefinitionRecord {
    const { name, parameters, variable, predecessor, history, step } = options;
    if (!this.capabilities.separation || !this.capabilities.replacement ||
        (this.capabilities.setTheory ?? "none") === "none" || !this.axioms.has("set.foundation")) {
      throw new KernelError("Membership recursion requires Separation, Replacement, and Foundation");
    }
    this.ensureFresh(name);
    const historyName = `${name}.history`;
    this.ensureFresh(historyName);
    this.validateParameters(parameters);
    if (!variable || !predecessor || !history ||
        new Set([...parameters, variable, predecessor, history]).size !== parameters.length + 3) {
      throw new KernelError(`Membership-recursion variables for ${name} must be distinct`);
    }
    this.checkTerm(step);
    this.ensureVariablesWithin(freeTermVariables(step), [...parameters, variable, history],
      `Membership-recursion step of ${name}`);

    const arity = parameters.length + 1;
    this.functions.set(name, arity);
    this.functions.set(historyName, arity);
    const pair = this.freshVariable("pair", new Set([...parameters, variable, predecessor, history]));
    const historyTerm = app(historyName, ...parameters.map(v), v(variable));
    const valueAtPredecessor = app(name, ...parameters.map(v), v(predecessor));
    const historyMembership = foralls([...parameters, variable, pair], iff(
      pred("in", v(pair), historyTerm),
      exists(predecessor, and(pred("in", v(predecessor), v(variable)),
        eq(v(pair), app("orderedPair", v(predecessor), valueAtPredecessor)))),
    ));
    const value = app(name, ...parameters.map(v), v(variable));
    const instantiatedStep = this.substituteMany(step, new Map([[history, historyTerm]]));
    const equation = foralls([...parameters, variable], eq(value, instantiatedStep));
    const record = this.recordDefinition(name, "membership-recursive", [...parameters, variable], new Map([
      ["history.membership", historyMembership],
      ["equation", equation],
    ]));
    this.recordAdmission("defineMembershipRecursiveFunction", { options: {
      name, parameters: [...parameters], variable, predecessor, history, step,
    } });
    return record;
  }

  /**
   * Class-sized recursion through the von Neumann ordinals.  ZF proves that
   * the three supplied (functional) clauses determine one value at every
   * ordinal.  The accompanying history is the Replacement set of all earlier
   * index/value pairs.  No evaluator equation is installed: this event is a
   * conservative, noncomputable definitional extension.
   */
  defineTransfiniteFunction(options: {
    readonly name: string;
    readonly parameters: readonly string[];
    readonly ordinal: string;
    readonly predecessor: string;
    readonly history: string;
    readonly successorIndex?: string;
    readonly ordinalCondition?: Formula;
    readonly limitCondition?: Formula;
    readonly zero: Term;
    readonly successor: Term;
    readonly limit: Term;
  }): DefinitionRecord {
    const {
      name, parameters, ordinal, predecessor, history, successorIndex,
      ordinalCondition, limitCondition, zero, successor, limit,
    } = options;
    if (!this.capabilities.separation || !this.capabilities.replacement ||
        (this.capabilities.setTheory ?? "none") === "none" || !this.axioms.has("set.foundation")) {
      throw new KernelError("Transfinite recursion requires Separation, Replacement, and Foundation");
    }
    this.ensureFresh(name);
    const historyName = `${name}.history`;
    this.ensureFresh(historyName);
    this.validateParameters(parameters);
    if (!ordinal || !predecessor || !history ||
        new Set([...parameters, ordinal, predecessor, history]).size !== parameters.length + 3) {
      throw new KernelError(`Transfinite recursion variables for ${name} must be distinct`);
    }

    const arity = parameters.length + 1;
    // Permit recursive calls while checking the clause terms, then retain the
    // symbol only after every syntactic guard has succeeded.
    this.functions.set(name, arity);
    try {
      this.checkTerm(zero);
      this.checkTerm(successor);
      this.checkTerm(limit);
      this.ensureVariablesWithin(freeTermVariables(zero), parameters, `Zero clause of ${name}`);
      this.ensureVariablesWithin(freeTermVariables(successor), [...parameters, predecessor], `Successor clause of ${name}`);
      this.ensureVariablesWithin(freeTermVariables(limit), [...parameters, ordinal, history], `Limit clause of ${name}`);
      if (this.collectRecursiveCalls(zero, name, arity).length !== 0 ||
          this.collectRecursiveCalls(limit, name, arity).length !== 0) {
        throw new KernelError(`${name} may recur only in its successor clause; limit clauses use their earlier-value history`);
      }
      for (const call of this.collectRecursiveCalls(successor, name, arity)) {
        const expected = [...parameters.map(v), v(predecessor)];
        if (call.args.length !== expected.length || call.args.some((argument, index) => !termEquals(argument, expected[index]!))) {
          throw new KernelError(`Successor recursion in ${name} must call the immediately preceding ordinal`);
        }
      }
    } catch (error) {
      this.functions.delete(name);
      throw error;
    }

    if (successorIndex) {
      if (this.functions.get(successorIndex) !== 1) throw new KernelError(`Bad ordinal successor function for ${name}`);
      const probe = v(this.freshVariable("ordinalProbe", new Set([...parameters, ordinal, predecessor, history])));
      const actual = this.evaluateFast(app(successorIndex, probe));
      const expected = this.evaluateFast(app("union2", probe, app("singleton", probe)));
      if (!termEquals(actual, expected)) throw new KernelError(`Ordinal successor for ${name} is not definitionally α ∪ {α}`);
    }
    const next = (term: Term): Term => successorIndex
      ? app(successorIndex, term)
      : app("union2", term, app("singleton", term));
    const canonicalOrdinal = vonNeumannOrdinal(v(ordinal));
    const canonicalLimit = vonNeumannLimit(v(ordinal), next);
    if (ordinalCondition) {
      this.ensureVariablesWithin(freeFormulaVariables(ordinalCondition), [ordinal], `Ordinal interface of ${name}`);
      if (!formulaEquals(this.expandDefinitions(ordinalCondition), this.expandDefinitions(canonicalOrdinal))) {
        throw new KernelError(`Ordinal interface for ${name} is not definitionally the von Neumann ordinals`);
      }
    }
    if (limitCondition) {
      this.ensureVariablesWithin(freeFormulaVariables(limitCondition), [ordinal], `Limit interface of ${name}`);
      if (!formulaEquals(this.expandDefinitions(limitCondition), this.expandDefinitions(canonicalLimit))) {
        throw new KernelError(`Limit interface for ${name} is not definitionally the standard limit-ordinal predicate`);
      }
    }
    const ordinalFormula = (term: Term): Formula => ordinalCondition
      ? substituteFormula(ordinalCondition, ordinal, term)
      : vonNeumannOrdinal(term);
    const limitFormula = (term: Term): Formula => limitCondition
      ? substituteFormula(limitCondition, ordinal, term)
      : vonNeumannLimit(term, next);

    this.functions.set(historyName, parameters.length + 1);
    const pair = this.freshVariable("pair", new Set([...parameters, ordinal, predecessor, history]));
    const earlier = this.freshVariable("earlier", new Set([...parameters, ordinal, predecessor, history, pair]));
    const historyTerm = app(historyName, ...parameters.map(v), v(ordinal));
    const valueAtEarlier = app(name, ...parameters.map(v), v(earlier));
    const historyMembership = foralls([...parameters, ordinal, pair], iff(
      pred("in", v(pair), historyTerm),
      exists(earlier, and(pred("in", v(earlier), v(ordinal)),
        eq(v(pair), app("orderedPair", v(earlier), valueAtEarlier)))),
    ));

    const value = (index: Term): Term => app(name, ...parameters.map(v), index);
    const zeroEquation = foralls(parameters, eq(value(nat(0)), zero));
    const successorEquation = foralls([...parameters, predecessor], imp(
      ordinalFormula(v(predecessor)), eq(value(next(v(predecessor))), successor),
    ));
    const instantiatedLimit = this.substituteMany(limit, new Map([[history, historyTerm]]));
    const limitEquation = foralls([...parameters, ordinal], imp(
      limitFormula(v(ordinal)), eq(value(v(ordinal)), instantiatedLimit),
    ));
    const outsideEquation = foralls([...parameters, ordinal], imp(
      not(ordinalFormula(v(ordinal))), eq(value(v(ordinal)), app("empty")),
    ));
    const record = this.recordDefinition(name, "transfinite-recursive", [...parameters, ordinal], new Map([
      ["history.membership", historyMembership],
      ["equation.zero", zeroEquation],
      ["equation.successor", successorEquation],
      ["equation.limit", limitEquation],
      ["outside", outsideEquation],
    ]));
    this.recordAdmission("defineTransfiniteFunction", { options: {
      name, parameters: [...parameters], ordinal, predecessor, history,
      ...(successorIndex ? { successorIndex } : {}),
      ...(ordinalCondition ? { ordinalCondition } : {}),
      ...(limitCondition ? { limitCondition } : {}),
      zero, successor, limit,
    } });
    return record;
  }

  checkProof(proof: Proof, assumptions: readonly Formula[] = closedAssumptions): Formula {
    if (assumptions.length === 0) {
      const previous = this.closedProofCache.get(proof);
      if (previous && Object.isFrozen(proof)) return previous;
      const checked = this.checkProofCached(proof, closedAssumptions, this.contextualProofCache);
      deepFreeze(proof);
      this.closedProofCache.set(proof, checked);
      return checked;
    }
    const assumptionIdentity = assumptions as object;
    const snapshot = this.contextualAssumptionSnapshots.get(assumptionIdentity);
    const changed = snapshot && (snapshot.length !== assumptions.length ||
      snapshot.some((formula, index) => formula !== assumptions[index]));
    if (changed) {
      // Public callers may reuse a mutable array.  Surface contexts are
      // immutable, so this uncommon defensive path can cheaply discard the
      // whole open cache rather than burden every proof node with a snapshot.
      this.contextualProofCache = emptyProofCache();
      this.contextualAssumptionSnapshots = new WeakMap();
    }
    if (!snapshot || changed) {
      const replacement = [...assumptions];
      // The caller may replace array entries, but retained formula identities
      // must be deeply immutable before they can identify a cached context.
      deepFreeze(replacement);
      this.contextualAssumptionSnapshots.set(assumptionIdentity, replacement);
    }
    const checked = this.checkProofCached(proof, assumptions, this.contextualProofCache);
    deepFreeze(proof);
    return checked;
  }

  /** A deterministic, agent-friendly account of the environment's strength. */
  foundationReport(): FoundationReport {
    const instances = (kind: DefinitionKind): string[] => [...this.definitions.values()]
      .filter(item => item.kind === kind).map(item => item.name).sort();
    return {
      profile: this.capabilities.setTheory ?? "none",
      axioms: [...this.axioms.keys()].sort(),
      schemaInstances: {
        separation: instances("separation"),
        replacement: instances("replacement"),
        uniqueChoice: instances("unique-choice"),
        datatype: [...this.datatypes.keys()].sort(),
        wellFoundedRecursion: instances("well-founded-set-recursive"),
        membershipRecursion: instances("membership-recursive"),
        transfiniteRecursion: instances("transfinite-recursive"),
      },
    };
  }

  checkProofWithStats(proof: Proof, assumptions: readonly Formula[] = []): {
    readonly formula: Formula;
    readonly stats: ProofCheckStats;
  } {
    const stats: ProofCheckStats = { nodesVisited: 0, cacheHits: 0 };
    const formula = this.checkProofCached(proof, assumptions, emptyProofCache(), stats);
    return { formula, stats };
  }

  private checkProofCached(
    proof: Proof,
    assumptions: readonly Formula[],
    cache: ProofCache | undefined,
    stats?: ProofCheckStats,
  ): Formula {
    if (!cache) return this.checkProofNode(proof, assumptions, undefined, stats);
    let context = cache.contextTokens.get(assumptions as object);
    if (!context) {
      // Sorted distinct ids of the assumptions, by insertion into a small array.
      const ids: number[] = [];
      for (const assumption of assumptions) {
        let id = cache.formulaIdsByObject.get(assumption);
        if (id === undefined) {
          const text = formulaCanonical(assumption);
          id = cache.formulaIds.get(text);
          if (id === undefined) { id = cache.formulaIds.size; cache.formulaIds.set(text, id); }
          cache.formulaIdsByObject.set(assumption, id);
        }
        let position = ids.length;
        while (position > 0 && ids[position - 1]! > id) position -= 1;
        if (position > 0 && ids[position - 1] === id) continue;
        ids.splice(position, 0, id);
      }
      let node = cache.contextTrie;
      for (const id of ids) {
        let next = node.children.get(id);
        if (!next) { next = { children: new Map() }; node.children.set(id, next); }
        node = next;
      }
      context = node.token ??= {};
      cache.contextTokens.set(assumptions as object, context);
    }
    const carried = CheckedProofNode.of(proof);
    const previous = carried?.token === cache.token ? carried : cache.results.get(proof);
    const cached = previous?.context === context ? previous.formula : previous?.others?.get(context);
    if (cached) {
      if (stats) stats.cacheHits += 1;
      return cached;
    }
    if (stats) stats.nodesVisited += 1;
    const result = this.checkProofNode(proof, assumptions, cache, stats);
    // A later parent may fail. Every retained child must already be immutable.
    deepFreeze(proof);
    deepFreeze(result);
    // Most nodes occur in one assumption context. Allocate the secondary
    // context map only when this same proof node is checked in another one.
    // Context identity and all validation/invalidation rules are unchanged.
    if (previous) {
      previous.others ??= new WeakMap<object, Formula>();
      previous.others.set(context, result);
    } else {
      const created: CachedCheck = { token: cache.token, context, formula: result };
      // A node that carries another cache's result keeps it; this one goes to the table.
      if (carried !== undefined || !CheckedProofNode.install(proof, created)) cache.results.set(proof, created);
    }
    return result;
  }

  private checkProofNode(
    proof: Proof,
    assumptions: readonly Formula[],
    cache: ProofCache | undefined,
    stats?: ProofCheckStats,
  ): Formula {
    switch (proof.rule) {
      case "assumption":
        this.checkFormula(proof.formula);
        if (cache) {
          const context = cache.contextTokens.get(assumptions as object)!;
          let active = cache.activeAssumptions.get(context);
          if (!active) {
            active = new Set(assumptions.map(formulaCanonical));
            cache.activeAssumptions.set(context, active);
          }
          if (!active.has(formulaCanonical(proof.formula))) throw new KernelError("Formula is not an active assumption");
        } else if (!assumptions.some(item => formulaEquals(item, proof.formula))) {
          throw new KernelError("Formula is not an active assumption");
        }
        return proof.formula;
      case "axiom": {
        const result = this.axioms.get(proof.name);
        if (!result) throw new KernelError(`Unknown axiom: ${proof.name}`);
        return result;
      }
      case "theorem": {
        const result = this.theorems.get(proof.name);
        if (!result) throw new KernelError(`Unknown theorem: ${proof.name}`);
        return result;
      }
      case "definition": {
        const record = this.definitions.get(proof.name);
        const property = proof.property ?? "equation";
        const result = record?.properties.get(property);
        if (!result) throw new KernelError(`Unknown definition property: ${proof.name}.${property}`);
        return result;
      }
      case "refl":
        this.checkTerm(proof.term);
        return eq(proof.term, proof.term);
      case "compute":
        this.checkComputationalEquality(proof.left, proof.right, proof.definitions);
        return eq(proof.left, proof.right);
      case "rationalClassCompute":
        this.checkRationalClassEquality(proof.left, proof.right);
        return eq(proof.left, proof.right);
      case "symm": {
        const result = this.expectEquality(this.checkProofCached(proof.proof, assumptions, cache, stats));
        return eq(result.right, result.left);
      }
      case "trans": {
        const left = this.expectEquality(this.checkProofCached(proof.left, assumptions, cache, stats));
        const right = this.expectEquality(this.checkProofCached(proof.right, assumptions, cache, stats));
        if (!this.termEquals(left.right, right.left)) throw new KernelError("Equality transitivity has mismatched middle terms");
        return eq(left.left, right.right);
      }
      case "congr": {
        const arity = this.functions.get(proof.fn);
        if (arity === undefined || arity !== proof.proofs.length) throw new KernelError(`Bad congruence arity for ${proof.fn}`);
        const equalities = proof.proofs.map(item => this.expectEquality(this.checkProofCached(item, assumptions, cache, stats)));
        return eq(app(proof.fn, ...equalities.map(item => item.left)), app(proof.fn, ...equalities.map(item => item.right)));
      }
      case "eqElim": {
        const equality = this.expectEquality(this.checkProofCached(proof.equality, assumptions, cache, stats));
        const source = proof.reverse ? equality.right : equality.left;
        const target = proof.reverse ? equality.left : equality.right;
        const expectedEvidence = substituteFormula(proof.motive, proof.variable, source);
        const evidence = this.checkProofCached(proof.evidence, assumptions, cache, stats);
        if (!formulaEquals(evidence, expectedEvidence)) throw new KernelError("Equality elimination evidence does not match its motive");
        return substituteFormula(proof.motive, proof.variable, target);
      }
      case "impIntro": {
        // A theorem with many requirements is a long chain of nested
        // introductions. Walk the chain in a loop so its depth costs no
        // stack; each assumption is still checked and discharged in order.
        const discharged: Formula[] = [];
        let body: Proof = proof;
        while (body.rule === "impIntro") {
          this.checkFormula(body.assumption);
          discharged.push(body.assumption);
          body = body.body;
        }
        let result = this.checkProofCached(body, [...assumptions, ...discharged], cache, stats);
        for (let index = discharged.length - 1; index >= 0; index -= 1) result = imp(discharged[index]!, result);
        return result;
      }
      case "impElim": {
        const implication = this.checkProofCached(proof.implication, assumptions, cache, stats);
        if (implication.tag !== "imp") throw new KernelError("Implication elimination requires an implication");
        const argument = this.checkProofCached(proof.argument, assumptions, cache, stats);
        if (!formulaEquals(argument, implication.left)) throw new KernelError("Implication elimination argument mismatch");
        return implication.right;
      }
      case "forallIntro": {
        if (assumptions.some(item => freeFormulaVariables(item).has(proof.variable))) {
          throw new KernelError(`Cannot generalize ${proof.variable}: it is free in an assumption`);
        }
        return forall(proof.variable, this.checkProofCached(proof.body, assumptions, cache, stats));
      }
      case "forallElim": {
        this.checkTerm(proof.term);
        const universal = this.checkProofCached(proof.universal, assumptions, cache, stats);
        if (universal.tag !== "forall") throw new KernelError("Universal elimination requires a universal formula");
        return substituteFormula(universal.body, universal.variable, proof.term);
      }
      case "andIntro":
        return and(
          this.checkProofCached(proof.left, assumptions, cache, stats),
          this.checkProofCached(proof.right, assumptions, cache, stats),
        );
      case "andElimLeft": {
        const conjunction = this.checkProofCached(proof.conjunction, assumptions, cache, stats);
        if (conjunction.tag !== "and") throw new KernelError("Conjunction elimination requires a conjunction");
        return conjunction.left;
      }
      case "andElimRight": {
        const conjunction = this.checkProofCached(proof.conjunction, assumptions, cache, stats);
        if (conjunction.tag !== "and") throw new KernelError("Conjunction elimination requires a conjunction");
        return conjunction.right;
      }
      case "orIntroLeft": {
        this.checkFormula(proof.right);
        return or(this.checkProofCached(proof.proof, assumptions, cache, stats), proof.right);
      }
      case "orIntroRight": {
        this.checkFormula(proof.left);
        return or(proof.left, this.checkProofCached(proof.proof, assumptions, cache, stats));
      }
      case "orElim": {
        const disjunction = this.checkProofCached(proof.disjunction, assumptions, cache, stats);
        if (disjunction.tag !== "or") throw new KernelError("Disjunction elimination requires a disjunction");
        const left = this.checkProofCached(proof.left, [...assumptions, disjunction.left], cache, stats);
        const right = this.checkProofCached(proof.right, [...assumptions, disjunction.right], cache, stats);
        if (!formulaEquals(left, right)) throw new KernelError("Disjunction branches prove different formulas");
        return left;
      }
      case "iffIntro": {
        const forward = this.checkProofCached(proof.forward, assumptions, cache, stats);
        const backward = this.checkProofCached(proof.backward, assumptions, cache, stats);
        if (forward.tag !== "imp" || backward.tag !== "imp" ||
            !formulaEquals(forward.left, backward.right) || !formulaEquals(forward.right, backward.left)) {
          throw new KernelError("Equivalence introduction requires proofs in both directions");
        }
        return iff(forward.left, forward.right);
      }
      case "iffElimLeft": {
        const equivalence = this.checkProofCached(proof.equivalence, assumptions, cache, stats);
        if (equivalence.tag !== "iff") throw new KernelError("Equivalence elimination requires an equivalence");
        return imp(equivalence.left, equivalence.right);
      }
      case "iffElimRight": {
        const equivalence = this.checkProofCached(proof.equivalence, assumptions, cache, stats);
        if (equivalence.tag !== "iff") throw new KernelError("Equivalence elimination requires an equivalence");
        return imp(equivalence.right, equivalence.left);
      }
      case "existsIntro": {
        this.checkTerm(proof.witness);
        this.checkFormula(proof.body);
        const evidence = this.checkProofCached(proof.evidence, assumptions, cache, stats);
        const expected = substituteFormula(proof.body, proof.variable, proof.witness);
        if (!formulaEquals(evidence, expected)) throw new KernelError("Existential witness proves the wrong instance");
        return exists(proof.variable, proof.body);
      }
      case "existsElim": {
        if (!proof.witness) throw new KernelError("Existential elimination needs a witness variable");
        const existential = this.checkProofCached(proof.existential, assumptions, cache, stats);
        if (existential.tag !== "exists") throw new KernelError("Existential elimination requires an existential");
        if (freeFormulaVariables(existential).has(proof.witness) ||
            assumptions.some(item => freeFormulaVariables(item).has(proof.witness))) {
          throw new KernelError("Existential witness is free in an outer assumption");
        }
        const instance = substituteFormula(existential.body, existential.variable, v(proof.witness));
        const result = this.checkProofCached(proof.body, [...assumptions, instance], cache, stats);
        if (freeFormulaVariables(result).has(proof.witness)) throw new KernelError("Existential witness escapes its branch");
        return result;
      }
      case "falseElim": {
        this.checkFormula(proof.conclusion);
        const absurdity = this.checkProofCached(proof.absurdity, assumptions, cache, stats);
        if (absurdity.tag !== "bottom") throw new KernelError("False elimination requires falsity");
        return proof.conclusion;
      }
      case "dne": {
        this.checkFormula(proof.proposition);
        const actual = this.checkProofCached(proof.proof, assumptions, cache, stats);
        const expected = not(not(proof.proposition));
        if (!formulaEquals(actual, expected)) throw new KernelError("Classical elimination requires a proof of double negation");
        return proof.proposition;
      }
      case "induction": {
        const datatype = this.datatypes.get(proof.datatype);
        if (!datatype) throw new KernelError(`Unknown induction datatype: ${proof.datatype}`);
        const datatypeParameters = datatype.parameters ?? [];
        if (proof.parameters.length !== datatypeParameters.length) {
          throw new KernelError(`Induction on ${proof.datatype} expects ${datatypeParameters.length} datatype parameters`);
        }
        if (!proof.variable) throw new KernelError("Induction needs a nonempty variable");
        proof.parameters.forEach(parameter => this.checkTerm(parameter));
        if (proof.parameters.some(parameter => freeTermVariables(parameter).has(proof.variable))) {
          throw new KernelError(`Induction variable ${proof.variable} occurs in a datatype parameter`);
        }
        if (freeFormulaVariables(proof.motive).has(proof.variable) === false) {
          // Constant motives are valid, but retaining this branch documents
          // that the distinguished variable is permitted.
        }
        if (assumptions.some(item => freeFormulaVariables(item).has(proof.variable))) {
          throw new KernelError(`Cannot induct on ${proof.variable}: it is free in an outer assumption`);
        }
        if (proof.cases.length !== datatype.constructors.length) throw new KernelError(`Induction on ${proof.datatype} needs one case per constructor`);
        const cases = new Map(proof.cases.map(item => [item.constructor, item]));
        if (cases.size !== proof.cases.length) throw new KernelError("Duplicate induction case");
        const fixedVariables = new Set<string>([proof.variable, ...freeFormulaVariables(proof.motive)]);
        proof.parameters.forEach(parameter => freeTermVariables(parameter, fixedVariables));
        for (const ctor of datatype.constructors) {
          const branch = cases.get(ctor.name);
          if (!branch) throw new KernelError(`Missing induction case: ${ctor.name}`);
          if (branch.fields.length !== ctor.arity || new Set(branch.fields).size !== branch.fields.length) {
            throw new KernelError(`Bad fields for induction case ${ctor.name}`);
          }
          if (branch.fields.some(name => !name || fixedVariables.has(name) ||
              assumptions.some(item => freeFormulaVariables(item).has(name)))) {
            throw new KernelError(`Induction fields for ${ctor.name} must be fresh from the context, parameters, and motive`);
          }
          const branchAssumptions: Formula[] = [...assumptions];
          for (let index = 0; index < ctor.arity; index += 1) {
            const field = v(branch.fields[index]!);
            if (ctor.recursiveFields.includes(index)) {
              branchAssumptions.push(pred(datatype.predicate, ...proof.parameters, field));
              branchAssumptions.push(substituteFormula(proof.motive, proof.variable, field));
            } else {
              const parameterField = ctor.parameterFields?.find(item => item.field === index);
              if (parameterField) branchAssumptions.push(pred("in", field, proof.parameters[parameterField.parameter]!));
            }
          }
          const actual = this.checkProofCached(branch.proof, branchAssumptions, cache, stats);
          const constructorTerm = app(ctor.name, ...branch.fields.map(v));
          const expected = substituteFormula(proof.motive, proof.variable, constructorTerm);
          if (!formulaEquals(actual, expected)) throw new KernelError(`Induction case ${ctor.name} proves the wrong formula`);
        }
        return forall(proof.variable, imp(pred(datatype.predicate, ...proof.parameters, v(proof.variable)), proof.motive));
      }
      case "wellFoundedInduction": {
        this.checkTerm(proof.relation);
        this.checkTerm(proof.domain);
        if (!proof.variable || !proof.predecessor || proof.variable === proof.predecessor) {
          throw new KernelError("Well-founded induction needs distinct nonempty variables");
        }
        const forbiddenParameters = new Set([proof.variable, proof.predecessor]);
        if ([...freeTermVariables(proof.relation), ...freeTermVariables(proof.domain)]
          .some(variable => forbiddenParameters.has(variable))) {
          throw new KernelError("The induction relation and domain may depend only on outer parameters");
        }
        if (freeFormulaVariables(proof.motive).has(proof.predecessor)) {
          throw new KernelError("The predecessor variable is free in the induction motive");
        }
        if (assumptions.some(item =>
          freeFormulaVariables(item).has(proof.variable) || freeFormulaVariables(item).has(proof.predecessor))) {
          throw new KernelError("A well-founded induction variable is free in an outer assumption");
        }
        const actualWellFounded = this.checkProofCached(proof.wellFounded, assumptions, cache, stats);
        const expectedWellFounded = pred("wellFoundedOn", proof.relation, proof.domain);
        if (!formulaEquals(actualWellFounded, expectedWellFounded)) {
          throw new KernelError("Well-founded induction received the wrong relation certificate");
        }
        const predecessorMotive = substituteFormula(proof.motive, proof.variable, v(proof.predecessor));
        const inductionHypothesis = forall(proof.predecessor, imp(
          and(
            pred("in", v(proof.predecessor), proof.domain),
            pred("relates", proof.relation, v(proof.predecessor), v(proof.variable)),
          ),
          predecessorMotive,
        ));
        const expectedStep = forall(proof.variable, imp(
          pred("in", v(proof.variable), proof.domain),
          imp(inductionHypothesis, proof.motive),
        ));
        const actualStep = this.checkProofCached(proof.step, assumptions, cache, stats);
        if (!formulaEquals(actualStep, expectedStep)) {
          throw new KernelError("Well-founded induction step proves the wrong formula");
        }
        return forall(proof.variable, imp(
          pred("in", v(proof.variable), proof.domain),
          proof.motive,
        ));
      }
    }
  }

  digest(): string {
    return this.cachedDigest ??= sha256Hex(canonicalRetained(this.environmentSnapshot()));
  }

  /** Canonical, language-neutral description of everything proof replay trusts. */
  environmentSnapshot(): object {
    const byName = <T>([left]: readonly [string, T], [right]: readonly [string, T]): number =>
      left < right ? -1 : left > right ? 1 : 0;
    return {
      capabilities: this.capabilities,
      functions: [...this.functions].sort(byName),
      predicates: [...this.predicates].sort(byName),
      axioms: [...this.axioms].sort(byName),
      theorems: [...this.theorems].sort(byName),
      definitions: [...this.definitions].map(([name, item]) => [name, {
        kind: item.kind,
        parameters: item.parameters,
        properties: [...item.properties].sort(byName),
      }] as [string, object]).sort(byName),
      datatypes: [...this.datatypes].sort(byName),
      recursiveFunctions: [...this.recursiveFunctions].sort(byName),
      functionBodies: [...this.functionBodies].sort(byName),
    };
  }

  private recordDefinition(name: string, kind: DefinitionKind, parameters: readonly string[], properties: ReadonlyMap<string, Formula>): DefinitionRecord {
    for (const formula of properties.values()) {
      this.checkFormula(formula);
      this.ensureClosed(formula, `Definition property of ${name}`);
      deepFreeze(formula);
    }
    const record = { name, kind, parameters: [...parameters], properties };
    this.definitions.set(name, record);
    this.cachedDigest = undefined;
    return record;
  }

  private recordAdmission(operation: KernelAdmissionOperation, payload: Readonly<Record<string, unknown>>): void {
    deepFreeze(payload);
    this.admissions.push(Object.freeze({ operation, payload }));
  }

  /** Fully unfold acyclic predicate/function definitions for extension guards. */
  private expandDefinitions(formula: Formula, fuel = 10_000): Formula {
    if (fuel < 1) throw new KernelError("Definitional expansion limit exceeded");
    const recurse = (value: Formula): Formula => this.expandDefinitions(value, fuel - 1);
    switch (formula.tag) {
      case "bottom": return formula;
      case "eq": return eq(this.evaluateFast(formula.left), this.evaluateFast(formula.right));
      case "pred": {
        const record = this.definitions.get(formula.pred);
        const equation = record?.kind === "predicate" ? record.properties.get("equation") : undefined;
        if (equation) {
          const parameters: string[] = [];
          let body = equation;
          while (body.tag === "forall") { parameters.push(body.variable); body = body.body; }
          if (body.tag === "iff" && parameters.length === formula.args.length) {
            const predicateSide = body.left.tag === "pred" && body.left.pred === formula.pred ? body.left :
              body.right.tag === "pred" && body.right.pred === formula.pred ? body.right : undefined;
            const definitionSide = predicateSide === body.left ? body.right : body.left;
            if (predicateSide) {
              let instance = definitionSide;
              parameters.forEach((parameter, index) => { instance = substituteFormula(instance, parameter, formula.args[index]!); });
              return recurse(instance);
            }
          }
        }
        return pred(formula.pred, ...formula.args.map(argument => this.evaluateFast(argument)));
      }
      case "imp": return imp(recurse(formula.left), recurse(formula.right));
      case "and": return and(recurse(formula.left), recurse(formula.right));
      case "or": return or(recurse(formula.left), recurse(formula.right));
      case "iff": return iff(recurse(formula.left), recurse(formula.right));
      case "forall": return forall(formula.variable, recurse(formula.body));
      case "exists": return exists(formula.variable, recurse(formula.body));
    }
  }

  private freshVariable(base: string, forbidden: ReadonlySet<string>): string {
    if (!forbidden.has(base)) return base;
    for (let index = 1; ; index += 1) {
      const candidate = `${base}_${index}`;
      if (!forbidden.has(candidate)) return candidate;
    }
  }

  private patternBindings(patterns: readonly Pattern[]): string[] {
    const result: string[] = [];
    const visit = (pattern: Pattern): void => {
      if (pattern.tag === "bind") result.push(pattern.name);
      else pattern.args.forEach(visit);
    };
    patterns.forEach(visit);
    return result;
  }

  private patternTerm(pattern: Pattern): Term {
    return pattern.tag === "bind" ? v(pattern.name) : app(pattern.name, ...pattern.args.map(item => this.patternTerm(item)));
  }

  private recursiveSubterms(pattern: Extract<Pattern, { tag: "ctor" }>, constructor: ConstructorSpec): string[] {
    const result: string[] = [];
    const collect = (item: Pattern): void => {
      if (item.tag === "bind") result.push(item.name);
      else item.args.forEach(collect);
    };
    constructor.recursiveFields.forEach(index => collect(pattern.args[index]!));
    return result;
  }

  private validatePattern(pattern: Pattern): void {
    if (pattern.tag === "bind") {
      if (!pattern.name) throw new KernelError("Empty pattern variable");
      return;
    }
    const constructor = [...this.datatypes.values()]
      .flatMap(datatype => datatype.constructors)
      .find(item => item.name === pattern.name);
    if (!constructor || constructor.arity !== pattern.args.length) throw new KernelError(`Unknown or malformed constructor pattern: ${pattern.name}`);
    pattern.args.forEach(item => this.validatePattern(item));
  }

  private checkRecursiveBody(
    term: Term,
    name: string,
    arity: number,
    decreasingParameter: number,
    smallerVariables: ReadonlySet<string>,
  ): void {
    if (term.tag === "var" || term.tag === "nat") return;
    if (term.fn === name) {
      if (term.args.length !== arity) throw new KernelError(`Recursive call of ${name} has the wrong arity`);
      const decreasingArgument = term.args[decreasingParameter];
      if (decreasingArgument?.tag !== "var" || !smallerVariables.has(decreasingArgument.name)) {
        throw new KernelError(`Recursive call of ${name} is not on a structurally smaller value`);
      }
    } else {
      const fnArity = this.functions.get(term.fn);
      if (fnArity === undefined) throw new KernelError(`Unknown function: ${term.fn}`);
      if (fnArity !== term.args.length) throw new KernelError(`Function ${term.fn} expects ${fnArity} arguments, got ${term.args.length}`);
    }
    term.args.forEach(arg => this.checkRecursiveBody(arg, name, arity, decreasingParameter, smallerVariables));
  }

  private collectRecursiveCalls(term: Term, name: string, arity: number): Extract<Term, { tag: "app" }>[] {
    if (term.tag === "var" || term.tag === "nat") return [];
    const result: Extract<Term, { tag: "app" }>[] = [];
    if (term.fn === name) {
      if (term.args.length !== arity) throw new KernelError(`Recursive call of ${name} has the wrong arity`);
      result.push(term);
    } else {
      const fnArity = this.functions.get(term.fn);
      if (fnArity === undefined) throw new KernelError(`Unknown function: ${term.fn}`);
      if (fnArity !== term.args.length) throw new KernelError(`Function ${term.fn} expects ${fnArity} arguments, got ${term.args.length}`);
    }
    for (const argument of term.args) result.push(...this.collectRecursiveCalls(argument, name, arity));
    return result;
  }

  private matchPattern(pattern: Pattern, term: Term, bindings: Map<string, Term>): boolean {
    if (pattern.tag === "bind") {
      const previous = bindings.get(pattern.name);
      if (previous) return this.termEquals(previous, term);
      bindings.set(pattern.name, term);
      return true;
    }
    const numeral = naturalValue(term);
    if (pattern.name === "zero" && pattern.args.length === 0 && numeral === 0n) return true;
    if (pattern.name === "succ" && pattern.args.length === 1 && numeral !== undefined && numeral > 0n) {
      return this.matchPattern(pattern.args[0]!, nat(numeral - 1n), bindings);
    }
    if (term.tag !== "app" || term.fn !== pattern.name || term.args.length !== pattern.args.length) return false;
    return pattern.args.every((item, index) => this.matchPattern(item, term.args[index]!, bindings));
  }

  private isDatatypeConstructor(name: string): boolean {
    return [...this.datatypes.values()].some(datatype =>
      datatype.constructors.some(constructor => constructor.name === name));
  }

  private substituteMany(term: Term, substitutions: ReadonlyMap<string, Term>): Term {
    if (term.tag === "var") return substitutions.get(term.name) ?? term;
    if (term.tag === "nat") return term;
    return app(term.fn, ...term.args.map(arg => this.substituteMany(arg, substitutions)));
  }

  private evaluateCertifiedWithFuel(term: Term, fuel: { remaining: number }): { readonly value: Term; readonly proof: Proof } {
    if (fuel.remaining-- <= 0) throw new KernelError("Evaluation exhausted its fuel");
    if (term.tag === "var" || term.tag === "nat") return { value: term, proof: refl(term) };
    const evaluatedArgs = term.args.map(arg => this.evaluateCertifiedWithFuel(arg, fuel));
    const args = evaluatedArgs.map(item => item.value);
    const normalizedApplication = app(term.fn, ...args);
    const argumentProof = congr(term.fn, ...evaluatedArgs.map(item => item.proof));

    const recursive = this.recursiveFunctions.get(term.fn);
    if (recursive) {
      for (let equationIndex = 0; equationIndex < recursive.equations.length; equationIndex += 1) {
        const equation = recursive.equations[equationIndex]!;
        const bindings = new Map<string, Term>();
        if (equation.patterns.every((pattern, index) => this.matchPattern(pattern, args[index]!, bindings))) {
          const bindingOrder = this.patternBindings(equation.patterns);
          let unfolding: Proof = definitionProof(term.fn, `equation.${equationIndex}`);
          for (const variable of bindingOrder) unfolding = forallElim(unfolding, bindings.get(variable)!);
          const result = this.evaluateCertifiedWithFuel(this.substituteMany(equation.body, bindings), fuel);
          return {
            value: result.value,
            proof: trans(argumentProof, trans(unfolding, result.proof)),
          };
        }
      }
      return { value: normalizedApplication, proof: argumentProof };
    }

    // A constructor may also have a transparent set-theoretic definition.
    // Computation nevertheless keeps the constructor view canonical: unfolding
    // von Neumann successors here would turn a linear numeral into an
    // exponentially duplicated set term and destroy structural evaluation.
    const explicit = this.isDatatypeConstructor(term.fn) ? undefined : this.functionBodies.get(term.fn);
    if (explicit) {
      const substitutions = new Map(explicit.parameters.map((name, index) => [name, args[index]!]));
      let unfolding: Proof = definitionProof(term.fn);
      for (const argument of args) unfolding = forallElim(unfolding, argument);
      const result = this.evaluateCertifiedWithFuel(this.substituteMany(explicit.body, substitutions), fuel);
      return {
        value: result.value,
        proof: trans(argumentProof, trans(unfolding, result.proof)),
      };
    }
    return { value: normalizedApplication, proof: argumentProof };
  }

  private evaluateFastInternal(
    term: Term,
    state: {
      remaining: number; calls: number; reductions: number; cacheHits: number; memo: WeakMap<object, Term>;
      allowedDefinitions?: ReadonlySet<string>; usedDefinitions?: Set<string>;
    },
  ): Term {
    if (state.remaining-- <= 0) throw new KernelError("Evaluation exhausted its fuel");
    state.calls += 1;
    if (term.tag === "var" || term.tag === "nat") return term;
    const cached = state.memo.get(term);
    if (cached) { state.cacheHits += 1; return cached; }

    const args = term.args.map(argument => this.evaluateFastInternal(argument, state));
    const normalized = args.every((argument, index) => argument === term.args[index]) ? term : app(term.fn, ...args);
    const permitted = state.allowedDefinitions === undefined || state.allowedDefinitions.has(term.fn);
    const recursive = permitted ? this.recursiveFunctions.get(term.fn) : undefined;
    if (recursive) {
      for (const equation of recursive.equations) {
        const bindings = new Map<string, Term>();
        if (equation.patterns.every((pattern, index) => this.matchPattern(pattern, args[index]!, bindings))) {
          state.reductions += 1;
          state.usedDefinitions?.add(term.fn);
          const value = this.evaluateFastInternal(this.substituteMany(equation.body, bindings), state);
          state.memo.set(term, value);
          return value;
        }
      }
    }

    const explicit = permitted && !this.isDatatypeConstructor(term.fn) ? this.functionBodies.get(term.fn) : undefined;
    if (explicit) {
      state.reductions += 1;
      state.usedDefinitions?.add(term.fn);
      const substitutions = new Map(explicit.parameters.map((parameter, index) => [parameter, args[index]!]));
      const value = this.evaluateFastInternal(this.substituteMany(explicit.body, substitutions), state);
      state.memo.set(term, value);
      return value;
    }
    state.memo.set(term, normalized);
    return normalized;
  }

  private normalizeComputationalEquality(
    left: Term,
    right: Term,
    allowedDefinitions: ReadonlySet<string> | undefined,
    fuel: number,
  ): { readonly left: NativeValue; readonly right: NativeValue; readonly used: ReadonlySet<string> } {
    if (!Number.isSafeInteger(fuel) || fuel < 1) throw new KernelError("Evaluation fuel must be positive");
    this.checkTerm(left);
    this.checkTerm(right);
    const free = new Set([...freeTermVariables(left), ...freeTermVariables(right)]);
    if (free.size) throw new KernelError(`Kernel computation requires closed terms; free variables: ${[...free].sort().join(", ")}`);
    const leftResult = evaluateNative(this, left, fuel, { allowedDefinitions });
    const rightResult = evaluateNative(this, right, fuel, { allowedDefinitions });
    const used = new Set([...leftResult.definitions, ...rightResult.definitions]);
    return {
      left: leftResult.value,
      right: rightResult.value,
      used,
    };
  }

  private checkTerm(term: Term): void {
    if (term.tag === "var") {
      if (!term.name) throw new KernelError("Empty variable name");
      return;
    }
    if (term.tag === "nat") {
      if (!/^(?:0|[1-9]\d*)$/.test(term.value)) throw new KernelError(`Malformed natural literal: ${term.value}`);
      return;
    }
    const arity = this.functions.get(term.fn);
    if (arity === undefined) throw new KernelError(`Unknown function: ${term.fn}`);
    if (arity !== term.args.length) throw new KernelError(`Function ${term.fn} expects ${arity} arguments, got ${term.args.length}`);
    term.args.forEach(arg => this.checkTerm(arg));
  }

  private checkFormula(formula: Formula): void {
    switch (formula.tag) {
      case "bottom": return;
      case "eq": this.checkTerm(formula.left); this.checkTerm(formula.right); return;
      case "pred": {
        const arity = this.predicates.get(formula.pred);
        if (arity === undefined) throw new KernelError(`Unknown predicate: ${formula.pred}`);
        if (arity !== formula.args.length) throw new KernelError(`Predicate ${formula.pred} expects ${arity} arguments, got ${formula.args.length}`);
        formula.args.forEach(arg => this.checkTerm(arg));
        return;
      }
      case "imp": this.checkFormula(formula.left); this.checkFormula(formula.right); return;
      case "forall":
        if (!formula.variable) throw new KernelError("Empty quantified variable name");
        this.checkFormula(formula.body);
        return;
      case "and":
      case "or":
      case "iff":
        this.checkFormula(formula.left);
        this.checkFormula(formula.right);
        return;
      case "exists":
        if (!formula.variable) throw new KernelError("Empty quantified variable name");
        this.checkFormula(formula.body);
        return;
    }
  }

  private expectEquality(formula: Formula): Extract<Formula, { tag: "eq" }> {
    if (formula.tag !== "eq") throw new KernelError("Expected an equality proof");
    return formula;
  }

  private ensureFresh(name: string): void {
    if (!name) throw new KernelError("Empty symbol name");
    if (this.functions.has(name) || this.predicates.has(name) || this.definitions.has(name)) throw new KernelError(`Symbol already declared: ${name}`);
  }

  private ensureArity(arity: number): void {
    if (!Number.isSafeInteger(arity) || arity < 0) throw new KernelError(`Invalid arity: ${arity}`);
  }

  private validateParameters(parameters: readonly string[]): void {
    if (new Set(parameters).size !== parameters.length || parameters.some(name => !name)) throw new KernelError("Definition parameters must be distinct nonempty names");
  }

  private ensureClosed(formula: Formula, description: string): void {
    const variables = [...freeFormulaVariables(formula)];
    if (variables.length) throw new KernelError(`${description} has free variables: ${variables.join(", ")}`);
  }

  private ensureVariablesWithin(actual: ReadonlySet<string>, allowed: readonly string[], description: string): void {
    const allowedSet = new Set(allowed);
    const extras = [...actual].filter(name => !allowedSet.has(name));
    if (extras.length) throw new KernelError(`${description} has undeclared variables: ${extras.join(", ")}`);
  }

  private termContainsFunction(term: Term, name: string): boolean {
    return term.tag === "app" && (term.fn === name || term.args.some(arg => this.termContainsFunction(arg, name)));
  }

  private termEquals(left: Term, right: Term): boolean {
    return termEquals(left, right);
  }
}

/** Objects recursively frozen by this checker, as opposed to merely shallow-frozen by a caller. */
/**
 * The canonical serialization of `canonical` in ast.ts, memoized on retained
 * certificates. Every retained statement and body is deep-frozen, so its text
 * never changes, and an environment digest then re-serializes only the
 * snapshot's fresh arrays rather than every formula in the environment.
 */
const retainedCanonical = new WeakMap<object, string>();
function canonicalRetained(value: unknown): string {
  if (value === null || typeof value !== "object") return JSON.stringify(value);
  const retained = isDeeplyFrozen(value);
  if (retained) {
    const known = retainedCanonical.get(value);
    if (known !== undefined) return known;
  }
  const text = Array.isArray(value)
    ? `[${value.map(canonicalRetained).join(",")}]`
    : `{${Object.keys(value).sort().map(key => `${JSON.stringify(key)}:${canonicalRetained((value as Record<string, unknown>)[key])}`).join(",")}}`;
  if (retained) retainedCanonical.set(value, text);
  return text;
}
