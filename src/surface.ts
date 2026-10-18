// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { NameResolutionIndex, AmbiguousNameError } from "./name-resolution.ts";
import { resolveImportName } from "./module-names.ts";
import { and, app, bottom, canonical, containsFunction, eq, exists, forall, foralls, formulaEquals, formulaCanonical, freeFormulaVariables, freeTermVariables, iff, imp, nat, naturalValue, not, or, pred, substituteFormula, substituteTerm, termCanonical, termEquals, v, type Formula, type Term } from "./ast.ts";
import { sha256Hex } from "./hash.ts";
import { bind, ctor, Kernel, KernelError, type ConstructorSpec, type DatatypeRecord, type DefinitionRecord, type EvaluationStats, type Pattern, type RecursiveEquation } from "./kernel.ts";
import { compute,
  andElimLeft, andElimRight, andIntro, assume, at, axiom, calc, congr, definition, dne, eqElim, existsElim, existsIntro,
  falseElim, forallElim, forallIntro, iffIntro, iffElimLeft, iffElimRight, impElim, impIntro, induction, orElim,
  orIntroLeft, orIntroRight, rationalClassCompute, refl, symm, trans, wellFoundedInduction,
  theorem, type Proof,
} from "./proof.ts";
import { CARRIER_ARGUMENT_FUNCTIONS, formatFormula, formatTerm, fromSuperscript, registerStructureMember, ringNumeralValue, structureMember, structureProjection as structureFieldSymbol, type CarrierNotation, type FunctionNotation, type OperationNotation, type PredicateNotation, type PrettyOptions, type RingNotation, type RingPiece, type ScopedArgument } from "./pretty.ts";
import { evaluateNative, nativeValueToTerm } from "./runtime.ts";
import { InstanceResolutionError, InstanceResolutionLimitError, prepareInstanceProver, prepareRefinementProver, proveRefinement, type InstanceProver, type InstanceSynthesisResult, type RefinementProver, forkTypeIndex, moveTypeIndex,
  isBindingPredicate, isTransparentPredicate, openGuardFact, registerGuardPredicate, type GuardFact, type ScopeVisibility,
} from "./type-system.ts";
import { createSimpSession, prepareRewrites, rewriteFact, rewriteGoal, RewriteMismatch, settle, simplifyEqualityFact, simplifyEqualityGoal, simplifyFormulaFact, simplifyFormulaGoal, type GoalRewrite, type PreparedRewrites, type SettleStats } from "./tactics.ts";
import { excludedMiddle, proveCongruence, proveTautology } from "./decision-procedures.ts";
import { proveRealLinearArithmetic } from "./real-linarith.ts";
import { proveRationalLinearArithmetic } from "./rational-linarith.ts";
import { decideFiniteSet, FiniteDecideError, type FiniteNames } from "./finite-decide.ts";
import type { ProofNarrativeEntry, TacticScopeEntry, TacticStateSnapshot, TacticSuggestion, TacticTrace, TacticTraceStep } from "./tactic-trace.ts";

export class SurfaceError extends Error {
  readonly line: number;
  file?: string;
  partialTrace?: TacticTrace;

  constructor(line: number, message: string, partialTrace?: TacticTrace) {
    super(`line ${line}: ${message}`);
    this.line = line;
    this.partialTrace = partialTrace;
    this.name = "SurfaceError";
  }
}

export interface ElaboratedModule {
  readonly definitions: readonly string[];
  readonly theorems: readonly string[];
  /** Exact source spans for proof-producing declarations, keyed by elaborated name. */
  readonly theoremLocations: readonly SurfaceTheoremLocation[];
  readonly evaluations: readonly SurfaceEvaluation[];
  readonly sorries: readonly SurfaceSorry[];
}

export interface SurfaceTheoremLocation {
  readonly name: string;
  readonly lineStart: number;
  readonly lineEnd: number;
}

/** A deliberately admitted proof obligation, retained as visible provenance. */
export interface SurfaceSorry {
  readonly theorem: string;
  readonly axiom: string;
  readonly line: number;
  readonly goal: Formula;
}

export interface SurfaceEvaluation {
  readonly line: number;
  readonly expression: string;
  readonly value: string;
  readonly stats: EvaluationStats;
  readonly kind: "term" | "proposition";
}

export interface SurfaceModuleRecord {
  readonly name: string;
  readonly imports: readonly string[];
  /** Curated namespaces automatically opened by clients of this module. */
  readonly exportedOpens: readonly string[];
  readonly namespaces?: readonly string[];
  readonly definitions: readonly string[];
  readonly theorems: readonly string[];
}

export interface SurfaceClassRecord {
  readonly name: string;
  readonly element: string;
  readonly parameters: readonly string[];
  readonly parameterTypes: readonly ("Nat" | "Set" | "Class")[];
}

export interface SurfaceNotationRecord {
  readonly token: string;
  readonly precedence: number;
  /** Omitted for the original infix notation format; an alias is a function name spelled differently. */
  readonly fixity?: "prefix" | "postfix" | "numeral" | "alias" | "binder" | "mixfix" | "constant" | "function" | "sequence" | "coercion" | "scoped";
  readonly associativity: "left" | "right" | "none";
  readonly kind: "function" | "predicate";
  readonly reversed: boolean;
  readonly target: string;
  /** A `notation coercion` form: the sort the target produces from an operand of `operandType`. */
  readonly resultType?: string;
  /**
   * A `notation sequence` form: the value of the graph target at its
   * parameters and index, written out as the body of a big operator.
   */
  readonly template?: Term;
  readonly parameters?: readonly string[];
  readonly index?: string;
  /** User-facing definition selected by instance synthesis, when distinct from the generic target. */
  readonly definitionTarget?: string;
  /** Instance-synthesized arguments supplied before the displayed operands. */
  readonly leadingArguments?: readonly Term[];
  /** Optional soft type selecting one implementation of an overloaded token. */
  readonly operandType?: string;
  /** Optional left and right soft types for a heterogeneous infix notation. */
  readonly leftOperandType?: string;
  readonly rightOperandType?: string;
  /** A `via hypothesis` notation: the operation is read off a matching hypothesis in scope. */
  readonly hypothesis?: HypothesisPattern;
  /** A `notation guard` form: the target predicate is a transparent guard. */
  readonly transparent?: boolean;
  /**
   * A `notation scoped` form: the target's arguments, each a written
   * parameter passed through or a piece of a parameter naming a ring scope.
   */
  readonly expansion?: readonly ScopedArgument[];
  readonly module?: string;
}

/**
 * `notation infixr 70 "∘" => call2(comp(C), _, _) via hypothesis Category(C) for mor(C)`:
 * a hypothesis `predicate(...)` in scope binds its pattern variables to its
 * arguments, the operation is the template `output` at those arguments, and
 * the first carrier is the set whose members the operands must be when
 * several hypotheses supply different operations. Templates are terms over
 * the pattern variables.
 */
export interface HypothesisPattern {
  readonly predicate: string;
  readonly arity: number;
  /** The pattern variable at each argument position of the hypothesis. */
  readonly names: readonly string[];
  /** The operation of an infix notation, a template over the pattern variables. */
  readonly output?: Term;
  /**
   * The carriers, templates over the pattern variables: the operand set of an
   * infix operation; the objects and then the morphisms of a mixfix form.
   */
  readonly carriers: readonly Term[];
  /**
   * For a mixfix predicate notation supplied by a hypothesis, such as
   * `_ : _ ⟶ _` for `Morphism(C, _, _, _)` via `Category(C)`: the target
   * arguments filled from the hypothesis, each as the target position and the
   * template it is read from. The remaining target positions are the
   * placeholders, in order.
   */
  readonly fixed?: readonly { readonly target: number; readonly template: Term }[];
  /**
   * An infix form whose left operand is the structure itself, `G ⧸ N` for
   * `quotientGroup(G, N)` via `Group(G) for G`: the target takes the
   * structure and the right operand, and the form is read only when the
   * left operand is a term a hypothesis in scope makes such a structure.
   */
  readonly structureOperand?: true;
  /**
   * A function form written with an identifier, `ker(f)` for
   * `ringKernel(f, R, S.zero)` via `RingHom(f, R, S)`: the written
   * arguments, in order. A parameter named as a pattern variable is that
   * argument of the hypothesis, so `ker(f)` is read off the hypothesis about
   * `f`; any other parameter is a free placeholder of the template.
   */
  readonly parameters?: readonly string[];
}

/** A pattern template at the arguments of a matching hypothesis. */
function instantiatePattern(
  template: Term, pattern: HypothesisPattern, fact: Extract<Formula, { readonly tag: "pred" }>,
): Term {
  let result = template;
  pattern.names.forEach((name, index) => { result = substituteTerm(result, name, v(`$pattern${index}`)); });
  pattern.names.forEach((_, index) => { result = substituteTerm(result, `$pattern${index}`, fact.args[index]!); });
  return result;
}

export interface SurfaceTacticRecord {
  readonly name: string;
  readonly parameters: readonly string[];
  readonly body: string;
  readonly line?: number;
  readonly module?: string;
}

export interface SurfaceInstanceRecord {
  readonly name: string;
  readonly module?: string;
}

export interface SurfaceDatatypeRecord {
  readonly name: string;
  readonly predicate: string;
  readonly parameters: readonly string[];
  readonly constructors: readonly {
    readonly name: string;
    readonly fields: readonly { readonly name: string; readonly type: string }[];
  }[];
  /** Present when the datatype was declared as a `structure`. */
  readonly structure?: SurfaceStructureRecord;
}

/** The surface of a `structure`: its predicate, parameters, fields, and projections. */
export interface SurfaceStructureRecord {
  /** The predicate `S(self, …)` that conjoins the shape, the field typing, and the laws. */
  readonly predicate: string;
  readonly parameters: readonly string[];
  readonly fields: readonly string[];
  /** The projection function of each field, in field order. */
  readonly projections: readonly string[];
  readonly constructor: string;
  /** For each field, the structure its soft type names, or null. */
  readonly fieldStructures: readonly (string | null)[];
  /** The type of each field as written, `carrier × carrier → carrier`, for a child declared with `extends`. */
  readonly fieldTypes?: readonly string[];
  /** The parents declared with `extends`, in order. */
  readonly parents?: readonly SurfaceStructureParent[];
}

/**
 * A parent of a structure, `extends AbelianGroup as additive (mul := add, …)`:
 * the parent predicate, the structure it is over, the function `Ring.additive`
 * giving the parent value, and the child field each parent field became.
 */
export interface SurfaceStructureParent {
  readonly name: string;
  readonly predicate: string;
  readonly structure: string;
  readonly function: string;
  /** For each parent field in order, the child field it is, or null when fixed to a term. */
  readonly fields: readonly (string | null)[];
}

interface SurfaceEnvironment {
  readonly modules: Map<string, SurfaceModuleRecord>;
  readonly namespaces: Set<string>;
  readonly classes: Map<string, SurfaceClassRecord>;
  readonly classDefinitions: Map<string, SurfaceClassDefinition>;
  readonly notations: SurfaceNotationRecord[];
  readonly tactics: SurfaceTacticRecord[];
  readonly instances: SurfaceInstanceRecord[];
  readonly datatypes: Map<string, SurfaceDatatypeRecord>;
  /** Untrusted elaboration metadata. Kernel declarations retain full arity. */
  readonly signatures: Map<string, SurfaceSignature>;
  captureTacticTraces: boolean;
}

interface SurfaceSignature {
  readonly kind: "function" | "predicate" | "theorem";
  readonly parameters: readonly Binder[];
  /** Number of source requires clauses; excludes generated binder guards. */
  readonly requirementCount?: number;
  readonly resultType?: string;
  readonly resultTypeArguments?: readonly Term[];
}

interface SurfaceClassDefinition {
  readonly elementType: "Nat" | "Set";
  readonly parameterTypes: readonly ("Nat" | "Set" | "Class")[];
  readonly body: Formula;
  readonly predicateBacked: boolean;
}

export interface SurfaceEnvironmentIndex {
  readonly format: "grace17.surface-index";
  readonly version: 3;
  readonly module: string;
  readonly moduleDigest: string;
  readonly kernelEnvironment: string;
  readonly modules: readonly SurfaceModuleRecord[];
  readonly namespaces: readonly string[];
  readonly classes: readonly SurfaceClassRecord[];
  readonly classDefinitions: readonly {
    readonly name: string;
    readonly elementType: "Nat" | "Set";
    readonly parameterTypes: readonly ("Nat" | "Set" | "Class")[];
    readonly body: Formula;
    readonly predicateBacked: boolean;
  }[];
  /** Declaration order is significant when equal-precedence notation overlaps. */
  readonly notations: readonly SurfaceNotationRecord[];
  /** Declaration order is retained for deterministic tactic shadowing checks. */
  readonly tactics: readonly SurfaceTacticRecord[];
  /** Proof-producing instance declarations; declaration order has no priority. */
  readonly instances: readonly SurfaceInstanceRecord[];
  readonly datatypes: readonly SurfaceDatatypeRecord[];
  readonly signatures: readonly {
    readonly name: string;
    readonly kind: "function" | "predicate" | "theorem";
    readonly parameters: readonly Binder[];
    readonly requirementCount?: number;
    readonly resultType?: string;
    readonly resultTypeArguments?: readonly Term[];
  }[];
  readonly digest: string;
}

/**
 * The surface metadata one module adds to its import closure. A module store
 * keeps one delta per module and merges deltas in import order, so an editor
 * or checker loads only the modules it needs. Like the complete index, a
 * delta carries no logical authority.
 */
export interface SurfaceEnvironmentDelta {
  readonly format: "grace17.surface-delta";
  readonly version: 1;
  readonly module: string;
  readonly moduleDigest: string;
  readonly modules: readonly SurfaceModuleRecord[];
  readonly namespaces: readonly string[];
  readonly classes: readonly SurfaceClassRecord[];
  readonly classDefinitions: SurfaceEnvironmentIndex["classDefinitions"];
  readonly notations: readonly SurfaceNotationRecord[];
  readonly tactics: readonly SurfaceTacticRecord[];
  readonly instances: readonly SurfaceInstanceRecord[];
  readonly datatypes: readonly SurfaceDatatypeRecord[];
  readonly signatures: SurfaceEnvironmentIndex["signatures"];
  /** Expression carrier annotations the module recorded, by canonical term. */
  readonly annotations: readonly (readonly [term: string, carrier: string])[];
  readonly digest: string;
}

/** Opaque record of a kernel's surface metadata before one module elaborates. */
export interface SurfaceBaseline {
  readonly modules: ReadonlySet<string>;
  readonly namespaces: ReadonlySet<string>;
  readonly classes: ReadonlySet<string>;
  readonly classDefinitions: ReadonlySet<string>;
  readonly notations: number;
  readonly tactics: number;
  readonly instances: number;
  readonly datatypes: ReadonlySet<string>;
  readonly signatures: ReadonlySet<string>;
  readonly annotations: ReadonlySet<string>;
}

type SurfaceClassExpression =
  | { readonly tag: "named"; readonly name: string; readonly arguments: readonly (Term | SurfaceClassExpression)[] }
  | { readonly tag: "parameter"; readonly name: string }
  | { readonly tag: "set"; readonly term: Term };

const CLASS_PARAMETER_PREFIX = "$class:";

interface SurfaceScope {
  readonly rings?: readonly RingNotation[];
  readonly ringAliases?: readonly RingNotation[];
  readonly moduleName?: string;
  readonly namespaces: readonly string[];
  readonly opens: readonly string[];
  readonly imports: readonly string[];
  readonly pendingFunction?: string;
  readonly resolution?: NameResolutionIndex;
  readonly visibleModules?: ReadonlySet<string>;
  readonly line?: number;
  /** How the current declaration's text uses each receiver: the fields written on it and the applications it is an argument of. */
  readonly dottedFields?: ReadonlyMap<string, ReceiverUses>;
  readonly binderTypes?: ReadonlyMap<string, Binder>;
  /** Current checked proof-state formulas, used only to disambiguate surface notation. */
  readonly localFormulas?: () => readonly Formula[];
  /** The current goal, used only to disambiguate a short name among declarations of several arities. */
  readonly goal?: () => Formula | undefined;
  /** The hypotheses of the open sections, which a bare `apply` discharges among a theorem's requirements. */
  readonly sectionHypotheses?: () => readonly Formula[];
  /**
   * The definitions of the open sections, each with the section variables
   * it takes as leading parameters, dropped at its uses inside the section.
   */
  readonly sectionDefinitions?: ReadonlyMap<string, readonly string[]>;
  /** The variables and hypotheses the open sections bind, with their lines. */
  readonly sectionBindings?: () => readonly TacticScopeEntry[];
}

const surfaceEnvironments = new WeakMap<Kernel, SurfaceEnvironment>();
const resolutionIndices = new WeakMap<SurfaceEnvironment, NameResolutionIndex>();
function resolutionIndex(environment: SurfaceEnvironment): NameResolutionIndex {
  let index = resolutionIndices.get(environment);
  if (!index) {
    index = new NameResolutionIndex();
    for (const module of environment.modules.values()) {
      for (const name of [...module.definitions, ...module.theorems]) index.register(name, module.name);
      for (const name of module.namespaces ?? []) index.registerNamespace(name, module.name);
    }
    for (const datatype of environment.datatypes.values()) {
      const owner = index.owner(datatype.name);
      index.register(datatype.predicate, owner);
      for (const constructor of datatype.constructors) index.register(constructor.name, owner);
    }
    for (const tactic of environment.tactics) index.register(tactic.name, tactic.module);
    for (const name of environment.signatures.keys()) index.register(name);
    resolutionIndices.set(environment, index);
  }
  return index;
}
const surfaceSorries = new WeakMap<Kernel, SurfaceSorry[]>();
const surfaceLineages = new WeakMap<Kernel, object>();
interface CachedAuxiliaryTheorem {
  readonly name: string;
  readonly statement: Formula;
  readonly proof: Proof;
}
interface CachedTheoremDeclaration {
  readonly auxiliary?: CachedAuxiliaryTheorem;
  readonly name: string;
  readonly statement: Formula;
  readonly proof: Proof;
  readonly trace?: TacticTrace;
  /** Dependency checks may omit snapshots even when a trace shell exists. */
  readonly capturesTacticTrace: boolean;
  readonly signature: SurfaceSignature;
  readonly instance: boolean;
  /** Expression carrier annotations recorded while elaborating the declaration. */
  readonly annotations: readonly (readonly [string, string])[];
}
const theoremDeclarationCaches = new WeakMap<object, Map<string, CachedTheoremDeclaration>>();
const maximumTheoremDeclarations = 2_048;
const listLiteralCarriers = new WeakMap<object, Term>();
const notationResultTypes = new WeakMap<object, string>();
/**
 * Expression annotations such as (x:R) on a non-numeral term, recorded per
 * kernel. AST nodes are interned process-wide, so an annotation must never be
 * stored on the node itself: that would leak the carrier into every other
 * module and kernel that shares the interned node. Keying by kernel keeps the
 * old cross-formula propagation within one elaboration while isolating kernels.
 */
const kernelAnnotations = new WeakMap<Kernel, Map<string, string>>();
/**
 * Each module's annotations after its elaboration, inherited and own, so a
 * module sees the annotations of its import closure and nothing else.
 */
const moduleAnnotations = new WeakMap<Kernel, Map<string, ReadonlyMap<string, string>>>();
function moduleAnnotationsFor(kernel: Kernel): Map<string, ReadonlyMap<string, string>> {
  let store = moduleAnnotations.get(kernel);
  if (!store) { store = new Map(); moduleAnnotations.set(kernel, store); }
  return store;
}
function inheritAnnotations(kernel: Kernel, imported: string): void {
  const stored = moduleAnnotationsFor(kernel).get(imported);
  if (!stored || stored.size === 0) return;
  const annotations = annotationsFor(kernel);
  for (const [term, carrier] of stored) if (!annotations.has(term)) annotations.set(term, carrier);
}
function annotationsFor(kernel: Kernel): Map<string, string> {
  let annotations = kernelAnnotations.get(kernel);
  if (!annotations) { annotations = new Map(); kernelAnnotations.set(kernel, annotations); }
  return annotations;
}
const ringPrograms = new WeakMap<Kernel, PreparedRewrites>();
const arithmeticCancellation = new WeakMap<Kernel, { readonly left: Proof; readonly right: Proof }>();
interface SurfaceVisibilityCache {
  readonly environment: SurfaceEnvironment;
  readonly stamp: string;
  readonly reachable: Map<string, ReadonlySet<string>>;
  readonly instances: Map<string, ReadonlySet<string>>;
  readonly notationGroups: Map<string, ReadonlyMap<string, readonly SurfaceNotationRecord[]>>;
  readonly resultTypes: Map<string, ReadonlyMap<string, readonly SurfaceNotationRecord[]>>;
  readonly visibility: Map<string, ScopeVisibility>;
}
const surfaceVisibilityCaches = new WeakMap<Kernel, SurfaceVisibilityCache>();
interface LinearArithmeticPresentation {
  readonly carrier: string;
  readonly add: string;
  readonly mul: string;
  readonly successor: string;
  readonly less: string;
  readonly lessEqual: string;
  readonly strictGap: Proof;
  readonly lessEqualReflexive: Proof;
  readonly lessEqualZero: Proof;
  readonly lessEqualAddRight: Proof;
  readonly lessEqualAddLeftCancel: Proof;
  readonly lessEqualAntisymmetric: Proof;
  readonly lessIrreflexive: Proof;
  readonly lessTransitiveLessEqual: Proof;
  readonly lessOfNotLessEqual: Proof;
  readonly lessEqualOfNotLess: Proof;
  readonly addLessLess: Proof;
  readonly addLessLessEqual: Proof;
  readonly addLessEqualLess: Proof;
  readonly addLessEqualLessEqual: Proof;
}
const linearArithmeticPresentations = new WeakMap<Kernel, LinearArithmeticPresentation>();

/** Copy already-checked surface metadata alongside `Kernel.fork()`. */
export function forkSurfaceEnvironment(source: Kernel, target: Kernel): void {
  const environment = surfaceEnvironments.get(source);
  if (!environment) return;
  const copied: SurfaceEnvironment = {
    modules: new Map(environment.modules),
    namespaces: new Set(environment.namespaces),
    classes: new Map(environment.classes),
    classDefinitions: new Map(environment.classDefinitions),
    notations: [...environment.notations],
    tactics: [...environment.tactics],
    instances: [...environment.instances],
    datatypes: new Map(environment.datatypes),
    signatures: new Map(environment.signatures),
    captureTacticTraces: environment.captureTacticTraces,
  };
  surfaceEnvironments.set(target, copied);
  const names = resolutionIndices.get(environment);
  if (names) resolutionIndices.set(copied, names.fork());
  surfaceSorries.set(target, [...(surfaceSorries.get(source) ?? [])]);
  const lineage = surfaceLineages.get(source);
  if (lineage) surfaceLineages.set(target, lineage);
  // Expression carrier annotations follow the environment they were made in,
  // so a module checked in a fork sees the annotations of its imports exactly
  // as a single-kernel check does. Unrelated kernels still share nothing.
  const annotations = kernelAnnotations.get(source);
  if (annotations) kernelAnnotations.set(target, new Map(annotations));
  const perModule = moduleAnnotations.get(source);
  if (perModule) moduleAnnotations.set(target, new Map(perModule));
  // Prepared rule tables are derived from library theorems the fork shares,
  // and a single kernel keeps them across modules in the same way.
  for (const cache of [ringPrograms, linearArithmeticPresentations, arithmeticCancellation] as const) {
    const prepared = (cache as WeakMap<Kernel, unknown>).get(source);
    if (prepared !== undefined && !(cache as WeakMap<Kernel, unknown>).has(target)) (cache as WeakMap<Kernel, unknown>).set(target, prepared);
  }
  forkTypeIndex(source, target);
}

/**
 * Hand the surface metadata of `source` to `target` without copying, for a
 * loader that replaces `source` by `target` and never uses `source` again.
 */
export function moveSurfaceEnvironment(source: Kernel, target: Kernel): void {
  for (const cache of [
    surfaceEnvironments, surfaceSorries, surfaceLineages, kernelAnnotations, moduleAnnotations,
    ringPrograms, linearArithmeticPresentations, arithmeticCancellation,
  ] as readonly WeakMap<Kernel, unknown>[]) {
    const value = cache.get(source);
    if (value === undefined) continue;
    cache.set(target, value);
    cache.delete(source);
  }
  moveTypeIndex(source, target);
}

/** Tactic traces are editor provenance, not trusted kernel data. */
export function setSurfaceTraceCapture(kernel: Kernel, enabled: boolean): void {
  const environment = surfaceEnvironments.get(kernel);
  if (environment) environment.captureTacticTraces = enabled;
  else surfaceEnvironments.set(kernel, {
    modules: new Map(), namespaces: new Set(), classes: new Map(), classDefinitions: new Map(),
    notations: [], tactics: [], instances: [], datatypes: new Map(), signatures: new Map(), captureTacticTraces: enabled,
  });
}

export function moduleReport(kernel: Kernel): readonly SurfaceModuleRecord[] {
  const environment = surfaceEnvironments.get(kernel);
  return environment ? [...environment.modules.values()].sort((a, b) => a.name.localeCompare(b.name)) : [];
}

export function classReport(kernel: Kernel): readonly SurfaceClassRecord[] {
  const environment = surfaceEnvironments.get(kernel);
  return environment ? [...environment.classes.values()].sort((a, b) => a.name.localeCompare(b.name)) : [];
}

export function notationReport(kernel: Kernel): readonly SurfaceNotationRecord[] {
  const environment = surfaceEnvironments.get(kernel);
  const builtins: SurfaceNotationRecord[] = [];
  if (kernel.predicates.has("in")) builtins.push({
    token: "∈", precedence: 50, associativity: "none", kind: "predicate", reversed: false, target: "in",
  });
  const union = [...kernel.functions].find(([name, arity]) => name.endsWith("union") && arity === 1)?.[0];
  if (union) builtins.push({
    token: "⋃", precedence: 90, associativity: "none", kind: "function", reversed: false, target: union,
  });
  const powerset = [...kernel.functions].find(([name, arity]) =>
    (name === "powerset" || name.endsWith(".powerset")) && arity === 1)?.[0];
  if (powerset) builtins.push({
    token: "𝒫", precedence: 90, associativity: "none", kind: "function", reversed: false, target: powerset,
  });
  for (const [token, target] of [["ℕ", "omega"], ["ℤ", "integers"], ["ℚ", "rationals"], ["ℝ", "reals"]] as const) {
    const symbol = [...kernel.functions].find(([name, arity]) =>
      (name === target || name.endsWith(`.${target}`)) && arity === 0)?.[0];
    if (symbol) builtins.push({
      token, precedence: 100, associativity: "none", kind: "function", reversed: false, target: symbol,
    });
  }
  return [...builtins, ...(environment?.notations ?? [])].sort((a, b) =>
    a.token.localeCompare(b.token) || a.target.localeCompare(b.target));
}

export function tacticReport(kernel: Kernel): readonly SurfaceTacticRecord[] {
  const environment = surfaceEnvironments.get(kernel);
  return environment ? [...environment.tactics].sort((a, b) => a.name.localeCompare(b.name)) : [];
}

export function instanceReport(kernel: Kernel): readonly SurfaceInstanceRecord[] {
  const environment = surfaceEnvironments.get(kernel);
  return environment ? [...environment.instances].sort((a, b) => a.name.localeCompare(b.name)) : [];
}

export function datatypeReport(kernel: Kernel): readonly SurfaceDatatypeRecord[] {
  const environment = surfaceEnvironments.get(kernel);
  return environment ? [...environment.datatypes.values()].sort((a, b) => a.name.localeCompare(b.name)) : [];
}

/** Export editor/elaborator metadata. This sidecar never carries logical authority. */
export function exportSurfaceEnvironmentIndex(
  kernel: Kernel, module: string, moduleDigest: string,
): SurfaceEnvironmentIndex {
  if (!module || !surfaceIndexDigest(moduleDigest)) throw new KernelError("Malformed surface-index module binding");
  const environment = surfaceEnvironments.get(kernel) ?? emptySurfaceEnvironment();
  const body = {
    format: "grace17.surface-index" as const,
    version: 3 as const,
    module,
    moduleDigest,
    kernelEnvironment: kernel.digest(),
    modules: [...environment.modules.values()].sort((a, b) => a.name.localeCompare(b.name)),
    namespaces: [...environment.namespaces].sort(),
    classes: [...environment.classes.values()].sort((a, b) => a.name.localeCompare(b.name)),
    classDefinitions: [...environment.classDefinitions].map(([name, definition]) => ({ name, ...definition }))
      .sort((a, b) => a.name.localeCompare(b.name)),
    notations: [...environment.notations],
    tactics: [...environment.tactics],
    instances: [...environment.instances],
    datatypes: [...environment.datatypes.values()].sort((a, b) => a.name.localeCompare(b.name)),
    signatures: [...environment.signatures].map(([name, signature]) => ({ name, ...signature }))
      .sort((a, b) => a.name.localeCompare(b.name)),
  };
  return surfaceIndexFreeze({ ...body, digest: sha256Hex(canonical(body)) });
}

export function encodeSurfaceEnvironmentIndex(index: SurfaceEnvironmentIndex): Uint8Array {
  validateSurfaceEnvironmentIndex(index);
  return new TextEncoder().encode(canonical(index));
}

export function decodeSurfaceEnvironmentIndex(bytes: Uint8Array): SurfaceEnvironmentIndex {
  let value: unknown;
  try { value = JSON.parse(new TextDecoder("utf-8", { fatal: true }).decode(bytes)); }
  catch { throw new KernelError("Malformed surface-index encoding"); }
  validateSurfaceEnvironmentIndex(value);
  return value;
}

/**
 * Install a complete index only beside the exact checked kernel it describes.
 * A forged index can at worst mislead elaboration; subsequent declarations and
 * proofs are still validated by the kernel.
 */
export function installSurfaceEnvironmentIndex(kernel: Kernel, index: SurfaceEnvironmentIndex): void {
  validateSurfaceEnvironmentIndex(index);
  if (kernel.checkedModuleReceipt(index.module) !== index.moduleDigest) {
    throw new KernelError("Surface index is not bound to a checked module receipt");
  }
  if (kernel.digest() !== index.kernelEnvironment) {
    throw new KernelError("Surface index belongs to a different kernel environment");
  }
  registerNotationGuards(kernel, index.notations);
  surfaceEnvironments.set(kernel, {
    modules: new Map(index.modules.map(item => [item.name, item])),
    namespaces: new Set(index.namespaces),
    classes: new Map(index.classes.map(item => [item.name, item])),
    classDefinitions: new Map(index.classDefinitions.map(({ name, ...definition }) => [name, definition])),
    notations: [...index.notations],
    tactics: [...index.tactics],
    instances: [...index.instances],
    datatypes: new Map(index.datatypes.map(item => [item.name, item])),
    signatures: new Map(index.signatures.map(({ name, ...signature }) => [name, signature])),
    captureTacticTraces: false,
  });
  for (const item of index.datatypes) registerStructureNotation(item);
}

function emptySurfaceEnvironment(): SurfaceEnvironment {
  return {
    modules: new Map(), namespaces: new Set(), classes: new Map(), classDefinitions: new Map(),
    notations: [], tactics: [], instances: [], datatypes: new Map(), signatures: new Map(), captureTacticTraces: false,
  };
}

export function captureSurfaceBaseline(kernel: Kernel): SurfaceBaseline {
  const environment = surfaceEnvironments.get(kernel) ?? emptySurfaceEnvironment();
  return {
    modules: new Set(environment.modules.keys()),
    namespaces: new Set(environment.namespaces),
    classes: new Set(environment.classes.keys()),
    classDefinitions: new Set(environment.classDefinitions.keys()),
    notations: environment.notations.length,
    tactics: environment.tactics.length,
    instances: environment.instances.length,
    datatypes: new Set(environment.datatypes.keys()),
    signatures: new Set(environment.signatures.keys()),
    annotations: new Set(kernelAnnotations.get(kernel)?.keys() ?? []),
  };
}

/** Export the surface metadata added since `baseline`, bound to a checked module receipt. */
export function exportSurfaceEnvironmentDelta(
  kernel: Kernel, baseline: SurfaceBaseline, module: string, moduleDigest: string,
): SurfaceEnvironmentDelta {
  if (!module || !surfaceIndexDigest(moduleDigest)) throw new KernelError("Malformed surface-delta module binding");
  const environment = surfaceEnvironments.get(kernel) ?? emptySurfaceEnvironment();
  const byName = <T extends { readonly name: string }>(a: T, b: T): number => a.name.localeCompare(b.name);
  const body = {
    format: "grace17.surface-delta" as const,
    version: 1 as const,
    module,
    moduleDigest,
    modules: [...environment.modules.values()].filter(item => !baseline.modules.has(item.name)).sort(byName),
    namespaces: [...environment.namespaces].filter(item => !baseline.namespaces.has(item)).sort(),
    classes: [...environment.classes.values()].filter(item => !baseline.classes.has(item.name)).sort(byName),
    classDefinitions: [...environment.classDefinitions].filter(([name]) => !baseline.classDefinitions.has(name))
      .map(([name, definition]) => ({ name, ...definition })).sort(byName),
    notations: environment.notations.slice(baseline.notations),
    tactics: environment.tactics.slice(baseline.tactics),
    instances: environment.instances.slice(baseline.instances),
    datatypes: [...environment.datatypes.values()].filter(item => !baseline.datatypes.has(item.name)).sort(byName),
    signatures: [...environment.signatures].filter(([name]) => !baseline.signatures.has(name))
      .map(([name, signature]) => ({ name, ...signature })).sort(byName),
    annotations: [...(moduleAnnotations.get(kernel)?.get(module) ?? kernelAnnotations.get(kernel) ?? [])]
      .sort(([left], [right]) => left.localeCompare(right)),
  };
  return surfaceIndexFreeze({ ...body, digest: sha256Hex(canonical(body)) });
}

export function encodeSurfaceEnvironmentDelta(delta: SurfaceEnvironmentDelta): Uint8Array {
  validateSurfaceEnvironmentDelta(delta);
  return new TextEncoder().encode(canonical(delta));
}

export function decodeSurfaceEnvironmentDelta(bytes: Uint8Array): SurfaceEnvironmentDelta {
  let value: unknown;
  try { value = JSON.parse(new TextDecoder("utf-8", { fatal: true }).decode(bytes)); }
  catch { throw new KernelError("Malformed surface-delta encoding"); }
  validateSurfaceEnvironmentDelta(value);
  return value;
}

/**
 * Merge one module's surface metadata beside its checked receipt. Deltas are
 * merged in import order, which keeps notation and tactic declaration order
 * consistent with a single-kernel elaboration of the same modules.
 */
export function mergeSurfaceEnvironmentDelta(kernel: Kernel, delta: SurfaceEnvironmentDelta, binding: "receipt" | "foundation" = "receipt"): void {
  validateSurfaceEnvironmentDelta(delta);
  const bound = binding === "foundation" ? kernel.foundationDigest() : kernel.checkedModuleReceipt(delta.module);
  if (bound !== delta.moduleDigest) {
    throw new KernelError(binding === "foundation" ? "Surface delta is not bound to this foundation" : "Surface delta is not bound to a checked module receipt");
  }
  let environment = surfaceEnvironments.get(kernel);
  if (!environment) { environment = emptySurfaceEnvironment(); surfaceEnvironments.set(kernel, environment); }
  if (environment.modules.has(delta.module)) throw new KernelError(`Surface delta for ${delta.module} is already merged`);
  for (const item of delta.modules) environment.modules.set(item.name, item);
  for (const item of delta.namespaces) environment.namespaces.add(item);
  for (const item of delta.classes) environment.classes.set(item.name, item);
  for (const { name, ...definition } of delta.classDefinitions) environment.classDefinitions.set(name, definition);
  environment.notations.push(...delta.notations);
  registerNotationGuards(kernel, delta.notations);
  environment.tactics.push(...delta.tactics);
  environment.instances.push(...delta.instances);
  // Records are keyed by their refinement predicate, as a declaration keys
  // them, so a merged record never sits beside itself under a second key.
  for (const item of delta.datatypes) {
    environment.datatypes.set(item.predicate, item);
    registerStructureNotation(item);
  }
  for (const { name, ...signature } of delta.signatures) environment.signatures.set(name, signature);
  const names = resolutionIndices.get(environment);
  if (names) {
    for (const module of delta.modules) {
      for (const name of [...module.definitions, ...module.theorems]) names.register(name, module.name);
      for (const name of module.namespaces ?? []) names.registerNamespace(name, module.name);
    }
    for (const datatype of delta.datatypes) {
      const owner = names.owner(datatype.name);
      names.register(datatype.predicate, owner);
      for (const constructor of datatype.constructors) names.register(constructor.name, owner);
    }
    for (const tactic of delta.tactics) names.register(tactic.name, tactic.module);
    for (const { name } of delta.signatures) names.register(name);
  }
  moduleAnnotationsFor(kernel).set(delta.module, new Map(delta.annotations));
}

function validateSurfaceEnvironmentDelta(value: unknown): asserts value is SurfaceEnvironmentDelta {
  if (!surfaceIndexRecord(value) || value.format !== "grace17.surface-delta" || value.version !== 1 ||
      typeof value.module !== "string" || !value.module || !surfaceIndexDigest(value.moduleDigest) ||
      !surfaceIndexDigest(value.digest) || !Array.isArray(value.annotations) ||
      value.annotations.some(item => !Array.isArray(item) || item.length !== 2 ||
        typeof item[0] !== "string" || typeof item[1] !== "string") ||
      surfaceIndexContentsMalformed(value)) {
    throw new KernelError("Malformed surface-delta envelope");
  }
  const { digest, ...body } = value;
  if (sha256Hex(canonical(body)) !== digest) throw new KernelError("Malformed or corrupted surface delta");
  surfaceIndexFreeze(value);
}

/** Shared shape check for the record lists of a complete index and a delta. */
function surfaceIndexContentsMalformed(value: Record<string, unknown>): boolean {
  if (!Array.isArray(value.modules) || !Array.isArray(value.namespaces) || !Array.isArray(value.classes) ||
      !Array.isArray(value.classDefinitions) || !Array.isArray(value.notations) || !Array.isArray(value.tactics) ||
      !Array.isArray(value.instances) || !Array.isArray(value.datatypes) || !Array.isArray(value.signatures)) return true;
  return value.namespaces.some(item => typeof item !== "string") ||
      value.modules.some(item => !surfaceIndexRecord(item) || typeof item.name !== "string" ||
        [item.imports, item.exportedOpens, item.definitions, item.theorems, item.namespaces ?? []].some(
          names => !Array.isArray(names) || names.some(name => typeof name !== "string"))) ||
      value.classes.some(item => !surfaceIndexRecord(item) || typeof item.name !== "string") ||
      value.classDefinitions.some(item => !surfaceIndexRecord(item) || typeof item.name !== "string" || !surfaceIndexRecord(item.body)) ||
      value.notations.some(item => !surfaceIndexRecord(item) || typeof item.token !== "string" || typeof item.target !== "string" ||
        (item.definitionTarget !== undefined && typeof item.definitionTarget !== "string") ||
        (item.leftOperandType !== undefined && typeof item.leftOperandType !== "string") ||
        (item.rightOperandType !== undefined && typeof item.rightOperandType !== "string") ||
        (item.leadingArguments !== undefined && (!Array.isArray(item.leadingArguments) ||
          item.leadingArguments.some(argument => !surfaceIndexTerm(argument)))) ||
        (item.transparent !== undefined && typeof item.transparent !== "boolean") ||
        (item.resultType !== undefined && typeof item.resultType !== "string") ||
        (item.template !== undefined && !surfaceIndexTerm(item.template)) ||
        (item.index !== undefined && typeof item.index !== "string") ||
        (item.parameters !== undefined && (!Array.isArray(item.parameters) ||
          item.parameters.some(parameter => typeof parameter !== "string"))) ||
        (item.hypothesis !== undefined && (!surfaceIndexRecord(item.hypothesis) ||
          typeof item.hypothesis.predicate !== "string" || !Number.isSafeInteger(item.hypothesis.arity) ||
          !Array.isArray(item.hypothesis.names) || !Array.isArray(item.hypothesis.carriers)))) ||
      value.tactics.some(item => !surfaceIndexRecord(item) || typeof item.name !== "string" || typeof item.body !== "string") ||
      value.instances.some(item => !surfaceIndexRecord(item) || typeof item.name !== "string") ||
      value.datatypes.some(item => !surfaceIndexRecord(item) || typeof item.name !== "string") ||
      value.signatures.some(item => !surfaceIndexRecord(item) || typeof item.name !== "string" || !Array.isArray(item.parameters) ||
        (item.requirementCount !== undefined && (item.kind !== "theorem" ||
          !Number.isSafeInteger(item.requirementCount) || (item.requirementCount as number) < 0)));
}

function validateSurfaceEnvironmentIndex(value: unknown): asserts value is SurfaceEnvironmentIndex {
  if (!surfaceIndexRecord(value) || value.format !== "grace17.surface-index" || value.version !== 3 ||
      typeof value.module !== "string" || !value.module || !surfaceIndexDigest(value.moduleDigest) ||
      !surfaceIndexDigest(value.kernelEnvironment) || !surfaceIndexDigest(value.digest)) {
    throw new KernelError("Malformed surface-index envelope");
  }
  if (surfaceIndexContentsMalformed(value)) throw new KernelError("Malformed surface-index contents");
  const { digest, ...body } = value;
  if (sha256Hex(canonical(body)) !== digest) throw new KernelError("Malformed or corrupted surface index");
  surfaceIndexFreeze(value);
}

function surfaceIndexRecord(value: unknown): value is Record<string, unknown> {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

function surfaceIndexDigest(value: unknown): value is string {
  return typeof value === "string" && /^[0-9a-f]{64}$/.test(value);
}

function surfaceIndexTerm(value: unknown): value is Term {
  if (!surfaceIndexRecord(value) || typeof value.tag !== "string") return false;
  if (value.tag === "var") return typeof value.name === "string";
  if (value.tag === "nat") return typeof value.value === "string";
  return value.tag === "app" && typeof value.fn === "string" && Array.isArray(value.args) &&
    value.args.every(surfaceIndexTerm);
}

function surfaceIndexFreeze<T>(value: T, seen = new WeakSet<object>()): T {
  if (value === null || typeof value !== "object" || seen.has(value as object)) return value;
  seen.add(value as object);
  for (const child of Object.values(value as Record<string, unknown>)) surfaceIndexFreeze(child, seen);
  return Object.freeze(value);
}

interface SourceLine {
  readonly parsedFormula?: Formula;
  readonly number: number;
  readonly text: string;
  readonly indent: number;
  /** The step began a bullet, `. rw h`, so it opens a branch of its own. */
  readonly bullet?: true;
  readonly columnStart?: number;
  readonly columnEnd?: number;
  readonly narrative?: ProofNarrativeEntry;
}
interface Binder {
  readonly name: string;
  readonly type: string;
  readonly typeArguments?: readonly Term[];
  readonly implicit?: boolean;
  /** A guard written with a mixfix notation after the colon, as in `(f : A → B)` for FunctionBetween(f, A, B). */
  readonly guard?: Formula;
}

const SIMPLE_IDENTIFIER = /^[\p{L}_][\p{L}\p{M}\p{N}_]*$/u;
const QUALIFIED_IDENTIFIER = /^[\p{L}_][\p{L}\p{M}\p{N}_]*(?:\.[\p{L}_][\p{L}\p{M}\p{N}_]*)*$/u;

function malformedIdentifier(kind: string, name: string): string {
  if (/[\p{L}\p{M}\p{N}_]-[\p{L}\p{M}\p{N}_]|-[\p{L}\p{N}_]/u.test(name)) {
    return `hyphens are not permitted in ${kind} identifiers; use ${name.replaceAll("-", "_")}`;
  }
  return `malformed ${kind} name`;
}

function surfaceType(name: string): string {
  return name === "ℕ" ? "Nat" : name;
}

function surfaceSymbol(name: string): string {
  // Glyphs stand for declared names in every segment of a dotted reference,
  // so Grace.Cumulus.Real.Rationals.ℚ and Rationals.ℚ resolve like bare ℚ.
  if (name.includes(".") && name !== "ε₀.less") {
    const segments = name.split(".");
    const mapped = segments.map(surfaceSymbol);
    return mapped.every((segment, index) => segment === segments[index]) ? name : mapped.join(".");
  }
  if (name === "ℕ") return "omega";
  if (name === "ℤ") return "integers";
  if (name === "ℚ") return "rationals";
  if (name === "ℝ") return "reals";
  if (name === "ω") return "omega";
  if (name === "𝒫") return "powerset";
  if (name === "ε₀") return "epsilon0";
  if (name === "ε₀.less") return "epsilon0.less";
  return name;
}

/** Parse, elaborate, and kernel-check a small executable GRACE17 module. */
export interface ElaborateModuleOptions {
  /** The qualified name the module's file denotes, which qualifies a bare `module Name`. */
  readonly moduleName?: string;
}

export function elaborateModule(kernel: Kernel, source: string, options: ElaborateModuleOptions = {}): ElaboratedModule {
  // Carrier annotations such as (0:R) are a module's own reading of its
  // terms. Starting each module with none keeps elaboration independent of
  // which other modules happen to be loaded in the same kernel.
  // Carrier annotations such as (0:R) are inherited from the import closure
  // only, so elaboration does not depend on which other modules happen to
  // be loaded in the same kernel.
  kernelAnnotations.set(kernel, new Map());
  const lineage = surfaceLineages.get(kernel) ?? {};
  if (!surfaceLineages.has(kernel)) surfaceLineages.set(kernel, lineage);
  const declarationCache = theoremDeclarationCaches.get(lineage) ?? new Map<string, CachedTheoremDeclaration>();
  if (!theoremDeclarationCaches.has(lineage)) theoremDeclarationCaches.set(lineage, declarationCache);
  let moduleBaseStamp: string | undefined;
  let declarationChain = "";
  let declarationPrefixEnd = 0;
  const sorryStart = surfaceSorries.get(kernel)?.length ?? 0;
  const sourceLines = source.split(/\r?\n/);
  const lines = sourceLines.map((raw, index) => {
    const narrative = /^([ \t]*)(\.\s*)?--([!|])(?:\s+(.*)|\s*)$/.exec(raw);
    if (narrative) {
      const indent = [...narrative[1]!].reduce((width, character) => width + (character === "\t" ? 2 : 1), 0) + (narrative[2] ? 2 : 0);
      const entry: ProofNarrativeEntry = {
        line: index + 1, indent, kind: narrative[3] === "!" ? "heading" : "note", text: (narrative[4] ?? "").trim(),
      };
      return { number: index + 1, text: raw.trim(), indent, columnStart: narrative[1]!.length + 1, columnEnd: raw.trimEnd().length + 1, narrative: entry };
    }
    const content = raw.replace(/--.*$/, "");
    const leading = content.match(/^[ \t]*/)![0]!;
    return {
      number: index + 1,
      text: content.trim(),
      indent: [...leading].reduce((width, character) => width + (character === "\t" ? 2 : 1), 0),
      columnStart: leading.length + 1,
      columnEnd: content.trimEnd().length + 1,
    };
  }).filter(line => line.text.length > 0);
  const definitions: string[] = [];
  const theorems: string[] = [];
  const theoremLocations: SurfaceTheoremLocation[] = [];
  const pendingDefinitionTypes: { name: string; line: SourceLine; scope: SurfaceScope }[] = [];
  const evaluations: SurfaceEvaluation[] = [];
  const environment = surfaceEnvironments.get(kernel) ?? {
    modules: new Map(), namespaces: new Set<string>(), classes: new Map<string, SurfaceClassRecord>(),
    classDefinitions: new Map<string, SurfaceClassDefinition>(), notations: [], tactics: [], instances: [], datatypes: new Map(),
    signatures: new Map<string, SurfaceSignature>(), captureTacticTraces: true,
  };
  surfaceEnvironments.set(kernel, environment);
  let moduleName: string | undefined;
  let implicitNamespace = false;
  const imports: string[] = [];
  const namespaces: string[] = [];
  const namespaceFrames: { name: string; depth: number; openCount: number; implicit?: boolean; saved?: string[] }[] = [];
  const sections: {
    name: string; line: number; variables: string[]; hypotheses: SourceLine[]; openCount: number; rings: RingNotation[];
    definitions: { name: string; variables: string[] }[]; bindings: TacticScopeEntry[];
  }[] = [];
  const sectionVariables = (): string[] => sections.flatMap(frame => frame.variables);
  const sectionHypotheses = (): SourceLine[] => sections.flatMap(frame => frame.hypotheses);
  const declaredNamespaces = new Set<string>();
  let currentLine = 1;
  const names = resolutionIndex(environment);
  const opens: string[] = [];
  const inheritedOpens: string[] = [];
  const exportedOpens: string[] = [];
  let notationDeclarations = 0;
  let currentBlock: readonly SourceLine[] = [];

  const scope = (pendingFunction?: string): SurfaceScope => ({
    dottedFields: dottedFieldsOf(currentBlock),
    rings: sections.flatMap(frame => frame.rings),
    sectionBindings: () => sections.flatMap(frame => frame.bindings),
    localFormulas: () => sectionHypotheses().flatMap(line => line.parsedFormula ? [line.parsedFormula] : []),
    sectionHypotheses: () => sectionHypotheses().flatMap(line => line.parsedFormula ? [line.parsedFormula] : []),
    sectionDefinitions: new Map(sections.flatMap(frame => frame.definitions.map(item => [item.name, item.variables] as const))),
    moduleName, namespaces: [...namespaces], opens: [...opens, ...inheritedOpens], imports: [...imports], pendingFunction,
    resolution: names, line: currentLine,
    visibleModules: reachableImports(surfaceVisibilityCache(kernel, environment), environment,
      { moduleName, imports, namespaces, opens }),
  });
  const prefix = (): string => namespaces.join(".");

  for (let cursor = 0; cursor < lines.length;) {
    // A section clause, `hypothesis name : …` or `variable (…`, continues
    // on the more indented lines beneath it.
    let clauseSpan = 1;
    let line = lines[cursor]!;
    if (/^(?:hypothesis|variable)\s/u.test(line.text)) {
      while (cursor + clauseSpan < lines.length) {
        const next = lines[cursor + clauseSpan]!;
        if (next.narrative || next.indent <= line.indent) break;
        line = { ...line, text: `${line.text} ${next.text}`, columnEnd: next.columnEnd };
        clauseSpan += 1;
      }
    }
    currentLine = line.number;
    currentBlock = [line];
    const moduleMatch = /^module\s+(\S+)$/.exec(line.text);
    if (moduleMatch) {
      if (moduleName || definitions.length || theorems.length || evaluations.length || notationDeclarations || imports.length || namespaces.length || sections.length) {
        throw new SurfaceError(line.number, "module declaration must be first");
      }
      if (!QUALIFIED_IDENTIFIER.test(moduleMatch[1]!)) throw new SurfaceError(line.number, "malformed module name");
      const declared = surfaceSymbol(moduleMatch[1]!);
      if (declared.includes(".")) {
        if (options.moduleName && options.moduleName !== declared) {
          throw new SurfaceError(line.number, `module ${moduleMatch[1]} is declared in the file of ${options.moduleName}`);
        }
        moduleName = declared;
      } else {
        // A bare module name in a file under a module root takes its
        // qualification from the file's place there. A file outside any
        // root is a top-level module with the bare name.
        if (options.moduleName && options.moduleName.split(".").at(-1) !== declared) {
          throw new SurfaceError(line.number, `module ${moduleMatch[1]} does not match its file, which denotes ${options.moduleName}`);
        }
        moduleName = options.moduleName ?? declared;
      }
      // Every module opens its own namespace implicitly and exports it, so
      // its declarations are reachable qualified by the module name and
      // unqualified by its importers; a file never writes `namespace M` for
      // its own module M.
      implicitNamespace = true;
      if (environment.modules.has(moduleName)) throw new SurfaceError(line.number, `module ${moduleName} is already loaded`);
      if (implicitNamespace) {
        namespaceFrames.push({ name: moduleName, depth: namespaces.length, openCount: opens.length, implicit: true });
        namespaces.push(...moduleName.split("."));
        environment.namespaces.add(prefix());
        declaredNamespaces.add(prefix());
        names.registerNamespace(prefix(), moduleName);
        if (!opens.includes(moduleName)) opens.push(moduleName);
        if (!exportedOpens.includes(moduleName)) exportedOpens.push(moduleName);
      }
      cursor += 1;
      continue;
    }
    const importMatch = /^import\s+(\S+)$/.exec(line.text);
    if (importMatch) {
      if (sections.length) throw new SurfaceError(line.number, "imports belong outside theorem sections");
      // An import is read relative to this module, innermost first.
      const written = surfaceSymbol(importMatch[1]!);
      const imported = resolveImportName(moduleName, written, candidate => environment.modules.has(candidate)) ?? written;
      if (!QUALIFIED_IDENTIFIER.test(importMatch[1]!) || !environment.modules.has(imported)) {
        throw new SurfaceError(line.number, `unknown imported module ${importMatch[1]}`);
      }
      if (!imports.includes(imported)) imports.push(imported);
      inheritAnnotations(kernel, imported);
      // Public opens compose through entrypoint modules. Ordinary `open`
      // directives remain local and therefore never leak accidentally.
      for (const opened of environment.modules.get(imported)!.exportedOpens) {
        if (!inheritedOpens.includes(opened)) inheritedOpens.push(opened);
        if (!exportedOpens.includes(opened)) exportedOpens.push(opened);
      }
      cursor += 1;
      continue;
    }
    const sectionMatch = /^section\s+(\S+)$/.exec(line.text);
    if (sectionMatch) {
      if (!SIMPLE_IDENTIFIER.test(sectionMatch[1]!)) throw new SurfaceError(line.number, "malformed section name");
      sections.push({ name: sectionMatch[1]!, line: line.number, variables: [], hypotheses: [], openCount: opens.length, rings: [], definitions: [], bindings: [] });
      cursor += 1;
      continue;
    }
    if (line.text.startsWith("notation ring ")) {
      if (!sections.length) throw new SurfaceError(line.number, "ring notation requires an open theorem section");
      const match = /^notation ring ([\p{L}_][\p{L}\p{M}\p{N}_]*)\s*:=\s*(.+)$/u.exec(line.text);
      if (!match) throw new SurfaceError(line.number, "expected notation ring R := (A, add, zero, neg, mul, one) or P := R[I] or Q := R ⧸ J or S := R ↾ T");
      const binders = parseBinderGroups(sectionVariables().join(" "), line.number).binders;
      if (binders.some(b => b.name === match[1]) || scope().rings?.some(r => r.name === match[1]))
        throw new SurfaceError(line.number, `ring notation name ${match[1]} is already in scope`);
      const variables = new Set(binders.map(b => b.name));
      const polynomial = /^([\p{L}_][\p{L}\p{M}\p{N}_]*)\[(.+)\]$/u.exec(match[2]!);
      const quotient = /^([\p{L}_][\p{L}\p{M}\p{N}_]*)\s*⧸\s*(.+)$/u.exec(match[2]!);
      const restriction = /^([\p{L}_][\p{L}\p{M}\p{N}_]*)\s*↾\s*(.+)$/u.exec(match[2]!);
      let terms: Term[];
      if (restriction) {
        const base = scope().rings?.find(r => r.name === restriction[1]);
        if (!base) throw new SurfaceError(line.number, `unknown restriction base ring notation ${restriction[1]}`);
        const carrier = parseTerm(restriction[2]!, kernel, variables, line.number, scope());
        const fn = (name: string): string => resolveExisting(`Grace.Cumulus.Set.Relation.${name}`, scope(),
          candidate => kernel.functions.get(candidate) === 2, line.number,
          "restricted ring operation (import Grace.Cumulus.Algebra.Restriction)");
        const restrict = fn("restrict");
        const square = app(fn("product"), carrier, carrier);
        terms = [carrier, app(restrict, base.add, square), base.zero,
          app(restrict, base.neg, carrier), app(restrict, base.mul, square), base.one];
      } else if (quotient) {
        const base = scope().rings?.find(r => r.name === quotient[1]);
        if (!base) throw new SurfaceError(line.number, `unknown quotient base ring notation ${quotient[1]}`);
        const ideal = parseTerm(quotient[2]!, kernel, variables, line.number, scope());
        const fn = (name: string, arity: number): string => resolveExisting(name, scope(),
          candidate => kernel.functions.get(candidate) === arity, line.number,
          "quotient ring operation (import Grace.Cumulus.Algebra.Ring.Quotient)");
        const relation = app(fn("Grace.Cumulus.Algebra.Ring.QuotientCore.idealRelation", 4), base.carrier, base.add, base.neg, ideal);
        const binary = fn("Grace.Cumulus.Relation.QuotientOperations.quotientBinary", 3);
        const unary = fn("Grace.Cumulus.Relation.QuotientOperations.quotientUnary", 3);
        const cls = fn("Grace.Cumulus.Relation.Quotient.equivalenceClass", 3);
        terms = [app(fn("Grace.Cumulus.Relation.Quotient.quotient", 2), base.carrier, relation),
          app(binary, base.carrier, relation, base.add), app(cls, base.carrier, relation, base.zero),
          app(unary, base.carrier, relation, base.neg), app(binary, base.carrier, relation, base.mul),
          app(cls, base.carrier, relation, base.one)];
      } else if (polynomial) {
        const base = scope().rings?.find(r => r.name === polynomial[1]);
        if (!base) throw new SurfaceError(line.number, `unknown coefficient ring notation ${polynomial[1]}`);
        const index = parseTerm(polynomial[2]!, kernel, variables, line.number, { ...scope(), rings: [] });
        const fn = (name: string, arity: number): string => resolveExisting(name, scope(),
          candidate => kernel.functions.get(candidate) === arity, line.number,
          "polynomial ring operation (import Grace.Cumulus.Algebra.Polynomial.Ring)");
        const args = [index, base.carrier, base.add, base.zero, base.neg, base.mul, base.one];
        terms = [app(fn("polynomials", 3), index, base.carrier, base.zero),
          app(fn("polynomialAdd", 7), ...args),
          app(fn("constantFunction", 3), app(fn("monomials", 1), index), base.carrier, base.zero),
          app(fn("polynomialNeg", 7), ...args), app(fn("polynomialMul", 7), ...args),
          app(fn("polynomialConstant", 4), index, base.carrier, base.zero, base.one)];
      } else {
        if (!match[2]!.startsWith("(") || !match[2]!.endsWith(")"))
          throw new SurfaceError(line.number, "expected notation ring R := (A, add, zero, neg, mul, one) or P := R[I] or Q := R ⧸ J or S := R ↾ T");
        const parts = splitTopLevel(match[2]!.slice(1, -1), ",");
        if (parts.length !== 6) throw new SurfaceError(line.number, "ring notation expects carrier, add, zero, neg, mul, one");
        terms = parts.map(part => parseTerm(part, kernel, variables, line.number, { ...scope(), rings: [] }));
      }
      const [carrier, add, zero, neg, mul, one] = terms as [Term, Term, Term, Term, Term, Term];
      const call1 = resolveExisting("apply", scope(), name => kernel.functions.get(name) === 2, line.number, "function application");
      const call2 = resolveExisting("call2", scope(), name => kernel.functions.get(name) === 3, line.number, "binary operation application");
      sections.at(-1)!.rings.push({ name: match[1]!, carrier, add, zero, neg, mul, one, call1, call2 });
      cursor += 1;
      continue;
    }
    const variableMatch = /^variable\s+(.+)$/.exec(line.text);
    if (variableMatch) {
      if (!sections.length) throw new SurfaceError(line.number, "variable requires an open theorem section");
      const parsed = parseBinderGroups([...sectionVariables(), variableMatch[1]!].join(" "), line.number);
      if (parsed.rest || !parsed.binders.length) throw new SurfaceError(line.number, "variable expects binder groups, for example (A x : Set)");
      const hypothesisNames = new Set(sectionHypotheses().map(item => /^requires\s+(\S+)\s*:/.exec(item.text)?.[1]));
      if (parsed.binders.some(item => hypothesisNames.has(item.name))) throw new SurfaceError(line.number, "section variables and hypotheses must have distinct names");
      if (parsed.binders.some(b => scope().rings?.some(r => r.name === b.name)))
        throw new SurfaceError(line.number, "section variable collides with a ring notation name");
      sections.at(-1)!.variables.push(variableMatch[1]!);
      for (const binder of parseBinderGroups(variableMatch[1]!, line.number).binders) {
        sections.at(-1)!.bindings.push({ name: binder.name, kind: "section variable", line: line.number, sort: binder.type });
      }
      cursor += clauseSpan;
      continue;
    }
    const hypothesisMatch = /^hypothesis\s+([\p{L}_][\p{L}\p{M}\p{N}_]*)\s*:\s*(.+)$/u.exec(line.text);
    if (hypothesisMatch) {
      if (!sections.length) throw new SurfaceError(line.number, "hypothesis requires an open theorem section");
      const binders = parseBinderGroups(sectionVariables().join(" "), line.number).binders;
      if (binders.some(item => item.name === hypothesisMatch[1]) || sectionHypotheses().some(item =>
          /^requires\s+(\S+)\s*:/.exec(item.text)?.[1] === hypothesisMatch[1]))
        throw new SurfaceError(line.number, "section variables and hypotheses must have distinct names");
      const parsedFormula = parseFormula(hypothesisMatch[2]!, kernel, new Set(binders.map(item => item.name)), line.number, scopedBinders(scope(), binders));
      sections.at(-1)!.hypotheses.push({ ...line, parsedFormula, text: `requires ${hypothesisMatch[1]} : ${hypothesisMatch[2]}`, indent: 2 });
      sections.at(-1)!.bindings.push({ name: hypothesisMatch[1]!, kind: "section hypothesis", line: line.number });
      cursor += clauseSpan;
      continue;
    }
    const namespaceMatch = /^namespace\s+(\S+)$/.exec(line.text);
    if (namespaceMatch) {
      if (sections.length) throw new SurfaceError(line.number, "close the theorem section before opening a namespace");
      if (!QUALIFIED_IDENTIFIER.test(namespaceMatch[1]!)) throw new SurfaceError(line.number, "malformed namespace name");
      // Reopening the module's own implicit namespace changes nothing.
      if (implicitNamespace && surfaceSymbol(namespaceMatch[1]!) === moduleName && namespaces.join(".") === moduleName) {
        namespaceFrames.push({ name: namespaceMatch[1]!, depth: namespaces.length, openCount: opens.length });
        cursor += 1;
        continue;
      }
      // `namespace _root_.Euclidean` opens a namespace at the root, shared by
      // several modules, rather than one nested in the enclosing namespaces.
      const rooted = namespaceMatch[1]!.startsWith("_root_.");
      if (rooted) {
        const absolute = namespaceMatch[1]!.slice(7);
        if (!QUALIFIED_IDENTIFIER.test(absolute)) throw new SurfaceError(line.number, "malformed namespace name");
        namespaceFrames.push({ name: absolute, depth: namespaces.length, openCount: opens.length, saved: [...namespaces] });
        namespaces.length = 0;
        namespaces.push(...absolute.split("."));
        environment.namespaces.add(prefix());
        declaredNamespaces.add(prefix());
        names.registerNamespace(prefix(), moduleName);
        cursor += 1;
        continue;
      }
      namespaceFrames.push({ name: namespaceMatch[1]!, depth: namespaces.length, openCount: opens.length });
      namespaces.push(...namespaceMatch[1]!.split("."));
      environment.namespaces.add(prefix());
      declaredNamespaces.add(prefix());
      names.registerNamespace(prefix(), moduleName);
      cursor += 1;
      continue;
    }
    const endMatch = /^end(?:\s+(\S+))?$/.exec(line.text);
    if (endMatch) {
      if (sections.length) {
        const frame = sections.at(-1)!;
        if (endMatch[1] && endMatch[1] !== frame.name) throw new SurfaceError(line.number, `expected end ${frame.name}`);
        sections.pop();
        opens.length = frame.openCount;
        cursor += 1;
        continue;
      }
      if (namespaces.length === 0) throw new SurfaceError(line.number, "end without an open namespace");
      const frame = namespaceFrames.pop()!;
      if (frame.implicit) {
        // The implicit module namespace closes itself at the end of the file;
        // an explicit `end Module` for it is accepted and changes nothing.
        namespaceFrames.push(frame);
        if (endMatch[1] && surfaceSymbol(endMatch[1]) !== moduleName) throw new SurfaceError(line.number, `expected end ${moduleName}`);
        cursor += 1;
        continue;
      }
      if (endMatch[1] && endMatch[1] !== frame.name) throw new SurfaceError(line.number, `expected end ${frame.name}`);
      if (frame.saved) {
        namespaces.length = 0;
        namespaces.push(...frame.saved);
      } else {
        namespaces.length = frame.depth;
      }
      opens.length = frame.openCount;
      cursor += 1;
      continue;
    }
    const openMatch = /^open\s+(\S+)$/.exec(line.text);
    if (openMatch) {
      const opened = resolveNamespace(openMatch[1]!, scope(), environment, line.number);
      if (!opens.includes(opened)) opens.push(opened);
      cursor += 1;
      continue;
    }
    const exportOpenMatch = /^export\s+open\s+(\S+)$/.exec(line.text);
    if (exportOpenMatch) {
      if (sections.length) throw new SurfaceError(line.number, "export open belongs outside theorem sections");
      const opened = resolveNamespace(exportOpenMatch[1]!, scope(), environment, line.number);
      if (!opens.includes(opened)) opens.push(opened);
      if (!exportedOpens.includes(opened)) exportedOpens.push(opened);
      cursor += 1;
      continue;
    }
    let end = cursor + 1;
    while (end < lines.length && !/^(?:noncomputable\s+(?:transfinite|foundation|well-founded)\s+def|datatype|structure|class|defgraph|defchoose|defunique|def|define|predicate|theorem|lemma|instance|eval|notation|tactic|module|import|namespace|section|variable|hypothesis|export\s+open|open|end)\b/.test(lines[end]!.text)) end += 1;
    let block = lines.slice(cursor, end);
    currentBlock = block;
    if (sections.length) {
      const theoremHeader = /^(theorem|lemma|instance)\s+(\S+)(.*)$/.exec(line.text);
      // A definition in a section takes the section variables as its leading
      // parameters, in order, and is applied without them inside the section.
      const definitionHeader = theoremHeader ? undefined : /^(def|predicate)\s+(\S+)\s+(.*)$/.exec(line.text);
      if (definitionHeader) {
        const variables = parseBinderGroups(sectionVariables().join(" "), line.number).binders.map(item => item.name);
        const declared = qualifyDeclaration(surfaceSymbol(definitionHeader[2]!), scope());
        block = [{ ...line, text: `${definitionHeader[1]} ${definitionHeader[2]} ${[...sectionVariables(), definitionHeader[3]!].join(" ")}` },
          ...block.slice(1)];
        sections.at(-1)!.definitions.push({ name: declared, variables });
      } else if (!theoremHeader) {
        throw new SurfaceError(line.number, "theorem sections contain variable, hypothesis, definition, and theorem/lemma/instance declarations");
      }
    }
    if (sections.length && /^(theorem|lemma|instance)\s/.test(line.text)) {
      const theoremHeader = /^(theorem|lemma|instance)\s+(\S+)(.*)$/.exec(line.text)!;
      const binders = [...sectionVariables(), theoremHeader[3]!.trim()].filter(Boolean).join(" ");
      const parsed = parseBinderGroups(binders, line.number);
      if (parsed.rest) throw new SurfaceError(line.number, "malformed theorem section binders");
      const used = new Set(parsed.binders.map(item => item.name));
      for (const item of [...sectionHypotheses(), ...block.slice(1).filter(item => item.text.startsWith("requires "))]) {
        const name = /^requires\s+(\S+)\s*:/.exec(item.text)?.[1];
        if (name && used.has(name)) throw new SurfaceError(item.number, `duplicate section/theorem binder or hypothesis ${name}`);
        if (name) used.add(name);
      }
      block = [{ ...line, text: `${theoremHeader[1]} ${theoremHeader[2]} ${binders}` }, ...sectionHypotheses(), ...block.slice(1)];
    }
    const definitionStart = definitions.length, theoremStart = theorems.length;
    if (line.text.startsWith("noncomputable transfinite def ")) definitions.push(elaborateTransfiniteDefinition(kernel, block, scope()));
    else if (line.text.startsWith("noncomputable foundation def ")) definitions.push(elaborateMembershipRecursiveDefinition(kernel, block, scope()));
    else if (line.text.startsWith("noncomputable well-founded def ")) definitions.push(elaborateWellFoundedSetDefinition(kernel, block, scope()));
    else if (line.text.startsWith("datatype ")) definitions.push(elaborateDatatype(kernel, block, scope(), environment));
    else if (line.text.startsWith("structure ")) {
      const structure = elaborateStructure(kernel, block, scope(), environment);
      definitions.push(...structure.definitions);
      theorems.push(...structure.theorems);
      theoremLocations.push(...structure.theorems.map(name => ({
        name, lineStart: line.number, lineEnd: block.findLast(item => item.text)?.number ?? line.number,
      })));
    }
    else if (line.text.startsWith("defgraph ")) {
      const graph = elaborateGraphDefinition(kernel, block, scope());
      definitions.push(graph.definition);
      theorems.push(...graph.theorems);
      theoremLocations.push(...graph.theorems.map(name => ({
        name, lineStart: line.number, lineEnd: block.findLast(item => item.text)?.number ?? line.number,
      })));
    }
    else if (line.text.startsWith("defchoose ") || line.text.startsWith("defunique ")) {
      const chosen = elaborateChosenDefinition(kernel, block, scope());
      definitions.push(...chosen.definitions);
      theorems.push(...chosen.theorems);
      theoremLocations.push(...chosen.theorems.map(name => ({
        name, lineStart: line.number, lineEnd: block.findLast(item => item.text)?.number ?? line.number,
      })));
    }
    else if (line.text.startsWith("def ")) {
      const marker = block.findIndex(item => item.text === "proof");
      const declaration = marker < 0 ? block : block.slice(0, marker);
      const equationStyle = declaration.slice(1).some(item => item.text.startsWith("|")) ||
        /(?:->|→)\s*\S+\s*$/.test(line.text);
      const name = equationStyle
        ? elaborateDefinition(kernel, declaration, scope())
        : elaborateExplicitDefinition(kernel, declaration, scope());
      definitions.push(name);
      const result = elaborateDefinitionType(kernel, name, line, scope(),
        marker < 0 ? undefined : block.slice(marker + 1));
      if (result === "pending") pendingDefinitionTypes.push({ name, line, scope: scope() });
      else if (result === "proved") {
        theorems.push(`${name}.type`);
        theoremLocations.push({ name: `${name}.type`, lineStart: line.number,
          lineEnd: block.at(-1)!.number });
      }
    }
    else if (line.text.startsWith("define ")) {
      const marker = block.findIndex(item => item.text === "proof");
      const name = elaborateDefinition(kernel, marker < 0 ? block : block.slice(0, marker), scope());
      definitions.push(name);
      const result = elaborateDefinitionType(kernel, name, line, scope(),
        marker < 0 ? undefined : block.slice(marker + 1));
      if (result === "pending") pendingDefinitionTypes.push({ name, line, scope: scope() });
      else if (result === "proved") {
        theorems.push(`${name}.type`);
        theoremLocations.push({ name: `${name}.type`, lineStart: line.number, lineEnd: block.at(-1)!.number });
      }
    }
    else if (line.text.startsWith("predicate ")) definitions.push(elaboratePredicateDefinition(kernel, block, scope()));
    else if (line.text.startsWith("class ")) definitions.push(elaborateClassDefinition(kernel, block, scope(), environment));
    else if (line.text.startsWith("theorem ") || line.text.startsWith("lemma ") || line.text.startsWith("instance ")) {
      // This key is only an elaborator cache hint: a reused proof is always
      // checked again by Kernel.addTheorem.  Computing the cryptographic
      // digest of a large environment here made the first theorem in every
      // freshly opened file pay for serializing the entire library.
      moduleBaseStamp ??= [
        kernel.functions.size, kernel.predicates.size, kernel.axioms.size,
        kernel.theorems.size, kernel.definitions.size, kernel.datatypes.size,
      ].join(":");
      // A declaration ending at EOF must not absorb trailing whitespace or
      // comments into its incremental-cache key.  Those edits do not
      // change elaboration, and treating them as part of the proof made the
      // final (often largest) theorem needlessly re-elaborate.  Narrative
      // comments have nonempty `text`, so proof presentation edits still
      // invalidate the declaration as intended.
      const cacheLineEnd = block.findLast(item => item.text.length > 0)?.number ?? line.number;
      const lineEnd = cacheLineEnd;
      // Chain declaration-sized hashes instead of hashing the entire source
      // prefix for every theorem.  The chain still invalidates every
      // downstream declaration after a semantic edit, but makes a module's
      // cache-key work linear rather than quadratic in its source length.
      declarationChain = sha256Hex(JSON.stringify([
        declarationChain || moduleBaseStamp,
        sourceLines.slice(declarationPrefixEnd, cacheLineEnd).join("\n"),
      ]));
      declarationPrefixEnd = cacheLineEnd;
      const declarationKey = declarationChain;
      const candidate = declarationCache.get(declarationKey);
      // A checked proof and an interactive trace are separate cache capabilities.
      // Re-elaborate a dependency-only entry when the editor requests snapshots.
      const cached = candidate && (!environment.captureTacticTraces || candidate.capturesTacticTrace)
        ? candidate : undefined;
      let name: string;
      if (cached) {
        // Generalized induction may introduce a dependency before the public
        // theorem. Replay both through the kernel, in admission order.
        if (cached.auxiliary) {
          const auxiliary = cached.auxiliary;
          kernel.addTheorem(auxiliary.name, auxiliary.statement, auxiliary.proof);
        }
        kernel.addTheorem(cached.name, cached.statement, cached.proof);
        if (cached.trace) kernel.setTheoremTacticTrace(cached.name, cached.trace);
        environment.signatures.set(cached.name, cached.signature);
        if (cached.instance) registerInstanceDeclaration(kernel, cached.name, scope());
        if (cached.annotations.length) {
          const annotations = annotationsFor(kernel);
          for (const [term, type] of cached.annotations) annotations.set(term, type);
        }
        name = cached.name;
        names.register(name, moduleName);
        declarationCache.delete(declarationKey);
        declarationCache.set(declarationKey, cached);
      } else {
        const profileStart = globalThis.performance?.now();
        const sorryCount = surfaceSorries.get(kernel)?.length ?? 0;
        const theoremCount = kernel.theorems.size;
        const annotationsBefore = new Set(kernelAnnotations.get(kernel)?.keys() ?? []);
        try { name = elaborateTheorem(kernel, block, scope()); }
        catch (error) {
          if (error instanceof SurfaceError && error.partialTrace) {
            const goals = error.partialTrace.initial.goals;
            const facts = goals.flatMap(goal => [...goal.assumptions, ...goal.locals.map(local => local.formula)]);
            const conclusions = goals.map(goal => goal.goal);
            const operations = displayOperations(kernel, scope(), facts, conclusions);
            const predicates = displayPredicates(kernel, scope(), facts);
            const functors = displayFunctors(facts);
            const carriers = displayCarriers(kernel, scope(), facts, conclusions);
            const functions = displayFunctions(kernel, scope(), facts);
            if (scope().rings?.length || operations.length || predicates.length || functors.length || carriers.length ||
                functions.length) {
              error.partialTrace = { ...error.partialTrace,
                ...(scope().rings?.length ? { rings: scope().rings } : {}),
                ...(operations.length ? { operations } : {}),
                ...(predicates.length ? { predicates } : {}),
                ...(functors.length ? { functors } : {}),
                ...(carriers.length ? { carriers } : {}),
                ...(functions.length ? { functions } : {}) };
            }
          }
          throw error;
        }
        const signature = environment.signatures.get(name)!;
        const statement = kernel.theorems.get(name)!;
        const proof = kernel.theoremProofs.get(name)!;
        if ((surfaceSorries.get(kernel)?.length ?? 0) === sorryCount) {
          declarationCache.set(declarationKey, {
            name, statement, proof, signature,
            capturesTacticTrace: environment.captureTacticTraces && kernel.theoremTacticTraces.has(name),
            ...(kernel.theorems.size > theoremCount + 1 && kernel.theorems.has(`${name}.generalized_induction_aux`)
              ? { auxiliary: {
                name: `${name}.generalized_induction_aux`,
                statement: kernel.theorems.get(`${name}.generalized_induction_aux`)!,
                proof: kernel.theoremProofs.get(`${name}.generalized_induction_aux`)!,
              } } : {}),
            ...(kernel.theoremTacticTraces.get(name) ? { trace: kernel.theoremTacticTraces.get(name)! } : {}),
            instance: line.text.startsWith("instance "),
            annotations: [...(kernelAnnotations.get(kernel) ?? [])].filter(([term]) => !annotationsBefore.has(term)),
          });
          while (declarationCache.size > maximumTheoremDeclarations) {
            declarationCache.delete(declarationCache.keys().next().value!);
          }
        }
        const profileThreshold = Number((globalThis as typeof globalThis & {
          process?: { env?: Record<string, string | undefined> };
        }).process?.env?.GRACE_PROFILE_THEOREMS_MS ?? "0");
        if (profileStart !== undefined && profileThreshold > 0) {
          const elapsed = globalThis.performance.now() - profileStart;
          if (elapsed >= profileThreshold) console.error(`${elapsed.toFixed(2)} ms\t${name}`);
        }
      }
      const notationTrace = kernel.theoremTacticTraces.get(name);
      if (notationTrace) {
        const hypotheses = statementHypotheses(kernel.theorems.get(name)!);
        const conclusions = [statementConclusion(kernel.theorems.get(name)!)];
        const operations = displayOperations(kernel, scope(), hypotheses, conclusions);
        const predicates = displayPredicates(kernel, scope(), hypotheses);
        const functors = displayFunctors(hypotheses);
        const carriers = displayCarriers(kernel, scope(), hypotheses, conclusions);
        const functions = displayFunctions(kernel, scope(), hypotheses);
        if (scope().rings?.length || operations.length || predicates.length || functors.length || carriers.length ||
            functions.length) {
          kernel.setTheoremTacticTrace(name, { ...notationTrace,
            ...(scope().rings?.length ? { rings: scope().rings } : {}),
            ...(operations.length ? { operations } : {}),
            ...(predicates.length ? { predicates } : {}),
            ...(functors.length ? { functors } : {}),
            ...(carriers.length ? { carriers } : {}),
            ...(functions.length ? { functions } : {}) });
        }
      }
      theorems.push(name);
      theoremLocations.push({
        name,
        lineStart: line.number,
        lineEnd,
      });
    }
    else if (line.text.startsWith("eval ")) evaluations.push(elaborateEvaluation(kernel, block, scope()));
    else if (line.text.startsWith("notation ")) {
      elaborateNotation(kernel, block, scope(), environment);
      notationDeclarations += 1;
    } else if (line.text.startsWith("tactic ")) elaborateTacticDeclaration(block, scope(), environment);
    else throw new SurfaceError(line.number, "expected a module directive, open/export open, datatype, structure, definition, class, theorem, lemma, instance, notation, tactic, recursive definition, or eval command");
    for (let i = definitionStart; i < definitions.length; i++) names.register(definitions[i]!, moduleName);
    for (let i = theoremStart; i < theorems.length; i++) names.register(theorems[i]!, moduleName);
    cursor = end;
  }
  // Foundational definitions may need a closure lemma proved later in the
  // same module. Their annotations never supply evidence while pending.
  for (const item of pendingDefinitionTypes) {
    const result = elaborateDefinitionType(kernel, item.name, item.line, item.scope);
    if (result === "pending") throw new SurfaceError(item.line.number,
      `cannot prove declared result type of ${item.name}; add a proof block to the definition or prove ${item.name}.type in this module`);
    if (!theorems.includes(`${item.name}.type`)) {
      theorems.push(`${item.name}.type`);
      theoremLocations.push({ name: `${item.name}.type`, lineStart: item.line.number, lineEnd: item.line.number });
      names.register(`${item.name}.type`, moduleName);
    }
  }
  if (sections.length) throw new SurfaceError(sections.at(-1)!.line, `section ${sections.at(-1)!.name} is not closed`);
  if (namespaceFrames.length === 1 && namespaceFrames[0]!.implicit) {
    const frame = namespaceFrames.pop()!;
    namespaces.length = frame.depth;
    // A module that only gathers imports has nothing of its own to export;
    // opening its namespace would only make the names of its children
    // reachable through the namespace suffix, as Set.Ordinal.next via Set.
    if (moduleName && definitions.length === 0 && theorems.length === 0 && evaluations.length === 0 && !notationDeclarations) {
      const index = exportedOpens.indexOf(moduleName);
      if (index >= 0) exportedOpens.splice(index, 1);
    }
  }
  if (namespaces.length) throw new SurfaceError(lines.at(-1)?.number ?? 1, `namespace ${namespaces.at(-1)} is not closed`);
  if (moduleName) {
    environment.modules.set(moduleName, { name: moduleName, imports, exportedOpens, definitions, theorems, namespaces: [...declaredNamespaces] });
    moduleAnnotationsFor(kernel).set(moduleName, new Map(kernelAnnotations.get(kernel) ?? []));
  }
  return { definitions, theorems, theoremLocations, evaluations, sorries: (surfaceSorries.get(kernel) ?? []).slice(sorryStart) };
}

/**
 * Elaborate a set-sized recursion over a relation whose well-foundedness has
 * already been proved in Grace17.  The certificate remains a
 * theorem; this declaration feeds its checked proof to the kernel's
 * conservative Replacement-backed recursion schema.
 */
function elaborateWellFoundedSetDefinition(kernel: Kernel, block: readonly SourceLine[], scope: SurfaceScope): string {
  const header = block[0]!;
  block = joinDefinitionClauseContinuations(block);
  const match = /^noncomputable\s+well-founded\s+def\s+(\S+)\s*\((.*)\)\s*:\s*(\S+)$/u.exec(header.text);
  if (!match || !QUALIFIED_IDENTIFIER.test(match[1]!)) {
    throw new SurfaceError(header.number,
      "expected `noncomputable well-founded def collapse (r A x : Set) : Set`");
  }
  const name = qualifyDeclaration(surfaceSymbol(match[1]!), scope);
  const binders = resolveBinderTypes(parseBinders(match[2]!, header.number), kernel, scope, header.number);
  if (surfaceType(match[3]!) !== "Set") {
    throw new SurfaceError(header.number, "a well-founded recursive definition must currently return Set");
  }
  const index = binders.at(-1);
  if (!index || index.type !== "Set") {
    throw new SurfaceError(header.number, "the final well-founded recursion argument must have type Set");
  }
  const parameters = binders.slice(0, -1).map(item => item.name);
  const over = block.find(line => line.text.startsWith("over "));
  const certified = block.find(line => line.text.startsWith("certified by "));
  const clauses = block.filter(line => line.text.startsWith("|"));
  const stray = block.slice(1).find(line =>
    !line.text.startsWith("over ") && !line.text.startsWith("certified by ") && !line.text.startsWith("|"));
  if (stray) throw new SurfaceError(stray.number, "expected an over, certified by, or history clause");
  if (!over) throw new SurfaceError(header.number, "a well-founded definition needs `over domain ordered by relation`");
  if (!certified) throw new SurfaceError(header.number, "a well-founded definition needs `certified by theorem`");
  if (clauses.length !== 1) throw new SurfaceError(header.number, "a well-founded definition needs exactly one history clause");
  const order = /^over\s+(.+?)\s+ordered\s+by\s+(.+)$/u.exec(over.text);
  if (!order) throw new SurfaceError(over.number, "expected `over domain ordered by relation`");
  const certificateName = /^certified\s+by\s+(\S+)$/u.exec(certified.text)?.[1];
  if (!certificateName) throw new SurfaceError(certified.number, "expected `certified by theorem`");
  const clause = /^\|\s*([\p{L}_][\p{L}\p{M}\p{N}_]*)\s+using\s+([\p{L}_][\p{L}\p{M}\p{N}_]*)\s*(?:=>|⇒)\s*(.+)$/u.exec(clauses[0]!.text);
  if (!clause) throw new SurfaceError(clauses[0]!.number, "expected `| x using history => step`");
  const clauseIndex = clause[1]!;
  const history = clause[2]!;
  const variables = new Set(parameters);
  const domain = parseTerm(order[1]!, kernel, variables, over.number, scope);
  const relation = parseTerm(order[2]!, kernel, variables, over.number, scope);
  const predecessor = freshSurfaceVariable("predecessor", new Set([...parameters, index.name, clauseIndex, history]));
  const body = parseTerm(clause[3]!, kernel, new Set([...parameters, clauseIndex, history]), clauses[0]!.number, scope);
  const step = substituteTerm(body, clauseIndex, v(index.name));
  const precedes = pred("relates", relation, v(predecessor), v(index.name));

  // User certificates use the public wellFoundedOn predicate.  Convert that
  // theorem to the kernel schema's curried subset/nonempty presentation.
  let publicCertificate = resolveProof(kernel, certificateName, certified.number, scope);
  for (const parameter of parameters) publicCertificate = forallElim(publicCertificate, v(parameter));
  const expectedPublic = pred("wellFoundedOn", relation, domain);
  if (!formulaEquals(kernel.checkProof(publicCertificate), expectedPublic)) {
    throw new SurfaceError(certified.number,
      `certificate ${certificateName} must prove wellFoundedOn(${formatTerm(relation)}, ${formatTerm(domain)})`);
  }
  const forbidden = new Set([...parameters, index.name, predecessor, history, ...freeTermVariables(domain), ...freeTermVariables(relation)]);
  const subset = freshSurfaceVariable("subset", forbidden); forbidden.add(subset);
  const minimum = freshSurfaceVariable("minimum", forbidden); forbidden.add(minimum);
  const member = freshSurfaceVariable("member", forbidden);
  const domainSubset = forall(member, imp(pred("in", v(member), v(subset)), pred("in", v(member), domain)));
  const nonempty = not(eq(v(subset), app("empty")));
  const minimumBody = and(
    pred("in", v(minimum), v(subset)),
    forall(predecessor, imp(pred("relates", relation, v(predecessor), v(minimum)),
      not(pred("in", v(predecessor), v(subset))))),
  );
  const wellFoundedEquation = resolveProof(kernel, "wellFoundedOn", certified.number, scope);
  let unfolded = iffElimLeft(at(wellFoundedEquation, relation, domain));
  unfolded = impElim(unfolded, publicCertificate);
  const subsetEquation = resolveProof(kernel, "subset", certified.number, scope);
  const subsetProof = impElim(iffElimRight(at(subsetEquation, v(subset), domain)), assume(domainSubset));
  const oldExistential = impElim(forallElim(unfolded, v(subset)),
    andIntro(subsetProof, assume(nonempty)));
  const oldMinimumBody = and(
    pred("in", v(minimum), v(subset)),
    forall(predecessor, imp(pred("in", v(predecessor), v(subset)),
      not(pred("relates", relation, v(predecessor), v(minimum))))),
  );
  const oldMinimum = assume(oldMinimumBody);
  const relationAtPredecessor = pred("relates", relation, v(predecessor), v(minimum));
  const predecessorInSubset = pred("in", v(predecessor), v(subset));
  const noRelation = impElim(forallElim(andElimRight(oldMinimum), v(predecessor)),
    assume(predecessorInSubset));
  const predecessorOutside = impIntro(relationAtPredecessor, impIntro(predecessorInSubset,
    impElim(noRelation, assume(relationAtPredecessor))));
  const convertedMinimum = existsIntro(minimum, minimumBody, v(minimum), andIntro(
    andElimLeft(oldMinimum), forallIntro(predecessor, predecessorOutside),
  ));
  let schemaBody: Proof = forallIntro(subset, impIntro(domainSubset, impIntro(nonempty,
    existsElim(oldExistential, minimum, convertedMinimum),
  )));
  for (const parameter of [...parameters].reverse()) schemaBody = forallIntro(parameter, schemaBody);
  try {
    kernel.defineWellFoundedSetFunction({
      name, parameters, variable: index.name, predecessor, history, domain, precedes, step,
      wellFounded: schemaBody,
    });
  } catch (error) {
    throw new SurfaceError(header.number, error instanceof Error ? error.message : String(error));
  }
  surfaceEnvironments.get(kernel)!.signatures.set(name, {
    kind: "function", parameters: binders, resultType: "Set",
  });
  return name;
}

function elaborateMembershipRecursiveDefinition(kernel: Kernel, block: readonly SourceLine[], scope: SurfaceScope): string {
  const header = block[0]!;
  block = joinDefinitionClauseContinuations(block);
  const match = /^noncomputable\s+foundation\s+def\s+(\S+)\s*\((.*)\)\s*:\s*(\S+)$/u.exec(header.text);
  if (!match || !QUALIFIED_IDENTIFIER.test(match[1]!)) {
    throw new SurfaceError(header.number,
      "expected `noncomputable foundation def rank (x : Set) : Set`");
  }
  const name = qualifyDeclaration(surfaceSymbol(match[1]!), scope);
  const binders = resolveBinderTypes(parseBinders(match[2]!, header.number), kernel, scope, header.number);
  if (surfaceType(match[3]!) !== "Set") {
    throw new SurfaceError(header.number, "a foundation-recursive definition must currently return Set");
  }
  const index = binders.at(-1);
  if (!index || index.type !== "Set") {
    throw new SurfaceError(header.number, "the final foundation-recursion argument must have type Set");
  }
  const parameters = binders.slice(0, -1).map(item => item.name);
  if (block.length !== 2) {
    throw new SurfaceError(header.number, "a foundation-recursive definition needs exactly one member-history clause");
  }
  const clause = /^\|\s*([\p{L}_][\p{L}\p{M}\p{N}_]*)\s+using\s+([\p{L}_][\p{L}\p{M}\p{N}_]*)\s*(?:=>|⇒)\s*(.+)$/u.exec(block[1]!.text);
  if (!clause) {
    throw new SurfaceError(block[1]!.number, "expected `| x using history => step`");
  }
  const clauseIndex = clause[1]!;
  const history = clause[2]!;
  const predecessor = freshSurfaceVariable("member", new Set([...parameters, index.name, clauseIndex, history]));
  const body = parseTerm(clause[3]!, kernel, new Set([...parameters, clauseIndex, history]), block[1]!.number, scope);
  const step = substituteTerm(body, clauseIndex, v(index.name));
  try {
    kernel.defineMembershipRecursiveFunction({
      name, parameters, variable: index.name, predecessor, history, step,
    });
  } catch (error) {
    throw new SurfaceError(header.number, error instanceof Error ? error.message : String(error));
  }
  return name;
}

function elaborateTransfiniteDefinition(kernel: Kernel, block: readonly SourceLine[], scope: SurfaceScope): string {
  const header = block[0]!;
  block = joinDefinitionClauseContinuations(block);
  const match = /^noncomputable\s+transfinite\s+def\s+(\S+)\s*\((.*)\)\s*:\s*(\S+)$/u.exec(header.text);
  if (!match || !QUALIFIED_IDENTIFIER.test(match[1]!)) {
    throw new SurfaceError(header.number, "expected `noncomputable transfinite def V (α : Ordinal) : Set`");
  }
  const name = qualifyDeclaration(surfaceSymbol(match[1]!), scope);
  const pendingScope = { ...scope, pendingFunction: name };
  const binders = resolveBinderTypes(parseBinders(match[2]!, header.number), kernel, pendingScope, header.number);
  if (surfaceType(match[3]!) !== "Set") throw new SurfaceError(header.number, "a transfinite definition must currently return Set");
  const index = binders.at(-1)!;
  const environment = surfaceEnvironments.get(kernel);
  if (!index.type.endsWith(".Ordinal") || !environment?.classes.has(index.type)) {
    throw new SurfaceError(header.number, "the final transfinite index must have the von Neumann Ordinal soft type");
  }
  const parameters = binders.slice(0, -1).map(item => item.name);
  const branches = block.slice(1);
  if (branches.length !== 3 || branches.some(line => !line.text.startsWith("|"))) {
    throw new SurfaceError(header.number, "a transfinite definition needs exactly 0, succ, and limit clauses");
  }
  const parsed = branches.map(line => {
    const equation = /^\|\s*(.*?)\s*(?:=>|⇒)\s*(.+)$/u.exec(line.text);
    if (!equation) throw new SurfaceError(line.number, "malformed transfinite clause");
    return { line, pattern: equation[1]!.trim(), body: equation[2]!.trim() };
  });
  const zeroClause = parsed.find(item => item.pattern === "0");
  const successorClause = parsed.find(item => /^succ\s+([\p{L}_][\p{L}\p{M}\p{N}_]*)$/u.test(item.pattern));
  const limitClause = parsed.find(item => /^limit\s+([\p{L}_][\p{L}\p{M}\p{N}_]*)$/u.test(item.pattern));
  if (!zeroClause || !successorClause || !limitClause || new Set([zeroClause, successorClause, limitClause]).size !== 3) {
    throw new SurfaceError(header.number, "expected one clause each for `0`, `succ β`, and `limit λ`");
  }
  const predecessor = /^succ\s+(.+)$/u.exec(successorClause.pattern)![1]!;
  const limitIndex = /^limit\s+(.+)$/u.exec(limitClause.pattern)![1]!;
  const history = freshSurfaceVariable("history", new Set([...parameters, index.name, predecessor, limitIndex]));
  const escape = (source: string): string => source.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const normalize = (source: string, recursiveBinder?: string): string => {
    let result = source.replaceAll("∅", "empty").replace(/𝒫\s*\(/gu, "powerset(");
    if (recursiveBinder) {
      result = result.replace(new RegExp(`${escape(match[1]!)}\\s+${escape(recursiveBinder)}(?![\\p{L}\\p{M}\\p{N}_])`, "u"), `${match[1]}(${recursiveBinder})`);
    }
    return result;
  };
  const zero = parseTerm(normalize(zeroClause.body), kernel, new Set(parameters), zeroClause.line.number, pendingScope);
  const successor = parseTerm(normalize(successorClause.body, predecessor), kernel,
    new Set([...parameters, predecessor]), successorClause.line.number, pendingScope);
  let limit: Term;
  const comprehension = new RegExp(`^⋃\\s*\\{\\s*${escape(match[1]!)}\\s+([\\p{L}_][\\p{L}\\p{M}\\p{N}_]*)\\s*\\|\\s*\\1\\s*<\\s*${escape(limitIndex)}\\s*\\}$`, "u")
    .exec(limitClause.body);
  if (comprehension) {
    const union = resolveExisting("union", pendingScope, candidate => kernel.functions.get(candidate) === 1,
      limitClause.line.number, "union function");
    const range = resolveExisting("Relation.range", pendingScope, candidate => kernel.functions.get(candidate) === 1,
      limitClause.line.number, "relation range function");
    limit = app(union, app(range, v(history)));
  } else {
    limit = parseTerm(normalize(limitClause.body), kernel, new Set([...parameters, limitIndex, history]),
      limitClause.line.number, pendingScope);
  }
  // Clause binders are surface-local names. The kernel represents the current
  // limit ordinal with the definition header's index variable, just as the
  // generated limit equation does. Translate before applying kernel scope
  // guards so a clause may refer directly to its `limit lambda` binder.
  limit = substituteTerm(limit, limitIndex, v(index.name));
  try {
    const successorIndex = resolveExisting("next", pendingScope, candidate => kernel.functions.get(candidate) === 1,
      header.number, "ordinal successor function");
    const limitPredicate = resolveExisting("Limit", pendingScope, candidate => kernel.predicates.get(candidate) === 1,
      header.number, "ordinal limit predicate");
    const ordinalCondition = pred(index.type, v(index.name));
    const limitCondition = pred(limitPredicate, v(index.name));
    kernel.defineTransfiniteFunction({
      name, parameters, ordinal: index.name, predecessor, history,
      successorIndex, ordinalCondition, limitCondition, zero, successor, limit,
    });
  } catch (error) {
    throw new SurfaceError(header.number, error instanceof Error ? error.message : String(error));
  }
  return name;
}

function elaborateTacticDeclaration(
  block: readonly SourceLine[], scope: SurfaceScope, environment: SurfaceEnvironment,
): void {
  const line = block[0]!;
  if (block.length !== 1) throw new SurfaceError(block[1]!.number, "tactic declarations must fit on one line");
  const match = /^tactic\s+([^\s(]+)(?:\(([^)]*)\))?\s*:=\s*(.+)$/u.exec(line.text);
  if (!match || !QUALIFIED_IDENTIFIER.test(match[1]!)) {
    throw new SurfaceError(line.number, "expected `tactic finish := assumption` or `tactic solve(rule) := settle with $rule`");
  }
  const parameters = match[2]?.trim() ? match[2]!.split(",").map(item => item.trim()) : [];
  if (parameters.some(item => !SIMPLE_IDENTIFIER.test(item)) || new Set(parameters).size !== parameters.length) {
    throw new SurfaceError(line.number, "tactic parameters must be distinct identifiers");
  }
  const name = qualifyDeclaration(match[1]!, scope);
  if (environment.tactics.some(item => item.name === name)) throw new SurfaceError(line.number, `tactic ${name} is already declared`);
  environment.tactics.push({ name, parameters, body: match[3]!, line: line.number, module: scope.moduleName });
}

function elaborateDatatype(
  kernel: Kernel, block: readonly SourceLine[], scope: SurfaceScope, environment: SurfaceEnvironment,
): string {
  const header = block[0]!;
  const match = /^datatype\s+([^\s(]+)(?:\(([^)]*)\))?$/.exec(header.text);
  if (!match || !QUALIFIED_IDENTIFIER.test(match[1]!)) throw new SurfaceError(header.number, "expected `datatype List(A : Set)`");
  const predicate = qualifyDeclaration(match[1]!, scope);
  const name = `${predicate}.inductive`;
  const parameterBinders = match[2]?.trim() ? parseBinders(match[2]!, header.number) : [];
  if (parameterBinders.some(item => item.type !== "Set")) throw new SurfaceError(header.number, "datatype parameters are currently Set carriers");
  const parameters = parameterBinders.map(item => item.name);
  const constructorLines = block.slice(1);
  if (constructorLines.length === 0) throw new SurfaceError(header.number, `datatype ${predicate} needs constructors`);
  const constructors = constructorLines.map(line => {
    const constructor = /^\|\s*([^\s(]+)(?:\((.*)\))?$/.exec(line.text);
    if (!constructor || !SIMPLE_IDENTIFIER.test(constructor[1]!)) throw new SurfaceError(line.number, "malformed datatype constructor");
    const rawFields = constructor[2]?.trim() ? splitTopLevel(constructor[2]!, ",") : [];
    const fields = rawFields.flatMap(field => {
      const fieldMatch = /^\s*(.+?)\s*:\s*(\S+)\s*$/.exec(field);
      if (!fieldMatch) throw new SurfaceError(line.number, "constructor fields need types, as in `head : Set, tail : self`");
      const names = fieldMatch[1]!.trim().split(/\s+/);
      const type = fieldMatch[2]!;
      if (names.some(item => !SIMPLE_IDENTIFIER.test(item)) || !["Set", "self", ...parameters].includes(type)) {
        throw new SurfaceError(line.number, "constructor fields must have type `Set`, `self`, or a datatype parameter");
      }
      return names.map(fieldName => ({ name: fieldName, type }));
    });
    if (new Set(fields.map(item => item.name)).size !== fields.length) throw new SurfaceError(line.number, "constructor fields must be distinct");
    return { name: `${predicate}.${constructor[1]}`, fields };
  });
  try {
    kernel.declareDatatype({
      name, predicate, parameters, setTheoreticEncoding: true,
      constructors: constructors.map(item => ({
        name: item.name, arity: item.fields.length,
        recursiveFields: item.fields.flatMap((field, index) => field.type === "self" ? [index] : []),
        parameterFields: item.fields.flatMap((field, index) => {
          const parameter = parameters.indexOf(field.type);
          return parameter < 0 ? [] : [{ field: index, parameter }];
        }),
      })),
    });
  } catch (error) {
    throw new SurfaceError(header.number, error instanceof Error ? error.message : String(error));
  }
  scope.resolution?.register(name, scope.moduleName);
  for (const constructor of constructors) scope.resolution?.register(constructor.name, scope.moduleName);
  environment.datatypes.set(predicate, { name, predicate, parameters, constructors });
  environment.namespaces.add(predicate);
  return name;
}

/**
 * `structure Category` followed by field lines `| obj mor : Set`,
 * `| dom cod : mor → obj`, and an optional `where` block of named laws
 * declares a one-constructor datatype `Category.inductive` with the
 * refinement predicate `Category.Data`, the constructor `Category.mk`, one
 * projection `Category.obj`, … per field, defined by structural recursion
 * on the constructor, and the predicate `Category(self)` that conjoins
 * `Category.Data(self)`, the typing of the soft-typed fields, and the laws,
 * each stated at the projections of `self`. Structure parameters, as in
 * `structure Functor (C D : Set)`, follow the value in the predicate:
 * `Functor(F, C, D)`. The generated theorems are the projection laws
 * `Category.mk.obj`, …, the shape `Category.mk.data`, eta `Category.eta`,
 * and the introduction `Category.intro`, which takes the fields and asks
 * for the typing and the laws over them. Every one is a kernel proof built
 * from the datatype's own laws and the projection equations.
 */
/** Replace several variables of a term at once; the replacements mention none of the variables replaced. */
function substituteManyTerm(term: Term, substitution: ReadonlyMap<string, Term>): Term {
  let result = term;
  for (const [name, value] of substitution) result = substituteTerm(result, name, value);
  return result;
}

/** `AbelianGroup` as `abelian_group`: the lemma-name form of a predicate name. */
function snakeCaseName(name: string): string {
  return name.replace(/(?<=\p{Ll}|\p{N})(?=\p{Lu})/gu, "_").toLowerCase();
}

function elaborateStructure(
  kernel: Kernel, block: readonly SourceLine[], scope: SurfaceScope, environment: SurfaceEnvironment,
): { readonly definitions: string[]; readonly theorems: string[] } {
  const header = block[0]!;
  // The header continues on the following lines up to the first field line
  // or `where`, so that a list of parents may be laid out one per line.
  let headerText = header.text;
  let bodyStart = 1;
  while (bodyStart < block.length && /\bextends\b/u.test(headerText) &&
      !block[bodyStart]!.text.startsWith("|") && block[bodyStart]!.text !== "where") {
    headerText = `${headerText} ${block[bodyStart]!.text}`;
    bodyStart += 1;
  }
  const match = /^structure\s+([^\s(]+)\s*(\((?:[^()]|\([^()]*\))*\))?(?:\s+extends\s+(.+))?$/u.exec(headerText);
  if (!match || !QUALIFIED_IDENTIFIER.test(match[1]!)) {
    throw new SurfaceError(header.number, "expected `structure Category`, `structure Functor (C D : Set)`, or `structure Ring extends AbelianGroup as additive (mul := add, one := zero, inv := neg)`");
  }
  const name = qualifyDeclaration(surfaceSymbol(match[1]!), scope);
  const parameterGroups = match[2] ? parseBinderGroups(match[2], header.number) : { binders: [] as Binder[], rest: "" };
  if (parameterGroups.rest) throw new SurfaceError(header.number, `unexpected structure header text ${parameterGroups.rest}`);
  const parameters = parameterGroups.binders;
  if (parameters.some(item => item.implicit)) {
    throw new SurfaceError(header.number, "structure parameters are explicit binders, as in `structure Functor (C D : Set)` or `structure Module (R : Ring)`");
  }
  const parameterNames = parameters.map(item => item.name);

  // The parents: `extends AbelianGroup as additive (mul := add, one := zero, inv := neg), Monoid as multiplicative (inv := ∅)`.
  // Each is a structure, or a unary predicate over one, named by `as`; its
  // fields become fields of the child under their own names unless assigned
  // another name, or are fixed to a term over the child's fields and
  // parameters, as the inverse the multiplicative monoid of a ring does not
  // carry.
  interface ParentDraft {
    readonly written: string;
    readonly name: string;
    readonly predicate: string;
    readonly record: SurfaceDatatypeRecord;
    /** For each parent field, the child field it becomes, or null when fixed. */
    readonly map: (string | null)[];
    readonly fixedTexts: (string | null)[];
  }
  const parentDrafts: ParentDraft[] = [];
  const inherited: { readonly name: string; readonly type: string; readonly from: string }[] = [];
  const parentClauses = match[3] ? splitTopLevel(match[3], ",").map(piece => piece.trim()).filter(Boolean) : [];
  for (const clause of parentClauses) {
    const parsed = /^(\S+)(?:\s+as\s+([\p{L}_][\p{L}\p{M}\p{N}_]*))?\s*(?:\((.*)\))?$/u.exec(clause);
    if (!parsed) throw new SurfaceError(header.number, "a parent is written `extends Group as group` or `extends Group as group (mul := add)`");
    const written = parsed[1]!;
    if (!parsed[2]) throw new SurfaceError(header.number, `name the parent ${written} with \`as\`, as in \`extends ${written} as base\``);
    const predicate = resolveOptional(surfaceSymbol(written), scope, candidate => kernel.predicates.get(candidate) === 1);
    if (!predicate) throw new SurfaceError(header.number, `unknown parent ${written}; a parent is a structure or a unary predicate over one`);
    const over = receiverParameters(kernel, predicate).get(0);
    const record = structureOfPredicate(kernel, predicate) ?? (over ? structureOfPredicate(kernel, over) : undefined);
    if (!record) throw new SurfaceError(header.number, `parent ${written} is not a structure or a predicate over one`);
    const structure = record.structure!;
    if (structure.parameters.length) throw new SurfaceError(header.number, `parent ${written} takes parameters, which extends does not support`);
    if (!structure.fieldTypes) throw new SurfaceError(header.number, `parent ${written} was built without field types; rebuild its module`);
    const assignments = new Map<string, string>();
    for (const piece of parsed[3] ? splitTopLevel(parsed[3], ",").map(item => item.trim()).filter(Boolean) : []) {
      const assignment = /^([\p{L}_][\p{L}\p{M}\p{N}_]*)\s*:=\s*(.+)$/u.exec(piece);
      if (!assignment) throw new SurfaceError(header.number, `a parent field is renamed or fixed as \`mul := add\` or \`inv := ∅\`, not ${piece}`);
      if (!structure.fields.includes(assignment[1]!)) {
        throw new SurfaceError(header.number, `${assignment[1]} is not a field of ${shortName(structure.predicate)}`);
      }
      if (assignments.has(assignment[1]!)) throw new SurfaceError(header.number, `${assignment[1]} is assigned twice`);
      assignments.set(assignment[1]!, assignment[2]!.trim());
    }
    const rename = new Map<string, string>();
    const map: (string | null)[] = [];
    const fixedTexts: (string | null)[] = [];
    for (const field of structure.fields) {
      const target = assignments.get(field) ?? field;
      if (SIMPLE_IDENTIFIER.test(target) && !parameterNames.includes(target)) {
        map.push(target);
        fixedTexts.push(null);
        rename.set(field, target);
      } else {
        map.push(null);
        fixedTexts.push(target);
      }
    }
    structure.fields.forEach((field, index) => {
      const target = map[index];
      if (!target) return;
      const type = structure.fieldTypes![index]!.replace(/[\p{L}_][\p{L}\p{M}\p{N}_]*/gu, token => {
        if (structure.fields.includes(token) && !rename.has(token)) {
          throw new SurfaceError(header.number, `the type of ${field} in ${written} mentions ${token}, which is fixed`);
        }
        return rename.get(token) ?? token;
      });
      const existing = inherited.find(item => item.name === target);
      if (existing && existing.type !== type) {
        throw new SurfaceError(header.number, `field ${target} is inherited from ${existing.from} and ${written} with different types`);
      }
      if (!existing) inherited.push({ name: target, type, from: written });
    });
    parentDrafts.push({ written, name: parsed[2]!, predicate, record, map, fixedTexts });
  }

  const whereIndex = block.findIndex(line => line.text === "where");
  const fieldLines: SourceLine[] = [];
  for (const line of whereIndex < 0 ? block.slice(bodyStart) : block.slice(bodyStart, whereIndex)) {
    const previous = fieldLines.at(-1);
    if (line.text.startsWith("|")) fieldLines.push(line);
    else if (previous) fieldLines[fieldLines.length - 1] = { ...previous, text: `${previous.text} ${line.text}` };
    else throw new SurfaceError(line.number, "structure fields are written `| obj mor : Set` or `| dom cod : mor → obj`, one group per line, before `where`");
  }
  if (fieldLines.length === 0 && inherited.length === 0) {
    throw new SurfaceError(header.number, `structure ${shortName(name)} needs a field line such as \`| obj mor : Set\``);
  }
  const fieldGroups = [
    ...inherited.map(item => ({ line: header, binders: [{ name: item.name, type: item.type }] as Binder[] })),
    ...fieldLines.map(line => {
      const text = line.text.slice(1).trim();
      const parsed = text.startsWith("(") ? parseBinderGroups(text, line.number) : { binders: parseBinders(text, line.number), rest: "" };
      if (parsed.rest || parsed.binders.some(item => item.implicit)) {
        throw new SurfaceError(line.number, "structure fields are written `| obj mor : Set` or `| dom cod : mor → obj`");
      }
      for (const binder of parsed.binders) {
        const owner = inherited.find(item => item.name === binder.name);
        if (owner) throw new SurfaceError(line.number, `${binder.name} is already a field of ${shortName(name)}, inherited from ${owner.from}`);
      }
      return { line, binders: parsed.binders };
    }),
  ];
  const fields = fieldGroups.flatMap(group => group.binders);
  const fieldNames = fields.map(item => item.name);
  const parentNames = parentDrafts.map(item => item.name);
  const declared = [...parameterNames, ...fieldNames];
  const reservedNames = [...declared, ...parentNames];
  if (new Set(reservedNames).size !== reservedNames.length) {
    throw new SurfaceError(header.number, "structure fields, parents, and parameters must be distinct");
  }
  if (reservedNames.includes("self")) throw new SurfaceError(header.number, "`self` names the structure value in its laws and is not a field");
  const laws: { name: string; text: string; line: SourceLine }[] = [];
  for (const line of whereIndex < 0 ? [] : block.slice(whereIndex + 1)) {
    const law = /^([\p{L}_][\p{L}\p{M}\p{N}_]*)\s*:\s*(.+)$/u.exec(line.text);
    const previous = laws.at(-1);
    if (law && (!previous || line.indent <= previous.line.indent)) laws.push({ name: law[1]!, text: law[2]!, line });
    else if (previous) previous.text = `${previous.text} ${line.text}`;
    else throw new SurfaceError(line.number, "a structure law is written `name : formula` under `where`");
  }
  const lawNames = laws.map(item => item.name);
  if (new Set(lawNames).size !== lawNames.length || lawNames.some(item => reservedNames.includes(item))) {
    throw new SurfaceError(header.number, "structure laws need distinct names, different from the fields and the parents");
  }

  const dataPredicate = `${name}.Data`;
  const datatypeName = `${name}.inductive`;
  const constructorName = `${name}.mk`;
  const projections = fieldNames.map(field => `${name}.${field}`);
  const parentFunctions = parentNames.map(parent => `${name}.${parent}`);
  const self = "self";
  const variables = new Set(declared);
  try {
    kernel.declareDatatype({
      name: datatypeName, predicate: dataPredicate, parameters: [], setTheoreticEncoding: true,
      constructors: [{ name: constructorName, arity: fields.length, recursiveFields: [], parameterFields: [] }],
    });
    projections.forEach((projection, index) => kernel.defineStructuralFunction({
      name: projection, parameters: [self], datatype: datatypeName, decreasingParameter: 0,
      equations: [{ patterns: [ctor(constructorName, ...fieldNames.map(bind))], body: v(fieldNames[index]!) }],
    }));
  } catch (error) {
    throw new SurfaceError(header.number, error instanceof Error ? error.message : String(error));
  }
  for (const symbol of [datatypeName, dataPredicate, constructorName, ...projections]) scope.resolution?.register(symbol, scope.moduleName);
  environment.signatures.set(constructorName, { kind: "function", parameters: fieldNames.map(field => ({ name: field, type: "Set" })) });
  for (const projection of projections) environment.signatures.set(projection, { kind: "function", parameters: [{ name: self, type: "Set" }] });

  // The typing of the parameters, `(R : Ring)`, and of the fields: a soft
  // type or a mixfix guard after the colon, read with every field and
  // parameter as a variable and the earlier guards in scope, exactly as
  // theorem binders are.
  const resolvedParameters = resolveBinderTypes(parameters, kernel, { ...scope, line: header.number }, header.number);
  const parameterTyping = binderAssumptions(resolvedParameters);
  const parameterScope: SurfaceScope = {
    ...scope, binderTypes: new Map(resolvedParameters.map(item => [item.name, item])), localFormulas: () => parameterTyping,
  };
  const resolvedFields: Binder[] = [];
  const outer = new Set(declared);
  for (const group of fieldGroups) {
    // A field typed by another field or a parameter, `zero : carrier`, is
    // a member of it: the ascription is the membership guard.
    const binders = group.binders.map(item => outer.has(item.type) ? { ...item, type: `∈ ${item.type}` } : item);
    const resolved = resolveBinderTypes(binders, kernel, {
      ...parameterScope, line: group.line.number,
      localFormulas: () => [...parameterTyping, ...binderAssumptions(resolvedFields)],
    }, group.line.number, [], outer);
    resolvedFields.push(...resolved);
  }
  const typing = binderAssumptions(resolvedFields);
  const fieldStructures = resolvedFields.map(item =>
    !item.guard && item.type !== "Set" && !item.typeArguments?.length &&
      [...environment.datatypes.values()].some(record => record.structure?.predicate === item.type) ? item.type : null);
  // The parents as values over the fields: the parent's constructor at the
  // child's fields and the fixed terms, `Group.mk(carrier, add, zero, neg)`.
  const parents = parentDrafts.map(draft => {
    const structure = draft.record.structure!;
    const args = structure.fields.map((_, index) => {
      const child = draft.map[index];
      if (child) return v(child);
      return parseTerm(draft.fixedTexts[index]!, kernel, variables, header.number, { ...parameterScope, line: header.number });
    });
    return { ...draft, structure, args, value: app(structure.constructor, ...args) };
  });
  // The laws, with the typing and the earlier laws in scope for the
  // notation they supply: `f : a ⟶ b` under an earlier `Category(C)`.
  const lawFormulas: Formula[] = [];
  const parentLaws = parents.map(parent => pred(parent.predicate, parent.value));
  const lawScope: SurfaceScope = {
    ...scope, binderTypes: new Map([...resolvedParameters, ...resolvedFields].map(item => [item.name, item])),
    localFormulas: () => [...parameterTyping, ...typing, ...parentLaws, ...lawFormulas],
  };
  for (const law of laws) {
    lawFormulas.push(parseFormula(law.text, kernel, variables, law.line.number, { ...lawScope, line: law.line.number }));
  }
  // The hypotheses over the fields, in the order of the conjuncts: the
  // typing of the parameters, the typing of the fields, the parents, the laws.
  const hypotheses = [...parameterTyping, ...typing, ...parentLaws, ...lawFormulas];
  for (const formula of hypotheses) {
    const bound = boundFormulaVariables(formula);
    const clash = declared.find(item => bound.has(item));
    if (clash) throw new SurfaceError(header.number, `a law of ${shortName(name)} binds ${clash}, which is also a field or parameter; rename the bound variable`);
  }

  // The parent values as functions of the structure value, `Ring.additive(self)`.
  const projected = new Map(fieldNames.map((field, index) => [field, app(projections[index]!, v(self))]));
  parents.forEach((parent, index) => {
    const symbol = parentFunctions[index]!;
    try {
      kernel.defineFunction(symbol, [self], substituteManyTerm(parent.value, projected));
    } catch (error) {
      throw new SurfaceError(header.number, error instanceof Error ? error.message : String(error));
    }
    scope.resolution?.register(symbol, scope.moduleName);
    environment.signatures.set(symbol, { kind: "function", parameters: [{ name: self, type: "Set" }] });
  });

  // The predicate: the shape, then the typing, the parents, and the laws at
  // the projections.
  const parentConjuncts = parents.map((parent, index) => pred(parent.predicate, app(parentFunctions[index]!, v(self))));
  const projectedHypotheses = [
    ...parameterTyping, ...typing.map(formula => substituteManySurface(formula, projected)),
    ...parentConjuncts, ...lawFormulas.map(formula => substituteManySurface(formula, projected)),
  ];
  const conjuncts = [pred(dataPredicate, v(self)), ...projectedHypotheses];
  const body = conjuncts.slice(0, -1).reduceRight<Formula>((rest, item) => and(item, rest), conjuncts.at(-1)!);
  try {
    kernel.definePredicate(name, [self, ...parameterNames], body);
  } catch (error) {
    throw new SurfaceError(header.number, error instanceof Error ? error.message : String(error));
  }
  environment.signatures.set(name, { kind: "predicate", parameters: [{ name: self, type: "Set" }, ...parameters.map(item => ({ name: item.name, type: "Set" }))] });

  // The generated theorems, each a kernel proof from the datatype laws and
  // the projection equations.
  const fieldTerms = fieldNames.map(v);
  const made = app(constructorName, ...fieldTerms);
  const theorems: { name: string; statement: Formula; proof: Proof; parameters: Binder[]; requirementCount: number; instance?: true }[] = [];
  const fieldBinders = fieldNames.map(field => ({ name: field, type: "Set" }));
  const parameterBinders = parameterNames.map(parameter => ({ name: parameter, type: "Set" }));
  projections.forEach((projection, index) => theorems.push({
    name: `${constructorName}.${fieldNames[index]}`,
    statement: kernel.definitions.get(projection)!.properties.get("equation.0")!,
    proof: definition(projection, "equation.0"), parameters: fieldBinders, requirementCount: 0,
  }));
  theorems.push({
    name: `${constructorName}.data`,
    statement: foralls(fieldNames, pred(dataPredicate, made)),
    proof: fieldNames.reduceRight<Proof>((proof, field) => forallIntro(field, proof),
      at(definition(datatypeName, "constructor.mk"), ...fieldTerms)),
    parameters: fieldBinders, requirementCount: 0,
  });
  // Eta: a value of the structure is the constructor applied to its projections.
  {
    const cases = kernel.definitions.get(datatypeName)!.properties.get("cases")!;
    if (cases.tag !== "forall" || cases.body.tag !== "imp") throw new SurfaceError(header.number, "internal: malformed structure cases law");
    let existential = substituteFormula(cases.body.right, cases.variable, v(self));
    const instances: Formula[] = [];
    for (const field of fieldNames) {
      if (existential.tag !== "exists") throw new SurfaceError(header.number, "internal: malformed structure cases law");
      existential = substituteFormula(existential.body, existential.variable, v(field));
      instances.push(existential);
    }
    const witnessed = assume(existential);
    const components = projections.map(projection =>
      trans(congr(projection, witnessed), at(definition(projection, "equation.0"), ...fieldTerms)));
    let proof: Proof = trans(witnessed, symm(congr(constructorName, ...components)));
    const opened = impElim(at(definition(datatypeName, "cases"), v(self)), assume(pred(dataPredicate, v(self))));
    for (let index = fieldNames.length - 1; index >= 0; index -= 1) {
      proof = existsElim(index === 0 ? opened : assume(instances[index - 1]!), fieldNames[index]!, proof);
    }
    theorems.push({
      name: `${name}.eta`,
      statement: forall(self, imp(pred(dataPredicate, v(self)),
        eq(v(self), app(constructorName, ...projections.map(projection => app(projection, v(self))))))),
      proof: forallIntro(self, impIntro(pred(dataPredicate, v(self)), proof)),
      parameters: [{ name: self, type: "Set" }], requirementCount: 1,
    });
  }
  // Introduction: the typing, the parents, and the laws over the fields give
  // the predicate at the constructor; each hypothesis is rewritten field by
  // field to its projection of the constructed value, and a parent law to
  // the parent value of the constructed value.
  {
    const atConstructor = new Map(fieldNames.map((field, index) => [field, app(projections[index]!, made)]));
    const reserved = new Set([...declared, self, ...hypotheses.flatMap(formula => [...boundFormulaVariables(formula), ...freeFormulaVariables(formula)])]);
    let hole = "_x";
    while (reserved.has(hole)) hole = `_${hole}`;
    const parentStart = parameterTyping.length + typing.length;
    const rewritten = hypotheses.map((formula, position) => {
      let evidence: Proof = assume(formula);
      const free = freeFormulaVariables(formula);
      fieldNames.forEach((field, index) => {
        if (!free.has(field)) return;
        const assignment = new Map<string, Term>();
        for (let earlier = 0; earlier < index; earlier += 1) assignment.set(fieldNames[earlier]!, atConstructor.get(fieldNames[earlier]!)!);
        assignment.set(field, v(hole));
        const motive = substituteSimultaneously(formula, assignment, reserved);
        evidence = eqElim(at(definition(projections[index]!, "equation.0"), ...fieldTerms), hole, motive, evidence, true);
      });
      const parentIndex = position - parentStart;
      if (parentIndex >= 0 && parentIndex < parents.length) {
        const equation = at(definition(parentFunctions[parentIndex]!, "equation"), made);
        evidence = eqElim(equation, hole, pred(parents[parentIndex]!.predicate, v(hole)), evidence, true);
      }
      return evidence;
    });
    const shape = at(definition(datatypeName, "constructor.mk"), ...fieldTerms);
    const conjunction = [shape, ...rewritten].slice(0, -1).reduceRight<Proof>((rest, item) => andIntro(item, rest), [shape, ...rewritten].at(-1)!);
    const equivalence = at(definition(name, "equation"), made, ...parameterNames.map(v));
    const conclusion = pred(name, made, ...parameterNames.map(v));
    const proof = [...parameterNames, ...fieldNames].reduceRight<Proof>((inner, variable) => forallIntro(variable, inner),
      hypotheses.reduceRight<Proof>((inner, hypothesis) => impIntro(hypothesis, inner), impElim(iffElimRight(equivalence), conjunction)));
    theorems.push({
      name: `${name}.intro`,
      statement: foralls([...parameterNames, ...fieldNames], hypotheses.reduceRight<Formula>((rest, hypothesis) => imp(hypothesis, rest), conclusion)),
      proof, parameters: [...parameterBinders, ...fieldBinders], requirementCount: hypotheses.length,
    });
  }
  // The parents: the value as the parent's constructor at the projections,
  // each parent projection of it, the parent value of a constructed child,
  // the parent predicate as an instance of the child's, and the membership
  // of the shared carrier.
  parents.forEach((parent, index) => {
    const symbol = parentFunctions[index]!;
    const structure = parent.structure;
    const argsAtSelf = parent.args.map(argument => substituteManyTerm(argument, projected));
    theorems.push({
      name: `${symbol}.value`,
      statement: kernel.definitions.get(symbol)!.properties.get("equation")!,
      proof: definition(symbol, "equation"), parameters: [{ name: self, type: "Set" }], requirementCount: 0,
    });
    structure.projections.forEach((projection, position) => theorems.push({
      name: `${symbol}.${structure.fields[position]}`,
      statement: forall(self, eq(app(projection, app(symbol, v(self))), argsAtSelf[position]!)),
      proof: forallIntro(self, trans(congr(projection, at(definition(symbol, "equation"), v(self))),
        at(definition(projection, "equation.0"), ...argsAtSelf))),
      parameters: [{ name: self, type: "Set" }], requirementCount: 0,
    }));
    // `Ring.mk.additive`: the parent value of a constructed child, by the
    // projection equations under each argument.
    const atConstructed = (term: Term): Proof => {
      if (term.tag === "var") {
        const position = fieldNames.indexOf(term.name);
        return position < 0 ? refl(term) : at(definition(projections[position]!, "equation.0"), ...fieldTerms);
      }
      if (term.tag !== "app" || term.args.length === 0) return refl(term);
      return congr(term.fn, ...term.args.map(atConstructed));
    };
    theorems.push({
      name: `${constructorName}.${parent.name}`,
      statement: foralls(fieldNames, eq(app(symbol, made), parent.value)),
      proof: fieldNames.reduceRight<Proof>((proof, field) => forallIntro(field, proof),
        trans(at(definition(symbol, "equation"), made), congr(structure.constructor, ...parent.args.map(atConstructed)))),
      parameters: fieldBinders, requirementCount: 0,
    });
    {
      const hypothesis = pred(name, v(self), ...parameterNames.map(v));
      let conjunction: Proof = impElim(iffElimLeft(at(definition(name, "equation"), v(self), ...parameterNames.map(v))), assume(hypothesis));
      const position = 1 + parameterTyping.length + typing.length + index;
      for (let step = 0; step < position; step += 1) conjunction = andElimRight(conjunction);
      if (position < conjuncts.length - 1) conjunction = andElimLeft(conjunction);
      theorems.push({
        name: `${symbol}.${snakeCaseName(shortName(parent.predicate))}`,
        statement: foralls([self, ...parameterNames], imp(hypothesis, pred(parent.predicate, app(symbol, v(self))))),
        proof: [self, ...parameterNames].reduceRight<Proof>((inner, variable) => forallIntro(variable, inner), impIntro(hypothesis, conjunction)),
        parameters: [{ name: self, type: "Set" }, ...parameterBinders], requirementCount: 1, instance: true,
      });
    }
    const carrier = parent.map[0];
    if (carrier) {
      let element = "x";
      while (reservedNames.includes(element) || element === self) element = `_${element}`;
      const child = app(projections[fieldNames.indexOf(carrier)]!, v(self));
      const hypothesis = pred("in", v(element), child);
      let hole = "_h";
      while (reservedNames.includes(hole) || hole === self || hole === element) hole = `_${hole}`;
      theorems.push({
        name: `${symbol}.mem`,
        statement: forall(self, forall(element, imp(hypothesis, pred("in", v(element), app(structure.projections[0]!, app(symbol, v(self))))))),
        proof: forallIntro(self, forallIntro(element, impIntro(hypothesis,
          eqElim(at(theorem(`${symbol}.${structure.fields[0]}`), v(self)), hole, pred("in", v(element), v(hole)), assume(hypothesis), true)))),
        parameters: [{ name: self, type: "Set" }, { name: element, type: "Set" }], requirementCount: 1, instance: true,
      });
    }
  });
  for (const item of theorems) {
    try { kernel.addTheorem(item.name, item.statement, item.proof); }
    catch (error) { throw new SurfaceError(header.number, `structure ${shortName(name)}: ${error instanceof Error ? error.message : String(error)}`); }
    environment.signatures.set(item.name, { kind: "theorem", parameters: item.parameters, requirementCount: item.requirementCount });
    scope.resolution?.register(item.name, scope.moduleName);
    if (item.instance) registerInstanceDeclaration(kernel, item.name, scope);
  }
  const record: SurfaceDatatypeRecord = {
    name: datatypeName, predicate: dataPredicate, parameters: [],
    constructors: [{ name: constructorName, fields: fieldNames.map(field => ({ name: field, type: "Set" })) }],
    structure: {
      predicate: name, parameters: parameterNames, fields: fieldNames, projections, constructor: constructorName, fieldStructures,
      fieldTypes: fields.map(item => item.type),
      parents: parents.map((parent, index) => ({
        name: parent.name, predicate: parent.predicate, structure: parent.structure.predicate, function: parentFunctions[index]!,
        fields: parent.map,
      })),
    },
  };
  environment.datatypes.set(dataPredicate, record);
  environment.namespaces.add(name);
  registerStructureNotation(record);
  inheritParentNotations(kernel, scope, environment, record, parents.map(parent => parent.structure));
  return { definitions: [datatypeName, ...projections, ...parentFunctions, name], theorems: theorems.map(item => item.name) };
}

/**
 * The hypothesis notations of a parent whose fields keep their names apply
 * to the child: `*` via `Monoid(G) for G.carrier` becomes `*` via `Ring(R)
 * for R.carrier` when the ring's multiplication is still `mul`. A template
 * reads a parent projection of the pattern variable as the child's own
 * projection, and the bare pattern variable as the parent value; a form
 * that mentions a renamed or fixed field, or whose carrier is not a
 * projection of the child, is not inherited.
 */
function inheritParentNotations(
  kernel: Kernel, scope: SurfaceScope, environment: SurfaceEnvironment, record: SurfaceDatatypeRecord,
  parentStructures: readonly SurfaceStructureRecord[],
): void {
  const structure = record.structure!;
  const self = "self";
  const cache = surfaceVisibilityCache(kernel, environment);
  const reachable = reachableImports(cache, environment, scope);
  const visible = environment.notations.filter(item => item.hypothesis && item.hypothesis.arity === 1 &&
    (item.module === undefined || item.module === scope.moduleName || reachable.has(item.module)));
  (structure.parents ?? []).forEach((parent, index) => {
    const parentStructure = parentStructures[index]!;
    for (const notation of visible) {
      const pattern = notation.hypothesis!;
      if (pattern.predicate !== parent.predicate) continue;
      const variable = pattern.names[0]!;
      const translate = (term: Term): Term | undefined => {
        if (term.tag === "var") return term.name === variable ? app(parent.function, v(self)) : term;
        if (term.tag !== "app") return term;
        if (term.args.length === 1 && term.args[0]!.tag === "var" && (term.args[0] as { name: string }).name === variable) {
          const position = parentStructure.projections.indexOf(term.fn);
          if (position >= 0) {
            const child = parent.fields[position];
            if (child !== parentStructure.fields[position]) return undefined;
            return app(structure.projections[structure.fields.indexOf(child)]!, v(self));
          }
        }
        const args = term.args.map(translate);
        return args.some(item => item === undefined) ? undefined : app(term.fn, ...(args as Term[]));
      };
      const output = pattern.output ? translate(pattern.output) : undefined;
      if (pattern.output && !output) continue;
      const carriers = pattern.carriers.map(translate);
      if (carriers.some(item => !item || item.tag !== "app" || !structure.projections.includes(item.fn))) continue;
      const fixed = pattern.fixed?.map(item => ({ target: item.target, template: translate(item.template) }));
      if (fixed?.some(item => !item.template)) continue;
      const hypothesis: HypothesisPattern = {
        ...pattern, predicate: structure.predicate, arity: 1 + structure.parameters.length,
        names: [self, ...structure.parameters], carriers: carriers as Term[],
        ...(output ? { output } : {}),
        ...(fixed ? { fixed: fixed as { target: number; template: Term }[] } : {}),
      };
      const same = environment.notations.some(item => item.token === notation.token && item.module === scope.moduleName &&
        item.fixity === notation.fixity && item.hypothesis && JSON.stringify(item.hypothesis) === JSON.stringify(hypothesis));
      if (same) continue;
      const inherited: SurfaceNotationRecord = { ...notation, hypothesis, module: scope.moduleName };
      environment.notations.push(inherited);
      registerNotationGuards(kernel, [inherited]);
    }
  });
}

/** The variables a formula binds anywhere. */
function boundFormulaVariables(formula: Formula, into = new Set<string>()): Set<string> {
  switch (formula.tag) {
    case "bottom": case "eq": case "pred": return into;
    case "imp": case "and": case "or": case "iff":
      boundFormulaVariables(formula.left, into);
      return boundFormulaVariables(formula.right, into);
    case "forall": case "exists":
      into.add(formula.variable);
      return boundFormulaVariables(formula.body, into);
  }
}

/** Replace several free variables at once; the replacements may mention the variables replaced. */
function substituteSimultaneously(formula: Formula, assignment: ReadonlyMap<string, Term>, reserved: ReadonlySet<string>): Formula {
  const temporaries = new Map<string, string>();
  let result = formula;
  for (const variable of assignment.keys()) {
    let temporary = `_${variable}`;
    while (reserved.has(temporary) || temporaries.has(temporary)) temporary = `_${temporary}`;
    temporaries.set(variable, temporary);
    result = substituteFormula(result, variable, v(temporary));
  }
  for (const [variable, value] of assignment) result = substituteFormula(result, temporaries.get(variable)!, value);
  return result;
}

/** Make the members of a structure print as `C.obj`, `Category.mk(…)`, and `Category.Data(C)`. */
function registerStructureNotation(record: SurfaceDatatypeRecord): void {
  const structure = record.structure;
  if (!structure) return;
  registerStructureMember(record.predicate, { structure: structure.predicate, member: "Data", role: "data" });
  registerStructureMember(structure.constructor, { structure: structure.predicate, member: "mk", role: "constructor" });
  structure.fields.forEach((field, index) =>
    registerStructureMember(structure.projections[index]!, { structure: structure.predicate, member: field, role: "projection" }));
  for (const parent of structure.parents ?? []) {
    registerStructureMember(parent.function, { structure: structure.predicate, member: parent.name, role: "parent" });
  }
}

/** Whether `field` names a field or a parent of the structure, either written `C.field`. */
function structureHasMember(record: SurfaceDatatypeRecord, field: string): boolean {
  return record.structure!.fields.includes(field) || (record.structure!.parents ?? []).some(parent => parent.name === field);
}

/** The structures declared in modules this scope can see. */
function visibleStructures(kernel: Kernel, scope: SurfaceScope): SurfaceDatatypeRecord[] {
  const environment = surfaceEnvironments.get(kernel);
  if (!environment) return [];
  return [...environment.datatypes.values()].filter(item => item.structure && visibleDeclaration(item.name, scope));
}

/** The structure record whose predicate or data predicate is `predicate`. */
function structureOfPredicate(kernel: Kernel, predicate: string): SurfaceDatatypeRecord | undefined {
  const environment = surfaceEnvironments.get(kernel);
  if (!environment) return undefined;
  return [...environment.datatypes.values()].find(item => item.structure &&
    (item.structure.predicate === predicate || item.predicate === predicate));
}

/** The projection record declaring a function symbol, if it is one. */
function projectionOf(kernel: Kernel, symbol: string): { readonly record: SurfaceDatatypeRecord; readonly index: number } | undefined {
  const environment = surfaceEnvironments.get(kernel);
  if (!environment) return undefined;
  for (const record of environment.datatypes.values()) {
    const index = record.structure?.projections.indexOf(symbol) ?? -1;
    if (index >= 0) return { record, index };
  }
  return undefined;
}

/**
 * `C.obj`, and `obj(C)` when no declared function answers to `obj`: the
 * projection of the one visible structure with that field, or, among
 * several, of the structure a hypothesis in scope gives the receiver, the
 * structure a soft-typed field names when the receiver is itself a
 * projection, or the result type of the receiver's head. Otherwise the
 * error names the qualified spellings.
 */
function structureProjection(
  kernel: Kernel, scope: SurfaceScope, field: string, receiver: Term, line: number,
): Term | undefined {
  const candidates = visibleStructures(kernel, scope).filter(item => structureHasMember(item, field));
  if (candidates.length === 0) return undefined;
  const chosen = candidates.length === 1 ? candidates[0]! : selectStructureForReceiver(kernel, scope, receiver, candidates);
  if (!chosen) {
    const spellings = candidates.map(item => `${shortName(item.structure!.predicate)}.${field}(${formatTerm(receiver)})`);
    throw new SurfaceError(line, `ambiguous projection ${field} of ${formatTerm(receiver)}; no hypothesis in scope says which structure ${formatTerm(receiver)} is; write ${spellings.join(" or ")}`);
  }
  const parent = (chosen.structure!.parents ?? []).find(item => item.name === field);
  if (parent) return app(parent.function, receiver);
  return app(chosen.structure!.projections[chosen.structure!.fields.indexOf(field)]!, receiver);
}

const receiverParameterCache = new WeakMap<Kernel, Map<string, ReadonlyMap<number, string>>>();

/**
 * The parameters a declared symbol treats as values of a structure: those
 * its defining properties apply the structure's projections or predicate to,
 * or pass to a symbol that does. `hom(C, a, b)` treats `C` as a category, and
 * so does `IsProduct(C, a, b, p, p1, p2)` through `hom`. A parameter used
 * as two structures is left out.
 */
function receiverParameters(kernel: Kernel, symbol: string, visiting = new Set<string>()): ReadonlyMap<number, string> {
  let cache = receiverParameterCache.get(kernel);
  if (!cache) { cache = new Map(); receiverParameterCache.set(kernel, cache); }
  const known = cache.get(symbol);
  if (known) return known;
  const result = new Map<number, string>();
  const projection = projectionOf(kernel, symbol);
  if (projection) { result.set(0, projection.record.structure!.predicate); cache.set(symbol, result); return result; }
  const structure = structureOfPredicate(kernel, symbol);
  if (structure) { result.set(0, structure.structure!.predicate); cache.set(symbol, result); return result; }
  const record = kernel.definitions.get(symbol);
  if (!record || record.parameters.length === 0 || visiting.has(symbol)) return result;
  visiting.add(symbol);
  const mark = (argument: Term, structureName: string): void => {
    if (argument.tag !== "var") return;
    const index = record.parameters.indexOf(argument.name);
    if (index < 0) return;
    const previous = result.get(index);
    if (previous === undefined) result.set(index, structureName);
    else if (previous !== structureName) result.set(index, "");
  };
  const visitApplication = (applied: string, args: readonly Term[]): void => {
    if (applied === symbol) return;
    for (const [index, structureName] of receiverParameters(kernel, applied, visiting)) {
      if (structureName && args[index]) mark(args[index]!, structureName);
    }
  };
  const visitTerm = (term: Term): void => {
    if (term.tag !== "app") return;
    visitApplication(term.fn, term.args);
    term.args.forEach(visitTerm);
  };
  const visitFormula = (formula: Formula): void => {
    switch (formula.tag) {
      case "bottom": return;
      case "eq": visitTerm(formula.left); visitTerm(formula.right); return;
      case "pred": visitApplication(formula.pred, formula.args); formula.args.forEach(visitTerm); return;
      case "imp": case "and": case "or": case "iff": visitFormula(formula.left); visitFormula(formula.right); return;
      case "forall": case "exists": visitFormula(formula.body); return;
    }
  };
  for (const property of record.properties.values()) visitFormula(property);
  visiting.delete(symbol);
  cache.set(symbol, result);
  return result;
}

/** The head symbol of a plain definition's body, `Functor.mk` for `identityFunctor(C) := Functor.mk(…)`. */
function definitionHeadSymbol(kernel: Kernel, symbol: string): string | undefined {
  let head = symbol;
  for (let depth = 0; depth < 16; depth += 1) {
    const record = kernel.definitions.get(head);
    if (record?.kind !== "function") return head === symbol ? undefined : head;
    let equation = record.properties.get("equation");
    while (equation?.tag === "forall") equation = equation.body;
    if (equation?.tag !== "eq" || equation.right.tag !== "app") return head === symbol ? undefined : head;
    head = equation.right.fn;
  }
  return head;
}

/** The field names of the ring structure, in order. */
const RING_STRUCTURE_FIELDS = ["carrier", "add", "zero", "neg", "mul", "one"] as const;

/**
 * The ring scope a bundled hypothesis supplies for a variable: under
 * `CommRing(R)`, or any fact whose definition applies the ring structure's
 * projections to `R`, the name `R` before `[` is the scope
 * `(R.carrier, R.add, R.zero, R.neg, R.mul, R.one)`, so `R[0]`, `R[1]`, and
 * `R[2 * x]` are the ring's own constants and numerals.
 */
function bundledRingScope(kernel: Kernel, scope: SurfaceScope, name: string, variables: ReadonlySet<string>): RingNotation | undefined {
  const record = visibleStructures(kernel, scope).find(item => item.structure!.fields.length === RING_STRUCTURE_FIELDS.length &&
    RING_STRUCTURE_FIELDS.every((field, index) => item.structure!.fields[index] === field));
  if (!record) return undefined;
  const structure = record.structure!;
  // A variable under a local hypothesis, or a declared constant such as
  // `integerRing` under a closed instance `CommRing(integerRing)`.
  const constant = variables.has(name) ? undefined : resolveOptional(name, scope, candidate => kernel.functions.get(candidate) === 0);
  if (!variables.has(name) && !constant) return undefined;
  const receiver = constant ? app(constant) : v(name);
  const facts = constant ? closedInstanceFacts(kernel, scope)
    : [...expandedLocalFormulas(kernel, scope), ...binderAssumptions([...(scope.binderTypes?.values() ?? [])])];
  const supplied = facts.some(fact => fact.tag === "pred" && fact.args.some((argument, index) =>
    termEquals(argument, receiver) &&
    (fact.pred === structure.predicate || fact.pred === record.predicate ? index === 0
      : receiverParameters(kernel, fact.pred).get(index) === structure.predicate)));
  if (!supplied) return undefined;
  const call1 = resolveOptional("apply", scope, candidate => kernel.functions.get(candidate) === 2);
  const call2 = resolveOptional("call2", scope, candidate => kernel.functions.get(candidate) === 3);
  if (!call1 || !call2) return undefined;
  const [carrier, add, zero, neg, mul, one] = structure.projections.map(projection => app(projection, receiver)) as [Term, Term, Term, Term, Term, Term];
  return { name, carrier, add, zero, neg, mul, one, call1, call2 };
}

/**
 * The ring scope of a term built by the ring constructor, or by a
 * definition whose body is one, `polynomialRing(R, I)[2]`, when an instance
 * supplies its ring structure under the facts in scope.
 */
function bundledRingScopeOfTerm(kernel: Kernel, scope: SurfaceScope, term: Term): RingNotation | undefined {
  const record = structureValueOf(kernel, scope, term);
  if (!record || record.structure!.fields.length !== RING_STRUCTURE_FIELDS.length ||
      !RING_STRUCTURE_FIELDS.every((field, index) => record.structure!.fields[index] === field)) return undefined;
  const structure = record.structure!;
  const local = expandedLocalFormulas(kernel, scope);
  const facts = [...local, ...instanceStructureFacts(kernel, scope, term, local)];
  const supplied = facts.some(fact => fact.tag === "pred" && fact.args.some((argument, index) =>
    termEquals(argument, term) &&
    (fact.pred === structure.predicate || fact.pred === record.predicate ? index === 0
      : receiverParameters(kernel, fact.pred).get(index) === structure.predicate)));
  if (!supplied) return undefined;
  const call1 = resolveOptional("apply", scope, candidate => kernel.functions.get(candidate) === 2);
  const call2 = resolveOptional("call2", scope, candidate => kernel.functions.get(candidate) === 3);
  if (!call1 || !call2) return undefined;
  const [carrier, add, zero, neg, mul, one] = structure.projections.map(projection => app(projection, term)) as [Term, Term, Term, Term, Term, Term];
  return { name: formatTerm(term), carrier, add, zero, neg, mul, one, call1, call2 };
}

interface ReceiverUses {
  /** The fields written on the receiver, `R.carrier`. */
  readonly fields: ReadonlySet<string>;
  /** The applications the receiver is an argument of, `quotientRing(R, I)` as `quotientRing` at 0. */
  readonly applications: readonly { readonly symbol: string; readonly index: number }[];
}

const receiverUsesCache = new WeakMap<readonly SourceLine[], ReadonlyMap<string, ReceiverUses>>();

/**
 * How a declaration's text uses each dotted receiver: the fields written on
 * it, `R.carrier` and `R.mul` giving `R ↦ {carrier, mul}`, and the
 * applications it is an argument of, `quotientRing(R, I)`.
 */
function dottedFieldsOf(block: readonly SourceLine[]): ReadonlyMap<string, ReceiverUses> {
  const cached = receiverUsesCache.get(block);
  if (cached) return cached;
  const fields = new Map<string, Set<string>>();
  const applications = new Map<string, { symbol: string; index: number }[]>();
  const text = block.map(line => line.text).join("\n");
  for (const match of text.matchAll(/(?<![\p{L}\p{M}\p{N}_.])([\p{L}_][\p{L}\p{M}\p{N}_]*)\.([\p{L}_][\p{L}\p{M}\p{N}_]*)/gu)) {
    let set = fields.get(match[1]!);
    if (!set) { set = new Set(); fields.set(match[1]!, set); }
    set.add(match[2]!);
  }
  for (const match of text.matchAll(/(?<![\p{L}\p{M}\p{N}_])([\p{L}_][\p{L}\p{M}\p{N}_.]*)\(/gu)) {
    const open = match.index! + match[0].length - 1;
    let depth = 0;
    let close = -1;
    for (let cursor = open; cursor < text.length; cursor += 1) {
      if (text[cursor] === "(") depth += 1;
      else if (text[cursor] === ")") { depth -= 1; if (depth === 0) { close = cursor; break; } }
    }
    if (close < 0) continue;
    splitTopLevel(text.slice(open + 1, close), ",").forEach((argument, index) => {
      const name = argument.trim();
      if (!SIMPLE_IDENTIFIER.test(name)) return;
      let list = applications.get(name);
      if (!list) { list = []; applications.set(name, list); }
      list.push({ symbol: match[1]!, index });
    });
  }
  const result = new Map<string, ReceiverUses>();
  for (const name of new Set([...fields.keys(), ...applications.keys()])) {
    result.set(name, { fields: fields.get(name) ?? new Set(), applications: applications.get(name) ?? [] });
  }
  receiverUsesCache.set(block, result);
  return result;
}

function selectStructureForReceiver(
  kernel: Kernel, scope: SurfaceScope, receiver: Term, candidates: readonly SurfaceDatatypeRecord[],
): SurfaceDatatypeRecord | undefined {
  const facts = [...expandedLocalFormulas(kernel, scope), ...binderAssumptions([...(scope.binderTypes?.values() ?? [])])];
  const byHypothesis = candidates.filter(item => facts.some(fact => fact.tag === "pred" && fact.args.length > 0 &&
    (fact.pred === item.structure!.predicate || fact.pred === item.predicate) && termEquals(fact.args[0]!, receiver)));
  if (byHypothesis.length === 1) return byHypothesis[0];
  // A fact that already applies a structure's projections to the receiver,
  // directly or through a definition, as IsProduct(C, …) does to C.
  const used = new Set<string>();
  const visitApplication = (symbol: string, args: readonly Term[]): void => {
    for (const [index, structure] of receiverParameters(kernel, symbol)) {
      if (structure && args[index] && termEquals(args[index]!, receiver)) used.add(structure);
    }
  };
  const visitTerm = (term: Term): void => {
    if (term.tag !== "app") return;
    visitApplication(term.fn, term.args);
    term.args.forEach(visitTerm);
  };
  const visitFormula = (formula: Formula): void => {
    switch (formula.tag) {
      case "bottom": return;
      case "eq": visitTerm(formula.left); visitTerm(formula.right); return;
      case "pred": visitApplication(formula.pred, formula.args); formula.args.forEach(visitTerm); return;
      case "imp": case "and": case "or": case "iff": visitFormula(formula.left); visitFormula(formula.right); return;
      case "forall": case "exists": visitFormula(formula.body); return;
    }
  };
  facts.forEach(visitFormula);
  const byUsage = candidates.filter(item => used.has(item.structure!.predicate));
  if (byUsage.length === 1) return byUsage[0];
  if (receiver.tag === "var") {
    // The declaration's own text decides when it leaves one candidate: the
    // fields written on the receiver, `R.carrier` beside `R.add` and
    // `R.mul` is the ring's since no group has `add`, and the symbols the
    // receiver is passed to, `quotientRing(R, I)` treating `R` as a ring.
    const written = scope.dottedFields?.get(receiver.name);
    if (!written) return undefined;
    const byFields = candidates.filter(item => [...written.fields].every(field => structureHasMember(item, field)));
    if (byFields.length === 1) return byFields[0];
    const passed = new Set<string>();
    for (const application of written.applications) {
      const symbol = resolveOptional(surfaceSymbol(application.symbol), scope, candidate => kernel.definitions.has(candidate));
      const structure = symbol ? receiverParameters(kernel, symbol).get(application.index) : undefined;
      if (structure) passed.add(structure);
    }
    const byPassing = byFields.filter(item => passed.has(item.structure!.predicate));
    return byPassing.length === 1 ? byPassing[0] : undefined;
  }
  if (receiver.tag !== "app") return undefined;
  // A receiver built by the constructor, or by a definition whose body is
  // the constructor applied, as `identityFunctor(C) := Functor.mk(…)`.
  const head = definitionHeadSymbol(kernel, receiver.fn) ?? receiver.fn;
  const constructed = candidates.filter(item => item.structure!.constructor === head);
  if (constructed.length === 1) return constructed[0];
  const projection = receiver.args.length === 1 ? projectionOf(kernel, receiver.fn) : undefined;
  const declaredType = projection
    ? projection.record.structure!.fieldStructures[projection.index] ?? undefined
    : surfaceEnvironments.get(kernel)?.signatures.get(receiver.fn)?.resultType;
  if (!declaredType) return undefined;
  const byType = candidates.filter(item => item.structure!.predicate === declaredType);
  return byType.length === 1 ? byType[0] : undefined;
}

function userTacticInvocation(
  kernel: Kernel, text: string, scope: SurfaceScope,
): { readonly tactic: SurfaceTacticRecord; readonly arguments: readonly string[]; readonly at?: string } | undefined {
  // `ring_additive at abelian`: a declared tactic applied at a hypothesis.
  const match = /^([^\s(]+)(?:\((.*)\))?(?:\s+at\s+(\S.*))?$/u.exec(text.trim());
  if (!match) return undefined;
  const environment = surfaceEnvironments.get(kernel);
  if (!environment) return undefined;
  const name = resolveOptional(match[1]!, scope, candidate => environment.tactics.some(item => item.name === candidate));
  if (!name) return undefined;
  const tactic = environment.tactics.find(item => item.name === name)!;
  const arguments_ = match[2]?.trim() ? splitTopLevel(match[2]!, ",").map(item => item.trim()) : [];
  return { tactic, arguments: arguments_, ...(match[3] ? { at: match[3].trim() } : {}) };
}

function isUserTacticInvocation(kernel: Kernel, text: string, scope: SurfaceScope): boolean {
  return userTacticInvocation(kernel, text, scope) !== undefined;
}

function expandUserTactic(kernel: Kernel, text: string, scope: SurfaceScope, line: number): string {
  let result = text;
  const seen = new Set<string>();
  for (let depth = 0; depth < 32; depth += 1) {
    const invocation = userTacticInvocation(kernel, result, scope);
    if (!invocation) return result;
    if (seen.has(invocation.tactic.name)) throw new SurfaceError(line, `recursive tactic expansion involving ${invocation.tactic.name}`);
    seen.add(invocation.tactic.name);
    if (invocation.arguments.length !== invocation.tactic.parameters.length) {
      throw new SurfaceError(line, `tactic ${invocation.tactic.name} expects ${invocation.tactic.parameters.length} arguments`);
    }
    result = invocation.tactic.body;
    invocation.tactic.parameters.forEach((parameter, index) => {
      result = result.replaceAll(`$${parameter}`, invocation.arguments[index]!);
    });
    if (invocation.at) result = `${result} at ${invocation.at}`;
  }
  throw new SurfaceError(line, "tactic expansion limit exceeded");
}

function elaborateNotation(
  kernel: Kernel,
  block: readonly SourceLine[],
  scope: SurfaceScope,
  environment: SurfaceEnvironment,
): void {
  const line = block[0]!;
  if (block.length !== 1) throw new SurfaceError(block[1]!.number, "notation declarations must fit on one line");
  const infix = /^notation\s+(infixl|infixr|infix)\s+(\d+)\s+"([^"]+)"\s*(?:=>|⇒)\s*(?:(reverse)\s+)?(\S+?)(?:\s+for\s+(\S+?)(?:\s*,\s*(\S+))?)?$/u.exec(line.text);
  const prefixOrPostfix = /^notation\s+(prefix|postfix)\s+(\d+)\s+"([^"]+)"\s*(?:=>|⇒)\s*(\S+?)(?:\s+for\s+(\S+))?$/u.exec(line.text);
  // A unary operator declaration, normalized to the prefix capture layout.
  const prefix = prefixOrPostfix ? [prefixOrPostfix[0], prefixOrPostfix[2], prefixOrPostfix[3], prefixOrPostfix[4], prefixOrPostfix[5]] as unknown as RegExpExecArray : null;
  const unaryFixity: "prefix" | "postfix" = prefixOrPostfix?.[1] === "postfix" ? "postfix" : "prefix";
  const alias = /^notation\s+alias\s+"([\p{L}_][\p{L}\p{M}\p{N}_]*)"\s*(?:=>|⇒)\s*(\S+)$/u.exec(line.text);
  if (alias) { elaborateAliasNotation(kernel, line, scope, environment, alias[1]!, alias[2]!); return; }
  // `notation binder "∑" => realPartialSum for Real`: the big operator
  // `∑ k < n, uₖ` is realPartialSum(u, n), and prints that way again.
  const binder = /^notation\s+binder\s+"(\S+)"\s*(?:=>|⇒)\s*(\S+?)(?:\s+for\s+(\S+))?$/u.exec(line.text);
  if (binder) { elaborateBinderNotation(kernel, line, scope, environment, binder[1]!, binder[2]!, binder[3]); return; }
  // `notation sequence taylorTerms`: the graph is written in a big operator
  // by its value, `∑ k ≤ n, f⁽ᵏ⁾(A) * (B - A) ^ k / k!`, and prints that way.
  const sequence = /^notation\s+sequence\s+(\S+)$/u.exec(line.text);
  if (sequence) { elaborateSequenceNotation(kernel, line, scope, environment, sequence[1]!); return; }
  // `notation coercion realNat for Nat, Real`: a natural number in a real
  // position is read as realNat(n) and prints without the cast.
  const coercion = /^notation\s+coercion\s+(\S+)\s+for\s+(\S+?)\s*,\s*(\S+)$/u.exec(line.text);
  if (coercion) { elaborateCoercionNotation(kernel, line, scope, environment, coercion[1]!, coercion[2]!, coercion[3]!); return; }
  // `notation mixfix "_ : _ → _" => FunctionBetween`: a predicate written
  // with its arguments in the placeholders, around the literal tokens.
  // `notation mixfix "_ : _ ⟶ _" => Morphism(M, dom, cod, _, _, _) via hypothesis Category(O, M, dom, cod, comp, id) for O`:
  // the named target arguments are read off a matching hypothesis in scope,
  // the placeholders are written, and `for O` names the objects.
  const mixfixVia = /^notation\s+mixfix\s+"([^"]+)"\s*(?:=>|⇒)\s*(\S+?)\((.*?)\)\s+via\s+hypothesis\s+(\S+?)\((.*?)\)(?:\s+for\s+(.+))?$/u.exec(line.text);
  if (mixfixVia) {
    elaborateMixfixHypothesisNotation(kernel, line, scope, environment, mixfixVia[1]!, mixfixVia[2]!, mixfixVia[3]!,
      mixfixVia[4]!, mixfixVia[5]!, mixfixVia[6]);
    return;
  }
  // `notation guard "_ : _ ⥤ _" => Functor`: a mixfix predicate form whose
  // predicate is a transparent guard, opened to its conjuncts wherever local
  // evidence is consulted.
  const mixfix = /^notation\s+(mixfix|guard)\s+"([^"]+)"\s*(?:=>|⇒)\s*(\S+)$/u.exec(line.text);
  if (mixfix) { elaborateMixfixNotation(kernel, line, scope, environment, mixfix[2]!, mixfix[3]!, mixfix[1] === "guard"); return; }
  // `notation scoped IsIdeal(R, I) => IsIdeal(R.carrier, R.add, R.zero, R.neg, R.mul, I)`:
  // under a ring scope the written form names the scope in place of its pieces.
  const scoped = /^notation\s+scoped\s+([\p{L}_][\p{L}\p{M}\p{N}_]*)\((.*?)\)\s*(?:=>|⇒)\s*(\S+?)\((.*)\)$/u.exec(line.text);
  if (scoped) { elaborateScopedNotation(kernel, line, scope, environment, scoped[1]!, scoped[2]!, scoped[3]!, scoped[4]!); return; }
  const numeral = /^notation\s+numeral\s+"(\d+)"\s*(?:=>|⇒)\s*(\S+?)\s+for\s+(\S+)$/u.exec(line.text);
  // `notation infixr 70 "∘" => call2 via hypothesis Category(O, M, dom, cod, _, id) for M`:
  // the operation is the `_` argument of a matching hypothesis in scope, and
  // `for M` names the pattern variable whose members the operands are.
  // `notation postfix 90 "⁻¹" => apply(inv(G), _) via hypothesis Group(G) for carrier(G)`
  // reads a unary operation off the hypothesis the same way.
  // `notation function "ker(f)" => ringKernel(f, R, S[0]) via hypothesis RingHom(f, R, S)`:
  // a function written with an identifier; the parameters in the token are
  // its written arguments, and the hypothesis supplies the rest.
  const functionVia = /^notation\s+function\s+"([\p{L}_][\p{L}\p{M}\p{N}_]*)\(([^)]*)\)"\s*(?:=>|⇒)\s*(.+?)\s+via\s+hypothesis\s+(\S+?)\((.*?)\)(?:\s+for\s+(.+))?$/u.exec(line.text);
  if (functionVia) {
    elaborateFunctionHypothesisNotation(kernel, line, scope, environment, functionVia[1]!, functionVia[2]!,
      functionVia[3]!, functionVia[4]!, functionVia[5]!, functionVia[6]);
    return;
  }
  const hypothesisVia = /^notation\s+(infixl|infixr|infix|prefix|postfix)\s+(\d+)\s+"([^"]+)"\s*(?:=>|⇒)\s*(.+?)\s+via\s+hypothesis\s+(\S+?)\((.*?)\)\s+for\s+(.+)$/u.exec(line.text);
  if (hypothesisVia) {
    elaborateHypothesisNotation(kernel, line, scope, environment, hypothesisVia[1]!, hypothesisVia[2]!, hypothesisVia[3]!,
      hypothesisVia[4]!, hypothesisVia[5]!, hypothesisVia[6]!, hypothesisVia[7]!);
    return;
  }
  // `notation constant "⊥" => bot(P) via hypothesis BoundedLattice(P) for P.points`:
  // a constant of the structure, a term over the pattern variables, read
  // off the hypothesis in scope and printed back with the token.
  const constantVia = /^notation\s+constant\s+"([^"]+)"\s*(?:=>|⇒)\s*(.+?)\s+via\s+hypothesis\s+(\S+?)\((.*?)\)\s+for\s+(.+)$/u.exec(line.text);
  if (constantVia) {
    elaborateHypothesisNotation(kernel, line, scope, environment, "constant", "1000", constantVia[1]!,
      constantVia[2]!, constantVia[3]!, constantVia[4]!, constantVia[5]!);
    return;
  }
  const infixVia = /^notation\s+(infixl|infixr|infix)\s+(\d+)\s+"([^"]+)"\s*(?:=>|⇒)\s*(\S+)\s+via\s+(\S+\(.*\))\s+for\s+(\S+?)(?:\s*,\s*(\S+))?$/u.exec(line.text);
  const prefixVia = /^notation\s+prefix\s+(\d+)\s+"([^"]+)"\s*(?:=>|⇒)\s*(\S+)\s+via\s+(\S+\(.*\))\s+for\s+(\S+)$/u.exec(line.text);
  const numeralVia = /^notation\s+numeral\s+"(\d+)"\s+via\s+(\S+\(.*\))\s+for\s+(\S+)$/u.exec(line.text);
  // `notation numeral _ => f(a, b, _) for T`: every literal n of type T is
  // f(a, b, n), so one declaration covers all numerals.
  const numeralTemplate = /^notation\s+numeral\s+_\s*(?:=>|⇒)\s*(\S+?)\((.*)\)\s+for\s+(\S+)$/u.exec(line.text);
  if (!infix && !prefix && !numeral && !infixVia && !prefixVia && !numeralVia && !numeralTemplate) {
    throw new SurfaceError(line.number, 'expected infix, prefix, postfix, alias, or typed numeral notation');
  }
  const via = Boolean(infixVia || prefixVia || numeralVia);
  const fixity = numeralVia || numeralTemplate ? "numeral" : prefixVia ? "prefix" : infixVia?.[1] ??
    (numeral ? "numeral" : prefix ? unaryFixity : infix![1]!);
  const rawPrecedence = numeralVia || numeralTemplate ? "1000" : prefixVia ? prefixVia[1]! : infixVia ? infixVia[2]! :
    (numeral ? "1000" : prefix ? prefix[1]! : infix![2]!);
  const token = numeralTemplate ? "_" : numeralVia ? numeralVia[1]! : prefixVia ? prefixVia[2]! : infixVia ? infixVia[3]! :
    (numeral ? numeral[1]! : prefix ? prefix[2]! : infix![3]!);
  const reverse = via || prefix || numeral || numeralTemplate ? undefined : infix![4];
  let rawTarget = numeralTemplate ? numeralTemplate[1]! : numeralVia ? undefined : prefixVia ? prefixVia[3]! : infixVia ? infixVia[4]! :
    (numeral ? numeral[2]! : prefix ? prefix[3]! : infix![5]!);
  const instanceQuery = numeralTemplate ? undefined : numeralVia ? numeralVia[2]! : prefixVia ? prefixVia[4]! : infixVia?.[5];
  const rawOperandType = numeralTemplate ? numeralTemplate[3]! : numeralVia ? numeralVia[3]! : prefixVia ? prefixVia[5]! : infixVia ? infixVia[6]! :
    (numeral ? numeral[3]! : prefix ? prefix[4] : infix![6]);
  const rawRightOperandType = infixVia ? infixVia[7] : infix?.[7];
  const precedence = Number(rawPrecedence);
  if (!Number.isSafeInteger(precedence) || precedence < 0 || precedence > 1_000) {
    throw new SurfaceError(line.number, "notation precedence must be an integer from 0 to 1000");
  }
  // An infix operator may also be a word, as in `n choose k`; it is read
  // only between two operands, so it never shadows a name.
  const wordToken = /^[\p{L}_][\p{L}\p{M}\p{N}_]*$/u.test(token!);
  // An indexed postfix token, `⁽_⁾`, writes its index between the two
  // halves in superscript: f⁽ᵏ⁾ is iteratedDerivative(f, k).
  const indexedToken = fixity === "postfix" && /^[^\p{L}\p{M}\p{N}\s_(),."]+_[^\p{L}\p{M}\p{N}\s_(),."]+$/u.test(token!);
  // Superscript digits are punctuation here, so that ⁻¹ is a token, and so
  // are modifier letters, so that a postfix ᵀ or ᶜ is one.
  const modifierToken = fixity === "postfix" && /^(?:[^\p{L}\p{M}\p{Nd}\s_(),."]|\p{Lm})+$/u.test(token!);
  if (fixity !== "numeral" && !indexedToken && !modifierToken && !/^[^\p{L}\p{M}\p{N}\s_(),."]+$/u.test(token!) &&
      !(wordToken && (fixity === "infix" || fixity === "infixl" || fixity === "infixr"))) {
    throw new SurfaceError(line.number, "a notation token must be non-alphanumeric punctuation without whitespace, a modifier letter such as ᵀ for a postfix operator, or a word for an infix operator");
  }
  if (["=", "≠", "∈", "∉", "→", "↔", "∧", "∨"].includes(token!)) {
    throw new SurfaceError(line.number, `notation token ${token} is reserved by the formula grammar`);
  }
  const kind = fixity === "infix" ? "predicate" : "function";
  if (reverse && kind !== "predicate") throw new SurfaceError(line.number, "reverse notation is only valid for binary predicates");
  let leadingArguments: readonly Term[] | undefined;
  let definitionTarget: string | undefined;
  if (instanceQuery) {
    const query = /^(\S+?)\((.*)\)$/u.exec(instanceQuery);
    if (!query) throw new SurfaceError(line.number, "malformed notation instance query");
    const predicateName = resolveExisting(surfaceSymbol(query[1]!), scope,
      candidate => kernel.predicates.has(candidate), line.number, "instance predicate");
    const pieces = splitTopLevel(query[2]!, ",");
    const holes = pieces.flatMap((piece, index) => piece.trim() === "_" ? [index] : []);
    if (holes.length !== 1) throw new SurfaceError(line.number, "notation instance query must contain exactly one `_` output");
    const arguments_ = pieces.map(piece => piece.trim() === "_" ? undefined :
      parseTerm(piece, kernel, new Set(), line.number, scope));
    let resolved: InstanceSynthesisResult | undefined;
    try {
      resolved = prepareInstanceProver(kernel, visibleInstanceNames(kernel, scope), [], [], {}, scopeVisibility(kernel, scope)).resolve(predicateName, arguments_);
    } catch (error) {
      if (error instanceof InstanceResolutionError || error instanceof InstanceResolutionLimitError) {
        throw new SurfaceError(line.number, error.message);
      }
      throw error;
    }
    if (!resolved) throw new SurfaceError(line.number, `no instance resolves notation query ${instanceQuery}`);
    const operation = resolved.arguments[holes[0]!]!;
    if (fixity === "numeral") {
      if (operation.tag !== "app" || freeTermVariables(operation).size !== 0) {
        throw new SurfaceError(line.number, "a numeral instance output must be a closed function expression");
      }
      rawTarget = operation.fn;
      leadingArguments = operation.args;
    } else {
      leadingArguments = [operation];
      if (operation.tag === "app" && operation.args.length === 0) definitionTarget = operation.fn;
    }
  }
  if (numeralTemplate) {
    const pieces = splitTopLevel(numeralTemplate[2]!, ",").map(piece => piece.trim());
    if (pieces.length === 0 || pieces.at(-1) !== "_" || pieces.slice(0, -1).includes("_")) {
      throw new SurfaceError(line.number, "a numeral template takes the literal as its last argument, written `_`");
    }
    leadingArguments = pieces.slice(0, -1).map(piece => parseTerm(piece, kernel, new Set(), line.number, scope));
  }
  const unary = fixity === "prefix" || fixity === "postfix";
  const target = resolveExisting(surfaceSymbol(rawTarget!), scope, candidate =>
    kind === "function" ? kernel.functions.get(candidate) ===
      ((fixity === "numeral" ? (numeralTemplate ? 1 : 0) : unary ? (indexedToken ? 2 : 1) : 2) + (leadingArguments?.length ?? 0)) :
      kernel.predicates.get(candidate) === 2 + (leadingArguments?.length ?? 0),
  line.number, `${fixity === "numeral" ? "nullary" : unary ? "unary" : "binary"} ${kind} notation target`);
  const operandType = rawOperandType
    ? resolveExisting(surfaceSymbol(rawOperandType), scope,
      candidate => kernel.predicates.get(candidate) === 1, line.number, "unary soft type for notation")
    : undefined;
  const rightOperandType = rawRightOperandType
    ? resolveExisting(surfaceSymbol(rawRightOperandType), scope,
      candidate => kernel.predicates.get(candidate) === 1, line.number, "right unary soft type for notation")
    : undefined;
  const leftOperandType = rightOperandType ? operandType : undefined;
  const homogeneousOperandType = rightOperandType ? undefined : operandType;
  const sameScope = environment.notations.find(item =>
    item.token === token && item.module === scope.moduleName &&
    item.operandType === homogeneousOperandType && item.leftOperandType === leftOperandType &&
    item.rightOperandType === rightOperandType &&
    (item.fixity ?? "infix") === (fixity === "prefix" || fixity === "postfix" || fixity === "numeral" ? fixity : "infix"));
  if (sameScope) throw new SurfaceError(line.number, `notation ${token} is already declared in this module`);
  environment.notations.push({
    token: token!, precedence,
    ...(fixity === "prefix" || fixity === "postfix" || fixity === "numeral" ? { fixity } : {}),
    associativity: fixity === "infixl" ? "left" : fixity === "infixr" ? "right" : "none",
    kind, reversed: Boolean(reverse), target,
    ...(definitionTarget ? { definitionTarget } : {}),
    ...(leadingArguments ? { leadingArguments } : {}),
    ...(homogeneousOperandType ? { operandType: homogeneousOperandType } : {}),
    ...(leftOperandType ? { leftOperandType } : {}),
    ...(rightOperandType ? { rightOperandType } : {}),
    // A record declared before the module graph has no module; leaving the
    // key out keeps the record identical after a JSON round trip.
    ...(scope.moduleName ? { module: scope.moduleName } : {}),
  });
}

/**
 * `notation infixr 70 "∘" => call2 via hypothesis Category(O, M, dom, cod, _, id) for M`.
 * The predicate's arguments are pattern variables except for one `_`, the
 * operation; `for M` names the pattern variable that is the operands'
 * carrier. Nothing is resolved here: each use reads the operation off a
 * hypothesis in scope, and several declarations of the same token may name
 * different hypothesis shapes.
 */
function elaborateHypothesisNotation(
  kernel: Kernel, line: SourceLine, scope: SurfaceScope, environment: SurfaceEnvironment,
  fixity: string, rawPrecedence: string, token: string, rawTarget: string,
  rawPredicate: string, rawArguments: string, carrierName: string,
): void {
  const precedence = Number(rawPrecedence);
  if (!Number.isSafeInteger(precedence) || precedence < 0 || precedence > 1_000) {
    throw new SurfaceError(line.number, "notation precedence must be an integer from 0 to 1000");
  }
  // Superscript digits are punctuation here, so that ⁻¹ is a token, and so
  // are modifier letters, so that ᶜ is one.
  if (!/^(?:[^\p{L}\p{M}\p{Nd}\s_(),."]|\p{Lm})+$/u.test(token)) {
    throw new SurfaceError(line.number, "a hypothesis notation token must be non-alphanumeric punctuation without whitespace");
  }
  if (["=", "≠", "∈", "∉", "→", "↔", "∧", "∨"].includes(token)) {
    throw new SurfaceError(line.number, `notation token ${token} is reserved by the formula grammar`);
  }
  const unary = fixity === "prefix" || fixity === "postfix";
  const constant = fixity === "constant";
  const pieces = splitTopLevel(rawArguments, ",").map(piece => piece.trim());
  const predicate = resolveExisting(surfaceSymbol(rawPredicate), scope,
    candidate => kernel.predicates.get(candidate) === pieces.length, line.number, "hypothesis notation predicate");
  const holes = pieces.flatMap((piece, index) => piece === "_" ? [index] : []);
  const names = pieces.filter(piece => piece !== "_");
  if (names.some(piece => !SIMPLE_IDENTIFIER.test(piece)) || new Set(names).size !== names.length) {
    throw new SurfaceError(line.number, "the arguments of a hypothesis notation pattern are distinct pattern variables");
  }
  const templateVariables = new Set(names);
  // The templates are read under the hypothesis itself, so that `C.obj`
  // under `Functor(F, C, D)` finds the category the guard opens to.
  const templateScope: SurfaceScope = { ...scope, localFormulas: () => [pred(predicate, ...pieces.map(v))] };
  const template = (text: string, role: string): Term => {
    try { return parseTerm(text, kernel, templateVariables, line.number, templateScope); }
    catch (error) {
      if (!(error instanceof SurfaceError)) throw error;
      throw new SurfaceError(line.number, `the ${role} ${text} must be a term over the pattern variables of ${shortName(predicate)}: ${error.message}`);
    }
  };
  // `call2 via hypothesis Category(O, M, dom, cod, _, id)` reads the operation
  // off the `_` hole; `call2(comp(C), _, _) via hypothesis Category(C)` builds
  // it from the pattern variables.
  const written = /^(\S+?)\((.*)\)$/u.exec(rawTarget);
  let output: Term | undefined;
  let targetName: string;
  // `Le(P, _, _) via hypothesis PartialOrder(P)`: an infix predicate whose
  // fixed arguments are read off the hypothesis and whose two placeholders
  // are the operands; the operands' carrier decides between it and the
  // typed declarations of the same token.
  let fixed: { readonly target: number; readonly template: Term }[] | undefined;
  let predicateTarget: string | undefined;
  let structureOperand: string | undefined;
  if (constant) {
    if (holes.length) throw new SurfaceError(line.number, "a hypothesis pattern has no `_` hole for a constant");
    output = template(rawTarget, "constant");
    targetName = output.tag === "app" ? output.fn : rawTarget;
  } else if (written) {
    if (holes.length) throw new SurfaceError(line.number, "a hypothesis pattern has no `_` hole when the target names the operation");
    targetName = written[1]!;
    const targetPieces = splitTopLevel(written[2]!, ",").map(piece => piece.trim());
    const operands = unary ? 1 : 2;
    const functionTarget = resolveOptional(surfaceSymbol(targetName), scope,
      candidate => kernel.functions.get(candidate) === operands + 1);
    predicateTarget = functionTarget === undefined && !unary ? resolveOptional(surfaceSymbol(targetName), scope,
      candidate => kernel.predicates.get(candidate) === targetPieces.length) : undefined;
    if (predicateTarget) {
      if (targetPieces.filter(piece => piece === "_").length !== 2 || targetPieces.length < 3) {
        throw new SurfaceError(line.number, "a binary hypothesis predicate target is written P(…, _, _), with two placeholders among its arguments");
      }
      fixed = targetPieces.flatMap((piece, index) => piece === "_" ? [] : [{ target: index, template: template(piece, "fixed argument") }]);
    } else if (!unary && targetPieces.length === 2 && targetPieces[0] !== "_" && targetPieces[1] === "_") {
      // `quotientGroup(G, _) via hypothesis Group(G) for G`: the left operand
      // is the structure itself and the target takes it with the right operand.
      output = template(targetPieces[0]!, "structure");
      structureOperand = targetPieces[0]!;
    } else {
      if (targetPieces.length !== operands + 1 || targetPieces[0] === "_" || targetPieces.slice(1).some(piece => piece !== "_")) {
        throw new SurfaceError(line.number, unary
          ? "a unary hypothesis notation target is written f(operation, _)"
          : "a binary hypothesis notation target is written op(operation, _, _) or f(structure, _)");
      }
      output = template(targetPieces[0]!, "operation");
    }
  } else {
    if (holes.length !== 1) throw new SurfaceError(line.number, "a hypothesis notation pattern must contain exactly one `_` operation");
    targetName = rawTarget;
    output = v("_");
  }
  const carrier = template(carrierName, "carrier");
  if (freeTermVariables(carrier).size === 0) {
    throw new SurfaceError(line.number, `the carrier ${carrierName} must mention a pattern variable`);
  }
  if (structureOperand && !termEquals(carrier, output!)) {
    throw new SurfaceError(line.number, `a binary hypothesis notation target is written op(operation, _, _), or f(structure, _) with the structure named after for; the carrier ${carrierName} is not ${structureOperand}`);
  }
  const target = predicateTarget ?? (constant ? targetName : resolveExisting(surfaceSymbol(targetName), scope,
    candidate => kernel.functions.get(candidate) === (unary || structureOperand ? 2 : 3), line.number,
    unary ? "unary operation application target"
      : structureOperand ? "structure operation application target" : "binary operation application target"));
  const hypothesis: HypothesisPattern = fixed
    ? { predicate, arity: pieces.length, names: pieces, carriers: [carrier], fixed }
    : { predicate, arity: pieces.length, names: pieces, output: output!, carriers: [carrier],
      ...(structureOperand ? { structureOperand: true as const } : {}) };
  const recordFixity = unary || constant ? fixity as "prefix" | "postfix" | "constant" : undefined;
  const same = environment.notations.find(item => item.token === token && item.module === scope.moduleName &&
    item.fixity === recordFixity && item.hypothesis && JSON.stringify(item.hypothesis) === JSON.stringify(hypothesis));
  if (same) throw new SurfaceError(line.number, `notation ${token} is already declared in this module for this hypothesis`);
  const record: SurfaceNotationRecord = {
    token, precedence, associativity: fixity === "infixl" ? "left" : fixity === "infixr" ? "right" : "none",
    ...(recordFixity ? { fixity: recordFixity } : {}),
    kind: predicateTarget ? "predicate" : "function", reversed: false, target, hypothesis, ...(scope.moduleName ? { module: scope.moduleName } : {}),
  };
  environment.notations.push(record);
  registerNotationGuards(kernel, [record]);
}

/**
 * `notation function "ker(f)" => ringKernel(f, R, S[0]) via hypothesis RingHom(f, R, S)`:
 * a function written with an identifier. The parameters in the token are
 * the written arguments, and the target is a term over them and the pattern
 * variables of the hypothesis, which supplies the rest. A parameter named
 * as a pattern variable is that argument of the hypothesis, so `ker(f)` is
 * read off the hypothesis about `f`; `for X.carrier` names the carrier the
 * free parameters lie in, which chooses between several hypotheses.
 */
function elaborateFunctionHypothesisNotation(
  kernel: Kernel, line: SourceLine, scope: SurfaceScope, environment: SurfaceEnvironment,
  token: string, rawParameters: string, rawTarget: string, rawPredicate: string, rawArguments: string,
  carrierName: string | undefined,
): void {
  const parameters = splitTopLevel(rawParameters, ",").map(piece => piece.trim());
  if (!parameters.length || parameters.some(piece => !SIMPLE_IDENTIFIER.test(piece)) ||
      new Set(parameters).size !== parameters.length) {
    throw new SurfaceError(line.number, 'the parameters of a function notation are distinct identifiers, as in "ker(f)"');
  }
  const pieces = splitTopLevel(rawArguments, ",").map(piece => piece.trim());
  const predicate = resolveExisting(surfaceSymbol(rawPredicate), scope,
    candidate => kernel.predicates.get(candidate) === pieces.length, line.number, "hypothesis notation predicate");
  if (pieces.some(piece => !SIMPLE_IDENTIFIER.test(piece)) || new Set(pieces).size !== pieces.length) {
    throw new SurfaceError(line.number, "the arguments of a hypothesis pattern are distinct pattern variables");
  }
  const templateVariables = new Set([...pieces, ...parameters]);
  const templateScope: SurfaceScope = { ...scope, localFormulas: () => [pred(predicate, ...pieces.map(v))] };
  const template = (text: string, role: string): Term => {
    try { return parseTerm(text, kernel, templateVariables, line.number, templateScope); }
    catch (error) {
      if (!(error instanceof SurfaceError)) throw error;
      throw new SurfaceError(line.number, `the ${role} ${text} must be a term over the parameters and the pattern variables of ${shortName(predicate)}: ${error.message}`);
    }
  };
  const output = template(rawTarget, "target");
  const free = freeTermVariables(output);
  const unused = parameters.find(parameter => !free.has(parameter));
  if (unused !== undefined) {
    throw new SurfaceError(line.number, `the parameter ${unused} of ${token}(${parameters.join(", ")}) does not occur in ${rawTarget}`);
  }
  const carriers = carrierName === undefined ? [] : [template(carrierName.trim(), "carrier")];
  const hypothesis: HypothesisPattern = { predicate, arity: pieces.length, names: pieces, output, carriers, parameters };
  if (environment.notations.some(item => item.token === token && item.fixity === "function" && item.module === scope.moduleName &&
      JSON.stringify(item.hypothesis ?? null) === JSON.stringify(hypothesis))) {
    throw new SurfaceError(line.number, `notation ${token} is already declared in this module for this hypothesis`);
  }
  const record: SurfaceNotationRecord = {
    token, precedence: 1_000, fixity: "function", associativity: "none", kind: "function", reversed: false,
    target: output.tag === "app" ? output.fn : "$function", hypothesis, ...(scope.moduleName ? { module: scope.moduleName } : {}),
  };
  environment.notations.push(record);
  registerNotationGuards(kernel, [record]);
}

/**
 * `notation mixfix "_ : _ ⟶ _" => Morphism(M, dom, cod, _, _, _) via hypothesis Category(O, M, dom, cod, comp, id) for O`:
 * a typed binder or formula `f : a ⟶ b` is the predicate applied to the
 * arguments a matching hypothesis in scope supplies at the named positions
 * and to the written terms at the placeholders, in order. `for O` names the
 * pattern variable whose members the endpoints are, used with the other
 * fixed arguments to choose between several hypotheses. The predicate
 * becomes a transparent guard: a local fact of it is opened to its
 * definitional conjuncts wherever local evidence is consulted.
 */
function elaborateMixfixHypothesisNotation(
  kernel: Kernel, line: SourceLine, scope: SurfaceScope, environment: SurfaceEnvironment,
  pattern: string, rawTarget: string, rawTargetArguments: string, rawPredicate: string, rawArguments: string, carrierName: string | undefined,
): void {
  const trimmed = pattern.trim();
  const literals = mixfixLiterals(trimmed);
  if (!trimmed.startsWith("_") || !trimmed.endsWith("_") || literals.length < 1 ||
      literals.some(literal => !/^[^\p{L}\p{M}\p{N}\s_(),."]+$/u.test(literal))) {
    throw new SurfaceError(line.number, 'a mixfix pattern alternates placeholders and punctuation tokens, as in "_ : _ ⟶ _"');
  }
  const targetPieces = splitTopLevel(rawTargetArguments, ",").map(piece => piece.trim());
  const target = resolveExisting(surfaceSymbol(rawTarget), scope,
    candidate => kernel.predicates.get(candidate) === targetPieces.length, line.number,
    `mixfix notation target, a predicate of ${targetPieces.length} arguments`);
  const placeholders = targetPieces.flatMap((piece, index) => piece === "_" ? [index] : []);
  if (placeholders.length !== literals.length + 1) {
    throw new SurfaceError(line.number, `the target takes ${literals.length + 1} placeholder arguments \`_\`, one for each placeholder of the pattern`);
  }
  const pieces = splitTopLevel(rawArguments, ",").map(piece => piece.trim());
  const predicate = resolveExisting(surfaceSymbol(rawPredicate), scope,
    candidate => kernel.predicates.get(candidate) === pieces.length, line.number, "hypothesis notation predicate");
  if (pieces.some(piece => !SIMPLE_IDENTIFIER.test(piece)) || new Set(pieces).size !== pieces.length) {
    throw new SurfaceError(line.number, "the arguments of a hypothesis pattern are distinct pattern variables");
  }
  const templateVariables = new Set(pieces);
  const templateScope: SurfaceScope = { ...scope, localFormulas: () => [pred(predicate, ...pieces.map(v))] };
  const template = (text: string, role: string): Term => {
    try { return parseTerm(text, kernel, templateVariables, line.number, templateScope); }
    catch (error) {
      if (!(error instanceof SurfaceError)) throw error;
      throw new SurfaceError(line.number, `the ${role} ${text} must be a term over the pattern variables of ${shortName(predicate)}`);
    }
  };
  const fixed = targetPieces.flatMap((piece, index) =>
    piece === "_" ? [] : [{ target: index, template: template(piece, "fixed argument") }]);
  const carriers = carrierName === undefined ? [] :
    splitTopLevel(carrierName, ",").map(piece => template(piece.trim(), "carrier"));
  const hypothesis: HypothesisPattern = { predicate, arity: pieces.length, names: pieces, carriers, fixed };
  if (environment.notations.some(item => item.token === trimmed && item.fixity === "mixfix" && item.module === scope.moduleName &&
      JSON.stringify(item.hypothesis ?? null) === JSON.stringify(hypothesis))) {
    throw new SurfaceError(line.number, `notation ${trimmed} is already declared in this module for this hypothesis`);
  }
  const record: SurfaceNotationRecord = {
    token: trimmed, precedence: 0, fixity: "mixfix", associativity: "none", kind: "predicate", reversed: false, target,
    hypothesis, ...(scope.moduleName ? { module: scope.moduleName } : {}),
  };
  environment.notations.push(record);
  registerNotationGuards(kernel, [record]);
}

/**
 * `notation scoped IsIdeal(R, I) => IsIdeal(R.carrier, R.add, R.zero, R.neg, R.mul, I)`:
 * under a ring scope the written form names the scope in place of its
 * pieces. The written parameters are distinct pattern variables, and each
 * argument of the target is one of them passed through, or a piece of one
 * that must name an active scope, `R.add`. A parameter whose only piece is
 * the carrier also accepts an ordinary set. The target is a predicate or a
 * function of as many arguments as the expansion lists.
 */
function elaborateScopedNotation(
  kernel: Kernel, line: SourceLine, scope: SurfaceScope, environment: SurfaceEnvironment,
  head: string, rawParameters: string, rawTarget: string, rawArguments: string,
): void {
  const parameters = rawParameters.trim() ? splitTopLevel(rawParameters, ",").map(piece => piece.trim()) : [];
  if (!parameters.length || parameters.some(piece => !SIMPLE_IDENTIFIER.test(piece)) || new Set(parameters).size !== parameters.length) {
    throw new SurfaceError(line.number, `the parameters of the scoped notation ${head} are distinct pattern variables`);
  }
  const pieces = rawArguments.trim() ? splitTopLevel(rawArguments, ",").map(piece => piece.trim()) : [];
  const expansion: ScopedArgument[] = pieces.map(piece => {
    const dotted = /^([\p{L}_][\p{L}\p{M}\p{N}_]*)\.(carrier|add|zero|neg|mul|one)$/u.exec(piece);
    if (dotted) {
      if (!parameters.includes(dotted[1]!)) throw new SurfaceError(line.number, `${piece} is not a piece of a parameter of ${head}`);
      return { parameter: dotted[1]!, piece: dotted[2] as RingPiece };
    }
    if (!parameters.includes(piece)) {
      throw new SurfaceError(line.number, `the argument ${piece} of the target must be a parameter of ${head}, or a ring piece of one, as R.add`);
    }
    return { parameter: piece };
  });
  for (const parameter of parameters) {
    const uses = expansion.filter(argument => argument.parameter === parameter);
    if (!uses.length) throw new SurfaceError(line.number, `the parameter ${parameter} of ${head} is not used by the target`);
    if (uses.some(use => use.piece) && uses.some(use => !use.piece)) {
      throw new SurfaceError(line.number, `the parameter ${parameter} of ${head} names a ring scope in one argument and is passed through in another`);
    }
  }
  if (!expansion.some(argument => argument.piece)) {
    throw new SurfaceError(line.number, `the scoped notation ${head} names no ring scope piece, as R.carrier or R.mul, in the target`);
  }
  const symbol = surfaceSymbol(rawTarget);
  const predicate = resolveOptional(symbol, scope, candidate => kernel.predicates.get(candidate) === expansion.length);
  const fn = resolveOptional(symbol, scope, candidate => kernel.functions.get(candidate) === expansion.length);
  if (predicate && fn) {
    throw new SurfaceError(line.number, `ambiguous scoped notation target ${rawTarget}: a predicate and a function of ${expansion.length} arguments`);
  }
  const target = predicate ?? fn;
  if (!target) throw new SurfaceError(line.number, `unknown scoped notation target ${rawTarget}, a predicate or function of ${expansion.length} arguments`);
  if (environment.notations.some(item => item.fixity === "scoped" && item.token === head && item.module === scope.moduleName &&
      item.parameters?.length === parameters.length)) {
    throw new SurfaceError(line.number, `scoped notation ${head} of ${parameters.length} arguments is already declared in this module`);
  }
  environment.notations.push({
    token: head, precedence: 1_000, fixity: "scoped", associativity: "none", kind: predicate ? "predicate" : "function",
    reversed: false, target, parameters, expansion, ...(scope.moduleName ? { module: scope.moduleName } : {}),
  });
}

/**
 * The visible scoped notation a written name of `count` arguments selects,
 * or undefined; several declarations for one name and count are ambiguous.
 */
function scopedNotationFor(
  kernel: Kernel, scope: SurfaceScope, line: number, kind: "function" | "predicate", written: string, count: number,
): SurfaceNotationRecord | undefined {
  const candidates = visibleInfixNotationGroups(kernel, scope, line, kind, "scoped").get(shortName(written)) ?? [];
  const matching = candidates.filter(item => item.parameters?.length === count);
  if (matching.length > 1) {
    throw new SurfaceError(line, `ambiguous scoped notation ${written}; it is declared for ${matching.map(item => shortName(item.target)).join(" and ")}`);
  }
  return matching[0];
}

/**
 * The target's arguments for a written scoped form: a parameter passed
 * through is the written argument, a piece is read off the active ring
 * scope the written argument names, and a parameter used only as a carrier
 * may be an ordinary set.
 */
function expandScopedArguments(
  record: SurfaceNotationRecord, written: readonly string[], argument: (index: number) => Term,
  scope: SurfaceScope, line: number, head: string,
): Term[] {
  const rings = scope.ringAliases ?? scope.rings ?? [];
  const parsed = new Map<number, Term>();
  const term = (index: number): Term => {
    const cached = parsed.get(index);
    if (cached) return cached;
    const value = argument(index);
    parsed.set(index, value);
    return value;
  };
  return record.expansion!.map(item => {
    const index = record.parameters!.indexOf(item.parameter);
    if (!item.piece) return term(index);
    const name = written[index]!.trim();
    const ring = rings.find(candidate => candidate.name === name);
    if (ring) return ring[item.piece];
    if (record.expansion!.every(other => other.parameter !== item.parameter || other.piece === "carrier")) return term(index);
    throw new SurfaceError(line, `${head} argument ${index + 1} requires a scoped ring name; ${name} is not an active ring notation`);
  });
}

/**
 * Enter the predicates that hypothesis notations single out in the
 * type-system registry: the hypothesis shapes bind rule variables their
 * conclusions leave open, and a mixfix target is a transparent guard.
 */
function registerNotationGuards(kernel: Kernel, notations: readonly SurfaceNotationRecord[]): void {
  for (const notation of notations) {
    if (notation.fixity === "mixfix" && !notation.hypothesis) {
      registerGuardPredicate(kernel, notation.target, notation.transparent ? "transparent" : "binding", notation.module);
    }
    if (!notation.hypothesis) continue;
    registerGuardPredicate(kernel, notation.hypothesis.predicate, "binding", notation.module);
    // The predicate of a mixfix or infix form supplied by a hypothesis, such
    // as `Le(P, a, b)` for `a ≤ b`, opens to its definition wherever local
    // evidence is consulted.
    if (notation.fixity === "mixfix" || notation.kind === "predicate") {
      registerGuardPredicate(kernel, notation.target, "transparent", notation.module);
    }
  }
}

/** The literal tokens of a mixfix pattern such as `_ : _ → _`, between its placeholders. */
function mixfixLiterals(pattern: string): string[] {
  return pattern.split("_").slice(1, -1).map(piece => piece.trim());
}

/**
 * `notation mixfix "_ : _ → _" => FunctionBetween`: the pattern starts and
 * ends with a placeholder, placeholders alternate with literal punctuation
 * tokens, and the target is a predicate of as many arguments as there are
 * placeholders. The formula `f : A → B` is FunctionBetween(f, A, B) and
 * prints that way again when it stands on its own.
 */
function elaborateMixfixNotation(
  kernel: Kernel, line: SourceLine, scope: SurfaceScope, environment: SurfaceEnvironment, pattern: string, rawTarget: string,
  transparent = false,
): void {
  const trimmed = pattern.trim();
  const literals = mixfixLiterals(trimmed);
  if (!trimmed.startsWith("_") || !trimmed.endsWith("_") || literals.length < 1 ||
      literals.some(literal => !/^[^\p{L}\p{M}\p{N}\s_(),."]+$/u.test(literal))) {
    throw new SurfaceError(line.number, 'a mixfix pattern alternates placeholders and punctuation tokens, as in "_ : _ → _"');
  }
  const arity = literals.length + 1;
  const target = resolveExisting(surfaceSymbol(rawTarget), scope,
    candidate => kernel.predicates.get(candidate) === arity, line.number, `mixfix notation target, a predicate of ${arity} arguments`);
  if (environment.notations.some(item => item.token === trimmed && item.fixity === "mixfix" && item.module === scope.moduleName)) {
    throw new SurfaceError(line.number, `notation ${trimmed} is already declared in this module`);
  }
  const record: SurfaceNotationRecord = {
    token: trimmed, precedence: 0, fixity: "mixfix", associativity: "none", kind: "predicate", reversed: false, target,
    ...(transparent ? { transparent: true } : {}), ...(scope.moduleName ? { module: scope.moduleName } : {}),
  };
  environment.notations.push(record);
  registerNotationGuards(kernel, [record]);
}

/** A big operator over an index below a bound: `∑ k < n, uₖ` for a two-argument function of the sequence and the bound. */
function elaborateBinderNotation(
  kernel: Kernel, line: SourceLine, scope: SurfaceScope, environment: SurfaceEnvironment,
  token: string, rawTarget: string, rawType: string | undefined,
): void {
  if (/[\p{L}\p{N}_(),.\s"]/u.test(token)) throw new SurfaceError(line.number, "a binder token must be a symbol such as ∑");
  const target = resolveExisting(surfaceSymbol(rawTarget), scope,
    candidate => kernel.functions.get(candidate) === 2, line.number, "binder notation target taking the sequence and the bound");
  const operandType = rawType
    ? resolveExisting(surfaceSymbol(rawType), scope, candidate => kernel.predicates.get(candidate) === 1, line.number, "unary soft type for notation")
    : undefined;
  if (environment.notations.some(item => item.token === token && item.fixity === "binder" &&
      item.module === scope.moduleName && item.operandType === operandType)) {
    throw new SurfaceError(line.number, `notation ${token} is already declared in this module`);
  }
  environment.notations.push({
    token, precedence: 0, fixity: "binder", associativity: "none", kind: "function", reversed: false, target,
    ...(operandType ? { operandType } : {}), ...(scope.moduleName ? { module: scope.moduleName } : {}),
  });
}

/**
 * `notation sequence taylorTerms`: the bounded graph `taylorTerms(f, X, B)`,
 * defined by `defgraph` as the image of `k ↦ value` over its domain, is
 * written in a big operator by that value, `∑ k ≤ n, f⁽ᵏ⁾(A) * (B - A) ^ k / k!`
 * for `∑ k ≤ n, taylorTerms(f, A, B)(k)`, matching the body against the
 * value with the parameters as pattern variables, and such a sum prints
 * with the value written out. The template is read off the graph's
 * membership law, so nothing is declared twice.
 */
function elaborateSequenceNotation(
  kernel: Kernel, line: SourceLine, scope: SurfaceScope, environment: SurfaceEnvironment, rawTarget: string,
): void {
  const target = resolveExisting(surfaceSymbol(rawTarget), scope,
    candidate => kernel.definitions.get(candidate)?.kind === "replacement", line.number, "sequence notation graph defined by defgraph");
  const record = kernel.definitions.get(target)!;
  let membership = record.properties.get("membership");
  const bound: string[] = [];
  while (membership?.tag === "forall") { bound.push(membership.variable); membership = membership.body; }
  const image = membership?.tag === "iff" && membership.right.tag === "exists" && membership.right.body.tag === "and" &&
    membership.right.body.right.tag === "eq" ? membership.right : undefined;
  const pairing = image?.body.tag === "and" && image.body.right.tag === "eq" ? image.body.right.left : undefined;
  if (!image || !pairing || pairing.tag !== "app" || pairing.args.length !== 2 || shortName(pairing.fn) !== "orderedPair" ||
      pairing.args[0]!.tag !== "var" || pairing.args[0]!.name !== image.variable) {
    throw new SurfaceError(line.number, `${rawTarget} is not a graph of the form { (k ↦ value) | k ∈ A }`);
  }
  const token = shortName(target);
  if (environment.notations.some(item => item.fixity === "sequence" && item.target === target && item.module === scope.moduleName)) {
    throw new SurfaceError(line.number, `notation sequence ${rawTarget} is already declared in this module`);
  }
  environment.notations.push({
    token, precedence: 0, fixity: "sequence", associativity: "none", kind: "function", reversed: false, target,
    template: pairing.args[1]!, parameters: [...record.parameters], index: image.variable, ...(scope.moduleName ? { module: scope.moduleName } : {}),
  });
}

/**
 * `notation coercion realNat for Nat, Real`: an operand of the first sort
 * in a position of the second, an operand of a typed operator, a typed
 * comparison, or an equation whose other side has the second sort, is read
 * through the function, and prints without it where the position shows
 * the sort. Numerals keep their own typed declarations.
 */
function elaborateCoercionNotation(
  kernel: Kernel, line: SourceLine, scope: SurfaceScope, environment: SurfaceEnvironment,
  rawTarget: string, rawFrom: string, rawTo: string,
): void {
  const target = resolveExisting(surfaceSymbol(rawTarget), scope,
    candidate => kernel.functions.get(candidate) === 1, line.number, "unary coercion function");
  const operandType = resolveExisting(surfaceSymbol(rawFrom), scope,
    candidate => kernel.predicates.get(candidate) === 1, line.number, "unary soft type for the coercion's operand");
  const resultType = resolveExisting(surfaceSymbol(rawTo), scope,
    candidate => kernel.predicates.get(candidate) === 1, line.number, "unary soft type for the coercion's result");
  if (operandType === resultType) throw new SurfaceError(line.number, "a coercion must change the sort");
  if (environment.notations.some(item => item.fixity === "coercion" && item.module === scope.moduleName &&
      item.operandType === operandType && item.resultType === resultType)) {
    throw new SurfaceError(line.number, `a coercion from ${rawFrom} to ${rawTo} is already declared in this module`);
  }
  environment.notations.push({
    token: shortName(target), precedence: 1_000, fixity: "coercion", associativity: "none", kind: "function",
    reversed: false, target, operandType, resultType, ...(scope.moduleName ? { module: scope.moduleName } : {}),
  });
}

/**
 * `notation alias "C" => choose`: the function is written and printed as
 * `C(...)` wherever the alias is visible. A variable of the same name in
 * scope still denotes the variable.
 */
function elaborateAliasNotation(
  kernel: Kernel, line: SourceLine, scope: SurfaceScope, environment: SurfaceEnvironment, token: string, rawTarget: string,
): void {
  const target = resolveExisting(surfaceSymbol(rawTarget), scope, candidate => kernel.functions.has(candidate), line.number, "alias notation target");
  const sameScope = environment.notations.find(item => item.token === token && item.module === scope.moduleName && item.fixity === "alias");
  if (sameScope) throw new SurfaceError(line.number, `notation ${token} is already declared in this module`);
  environment.notations.push({
    token, precedence: 1_000, fixity: "alias", associativity: "none", kind: "function", reversed: false, target,
    ...(scope.moduleName ? { module: scope.moduleName } : {}),
  });
}

function elaborateEvaluation(kernel: Kernel, block: readonly SourceLine[], scope: SurfaceScope): SurfaceEvaluation {
  const line = block[0]!;
  if (block.length !== 1) throw new SurfaceError(block[1]!.number, "eval commands must fit on one line");
  const expression = line.text.slice("eval ".length).trim();
  if (!expression) throw new SurfaceError(line.number, "eval needs an expression");
  try {
    // Propositions are evaluated by proof search; the kernel has no Boolean
    // oracle. A displayed `true` therefore comes with a
    // kernel-checkable proof; `false` means the negation was proved.
    let formula: Formula | undefined;
    try { formula = parseFormula(expression, kernel, new Set(), line.number, scope); }
    catch (error) { if (!(error instanceof SurfaceError)) throw error; }
    if (formula) {
      const rules = evaluationRules(kernel);
      const settleStats: SettleStats = { rules: 0, termsVisited: 0, candidatesConsidered: 0, rewrites: 0 };
      let value: "true" | "false" | "unknown";
      try {
        settle(kernel, formula, { using: rules, stats: settleStats, fuel: 20_000, visibility: scopeVisibility(kernel, scope) });
        value = "true";
      } catch {
        try {
          settle(kernel, not(formula), { using: rules, stats: settleStats, fuel: 20_000, visibility: scopeVisibility(kernel, scope) });
          value = "false";
        } catch { value = "unknown"; }
      }
      return {
        line: line.number, expression, value, kind: "proposition",
        stats: { calls: settleStats.termsVisited, reductions: settleStats.rewrites, cacheHits: 0 },
      };
    }
    const term = parseTerm(expression, kernel, new Set(), line.number, scope);
    const evaluated = evaluateNative(kernel, term);
    return { line: line.number, expression, value: formatTerm(nativeValueToTerm(evaluated.value)), stats: evaluated.stats, kind: "term" };
  } catch (error) {
    if (error instanceof SurfaceError) throw error;
    throw new SurfaceError(line.number, error instanceof Error ? error.message : String(error));
  }
}

function evaluationRules(kernel: Kernel): Proof[] {
  const result: Proof[] = [];
  // A small deterministic evaluation simp-set. Feeding every theorem to the
  // logical saturator is both slower and less predictable than an explicit
  // computational vocabulary.
  for (const name of ["set.empty", "set.pairing", "set.union", "set.powerset", "nat.zero", "nat.succ"]) {
    if (kernel.axioms.has(name)) result.push(axiom(name));
  }
  for (const [name, record] of kernel.definitions) {
    for (const property of record.properties.keys()) {
      // Elimination/no-confusion schemas are excellent explicit proof rules,
      // but they are not computation rules. Feeding them to proposition eval
      // creates irrelevant case splits and destroys the small evaluator's
      // predictability.
      if (property === "cases" || property.startsWith("injective.") || property.startsWith("disjoint.")) continue;
      result.push(definition(name, property));
    }
  }
  return result;
}

function elaborateClassDefinition(
  kernel: Kernel,
  block: readonly SourceLine[],
  scope: SurfaceScope,
  environment: SurfaceEnvironment,
): string {
  const header = block[0]!;
  const declaration = joinDeclarationLines(block);
  const match = /^class\s+([^\s(]+)(?:\s*\(([^)]*)\))?\s*:=\s*(.+)$/u.exec(declaration);
  if (!match || !QUALIFIED_IDENTIFIER.test(match[1]!)) throw new SurfaceError(header.number, "malformed class definition");
  const name = qualifyDeclaration(surfaceSymbol(match[1]!), scope);
  const headerBinders = match[2]?.trim() ? parseBinders(match[2], header.number) : [];
  const rhs = match[3]!.trim();
  const comprehension = /^\{\s*([\p{L}_][\p{L}\p{M}\p{N}_]*)(?:\s*:\s*(\S+))?\s*\|\s*(.+)\s*\}$/u.exec(rhs);
  let binders = headerBinders;
  let bodySource = rhs;
  if (comprehension) {
    const element = comprehension[1]!;
    const explicitType = comprehension[2] ? surfaceType(comprehension[2]) : undefined;
    const matchingHeaderElement = headerBinders[0]?.name === element ? headerBinders[0] : undefined;
    if (!explicitType && !matchingHeaderElement) {
      throw new SurfaceError(header.number, `class comprehension variable ${element} needs a type, as in \`{ ${element} : Set | ... }\``);
    }
    if (explicitType && matchingHeaderElement && matchingHeaderElement.type !== explicitType) {
      throw new SurfaceError(header.number, `class comprehension variable ${element} has conflicting types ${matchingHeaderElement.type} and ${explicitType}`);
    }
    if (!matchingHeaderElement) binders = [{ name: element, type: explicitType! }, ...headerBinders];
    bodySource = comprehension[3]!.trim();
  } else if (rhs.startsWith("{")) {
    throw new SurfaceError(header.number, "expected an unbounded class comprehension such as `{ x : Set | condition }`");
  }
  if (binders.length === 0) throw new SurfaceError(header.number, "a class needs an element binder");
  if (new Set(binders.map(item => item.name)).size !== binders.length) {
    throw new SurfaceError(header.number, "class binders must be distinct");
  }
  if (!(["Nat", "Set"] as string[]).includes(binders[0]!.type)) {
    throw new SurfaceError(header.number, "a class element binder must be Nat or Set");
  }
  if (binders.slice(1).some(item => !["Nat", "Set", "Class"].includes(item.type))) {
    throw new SurfaceError(header.number, "class parameters must be Nat, Set, or Class");
  }
  const classParameters = new Set(binders.filter(item => item.type === "Class").map(item => item.name));
  const body = parseFormula(bodySource, kernel,
    new Set(binders.filter(item => item.type !== "Class").map(item => item.name)), header.number, scope, classParameters);
  const predicateBacked = classParameters.size === 0;
  if (predicateBacked) {
    try { kernel.definePredicate(name, binders.map(item => item.name), body); }
    catch (error) { throw new SurfaceError(header.number, error instanceof Error ? error.message : String(error)); }
  }
  const parameterTypes = binders.slice(1).map(item => item.type as "Nat" | "Set" | "Class");
  environment.classes.set(name, {
    name,
    element: binders[0]!.name,
    parameters: binders.slice(1).map(item => item.name),
    parameterTypes,
  });
  environment.classDefinitions.set(name, {
    elementType: binders[0]!.type as "Nat" | "Set",
    parameterTypes,
    body,
    predicateBacked,
  });
  return name;
}

/** Result annotations become ordinary checked theorems, never typing axioms. */
function elaborateDefinitionType(
  kernel: Kernel, name: string, line: SourceLine, scope: SurfaceScope,
  proofLines?: readonly SourceLine[],
): "proved" | "pending" | "set" {
  const environment = surfaceEnvironments.get(kernel)!;
  const signature = environment.signatures.get(name)!;
  if (!signature.resultType || signature.resultType === "Set") {
    if (proofLines) throw new SurfaceError(line.number, "Set is the kernel sort and needs no result-type proof");
    return "set";
  }
  const binders = signature.parameters;
  const assumptions = binderAssumptions(binders);
  const args = binders.map(item => v(item.name));
  const term = app(name, ...args);
  const goal = pred(signature.resultType, ...(signature.resultTypeArguments ?? []), term);
  let statement = assumptions.reduceRight<Formula>((body, assumption) => imp(assumption, body), goal);
  for (const binder of [...binders].reverse()) statement = forall(binder.name, statement);
  const theoremName = `${name}.type`;
  const existing = kernel.theorems.get(theoremName);
  if (existing) {
    if (!formulaEquals(existing, statement)) throw new SurfaceError(line.number,
      `${theoremName} does not establish the declared result type`);
    return "proved";
  }
  const theoremSignature: SurfaceSignature = { kind: "theorem", parameters: binders, requirementCount: 0 };
  const sourceTerm = (term: Term): string => term.tag === "var" ? term.name :
    term.tag === "nat" ? term.value : term.fn + (term.args.length ? `(${term.args.map(sourceTerm).join(",")})` : "");
  const binderSource = binders.map(item => {
    const type = item.type + (item.typeArguments?.length
      ? `(${item.typeArguments.map(term => sourceTerm(term)).join(",")})` : "");
    return item.implicit ? `{${item.name} : ${type}}` : `(${item.name} : ${type})`;
  }).join(" ");
  const implicit = binders.filter(item => item.implicit);
  const call = name + (implicit.length ? `{${implicit.map(item => `${item.name} := ${item.name}`).join(", ")}}` : "") +
    `(${binders.filter(item => !item.implicit).map(item => item.name).join(", ")})`;
  const goalSource = `${signature.resultType}(${[...(signature.resultTypeArguments ?? []).map(term => sourceTerm(term)), call].join(", ")})`;
  const prefix = scope.namespaces.join(".");
  const localName = prefix ? theoremName.slice(prefix.length + 1) : theoremName;
  if (proofLines) {
    if (!proofLines.length) throw new SurfaceError(line.number, "empty definition result-type proof");
    elaborateTheorem(kernel, [
      { ...line, text: `theorem ${localName} ${binderSource}` },
      { ...line, text: `shows ${goalSource}` },
      { ...line, text: "proof" },
      ...proofLines,
    ], scope);
    return "proved";
  }
  let evidence: Proof | undefined;
  const body = kernel.functionBodies.get(name)?.body;
  if (body) {
    const bodyEvidence = proveRefinement(kernel, body, signature.resultType,
      signature.resultTypeArguments ?? [], assumptions, [], scopeVisibility(kernel, scope));
    if (bodyEvidence) {
      const variable = freshSurfaceVariable("result", new Set(binders.map(item => item.name)));
      evidence = eqElim(at(definition(name, "equation"), ...args), variable,
        pred(signature.resultType, ...(signature.resultTypeArguments ?? []), v(variable)), bodyEvidence, true);
    }
  }
  evidence ??= proveRefinement(kernel, term, signature.resultType,
    signature.resultTypeArguments ?? [], assumptions, [], scopeVisibility(kernel, scope));
  if (!evidence) {
    const recursive = kernel.recursiveFunctions.get(name);
    if (recursive?.admission === "structural") {
      const datatype = kernel.datatypes.get(recursive.datatype)!;
      const decreasing = binders[recursive.decreasingParameter]!;
      const others = binders.filter(item => item !== decreasing && !item.implicit);
      const forbidden = new Set(binders.map(item => item.name));
      const fresh = (base: string): string => {
        const value = freshSurfaceVariable(base, forbidden);
        forbidden.add(value);
        return value;
      };
      const script = [`theorem ${localName} ${binderSource}`, `  shows ${goalSource}`, "proof",
        `  induction ${decreasing.name}${others.length ? ` generalizing ${others.map(item => item.name).join(" ")}` : ""}`];
      for (const constructor of datatype.constructors) {
        const fields = Array.from({ length: constructor.arity }, (_, i) => fresh(`__field${i}`));
        const hypotheses = constructor.recursiveFields.map((_, i) => fresh(`__ih${i}`));
        script.push(`  | ${constructor.name}${fields.length ? `(${fields.join(", ")})` : ""}${hypotheses.length ? ` using ${hypotheses.join(", ")}` : ""} =>`);
        // Generalized binders have kernel guards in the motive.
        const introductions = others.flatMap(item => [item.name, ...(item.type === "Set" || item.type === "Class" ? [] : [fresh(`__${item.name}_type`)])]);
        if (introductions.length) script.push(`    intros ${introductions.join(" ")}`);
        script.push(`    rw ${name}`, "    typecheck");
      }
      const lines = script.map((text, index) => ({ number: line.number + index, text: text.trim(), indent: text.length - text.trimStart().length }));
      try {
        elaborateTheorem(kernel, lines, scope);
        if (environment.captureTacticTraces) kernel.setTheoremTacticTrace(theoremName, {
          initial: tacticState(goal, assumptions, new Map()),
          steps: [{ line: line.number, command: "typecheck", before: tacticState(goal, assumptions, new Map()), after: { goals: [] } }],
        });
        return "proved";
      }
      catch (error) {
        if (!(error instanceof SurfaceError)) throw error;
        environment.signatures.delete(theoremName);
      }
    }
    return "pending";
  }
  let proof = assumptions.reduceRight<Proof>((body, assumption) => impIntro(assumption, body), evidence);
  for (const binder of [...binders].reverse()) proof = forallIntro(binder.name, proof);
  kernel.addTheorem(theoremName, statement, proof);
  environment.signatures.set(theoremName, theoremSignature);
  if (environment.captureTacticTraces) kernel.setTheoremTacticTrace(theoremName, {
    initial: tacticState(goal, assumptions, new Map()),
    steps: [{ line: line.number, command: "typecheck", before: tacticState(goal, assumptions, new Map()), after: { goals: [] } }],
  });
  return "proved";
}

function elaborateExplicitDefinition(kernel: Kernel, block: readonly SourceLine[], scope: SurfaceScope): string {
  const header = block[0]!;
  const match = /^def\s+(\S+)\s+(.+)$/.exec(joinDeclarationLines(block));
  if (!match) throw new SurfaceError(header.number, "malformed explicit definition");
  const [, rawName, tail] = match;
  if (!QUALIFIED_IDENTIFIER.test(rawName!)) throw new SurfaceError(header.number, "malformed definition name");
  const parsedHeader = parseBinderGroups(tail!, header.number);
  const result = /^:\s*(\S+)\s*:=\s*(.+)$/.exec(parsedHeader.rest);
  if (!result) throw new SurfaceError(header.number, "expected `def f {A : Set} (x : T(A)) : Set := ...`");
  const [, rawResultType, rhs] = result;
  const name = qualifyDeclaration(surfaceSymbol(rawName!), scope, { kernel, kind: "function", arity: parsedHeader.binders.length });
  const binders = resolveBinderTypes(parsedHeader.binders, kernel, scope, header.number);
  scope = scopedBinders(scope, binders);
  const rawType = surfaceType(rawResultType!);
  const variables = new Set(binders.map(item => item.name));
  const resultDescriptor = resolvedResultType(rawType, kernel, scope, header.number, variables);
  const resultType = resultDescriptor.type;
  const environment = surfaceEnvironments.get(kernel)!;
  environment.signatures.set(name, {
    kind: "function", parameters: binders, resultType, resultTypeArguments: resultDescriptor.arguments,
  });
  const comprehension = /^\{\s*(.+)\s*\}$/.exec(rhs!.trim());
  const comprehensionPieces = comprehension ? splitTopLevel(comprehension[1]!, "|") : [];
  try {
    if (comprehension && comprehensionPieces.length === 2) {
      if (resultType !== "Set") throw new SurfaceError(header.number, "a set comprehension must have result type Set");
      const pieces = comprehensionPieces;
      const binderSource = pieces[0]!;
      const membership = [" in ", "∈"].map(operator => [operator, findTopLevel(binderSource, operator)] as const)
        .find(([, index]) => index >= 0);
      if (membership) {
        const [operator, index] = membership;
        const element = binderSource.slice(0, index).trim();
        if (!SIMPLE_IDENTIFIER.test(element)) throw new SurfaceError(header.number, "malformed comprehension variable");
        const bound = parseTerm(binderSource.slice(index + operator.length), kernel, variables, header.number, scope);
        const conditionVariables = new Set(variables);
        conditionVariables.add(element);
        const boundFormula = pred("in", v(element), bound);
        const conditionScope = {
          ...scope,
          localFormulas: () => [...(scope.localFormulas?.() ?? []), boundFormula],
        };
        const condition = parseFormula(pieces[1]!, kernel, conditionVariables, header.number, conditionScope);
        kernel.defineSubset(name, binders.map(item => item.name), element, bound, condition);
      } else {
        // Replacement image: `{ expression | x in A }`. The functionality
        // certificate is generated from equality and replayed by the kernel.
        const imageBinder = pieces[1]!;
        const imageMembership = [" in ", "∈"].map(operator => [operator, findTopLevel(imageBinder, operator)] as const)
          .find(([, index]) => index >= 0);
        if (!imageMembership) throw new SurfaceError(header.number,
          "expected a bounded separation `{x in A | P}` or image `{f(x) | x in A}`");
        const [operator, index] = imageMembership;
        const input = imageBinder.slice(0, index).trim();
        if (!SIMPLE_IDENTIFIER.test(input) || variables.has(input)) {
          throw new SurfaceError(header.number, "image binder must be a fresh identifier");
        }
        const bound = parseTerm(imageBinder.slice(index + operator.length), kernel, variables, header.number, scope);
        const imageVariables = new Set(variables); imageVariables.add(input);
        const expression = parseTerm(pieces[0]!, kernel, imageVariables, header.number, scope);
        const output = freshSurfaceVariable("imageValue", imageVariables);
        const other = freshSurfaceVariable("otherImageValue", new Set([...imageVariables, output]));
        const relation = eq(expression, v(output));
        let functionality: Proof = impIntro(pred("in", v(input), bound), existsIntro(
          output, and(relation, forall(other, imp(eq(expression, v(other)), eq(v(other), v(output))))), expression,
          andIntro(refl(expression), forallIntro(other, impIntro(eq(expression, v(other)),
            symm(assume(eq(expression, v(other))))))),
        ));
        functionality = forallIntro(input, functionality);
        for (const parameter of binders.map(item => item.name).reverse()) functionality = forallIntro(parameter, functionality);
        kernel.defineReplacement({
          name, parameters: binders.map(item => item.name), domain: bound,
          input, output, relation, functionality,
        });
      }
    } else {
      kernel.defineFunction(name, binders.map(item => item.name), parseTerm(rhs!, kernel, variables, header.number, scope));
    }
  } catch (error) {
    if (error instanceof SurfaceError) throw error;
    throw new SurfaceError(header.number, error instanceof Error ? error.message : String(error));
  }
  return name;
}

/** Bounded witness definitions. Unique values use union in ZF; arbitrary values use Choice.
 * Every selection law is derived as a checked theorem. */
function elaborateChosenDefinition(
  kernel: Kernel, block: readonly SourceLine[], scope: SurfaceScope,
): { readonly definitions: readonly string[]; readonly theorems: readonly string[] } {
  const header = block[0]!;
  const uniqueMode = header.text.startsWith("defunique ");
  const kind = uniqueMode ? "defunique" : "defchoose";
  const uniqueMarker = block.findIndex(line => line.text === "uniqueness");
  if (uniqueMode && uniqueMarker < 0) throw new SurfaceError(header.number, "defunique needs a uniqueness proof");
  const proofMarker = block.findIndex(line => line.text === "proof");
  if (proofMarker < 0) throw new SurfaceError(header.number, `${kind} needs an existence proof`);
  if (uniqueMode && uniqueMarker <= proofMarker) throw new SurfaceError(header.number, "uniqueness must follow the existence proof");
  const headerEnd = block.findIndex(line => line.text.startsWith("requires ") || line.text === "proof");
  const heading = joinDeclarationLines(block.slice(0, headerEnd));
  const match = /^(?:defchoose|defunique)\s+(\S+)\s+(.+?)\s+\(([\p{L}_][\p{L}\p{M}\p{N}_]*)\s*∈\s*(.+)\)\s*:=\s*(.+)$/u.exec(heading);
  if (!match || !QUALIFIED_IDENTIFIER.test(match[1]!)) throw new SurfaceError(header.number,
    `expected \`${kind} f (parameters) (x ∈ A) := predicate\` followed by an existence proof`);
  const [, name, parameterSource, variable, domain, condition] = match;
  const parameters = parseBinderGroups(parameterSource!, header.number);
  if (parameters.rest || parameters.binders.some(binder =>
    !["Set", "Nat", "Real"].includes(binder.type) || binder.implicit || binder.name === variable)) {
    throw new SurfaceError(header.number, `${kind} parameters must be distinct explicit Set, Nat, or Real binders`);
  }
  const requirementLines = joinTheoremClauseContinuations(block.slice(headerEnd, proofMarker))
    .filter(line => line.text && !line.narrative);
  const requirements = requirementLines.map(line => {
    const parsed = /^requires\s+([\p{L}_][\p{L}\p{M}\p{N}_]*)\s*:\s*(.+)$/u.exec(line.text);
    if (!parsed) throw new SurfaceError(line.number, "expected `requires name : proposition`");
    return { name: parsed[1]!, source: line.text };
  });
  const body = block.slice(proofMarker + 1, uniqueMode ? uniqueMarker : undefined).filter(line => line.text);
  if (!body.length) throw new SurfaceError(header.number, `${kind} ${name} needs an existence proof body`);
  const parameterNames = parameters.binders.map(binder => binder.name);
  const params = parameterNames.join(", ");
  const at = (last: string): string => [params, last].filter(Boolean).join(", ");
  const candidate = `${name}.candidates`;
  const candidateTerm = parameterNames.length ? `${candidate}(${params})` : candidate;
  const chosenTerm = parameterNames.length ? `${name}(${params})` : name!;
  const typedEvidence = parameters.binders.filter(isGuardBinder).map(() => "assumption");
  const evidence = [...typedEvidence, ...requirements.map(item => item.name)].join(", ");
  const required = requirements.map(item => `  ${item.source}`).join("\n");
  const asLines = (source: string): SourceLine[] => source.split("\n").map((raw, offset) => ({
    number: header.number + offset, text: raw.trim(), indent: raw.length - raw.trimStart().length,
  }));
  const candidates = elaborateExplicitDefinition(kernel,
    asLines(`def ${candidate} ${parameterSource} : Set := { ${variable} ∈ ${domain} | ${condition} }`), scope);
  const chosen = elaborateExplicitDefinition(kernel,
    asLines(`def ${name} ${parameterSource} : Set := ${uniqueMode ? "union" : "choose"}(${candidateTerm})`), scope);
  const environment = surfaceEnvironments.get(kernel)!;
  const previousTraces = environment.captureTacticTraces;
  environment.captureTacticTraces = false;
  try {
    const existsSource = `theorem ${name}.exists ${parameterSource}
${required}
  shows ∃ ${variable} ∈ ${domain}, ${condition}`;
    // The existence and uniqueness proofs are authored: they keep their
    // original lines and the caller's tracing mode, so a failing step is
    // reported at its line with the proof state reached, as a theorem's is.
    const authored = (headerSource: string, marker: SourceLine, steps: readonly SourceLine[], what: string): string => {
      try {
        environment.captureTacticTraces = previousTraces;
        return elaborateTheorem(kernel, [
          ...asLines(headerSource).map(line => ({ ...line, number: header.number })),
          { ...marker, text: "proof" }, ...steps,
        ], scope);
      } catch (error) {
        if (!(error instanceof SurfaceError)) throw error;
        throw new SurfaceError(error.line,
          `${kind} ${name} needs a checked ${what} proof: ${error.message.replace(/^line \d+:\s*/, "")}`,
          error.partialTrace);
      } finally {
        environment.captureTacticTraces = false;
      }
    };
    const exists = authored(existsSource, block[proofMarker]!, body, "existence");
    if (uniqueMode) {
      const occupied = new Set(block.flatMap(line => line.text.match(/[\p{L}_][\p{L}\p{M}\p{N}_]*/gu) ?? []));
      let other = "uniqueOther";
      while (occupied.has(other)) other += "Next";
      const replaceValue = (value: string): string => condition!.replace(
        new RegExp(`(?<![\\p{L}\\p{M}\\p{N}_])${variable}(?![\\p{L}\\p{M}\\p{N}_])`, "gu"), value);
      const unique = authored(`theorem ${name}.unique ${parameterSource}
${required}
  shows ∀ ${variable} ∈ ${domain}, (${condition}) → ∀ ${other} ∈ ${domain}, (${replaceValue(other)}) → ${variable} = ${other}`,
        block[uniqueMarker]!, block.slice(uniqueMarker + 1).filter(line => line.text), "uniqueness");
      // Generated proof locals must not capture user parameters or requirements.
      const local: Record<string, string> = {};
      for (const base of ["sourceMember", "property", "uniqueLaw", "candidateData", "candidateMember", "value", "element", "member", "unionData", "shape", "item", "itemMember", "elementMember", "itemData", "itemDomain", "itemProperty", "firstUnique", "same"]) {
        let fresh = base;
        while (occupied.has(fresh)) fresh += "Next";
        occupied.add(fresh);
        local[base] = fresh;
      }
      const selected = elaborateTheorem(kernel, asLines(`theorem ${name}.selected ${parameterSource}
${required}
  shows ${chosenTerm} ∈ ${domain} ∧ (${replaceValue(chosenTerm!)})
proof
  obtain ⟨${variable}, ${local.sourceMember}, ${local.property}⟩ := ${name}.exists at ${params}${evidence ? ` with ${evidence}` : ""}
  have ${local.uniqueLaw} := ${name}.unique at ${params}${evidence ? ` with ${evidence}` : ""}
  have ${local.candidateData} : ${variable} ∈ ${domain} ∧ (${condition})
    constructor
    . exact ${local.sourceMember}
    . exact ${local.property}
  have ${local.candidateMember} := ${candidate}.membership.backward at ${at(variable!)} with ${local.candidateData}
  have ${local.value} : union(${candidateTerm}) = ${variable}
    apply set.extensionality at union(${candidateTerm}), ${variable}
    intro ${local.element}
    constructor
    . intro ${local.member}
      have ${local.unionData} := set.union at ${candidateTerm}, ${local.element}
      have ${local.shape} : ∃ ${local.item}, ${local.item} ∈ ${candidateTerm} ∧ ${local.element} ∈ ${local.item}
        tauto
      obtain ⟨${local.item}, ${local.itemMember}, ${local.elementMember}⟩ := ${local.shape}
      have ${local.itemData} := ${candidate}.membership.forward at ${at(local.item!)} with ${local.itemMember}
      rcases ${local.itemData} with ⟨${local.itemDomain}, ${local.itemProperty}⟩
      have ${local.firstUnique} := ${local.uniqueLaw} at ${variable} with ${local.sourceMember}, ${local.property}
      have ${local.same} := ${local.firstUnique} at ${local.item} with ${local.itemDomain}, ${local.itemProperty}
      cc
    . intro ${local.member}
      have ${local.unionData} := set.union at ${candidateTerm}, ${local.element}
      have ${local.shape} : ∃ ${local.item}, ${local.item} ∈ ${candidateTerm} ∧ ${local.element} ∈ ${local.item}
        refine ⟨${variable}, ${local.candidateMember}, ${local.member}⟩
      tauto
  rw under ${name}
  rw under ${local.value}
  exact ${local.candidateData}`), scope);
      return { definitions: [candidates, chosen], theorems: [exists, unique, selected] };
    }
    const selectedSource = `theorem ${name}.selected ${parameterSource}
${required}
  shows ${chosenTerm} ∈ ${domain} ∧ (${condition.replace(
    new RegExp(`(?<![\\p{L}\\p{M}\\p{N}_])${variable}(?![\\p{L}\\p{M}\\p{N}_])`, "gu"), chosenTerm)})
proof
  obtain ⟨${variable}, sourceMember, property⟩ := ${name}.exists at ${params}${evidence ? ` with ${evidence}` : ""}
  have candidateData : ${variable} ∈ ${domain} ∧ (${condition})
    constructor
    . exact sourceMember
    . exact property
  have candidateMember := ${candidate}.membership.backward at ${at(variable!)} with candidateData
  have nonempty : Nonempty(${candidateTerm})
    unfold Nonempty
    witness ${variable}
    exact candidateMember
  have picked := choose.member at ${candidateTerm} with nonempty
  have result := ${candidate}.membership.forward at ${at(`choose(${candidateTerm})`)} with picked
  rcases result with ⟨inDomain, chosenProperty⟩
  constructor
  . rw ${name}
    exact inDomain
  . rw under ← ${name} at chosenProperty
    exact chosenProperty`;
    let selected: string;
    try {
      selected = elaborateTheorem(kernel, asLines(selectedSource), scope);
    } catch (error) {
      if (!(error instanceof SurfaceError)) throw error;
      throw new SurfaceError(header.number, `${kind} ${name} could not derive selection: ${error.message}`);
    }
    return { definitions: [candidates, chosen], theorems: [exists, selected] };
  } finally {
    environment.captureTacticTraces = previousTraces;
  }
}

/** Expand a typed bounded graph into Replacement and ordinary checked laws.
 * The type of each value is a proof obligation, discharged by `typecheck`;
 * neither graph functionality nor application is added as a kernel rule.
 */
function elaborateGraphDefinition(
  kernel: Kernel, block: readonly SourceLine[], scope: SurfaceScope,
): { readonly definition: string; readonly theorems: readonly string[] } {
  const header = block[0]!;
  const headingEnd = block.findIndex(line => line.text.startsWith("requires ") || line.text === "proof");
  const heading = joinDeclarationLines(block.slice(0, headingEnd < 0 ? block.length : headingEnd));
  if (heading.includes("∈") && heading.includes(":=")) {
    return elaborateBoundedGraphDefinition(kernel, block, scope);
  }
  const declaration = joinDeclarationLines(block);
  const match = /^defgraph\s+(\S+)\s+\(([\p{L}_][\p{L}\p{M}\p{N}_]*)\s*:\s*(Nat|Real)\)\s*:\s*(Nat|Real)\s*:=\s*(.+)$/u.exec(declaration);
  if (!match || !QUALIFIED_IDENTIFIER.test(match[1]!)) throw new SurfaceError(header.number,
    "expected `defgraph f (n : Nat) : Real := expression` (Nat and Real carriers are supported)");
  const [, name, index, inputType, outputType, value] = match;
  const carrier = inputType === "Nat" ? "ℕ" : "ℝ";
  const codomain = outputType === "Nat" ? "ℕ" : "ℝ";
  const indexPattern = new RegExp(`(?<![\\p{L}\\p{M}\\p{N}_])${index}(?![\\p{L}\\p{M}\\p{N}_])`, "gu");
  const valueAt = (variable: string): string => value!.replace(indexPattern, variable);
  const inputMember = inputType === "Nat"
    ? `have indexMember : ${index} ∈ ℕ\n    settle with Nat`
    : `have indexMember : ${index} ∈ ℝ\n    settle with Real`;
  const typeFromMember = (variable: string, member: string, indent: string): string => inputType === "Nat"
    ? `have typedIndex : Nat(${variable})\n${indent}  exact nat.omega.backward at ${variable} with ${member}`
    : `have typedIndex : Real(${variable})\n${indent}  unfold Real\n${indent}  exact ${member}`;
  const outputMember = (term: string): string => outputType === "Nat"
    ? `have valueMember := nat.omega.forward at ${term} with typedValue`
    : `unfold Real at typedValue`;
  const outputEvidence = outputType === "Nat" ? "valueMember" : "typedValue";
  const asLines = (source: string): SourceLine[] => source.split("\n").map((raw, offset) => ({
    number: header.number + offset,
    text: raw.trim(),
    indent: raw.length - raw.trimStart().length,
  }));
  const graph = elaborateExplicitDefinition(kernel,
    asLines(`def ${name} : Set := { (${index} ↦ ${value}) | ${index} ∈ ${carrier} }`), scope);
  // These proofs have generated tactic lines, not source lines. Keep their
  // kernel certificates while suppressing misleading editor step locations.
  const environment = surfaceEnvironments.get(kernel)!;
  const previousTraces = environment.captureTacticTraces;
  environment.captureTacticTraces = false;
  try {
  const closedSource = `theorem ${name}.closed (${index} : ${inputType})
  shows ${outputType}(${value})
proof
  typecheck`;
  let closed: string;
  try {
    closed = elaborateTheorem(kernel, asLines(closedSource), scope);
  } catch (error) {
    if (!(error instanceof SurfaceError)) throw error;
    throw new SurfaceError(header.number,
      `defgraph ${name} needs a checked ${outputType} value for ${value}: ${error.message}`);
  }
  const relatesSource = `theorem ${name}.relates (${index} : ${inputType})
  shows relates(${name}, ${index}, ${value})
proof
  ${inputMember}
  unfold relates
  apply ${name}.membership.backward at (${index} ↦ ${value})
  witness ${index}
  refine ⟨indexMember, rfl⟩`;
  const functionSource = `theorem ${name}.function
  shows FunctionBetween(${name}, ${carrier}, ${codomain})
proof
  unfold FunctionBetween
  constructor
  . unfold RelationBetween
    unfold Subset
    intros p member
    have data := ${name}.membership.forward at p with member
    rcases data with ⟨sourceIndex, sourceMember, shape⟩
    rw ← shape
    ${typeFromMember("sourceIndex", "sourceMember", "    ")}
    have typedValue := ${name}.closed at sourceIndex with typedIndex
    ${outputMember(valueAt("sourceIndex"))}
    exact product.pair at sourceIndex, ${valueAt("sourceIndex")}, ${carrier}, ${codomain} with sourceMember, ${outputEvidence}
  . constructor
    . unfold Functional
      intros graphInput graphFirst graphInputFirst graphSecond graphInputSecond
      unfold relates at graphInputFirst
      have first := ${name}.membership.forward at (graphInput ↦ graphFirst) with graphInputFirst
      rcases first with ⟨firstIndex, firstMember, firstShape⟩
      unfold relates at graphInputSecond
      have second := ${name}.membership.forward at (graphInput ↦ graphSecond) with graphInputSecond
      rcases second with ⟨secondIndex, secondMember, secondShape⟩
      have firstCoordinates := orderedPair.injective at
        firstIndex, ${valueAt("firstIndex")}, graphInput, graphFirst with firstShape
      have secondCoordinates := orderedPair.injective at
        secondIndex, ${valueAt("secondIndex")}, graphInput, graphSecond with secondShape
      rcases firstCoordinates with ⟨firstSame, firstValue⟩
      rcases secondCoordinates with ⟨secondSame, secondValue⟩
      cc
    . intros ${index} indexMember
      ${typeFromMember(index!, "indexMember", "      ")}
      have typedValue := ${name}.closed at ${index} with typedIndex
      ${outputMember(value)}
      witness ${value}
      refine ⟨${outputEvidence}, _⟩
      exact ${name}.relates at ${index} with typedIndex`;
  const valueSource = `theorem ${name}.value (${index} : ${inputType})
  shows ${name}[${index}] = ${value}
proof
  have function := ${name}.function
  ${inputMember}
  have mapped := ${name}.relates at ${index} with assumption
  exact FunctionBetween.apply_value at
    ${name}, ${carrier}, ${codomain}, ${index}, ${value} with function, indexMember, mapped`;
  const relates = elaborateTheorem(kernel, asLines(relatesSource), scope);
  const functionLaw = elaborateTheorem(kernel, asLines(functionSource), scope);
  const valueLaw = elaborateTheorem(kernel, asLines(valueSource), scope);
  return { definition: graph, theorems: [closed, relates, functionLaw, valueLaw] };
  } finally {
    environment.captureTacticTraces = previousTraces;
  }
}

/** Bounded graph with an author supplied, checked codomain proof. */
function elaborateBoundedGraphDefinition(
  kernel: Kernel, block: readonly SourceLine[], scope: SurfaceScope,
): { readonly definition: string; readonly theorems: readonly string[] } {
  const header = block[0]!;
  const headerEnd = block.findIndex(line => line.text.startsWith("requires ") || line.text === "proof");
  const heading = joinDeclarationLines(block.slice(0, headerEnd < 0 ? block.length : headerEnd));
  const match = /^defgraph\s+(\S+)\s+(.*?)\(([\p{L}_][\p{L}\p{M}\p{N}_]*)\s*∈\s*(.+)\)\s*:\s*(.+?)\s*:=\s*(.+)$/u.exec(heading);
  if (!match || !QUALIFIED_IDENTIFIER.test(match[1]!)) throw new SurfaceError(header.number,
    "expected `defgraph f (A : Set) (x ∈ A) : B := expression` followed by a closure proof");
  const [, name, parameterSource, index, domain, codomain, value] = match;
  const parameters = parseBinderGroups(parameterSource!, header.number);
  if (parameters.rest || parameters.binders.some(binder =>
    !["Set", "Nat", "Real"].includes(binder.type) || binder.implicit) ||
      parameters.binders.some(binder => binder.name === index)) throw new SurfaceError(header.number,
    "bounded graph parameters must be distinct explicit Set, Nat, or Real binders");
  const proofMarker = block.findIndex(line => line.text === "proof");
  if (proofMarker < 0) throw new SurfaceError(header.number,
    `defgraph ${name} needs a proof that ${value} belongs to ${codomain}`);
  const requirementLines = joinTheoremClauseContinuations(block.slice(headerEnd, proofMarker))
    .filter(line => line.text && !line.narrative);
  const requirements = requirementLines.map(line => {
    const parsed = /^requires\s+([\p{L}_][\p{L}\p{M}\p{N}_]*)\s*:\s*(.+)$/u.exec(line.text);
    if (!parsed) throw new SurfaceError(line.number, "expected `requires name : proposition`");
    return { name: parsed[1]!, source: line.text };
  });
  const body = block.slice(proofMarker + 1).filter(line => line.text);
  if (!body.length) throw new SurfaceError(header.number, `defgraph ${name} needs a codomain proof body`);
  const arguments_ = parameters.binders.map(binder => binder.name);
  const paramDecl = parameterSource!.trim();
  const paramAt = arguments_.join(", ");
  const graph = arguments_.length ? `${name}(${paramAt})` : name!;
  const instantiation = (last: string): string => [paramAt, last].filter(Boolean).join(", ");
  const typedEvidence = parameters.binders.filter(isGuardBinder).map(() => "assumption");
  const proofInputs = (extra?: string): string =>
    [...typedEvidence, ...requirements.map(item => item.name), ...(extra ? [extra] : [])].join(", ");
  const graphPair = freshSurfaceVariable("graphPair", new Set([
    ...arguments_, index!, ...requirements.map(item => item.name),
  ]));
  const functionEvidence = freshSurfaceVariable("graphFunction", new Set([
    ...arguments_, index!, ...requirements.map(item => item.name),
  ]));
  const mappedEvidence = freshSurfaceVariable("graphMapped", new Set([
    ...arguments_, index!, ...requirements.map(item => item.name), functionEvidence,
  ]));
  const required = requirements.map(item => `  ${item.source}`).join("\n");
  const withRequirements = (extra?: string): string => [required, extra].filter(Boolean).join("\n");
  const indexPattern = new RegExp(`(?<![\\p{L}\\p{M}\\p{N}_])${index}(?![\\p{L}\\p{M}\\p{N}_])`, "gu");
  const valueAt = (variable: string): string => value!.replace(indexPattern, variable);
  const indexType = domain === "ℕ" ? "Nat" : domain === "ℝ" ? "Real" : "Set";
  const memberRequirement = indexType === "Set" ? `  requires member : ${index} ∈ ${domain}` : undefined;
  const proveIndexMember = indexType === "Set" ? "" :
    `  have member : ${index} ∈ ${domain}\n    settle with ${indexType}`;
  // No synthetic proof source is assigned to an editor line. The resulting
  // theorems are still fully checked by the kernel and independent replayers.
  const asLines = (source: string): SourceLine[] => source.split("\n").map((raw, offset) => ({
    number: header.number + offset, text: raw.trim(), indent: raw.length - raw.trimStart().length,
  }));
  // The requirements and the index's membership are in scope for the value,
  // so that it may use the notation they supply, as the generated theorems do.
  const parameterScope = scopedBinders(scope, parameters.binders);
  const parameterNames = new Set(arguments_);
  const valueFacts: Formula[] = [];
  for (const item of requirements) {
    const text = /^requires\s+[\p{L}_][\p{L}\p{M}\p{N}_]*\s*:\s*(.+)$/u.exec(item.source)![1]!;
    try {
      valueFacts.push(parseFormula(text, kernel, parameterNames, header.number,
        { ...parameterScope, localFormulas: () => [...(scope.localFormulas?.() ?? []), ...valueFacts] }));
    } catch (error) {
      if (!(error instanceof SurfaceError)) throw error;
    }
  }
  try { valueFacts.push(pred("in", v(index!), parseTerm(domain!, kernel, parameterNames, header.number, parameterScope))); }
  catch (error) { if (!(error instanceof SurfaceError)) throw error; }
  // The sorts of the parameters and of a natural or real index are in
  // scope for the value as well, so that f⁽ᵏ⁾(X) is a real under a real X.
  if (indexType !== "Set") valueFacts.push(pred(indexType, v(index!)));
  const parameterTyping = binderAssumptions(resolveBinderTypes(parameters.binders, kernel, { ...scope, line: header.number }, header.number));
  const valueScope: SurfaceScope = { ...parameterScope, localFormulas: () =>
    [...(scope.localFormulas?.() ?? []), ...parameterTyping, ...valueFacts] };
  const definition = elaborateExplicitDefinition(kernel,
    asLines(`def ${name} ${paramDecl} : Set := { (${index} ↦ (${value})) | ${index} ∈ ${domain} }`), valueScope);
  const environment = surfaceEnvironments.get(kernel)!;
  const previousTraces = environment.captureTacticTraces;
  environment.captureTacticTraces = false;
  try {
    const closedSource = `theorem ${name}.closed ${paramDecl} (${index} : ${indexType})
${withRequirements(`  requires member : ${index} ∈ ${domain}`)}
  shows ${value} ∈ ${codomain}`;
    let closed: string;
    try {
      // This proof is authored, unlike the relates/function/value scaffolding.
      // Keep its original lines (including multiline headers and blank lines)
      // and honor the caller's tracing mode for this proof only.
      environment.captureTacticTraces = previousTraces;
      closed = elaborateTheorem(kernel, [
        ...asLines(closedSource).map(line => ({ ...line, number: header.number })),
        block[proofMarker]!, ...body,
      ], scope);
    } catch (error) {
      if (!(error instanceof SurfaceError)) throw error;
      throw new SurfaceError(error.line,
        `defgraph ${name} needs a checked codomain proof: ${error.message.replace(/^line \d+:\s*/, "")}`,
        error.partialTrace);
    } finally {
      environment.captureTacticTraces = false;
    }
    const relatesSource = `theorem ${name}.relates ${paramDecl} (${index} : ${indexType})
${withRequirements(memberRequirement)}
  shows relates(${graph}, ${index}, ${value})
proof
${proveIndexMember}
  unfold relates
  apply ${name}.membership.backward at ${instantiation(`(${index} ↦ (${value}))`)}
  witness ${index}
  refine ⟨member, rfl⟩`;
    const functionSource = `theorem ${name}.function ${paramDecl}
${required}
  shows FunctionBetween(${graph}, ${domain}, ${codomain})
proof
  unfold FunctionBetween
  constructor
  . unfold RelationBetween
    unfold Subset
    intros ${graphPair} member
    have data := ${name}.membership.forward at ${instantiation(graphPair)} with member
    rcases data with ⟨sourceIndex, sourceMember, shape⟩
    rw ← shape
    ${indexType === "Set" ? "" : `have typedIndex : ${indexType}(sourceIndex)\n      ${indexType === "Nat" ? "exact nat.omega.backward at sourceIndex with sourceMember" : "unfold Real\n      exact sourceMember"}`}
    have valueMember := ${name}.closed at ${instantiation("sourceIndex")} with ${[...typedEvidence, ...(indexType === "Set" ? [] : ["typedIndex"]), ...requirements.map(item => item.name), "sourceMember"].join(", ")}
    exact product.pair at sourceIndex, ${valueAt("sourceIndex")}, ${domain}, ${codomain} with sourceMember, valueMember
  . constructor
    . unfold Functional
      intros graphInput graphFirst graphInputFirst graphSecond graphInputSecond
      unfold relates at graphInputFirst
      have first := ${name}.membership.forward at ${instantiation("(graphInput ↦ graphFirst)")} with graphInputFirst
      rcases first with ⟨firstIndex, firstMember, firstShape⟩
      unfold relates at graphInputSecond
      have second := ${name}.membership.forward at ${instantiation("(graphInput ↦ graphSecond)")} with graphInputSecond
      rcases second with ⟨secondIndex, secondMember, secondShape⟩
      have firstCoordinates := orderedPair.injective at
        firstIndex, ${valueAt("firstIndex")}, graphInput, graphFirst with firstShape
      have secondCoordinates := orderedPair.injective at
        secondIndex, ${valueAt("secondIndex")}, graphInput, graphSecond with secondShape
      rcases firstCoordinates with ⟨firstSame, firstValue⟩
      rcases secondCoordinates with ⟨secondSame, secondValue⟩
      cc
    . intros ${index} indexMember
      ${indexType === "Set" ? "" : `have typedIndex : ${indexType}(${index})\n        ${indexType === "Nat" ? `exact nat.omega.backward at ${index} with indexMember` : "unfold Real\n        exact indexMember"}`}
      have valueMember := ${name}.closed at ${instantiation(index!)} with ${[...typedEvidence, ...(indexType === "Set" ? [] : ["typedIndex"]), ...requirements.map(item => item.name), "indexMember"].join(", ")}
      witness ${value}
      refine ⟨valueMember, _⟩
      exact ${name}.relates at ${instantiation(index!)} with ${[...typedEvidence, ...(indexType === "Set" ? [] : ["typedIndex"]), ...requirements.map(item => item.name), ...(indexType === "Set" ? ["indexMember"] : [])].join(", ")}`;
    const valueSource = `theorem ${name}.value ${paramDecl} (${index} : ${indexType})
${withRequirements(memberRequirement)}
  shows ${graph}[${index}] = ${value}
proof
${proveIndexMember}
  have ${functionEvidence} := ${name}.function${paramAt ? ` at ${paramAt}` : ""}${proofInputs() ? ` with ${proofInputs()}` : ""}
  have ${mappedEvidence} := ${name}.relates at ${instantiation(index!)} with ${[...typedEvidence, ...(indexType === "Set" ? [] : ["assumption"]), ...requirements.map(item => item.name), ...(indexType === "Set" ? ["member"] : [])].join(", ")}
  exact FunctionBetween.apply_value at
    ${graph}, ${domain}, ${codomain}, ${index}, ${value} with ${functionEvidence}, member, ${mappedEvidence}`;
    const relates = elaborateTheorem(kernel, asLines(relatesSource), scope);
    const functionLaw = elaborateTheorem(kernel, asLines(functionSource), scope);
    const valueLaw = elaborateTheorem(kernel, asLines(valueSource), scope);
    return { definition, theorems: [closed, relates, functionLaw, valueLaw] };
  } finally {
    environment.captureTacticTraces = previousTraces;
  }
}

function elaboratePredicateDefinition(kernel: Kernel, block: readonly SourceLine[], scope: SurfaceScope): string {
  const header = block[0]!;
  const match = /^predicate\s+(\S+)\s+(.+)$/.exec(joinDeclarationLines(block));
  if (!match) throw new SurfaceError(header.number, "malformed predicate definition");
  const [, rawName, tail] = match;
  if (!QUALIFIED_IDENTIFIER.test(rawName!)) throw new SurfaceError(header.number, "malformed predicate name");
  const parsedHeader = parseBinderGroups(tail!, header.number);
  const body = /^:=\s*(.+)$/.exec(parsedHeader.rest);
  if (!body) throw new SurfaceError(header.number, "expected `predicate P {A : Set} (x : T(A)) := ...`");
  const rhs = body[1]!;
  const name = qualifyDeclaration(surfaceSymbol(rawName!), scope, { kernel, kind: "predicate", arity: parsedHeader.binders.length });
  const binders = resolveBinderTypes(parsedHeader.binders, kernel, scope, header.number);
  scope = scopedBinders(scope, binders);
  const variables = new Set(binders.map(item => item.name));
  surfaceEnvironments.get(kernel)!.signatures.set(name, { kind: "predicate", parameters: binders });
  try {
    const declaredBody = parseFormula(rhs!, kernel, variables, header.number, scope);
    // Soft-typed predicate parameters are part of the predicate's extension,
    // and do more than guide elaboration.  Thus `P(x : Nat)`
    // means `Nat(x) and ...`, allowing P(x) itself to recover the domain fact.
    // Set and Class are the ambient sorts and contribute no guard.
    const guardedBody = binderAssumptions(binders)
      .reduceRight<Formula>((result, guard) => and(guard, result), declaredBody);
    kernel.definePredicate(name, binders.map(item => item.name), guardedBody);
  } catch (error) {
    if (error instanceof SurfaceError) throw error;
    throw new SurfaceError(header.number, error instanceof Error ? error.message : String(error));
  }
  return name;
}

/**
 * A declaration ends at the next top-level declaration keyword, so its
 * physical lines can be parsed as one expression. Whitespace is insignificant
 * in Grace17 terms and formulas; joining with a single space also prevents two
 * adjacent tokens from being accidentally fused.
 */
function joinDeclarationLines(block: readonly SourceLine[]): string {
  return block.map(line => line.text).join(" ");
}

/** Join physical lines belonging to a `| pattern => body` equation. */
function joinDefinitionClauseContinuations(block: readonly SourceLine[]): readonly SourceLine[] {
  const result: SourceLine[] = [];
  for (const line of block) {
    const previous = result.at(-1);
    if (previous && !line.text.startsWith("|") && !line.text.startsWith("descends ") && previous.text.startsWith("|")) {
      result[result.length - 1] = { ...previous, text: `${previous.text} ${line.text}` };
    } else {
      result.push(line);
    }
  }
  return result;
}

function elaborateDefinition(kernel: Kernel, block: readonly SourceLine[], scope: SurfaceScope): string {
  const header = block[0]!;
  block = joinDefinitionClauseContinuations(block);
  const stray = block.slice(1).find(line => !line.text.startsWith("|") && !line.text.startsWith("descends "));
  if (stray) throw new SurfaceError(stray.number, "expected a defining equation or descends clause");
  const match = /^(?:def|define)\s+(\S+)\s+(.+)$/.exec(header.text);
  if (!match) throw new SurfaceError(header.number, "malformed definition header");
  const [, rawName, tail] = match;
  if (!QUALIFIED_IDENTIFIER.test(rawName!)) throw new SurfaceError(header.number, "malformed definition name");
  const parsedHeader = parseBinderGroups(tail!, header.number);
  const result = /^(?:->|→)\s*(\S+)$/.exec(parsedHeader.rest);
  if (!result) throw new SurfaceError(header.number, "expected `def f {A : Set} (x : T(A)) -> Set`");
  const rawResultType = result[1]!;
  const name = qualifyDeclaration(surfaceSymbol(rawName!), scope);
  scope = { ...scope, pendingFunction: name };
  const binders = resolveBinderTypes(parsedHeader.binders, kernel, scope, header.number);
  scope = scopedBinders(scope, binders);
  const rawType = surfaceType(rawResultType!);
  const resultDescriptor = resolvedResultType(rawType, kernel, scope, header.number, new Set(binders.map(item => item.name)));
  surfaceEnvironments.get(kernel)!.signatures.set(name, {
    kind: "function", parameters: binders, resultType: resultDescriptor.type, resultTypeArguments: resultDescriptor.arguments,
  });
  const descents = block.filter(line => line.text.startsWith("descends "));
  if (descents.length > 1) throw new SurfaceError(descents[1]!.number, "duplicate descends clause");
  const descent = descents[0];

  const equations: RecursiveEquation[] = block.filter(line => line.text.startsWith("|")).map(line => {
    const equationMatch = /^\|\s*(.*?)\s*(?:=>|⇒)\s*(.+)$/.exec(line.text);
    if (!equationMatch) throw new SurfaceError(line.number, "malformed defining equation");
    const patternTexts = splitTopLevel(equationMatch[1]!, ",");
    const explicitBinders = binders.filter(item => !item.implicit);
    if (patternTexts.length !== explicitBinders.length) {
      throw new SurfaceError(line.number, `expected ${explicitBinders.length} explicit patterns; implicit parameters are omitted`);
    }
    let explicitIndex = 0;
    const patterns = binders.map(binder => binder.implicit
      ? bind(binder.name)
      : parsePattern(patternTexts[explicitIndex++]!, kernel, scope, line.number));
    const variables = new Set<string>();
    patterns.forEach(pattern => collectPatternBindings(pattern, variables));
    return { patterns, body: parseTerm(equationMatch[2]!, kernel, variables, line.number, scope) };
  });
  if (equations.length === 0) throw new SurfaceError(header.number, `definition ${name} has no equations`);
  let decreasingParameter: number;
  let datatype: string;
  if (descent) {
    const decreasingName = descent.text.slice("descends ".length).trim();
    decreasingParameter = binders.findIndex(item => item.name === decreasingName);
    if (decreasingParameter < 0) throw new SurfaceError(descent.number, `unknown decreasing parameter ${decreasingName}`);
    const firstConstructor = equations.map(equation => equation.patterns[decreasingParameter]!)
      .find(pattern => pattern.tag === "ctor");
    const data = [...kernel.datatypes.values()].find(item => item.predicate === binders[decreasingParameter]!.type ||
      (binders[decreasingParameter]!.type === "Set" && firstConstructor?.tag === "ctor" &&
        item.constructors.some(ctor => ctor.name === firstConstructor.name)));
    if (!data) throw new SurfaceError(descent.number, `parameter ${decreasingName} does not have an inductive datatype`);
    datatype = data.name;
  } else {
    const candidates = binders.flatMap((binder, index) => {
      const roots = equations.map(equation => equation.patterns[index]!);
      // Set-valued executable code can state its constructor domain through
      // exhaustive patterns without claiming an unconstructed carrier set.
      const firstConstructor = roots.find(pattern => pattern.tag === "ctor");
      const data = [...kernel.datatypes.values()].find(item => item.predicate === binder.type ||
        (binder.type === "Set" && firstConstructor?.tag === "ctor" &&
          item.constructors.some(ctor => ctor.name === firstConstructor.name)));
      if (!data) return [];
      const constructors = data.constructors.map(item => item.name);
      const names = new Set(roots.filter(pattern => pattern.tag === "ctor").map(pattern => pattern.name));
      const exhaustive = roots.every(pattern => pattern.tag === "ctor") &&
        constructors.every(constructor => names.has(constructor)) && names.size === constructors.length;
      return exhaustive ? [{ index, datatype: data.name }] : [];
    });
    if (candidates.length === 0) {
      throw new SurfaceError(header.number, `cannot infer structural descent for ${name}; add descends <parameter>`);
    }
    if (candidates.length > 1) {
      throw new SurfaceError(header.number, `structural descent for ${name} is ambiguous; add descends <parameter>`);
    }
    decreasingParameter = candidates[0]!.index;
    datatype = candidates[0]!.datatype;
  }
  try {
    kernel.defineStructuralFunction({
      name: name!,
      parameters: binders.map(item => item.name),
      datatype,
      decreasingParameter,
      equations,
    });
  } catch (error) {
    if (error instanceof KernelError) throw new SurfaceError(header.number, error.message);
    throw error;
  }
  return name!;
}

function elaborateTheorem(kernel: Kernel, block: readonly SourceLine[], scope: SurfaceScope): string {
  const header = block[0]!;
  block = joinTheoremClauseContinuations(block);
  const narrative = block.flatMap(line => line.narrative ? [line.narrative] : []);
  const emptyNarrative = narrative.find(entry => !entry.text);
  if (emptyNarrative) throw new SurfaceError(emptyNarrative.line, "proof narrative text cannot be empty");
  const theoremBodyForValidation = joinTacticContinuations(block.slice(1).filter(line => !line.narrative)).flatMap(splitTacticLine);
  const stray = theoremBodyForValidation.find(line =>
    line.text !== "proof" && !line.text.startsWith("shows ") && !line.text.startsWith("requires ") && !line.text.startsWith("induction ") &&
    !line.text.startsWith("|") && !line.text.startsWith("settle") && !line.text.startsWith("witness ") && !line.text.startsWith("use ") &&
    !line.text.startsWith("have ") && !line.text.startsWith("apply ") && !line.text.startsWith("exact ") && !line.text.startsWith("show ") && !line.text.startsWith("refine ") &&
    line.text !== "calc" && !/^.+\s+:=\s+.+$/u.test(line.text) &&
    !["exact?", "apply?", "rw?", "typecheck", "synthesize"].includes(line.text) &&
    !line.text.startsWith("specialize ") &&
    !line.text.startsWith("intro") && !line.text.startsWith("by_contra ") && !line.text.startsWith("by_cases ") && !line.text.startsWith("obtain ") && !line.text.startsWith("unfold ") &&
    !line.text.startsWith("ext ") &&
    !line.text.startsWith("simp") && !line.text.startsWith("ring") && !line.text.startsWith("linear_combination ") && !line.text.startsWith("rewrite ") && !line.text.startsWith("rw ") && !line.text.startsWith("rwa ") &&
    !line.text.startsWith("cases ") && !line.text.startsWith("rcases ") && !line.text.startsWith("clear ") &&
    !line.text.startsWith("rename ") && !line.text.startsWith("revert ") && !line.text.startsWith("symm at ") &&
    !["left", "right", "constructor", "split", "assumption", "contradiction", "exfalso", "by_contra", "reflexivity", "rfl", "symm", "compute", "decide", "ring", "arith", "linarith", "tauto", "cc", "congruence", "sorry"].includes(line.text) &&
    !isUserTacticInvocation(kernel, line.text, scope));
  if (stray) {
    throw new SurfaceError(stray.number,
      `unexpected line in theorem: \`${stray.text}\`; a theorem holds requires and shows clauses, ` +
      "a proof marker, an induction clause, case lines `| C(x) =>`, and tactic steps such as have, exact, " +
      "apply, rw, simp, intro, obtain, cases, and calc; a proposition continued from the line above must " +
      "be more indented, after an operator or a comma, or begin with one");
  }
  const match = /^(theorem|lemma|instance)\s+(\S+?)(?:\s+(.*))?$/.exec(header.text);
  if (!match) throw new SurfaceError(header.number, "malformed theorem header");
  const [, declarationKind, rawName, binderText] = match;
  if (!QUALIFIED_IDENTIFIER.test(rawName!)) throw new SurfaceError(header.number, malformedIdentifier("theorem", rawName!));
  const name = qualifyDeclaration(surfaceSymbol(rawName!), scope);
  const parsedHeader = binderText === undefined ? { binders: [] as Binder[], rest: "" } : parseBinderGroups(binderText, header.number);
  if (parsedHeader.rest) throw new SurfaceError(header.number, `unexpected theorem header text ${parsedHeader.rest}`);
  // A binder typed by a structure variable of the header, (g : G), is
  // resolved once the requires clauses are read, since the hypothesis
  // supplying G's carrier, Group(G), may be among them.
  const deferred = new Set<string>();
  let binders = resolveBinderTypes(parsedHeader.binders, kernel, scope, header.number, [], new Set(), deferred);
  const outerScope = scope;
  scope = scopedBinders(scope, binders);
  if (binders.some(b => scope.rings?.some(r => r.name === b.name)))
    throw new SurfaceError(header.number, "theorem variable collides with a ring notation name");
  const variables = new Set(binders.map(item => item.name));
  const parseRequirements = (): ParsedRequirement[] => {
    const earlierRequirements: Formula[] = [];
    return block.filter(line => line.text.startsWith("requires "))
      .map(line => {
        const requirement = parseRequirement(line, kernel, variables, {
          ...scope, localFormulas: () => [...binderAssumptions(binders), ...earlierRequirements],
        });
        earlierRequirements.push(requirement.formula);
        return requirement;
      });
  };
  let parsedRequirements = parseRequirements();
  let requirements = parsedRequirements.map(item => item.formula);
  if (deferred.size) {
    binders = resolveBinderTypes(parsedHeader.binders, kernel, {
      ...outerScope, localFormulas: () => [...(outerScope.localFormulas?.() ?? []), ...requirements],
    }, header.number);
    scope = scopedBinders(outerScope, binders);
    // The requirements are read again with the binders' carriers in scope.
    parsedRequirements = parseRequirements();
    requirements = parsedRequirements.map(item => item.formula);
  }
  surfaceEnvironments.get(kernel)!.signatures.set(name, {
    kind: "theorem", parameters: binders, requirementCount: requirements.length,
  });
  scope = {
    ...scope,
    localFormulas: () => [...binderAssumptions(binders), ...requirements],
  };
  const showsLines = block.filter(line => line.text.startsWith("shows "));
  if (showsLines.length > 1) throw new SurfaceError(showsLines[1]!.number, "duplicate shows clause");
  const shows = showsLines[0];
  if (!shows) throw new SurfaceError(header.number, `theorem ${name} needs a shows clause`);
  const showsBody = shows.text.slice("shows ".length);
  const inlineProof = splitInlineProof(showsBody);
  const proofLines = block.filter(line => line.text === "proof");
  if (proofLines.length > 1) throw new SurfaceError(proofLines[1]!.number, "duplicate proof marker");
  if (inlineProof && proofLines.length) throw new SurfaceError(proofLines[0]!.number, "theorem has both an inline and a proof-block proof");
  if (!inlineProof && proofLines.length === 0) throw new SurfaceError(header.number, `theorem ${name} needs a proof block or trailing by tactic`);
  const goal = parseFormula(inlineProof?.formula ?? showsBody, kernel, variables, shows.number, scope);
  if (declarationKind === "instance") validateInstanceDeclaration(kernel, goal, requirements, binders, header.number, scopeVisibility(kernel, scope));
  const inductionPattern = /^induction\s+([\p{L}_][\p{L}\p{M}\p{N}_]*)(?:\s+generalizing\s+((?!with(?:\s|$))[\p{L}_][\p{L}\p{M}\p{N}_]*(?:\s+(?!with(?:\s|$))[\p{L}_][\p{L}\p{M}\p{N}_]*)*))?(?:\s+with)?$/u;
  const inductionLines = block.filter(line => inductionPattern.test(line.text));
  if (inductionLines.length > 1) throw new SurfaceError(inductionLines[1]!.number, "duplicate induction clause");
  const inductionLine = inductionLines[0];
  if (inlineProof && inductionLine) throw new SurfaceError(inductionLine.number, "inline proofs cannot also use an induction clause");
  // The names the proof can use without naming a declaration, for the
  // trace: section variables and hypotheses, the header's binders, and its
  // named premises, each with the line that binds it.
  const sectionBindings = scope.sectionBindings?.() ?? [];
  const sectionNames = new Set(sectionBindings.map(item => item.name));
  const scopeEntries: TacticScopeEntry[] = [
    ...sectionBindings,
    ...binders.filter(binder => !sectionNames.has(binder.name))
      .map(binder => ({ name: binder.name, kind: "binder" as const, line: header.number, sort: binder.type })),
    ...block.filter(line => line.text.startsWith("requires ")).flatMap(line => {
      const named = /^requires\s+(\S+)\s*:/u.exec(line.text)?.[1];
      return named && !sectionNames.has(named) ? [{ name: named, kind: "premise" as const, line: line.number }] : [];
    }),
  ];
  if (!inductionLine) {
    const marker = proofLines[0] ?? shows;
    const steps = inlineProof
      ? splitTacticLine({
        number: shows.number, text: inlineProof.tactic, indent: shows.indent,
        columnStart: (shows.columnStart ?? 1) + "shows ".length + inlineProof.tacticOffset,
        columnEnd: shows.columnEnd,
      })
      : joinTacticContinuations(block.filter(line => line.number > marker.number && !line.narrative &&
        !line.text.startsWith("shows ") && !line.text.startsWith("requires "))).flatMap(splitTacticLine);
    if (inlineProof && steps.length !== 1) {
      throw new SurfaceError(shows.number, "trailing by expects exactly one tactic; write a proof block for a sequence");
    }
    if (narrative.length === 0 && steps.length === 1 && (steps[0]!.text.startsWith("settle") || steps[0]!.text.startsWith("witness "))) {
      elaborateDirectTheorem(kernel, name, binders, requirements, goal, steps[0]!, scope);
    } else {
      if (steps.length === 0) {
        const initial = tacticState(goal, [...binderAssumptions(binders), ...requirements], new Map());
        throw new SurfaceError(marker.number, "empty proof block", {
          initial,
          steps: [],
          ...(narrative.length ? { narrative } : {}),
          ...(scopeEntries.length ? { scope: scopeEntries } : {}),
        });
      }
      elaborateTacticTheorem(kernel, name, binders, requirements, parsedRequirements.map(item => item.name), goal, steps, scope, undefined, narrative, scopeEntries);
    }
    if (declarationKind === "instance") registerInstanceDeclaration(kernel, name, scope);
    return name!;
  }
  const inductionMatch = inductionPattern.exec(inductionLine.text)!;
  const inductionVariable = inductionMatch[1]!;
  const generalizedNames = inductionMatch[2]?.trim().split(/\s+/u) ?? [];
  if (new Set(generalizedNames).size !== generalizedNames.length) {
    throw new SurfaceError(inductionLine.number, "duplicate generalized induction variable");
  }
  const inductionIndex = binders.findIndex(item => item.name === inductionVariable);
  if (inductionIndex < 0) throw new SurfaceError(inductionLine.number, `unknown induction variable ${inductionVariable}`);
  const inductionDatatype = [...kernel.datatypes.values()].find(item => item.predicate === binders[inductionIndex]!.type);
  if (!inductionDatatype) throw new SurfaceError(inductionLine.number, "induction requires an inductive datatype binder");
  const inductionParameters = binders[inductionIndex]!.typeArguments ?? [];
  for (const generalizedName of generalizedNames) {
    if (generalizedName === inductionVariable) {
      throw new SurfaceError(inductionLine.number, `cannot generalize the induction variable ${inductionVariable}`);
    }
    if (!binders.some(item => item.name === generalizedName)) {
      throw new SurfaceError(inductionLine.number, `unknown generalized variable ${generalizedName}`);
    }
  }
  const generalizedSet = new Set(generalizedNames);
  let changed = true;
  while (changed) {
    changed = false;
    for (const binder of binders) {
      if (binder.name === inductionVariable || generalizedSet.has(binder.name)) continue;
      const assumptions = binderAssumptions([binder]);
      if (assumptions.some(formula => [...generalizedSet].some(name => freeFormulaVariables(formula).has(name)))) {
        generalizedSet.add(binder.name);
        changed = true;
      }
    }
  }
  const generalizedBinders = binders.filter(item => generalizedSet.has(item.name));
  const dependentRequirements = parsedRequirements.filter(item => {
    const free = freeFormulaVariables(item.formula);
    return free.has(inductionVariable) || [...generalizedSet].some(name => free.has(name));
  });

  const outerBinders = binders.filter(item => item.name !== inductionVariable && !generalizedSet.has(item.name));
  const outerRequirements = parsedRequirements.filter(item => !dependentRequirements.includes(item));
  const outerAssumptions = [...binderAssumptions(outerBinders), ...outerRequirements.map(item => item.formula)];
  const generalizedAssumptions = [
    ...binderAssumptions(generalizedBinders),
    ...dependentRequirements.map(item => item.formula),
  ];
  let generalizedGoal = generalizedAssumptions.reduceRight<Formula>((result, assumption) => imp(assumption, result), goal);
  for (const binder of [...generalizedBinders].reverse()) generalizedGoal = forall(binder.name, generalizedGoal);
  const motive = outerAssumptions.reduceRight<Formula>((result, assumption) => imp(assumption, result), generalizedGoal);
  const initial = tacticState(goal, [...binderAssumptions(binders), ...requirements], new Map());
  const suggestedCases = inductionCaseSuggestions(kernel, inductionDatatype, scope);
  const suggestedGoals = suggestedCases.map(item => inductionCaseState(
    kernel, { number: inductionLine.number, text: item, indent: inductionLine.indent }, generalizedGoal, motive,
    inductionVariable, outerAssumptions, inductionDatatype, inductionParameters, scope, outerRequirements));
  const inductionStep: TacticTraceStep = {
    line: inductionLine.number, columnStart: inductionLine.columnStart, columnEnd: inductionLine.columnEnd,
    command: inductionLine.text, before: initial, after: { goals: suggestedGoals },
  };
  const caseLines = block.filter(line => line.number > inductionLine.number && line.text.startsWith("|"));
  if (caseLines.length === 0) {
    throw new SurfaceError(inductionLine.number,
      `induction on ${shortName(inductionDatatype.predicate)} has ${suggestedCases.length} constructor cases: ${suggestedCases.map(item => `\`${item}\``).join(", ")}`,
      { initial, steps: [inductionStep] });
  }
  let caseBlocks: readonly { header: SourceLine; body: readonly SourceLine[]; parsed: ParsedInductionBranch }[];
  try { caseBlocks = caseLines.map((line, index) => {
    const start = block.indexOf(line);
    const next = index + 1 < caseLines.length ? block.indexOf(caseLines[index + 1]!) : block.length;
    const body = block.slice(start + 1, next);
    if (body.some(item => !item.narrative && item.indent <= line.indent)) {
      const malformed = body.find(item => !item.narrative && item.indent <= line.indent)!;
      throw new SurfaceError(malformed.number, "induction case tactics must be indented beneath the case header");
    }
    const parsed = parseInductionBranch(kernel, line, inductionDatatype, scope);
    if (parsed.inline && body.length > 0) throw new SurfaceError(body[0]!.number, "an inline induction case cannot also have an indented tactic body");
    if (!parsed.inline && body.every(item => item.narrative)) throw new SurfaceError(line.number, "induction case needs an inline tactic or an indented tactic body");
    return { header: line, body, parsed };
  }); } catch (error) {
    const failure = error instanceof SurfaceError ? error : new SurfaceError(inductionLine.number, String(error));
    failure.partialTrace = { initial, steps: [inductionStep], ...(narrative.length ? { narrative } : {}) };
    if (/expected a constructor case/.test(failure.message)) {
      failure.message = `line ${failure.line}: expected a ${shortName(inductionDatatype.predicate)} constructor case: ${suggestedCases.map(item => `\`${item}\``).join(" or ")}`;
    }
    throw failure;
  }
  const branchGoals = caseLines.map(line => inductionCaseState(
    kernel, line, generalizedGoal, motive, inductionVariable, outerAssumptions, inductionDatatype, inductionParameters, scope, outerRequirements));
  const traceSteps: TacticTraceStep[] = [{
    ...inductionStep, after: { goals: branchGoals },
  }];
  const cases: Extract<Proof, { rule: "induction" }>["cases"] = [];
  for (let index = 0; index < caseBlocks.length; index += 1) {
    const caseBlock = caseBlocks[index]!;
    const line = caseBlock.header;
    const before = { goals: branchGoals.slice(index) };
    const arrow = /=>|⇒/.exec(line.text)!;
    const headerEnd = arrow.index + arrow[0].length;
    const headerStep: TacticTraceStep = {
      line: line.number, columnStart: line.columnStart, columnEnd: (line.columnStart ?? 1) + headerEnd,
      command: line.text.slice(0, headerEnd), before,
      after: { goals: [branchGoals[index]!, ...branchGoals.slice(index + 1)] },
    };
    const scriptLines = caseBlock.parsed.inline
      ? splitTacticLine({
          number: line.number, text: caseBlock.parsed.inline, indent: line.indent,
          columnStart: (line.columnStart ?? 1) + headerEnd + Math.max(0, line.text.slice(headerEnd).search(/\S/)),
        })
      : joinTacticContinuations(caseBlock.body.filter(item => !item.narrative)).flatMap(splitTacticLine);
    try {
      const elaborated = elaborateCase(kernel, line, scriptLines, generalizedGoal, motive, inductionVariable, outerAssumptions,
        outerRequirements,
        outerBinders, inductionDatatype, inductionParameters, scope);
      cases.push(elaborated.case);
      traceSteps.push(headerStep);
      for (const step of elaborated.trace.steps) traceSteps.push({
        ...step,
        before: { goals: [...step.before.goals, ...branchGoals.slice(index + 1)] },
        after: { goals: [...step.after.goals, ...branchGoals.slice(index + 1)] },
      });
    } catch (error) {
      const failure = error instanceof SurfaceError
        ? error
        : new SurfaceError(line.number, error instanceof Error ? error.message : String(error));
      // A failed compact branch is still a source-level tactic step. Keep the
      // branch focused so editors can display the residual goal instead of a
      // serialized internal term.
      if (!failure.partialTrace) traceSteps.push({
        line: line.number, columnStart: line.columnStart, columnEnd: line.columnEnd,
        command: line.text, before, after: before,
      });
      else if (caseBlock.parsed.inline) {
        traceSteps.push(headerStep);
        for (const step of failure.partialTrace.steps) traceSteps.push({
          ...step,
          before: { goals: [...step.before.goals, ...branchGoals.slice(index + 1)] },
          after: { goals: [...step.after.goals, ...branchGoals.slice(index + 1)] },
        });
      } else {
        traceSteps.push({ line: line.number, command: line.text, before,
          after: { goals: [failure.partialTrace.initial.goals[0]!, ...branchGoals.slice(index + 1)] } });
        for (const step of failure.partialTrace.steps) traceSteps.push({
          ...step,
          before: { goals: [...step.before.goals, ...branchGoals.slice(index + 1)] },
          after: { goals: [...step.after.goals, ...branchGoals.slice(index + 1)] },
        });
      }
      failure.partialTrace ??= { initial, steps: traceSteps, ...(narrative.length ? { narrative } : {}), ...(scopeEntries.length ? { scope: scopeEntries } : {}) };
      if (failure.partialTrace.initial !== initial) failure.partialTrace = { initial, steps: traceSteps, ...(narrative.length ? { narrative } : {}), ...(scopeEntries.length ? { scope: scopeEntries } : {}) };
      throw failure;
    }
  }
  const inductive = induction(inductionDatatype.name, inductionVariable, motive, cases, inductionParameters);
  let canonicalProof: Proof = inductive;
  for (const binder of [...outerBinders].reverse()) {
    canonicalProof = forallIntro(binder.name, canonicalProof);
  }
  let canonicalStatement = forall(inductionVariable,
    imp(pred(inductionDatatype.predicate, ...inductionParameters, v(inductionVariable)), motive));
  for (const binder of [...outerBinders].reverse()) canonicalStatement = forall(binder.name, canonicalStatement);
  const targetAssumptions = [...binderAssumptions(binders), ...requirements];
  let statement = targetAssumptions.reduceRight<Formula>((result, assumption) => imp(assumption, result), goal);
  for (const binder of [...binders].reverse()) statement = forall(binder.name, statement);
  if (formulaEquals(canonicalStatement, statement)) {
    try {
      kernel.addTheorem(name, canonicalStatement, canonicalProof);
      kernel.setTheoremTacticTrace(name, { initial, steps: traceSteps, ...(narrative.length ? { narrative } : {}), ...(scopeEntries.length ? { scope: scopeEntries } : {}) });
    } catch (error) {
      if (error instanceof KernelError) throw new SurfaceError(header.number, error.message);
      throw error;
    }
    if (declarationKind === "instance") registerInstanceDeclaration(kernel, name, scope);
    return name;
  }
  // The public statement keeps the declared parameter and requirement order,
  // so `at` lists and positional `with` premises follow the header. The
  // induction proof quantifies its variable innermost, so whenever that order
  // differs (an induction variable that is not the last parameter, or a
  // generalized induction) the proof is admitted as a checked auxiliary and
  // the public theorem instantiates it in the declared order.
  const auxiliaryName = `${name}.generalized_induction_aux`;
  try {
    kernel.addTheorem(auxiliaryName, canonicalStatement, canonicalProof);
  } catch (error) {
    if (error instanceof KernelError) throw new SurfaceError(header.number, error.message);
    throw error;
  }
  let bodyProof: Proof = theorem(auxiliaryName);
  for (const binder of outerBinders) bodyProof = forallElim(bodyProof, v(binder.name));
  bodyProof = forallElim(bodyProof, v(inductionVariable));
  const inductionAssumption = pred(inductionDatatype.predicate, ...inductionParameters, v(inductionVariable));
  bodyProof = impElim(bodyProof, assume(inductionAssumption));
  for (const assumption of outerAssumptions) bodyProof = impElim(bodyProof, assume(assumption));
  for (const binder of generalizedBinders) bodyProof = forallElim(bodyProof, v(binder.name));
  for (const assumption of generalizedAssumptions) bodyProof = impElim(bodyProof, assume(assumption));
  let proof = targetAssumptions.reduceRight<Proof>((result, assumption) => impIntro(assumption, result), bodyProof);
  for (const binder of [...binders].reverse()) proof = forallIntro(binder.name, proof);
  try {
    kernel.addTheorem(name, statement, proof);
    kernel.setTheoremTacticTrace(name, { initial, steps: traceSteps, ...(narrative.length ? { narrative } : {}), ...(scopeEntries.length ? { scope: scopeEntries } : {}) });
  } catch (error) {
    if (error instanceof KernelError) throw new SurfaceError(header.number, error.message);
    throw error;
  }
  if (declarationKind === "instance") registerInstanceDeclaration(kernel, name, scope);
  return name;
}

function registerInstanceDeclaration(kernel: Kernel, name: string, scope: SurfaceScope): void {
  surfaceEnvironments.get(kernel)!.instances.push({ name, ...(scope.moduleName ? { module: scope.moduleName } : {}) });
}

function validateInstanceDeclaration(
  kernel: Kernel, goal: Formula, requirements: readonly Formula[], binders: readonly Binder[], line: number,
  visibility: ScopeVisibility | undefined,
): void {
  if (requirements.some(requirement => !instancePremiseShape(requirement))) {
    throw new SurfaceError(line, "instance premises must be predicates or conjunctions of predicates");
  }
  if (goal.tag !== "pred" || goal.args.length === 0) {
    throw new SurfaceError(line, "instance conclusion must be a predicate application");
  }
  // Every theorem variable must be fixed by the requested instance head, or
  // by a premise of a hypothesis shape or guard that synthesis matches
  // against a local fact, which keeps synthesis first-order, indexed, and
  // immune to open-ended metavariable enumeration.
  const headVariables = freeFormulaVariables(goal);
  const bound = new Set(headVariables);
  const atoms: Formula[] = [];
  const flatten = (formula: Formula): void => {
    if (formula.tag === "and") { flatten(formula.left); flatten(formula.right); } else atoms.push(formula);
  };
  [...binderAssumptions(binders), ...requirements].forEach(flatten);
  for (const atom of atoms) {
    if (atom.tag === "pred" && isBindingPredicate(kernel, atom.pred, visibility)) freeFormulaVariables(atom).forEach(name => bound.add(name));
  }
  const unsafe = binders.map(item => item.name).filter(name => !bound.has(name));
  if (unsafe.length) {
    throw new SurfaceError(line,
      `instance variables must occur in its conclusion or in a hypothesis-shaped premise; unconstrained: ${unsafe.join(", ")}`);
  }
}

function instancePremiseShape(formula: Formula): boolean {
  if (formula.tag === "pred" && formula.args.length > 0) return true;
  return formula.tag === "and" && instancePremiseShape(formula.left) && instancePremiseShape(formula.right);
}

function splitInlineProof(source: string): { readonly formula: string; readonly tactic: string; readonly tacticOffset: number } | undefined {
  let depth = 0;
  for (let index = 0; index <= source.length - 4; index += 1) {
    const character = source[index];
    if (character === "(" || character === "[" || character === "{") depth += 1;
    else if (character === ")" || character === "]" || character === "}") depth = Math.max(0, depth - 1);
    if (depth === 0 && source.slice(index, index + 4) === " by ") {
      const formula = source.slice(0, index).trimEnd();
      const tactic = source.slice(index + 4).trim();
      if (!formula || !tactic) return undefined;
      return { formula, tactic, tacticOffset: index + 4 + source.slice(index + 4).search(/\S/) };
    }
  }
  return undefined;
}

function elaborateDirectTheorem(
  kernel: Kernel,
  name: string,
  binders: readonly Binder[],
  requirements: readonly Formula[],
  goal: Formula,
  line: SourceLine,
  scope: SurfaceScope,
): void {
  const settleMatch = /^settle(?:\s+with\s+(.+))?$/.exec(line.text);
  const witnessMatch = /^witness\s+(.+?)\s*(?:=>|⇒)\s*settle(?:\s+with\s+(.+))?$/.exec(line.text);
  if (!settleMatch && !witnessMatch) throw new SurfaceError(line.number, "malformed direct proof");
  const assumptions = [...binderAssumptions(binders), ...requirements];
  const initial = tacticState(goal, assumptions, new Map());
  const ruleText = settleMatch?.[1] ?? witnessMatch?.[2];
  const names = ruleText ? splitTopLevel(ruleText, ",").map(item => item.trim()) : [];
  try {
    const rules = names.length ? resolveRules(kernel, names, line.number, scope) : defaultSettleRules(kernel, line.number, scope);
    const ground = defaultGroundRules(kernel, line.number, scope);
    let proof: Proof;
    if (witnessMatch) {
      if (goal.tag !== "exists") throw new SurfaceError(line.number, "witness proof requires an existential goal");
      const witness = parseTerm(witnessMatch[1]!, kernel, new Set(binders.map(item => item.name)), line.number, scope);
      const instance = substituteFormula(goal.body, goal.variable, witness);
      proof = existsIntro(goal.variable, goal.body, witness,
        settle(kernel, instance, { using: rules, assumptions, ground, visibility: scopeVisibility(kernel, scope) }));
    } else {
      proof = settle(kernel, goal, { using: rules, assumptions, ground, visibility: scopeVisibility(kernel, scope) });
    }
    proof = assumptions.reduceRight<Proof>((result, assumption) => impIntro(assumption, result), proof);
    for (const binder of [...binders].reverse()) proof = forallIntro(binder.name, proof);
    let statement = assumptions.reduceRight<Formula>((result, assumption) => imp(assumption, result), goal);
    for (const binder of [...binders].reverse()) statement = forall(binder.name, statement);
    kernel.addTheorem(name, statement, proof);
    kernel.setTheoremTacticTrace(name, {
      initial,
      steps: [{ line: line.number, command: line.text, before: initial, after: { goals: [] } }],
    });
  } catch (error) {
    const failure = error instanceof SurfaceError
      ? error
      : new SurfaceError(line.number, error instanceof Error ? error.message : String(error));
    failure.partialTrace ??= {
      initial,
      steps: [{ line: line.number, command: line.text, before: initial, after: initial }],
    };
    throw failure;
  }
}

interface LocalProof {
  readonly proof: Proof;
  readonly formula: Formula;
}

interface ParsedRequirement {
  readonly name?: string;
  readonly formula: Formula;
}

type DestructurePattern =
  | { readonly tag: "bind"; readonly name: string }
  | { readonly tag: "substitute" }
  | { readonly tag: "tuple"; readonly items: readonly DestructurePattern[] };

/** Parse the recursive pattern language shared by `obtain` and `rcases`. */
function parseDestructurePattern(text: string, line: number): DestructurePattern {
  const source = text.trim();
  const delimited = (source.startsWith("⟨") && source.endsWith("⟩")) ||
    (source.startsWith("(") && source.endsWith(")"));
  if (delimited) {
    const items = splitPatternItems(source.slice(1, -1));
    if (items.length < 2) throw new SurfaceError(line, "a destructuring pattern needs at least two entries");
    return { tag: "tuple", items: items.map(item => parseDestructurePattern(item, line)) };
  }
  if (source === "rfl") return { tag: "substitute" };
  if (source !== "_" && !SIMPLE_IDENTIFIER.test(source)) {
    throw new SurfaceError(line, `malformed destructuring pattern ${source}`);
  }
  return { tag: "bind", name: source };
}

function splitPatternItems(text: string): string[] {
  const result: string[] = [];
  let depth = 0;
  let start = 0;
  for (let index = 0; index < text.length; index += 1) {
    const character = text[index];
    if (character === "(" || character === "{" || character === "[" || character === "⟨") depth += 1;
    else if (character === ")" || character === "}" || character === "]" || character === "⟩") depth -= 1;
    else if (character === "," && depth === 0) {
      result.push(text.slice(start, index).trim());
      start = index + 1;
    }
    if (depth < 0) return [text];
  }
  result.push(text.slice(start).trim());
  return result;
}

function parseRequirement(
  line: SourceLine,
  kernel: Kernel,
  variables: ReadonlySet<string>,
  scope: SurfaceScope,
): ParsedRequirement {
  const match = /^requires\s+(?:([\p{L}_][\p{L}\p{M}\p{N}_]*)\s*:\s*)?(.+)$/u.exec(line.text);
  if (!match) throw new SurfaceError(line.number, "malformed requirement");
  return {
    name: match[1],
    formula: line.parsedFormula ?? parseFormula(match[2]!, kernel, variables, line.number, scope),
  };
}

interface TacticGoal {
  // Lexical term scope travels with the goal, never with a sibling proof.
  readonly variables: Set<string>;
  readonly goal: Formula;
  readonly assumptions: readonly Formula[];
  readonly locals: Map<string, LocalProof>;
  readonly close: (proof: Proof) => void;
}

interface TacticScriptSeed {
  readonly assumptions: readonly Formula[];
  readonly locals: ReadonlyMap<string, LocalProof>;
  readonly variables: ReadonlySet<string>;
}

interface TacticScriptResult {
  readonly proof: Proof;
  readonly trace: TacticTrace;
}

function admitSorry(kernel: Kernel, theoremName: string, line: number, current: TacticGoal): Proof {
  let statement = current.assumptions.reduceRight<Formula>((result, assumption) => imp(assumption, result), current.goal);
  const variables = [...freeFormulaVariables(statement)].sort();
  for (const variable of [...variables].reverse()) statement = forall(variable, statement);

  const records = surfaceSorries.get(kernel) ?? [];
  let ordinal = records.filter(item => item.theorem === theoremName).length + 1;
  let axiomName = `sorry.${theoremName}.${line}.${ordinal}`;
  while (kernel.axioms.has(axiomName) || kernel.theorems.has(axiomName)) {
    ordinal += 1;
    axiomName = `sorry.${theoremName}.${line}.${ordinal}`;
  }
  kernel.addAxiom(axiomName, statement);

  let proof: Proof = axiom(axiomName);
  if (variables.length) proof = at(proof, ...variables.map(v));
  for (const assumption of current.assumptions) proof = impElim(proof, assume(assumption));
  records.push({ theorem: theoremName, axiom: axiomName, line, goal: current.goal });
  surfaceSorries.set(kernel, records);
  return proof;
}

interface ParsedInductionBranch {
  readonly constructor: ConstructorSpec;
  readonly fields: readonly string[];
  readonly hypotheses: readonly string[];
  readonly inline?: string;
  /** The case was written `| k + 1 =>`: its goal is presented with k + 1 in place of succ(k). */
  readonly successorSugar?: boolean;
}

function shortName(name: string): string { return name.split(".").at(-1)!; }

function inductionCaseSuggestions(kernel: Kernel, datatype: DatatypeRecord, scope: SurfaceScope): readonly string[] {
  const surface = surfaceEnvironments.get(kernel)?.datatypes.get(datatype.predicate);
  return datatype.constructors.map((constructor, constructorIndex) => {
    const recorded = surface?.constructors.find(item => item.name === constructor.name);
    const predicateName = shortName(datatype.predicate);
    const parts = constructor.name.split(".");
    const shortConstructorName = parts.length > 1 && parts.at(-2) === predicateName
      ? `${predicateName}.${parts.at(-1)}` : shortName(constructor.name);
    // Suggested branches are parsed to build the initial goal trace. Imported
    // constructors under nested namespaces may not resolve by their short name.
    const constructorName = resolveOptional(shortConstructorName, scope, candidate =>
      [...kernel.datatypes.values()].some(data => data.constructors.some(item => item.name === candidate))) === constructor.name
      ? shortConstructorName : constructor.name;
    const fields = Array.from({ length: constructor.arity }, (_, fieldIndex) =>
      recorded?.fields[fieldIndex]?.name ?? (constructor.recursiveFields.includes(fieldIndex)
        ? (constructor.recursiveFields.length === 1 ? "tail" : `part${fieldIndex + 1}`)
        : `x${fieldIndex + 1}`));
    const hypotheses = constructor.recursiveFields.map((fieldIndex, recursiveIndex) => {
      const field = fields[fieldIndex]!;
      return constructor.recursiveFields.length === 1 ? "ih"
        : `ih${field[0]!.toUpperCase()}${field.slice(1) || recursiveIndex + 1}`;
    });
    const pattern = `${constructorName}${fields.length ? `(${fields.join(", ")})` : ""}`;
    return `| ${pattern}${hypotheses.length ? ` using ${hypotheses.join(", ")}` : ""} =>`;
  });
}

/** Newlines are preferred, but semicolons permit compact sequential scripts. */
function splitTacticLine(line: SourceLine): readonly SourceLine[] {
  const pieces: { text: string; start: number; end: number; indent: number; bullet: boolean }[] = [];
  let start = 0;
  let depth = 0;
  // A `by` owns the rest of the line: `_ = t := by rw h; ring` and
  // `have h : P by rw h; ring` run both tactics on the nested goal, so a
  // `;` after the `by` is split by the nested script, not here.
  let owned = false;
  for (let index = 0; index <= line.text.length; index += 1) {
    const character = line.text[index];
    if (character === "(" || character === "[" || character === "{") depth += 1;
    else if (character === ")" || character === "]" || character === "}") depth = Math.max(0, depth - 1);
    if (depth === 0 && !owned && tacticByAt(line.text, index)) owned = true;
    if (index === line.text.length || (character === ";" && depth === 0 && !owned)) {
      const raw = line.text.slice(start, index);
      const leading = raw.match(/^\s*/)![0].length;
      const trailing = raw.match(/\s*$/)![0].length;
      const trimmed = raw.trim();
      const bulletWidth = /^\.\s*/.exec(trimmed)?.[0].length ?? 0;
      const text = trimmed.slice(bulletWidth);
      // The command following a bullet begins inside that branch. Preserve
      // its effective indentation for nested `have` and `calc` bodies.
      if (text) pieces.push({ text, start: start + leading, end: index - trailing,
        indent: line.indent + bulletWidth, bullet: bulletWidth > 0 });
      start = index + 1;
    }
  }
  return pieces.flatMap(piece => {
    const base = {
      number: line.number, indent: piece.indent, ...(piece.bullet ? { bullet: true as const } : {}),
      columnStart: (line.columnStart ?? 1) + piece.start,
      columnEnd: (line.columnStart ?? 1) + piece.end,
    };
    // rw [a, b, ← c] (at h) is the sequence of single rewrites.
    const list = /^(rewrite|rw|rwa)\s+(under\s+)?\[(.*)\](\s+at\s+[\p{L}_][\p{L}\p{M}\p{N}_']*)?$/u.exec(piece.text);
    const rules = list ? splitTopLevel(list[3]!, ",").map(item => item.trim()).filter(Boolean) : [];
    if (list && rules.length > 1) {
      // Only the first rewrite of the list begins the bullet; the rest
      // continue its branch. Each rewrite is located at its own rule, so a
      // failure in the list points at the rule that failed.
      const listStart = piece.text.indexOf("[") + 1;
      let searchFrom = listStart;
      return rules.map((rule, index) => {
        const ruleStart = piece.text.indexOf(rule, searchFrom);
        searchFrom = ruleStart + rule.length;
        return {
          ...base, ...(index > 0 ? { bullet: undefined } : {}),
          columnStart: base.columnStart + (index === 0 ? 0 : ruleStart),
          columnEnd: index === rules.length - 1 ? base.columnEnd : base.columnStart + ruleStart + rule.length,
          text: `${index === rules.length - 1 ? list[1] : "rw"} ${list[2] ?? ""}${rule}${list[4] ?? ""}`,
        };
      });
    }
    return [{ ...base, text: piece.text }];
  });
}

/** Whether the word `by` that introduces a tactic begins at `index`: the
 * `by` of `have h : P by …` or `:= by …`, not the `by` of `ordered by` or
 * `certified by` in a well-founded induction. */
function tacticByAt(text: string, index: number): boolean {
  if (text.slice(index, index + 2) !== "by") return false;
  if (index > 0 && !/\s/u.test(text[index - 1]!)) return false;
  if (index + 2 < text.length && !/\s/u.test(text[index + 2]!)) return false;
  const before = text.slice(0, index).trimEnd();
  return !/(?:^|\s)(?:ordered|certified)$/u.test(before);
}

/** Join a physical continuation only while the tactic grammar is incomplete,
 * which preserves the usual one-line boundary and gives continuations a stable,
 * parser-independent shape: open delimiters, a trailing comma/operator, or a
 * command ending where an argument is required. Continuations are indented;
 * an aligned line is accepted only to close an open delimiter.
 */
function joinTacticContinuations(lines: readonly SourceLine[]): readonly SourceLine[] {
  const result: SourceLine[] = [];
  for (const line of lines) {
    const previous = result.at(-1);
    if (previous) {
      const balance = delimiterBalance(previous.text);
      const indented = line.indent > previous.indent;
      const indentedContinuation = indented && tacticLineNeedsContinuation(previous.text);
      // A more-indented line that begins with a clause keyword or a binary
      // operator continues the step above it, as does any more-indented
      // line after a step that never opens a block of its own.
      const leadingClause = indented && /^(?:with|at|using)\b/u.test(line.text);
      const leadingOperator = indented && CONTINUATION_OPERATOR_START.test(line.text);
      const openStep = indented && !line.bullet && !line.text.startsWith("|") && !/^\.\s/u.test(line.text) &&
        !STEP_KEYWORD_START.test(line.text) && BLOCKLESS_STEP.test(previous.text) && !tacticLineOpensBlock(previous.text);
      if (balance > 0 || indentedContinuation || leadingClause || leadingOperator || openStep) {
        result[result.length - 1] = { ...previous, text: `${previous.text} ${line.text}` };
        continue;
      }
    }
    result.push(line);
  }
  return result;
}

/** The binary operators a proposition or term may break before or after. */
const CONTINUATION_OPERATORS =
  "→|->|↔|<->|∧|∨|=|≠|\\+|-|\\*|/|∘|∈|∉|⊆|⊂|⊇|⊃|∪|∩|∖|×|≤|≥|<|>|∣|⊑|⊓|⊔|↦|⟶|⇒|⧸|≃|≅|⊕|⊗|·ₐ|\\^";
const CONTINUATION_OPERATOR_START = new RegExp(`^(?:${CONTINUATION_OPERATORS})\\s`, "u");
/** Steps whose argument may run on, since nothing indented beneath them is a block of theirs. */
const BLOCKLESS_STEP = /^(?:exact|apply|witness|use|refine|specialize|obtain|rewrite|rw|rwa|unfold|intro|intros|symm|settle)\b/u;
/** A line that begins a step of its own, never a continuation. */
const STEP_KEYWORD_START = new RegExp("^(?:" + [
  "exact", "apply", "witness", "use", "refine", "show", "specialize", "obtain", "rewrite", "rw", "rwa", "unfold", "intro",
  "intros", "symm", "settle", "have", "calc", "simp", "simpa", "ring", "ring_nf", "linarith", "arith", "tauto", "cc",
  "congruence", "left", "right", "constructor", "split", "assumption", "contradiction", "exfalso", "by_contra", "by_cases",
  "reflexivity", "rfl", "compute", "decide", "sorry", "cases", "rcases", "clear", "rename", "revert", "induction", "ext",
  "linear_combination", "typecheck", "synthesize", "exact\\?", "apply\\?", "rw\\?",
].join("|") + ")(?:\\s|$)", "u");

/** `have h : P` and `have h : P by` own the indented block beneath them. */
function tacticLineOpensBlock(text: string): boolean {
  return /\bby\s*$/u.test(text) || (/^have\s/u.test(text) && findTopLevel(text, ":=") < 0 && findTopLevelWord(text, "by") < 0);
}

function tacticLineNeedsContinuation(text: string): boolean {
  // The premise wildcard completes an application; it is not multiplication.
  // In a bullet branch the next tactic is indented relative to `. have ...`.
  if (/(?:\bwith|,)\s*\*\s*$/u.test(text)) return false;
  // `have h :` with nothing after the colon takes its proposition from the
  // next, more indented line.
  if (/^have\s+[\p{L}_][\p{L}\p{M}\p{N}_]*\s*:$/u.test(text)) return true;
  return /[,]\s*$/.test(text) ||
    new RegExp(`(?:\\bat|\\bwith|\\busing|:=|=>|${CONTINUATION_OPERATORS}|\\band|\\bor)\\s*$`, "u").test(text) ||
    /^(?:exact|apply|rewrite|rw|unfold|have|specialize|obtain|cases|rcases|clear|rename|revert|witness|use)\s*$/.test(text);
}

function delimiterBalance(text: string): number {
  let balance = 0;
  for (const character of text) {
    if (character === "(" || character === "[" || character === "{" || character === "⟨") balance += 1;
    else if (character === ")" || character === "]" || character === "}" || character === "⟩") balance -= 1;
  }
  return balance;
}

function parseInductionBranch(
  kernel: Kernel, line: SourceLine, datatype: DatatypeRecord, scope: SurfaceScope,
): ParsedInductionBranch {
  const match = /^\|\s*(.+?)(?:\s+using\s+(.+?))?\s*(?:=>|⇒)(?:\s*(.*))?$/.exec(line.text);
  if (!match) throw new SurfaceError(line.number, "expected a constructor case such as `| C(x) =>` or `| C(x) => simp`");
  // `| k + 1 =>` is the successor case written as arithmetic; the case is
  // the constructor's, and its goal is presented with k + 1.
  const successorSugar = /^([\p{L}_][\p{L}\p{M}\p{N}_]*)\s*\+\s*1$/u.exec(match[1]!);
  const successor = successorSugar ? datatype.constructors.find(item => item.name.split(".").at(-1) === "succ" && item.recursiveFields.length === 1) : undefined;
  if (successorSugar && !successor) throw new SurfaceError(line.number, `${datatype.predicate} has no successor constructor for the case ${match[1]}`);
  const pattern = successor ? { tag: "ctor" as const, name: successor.name, args: [{ tag: "bind" as const, name: successorSugar![1]! }] } : parsePattern(match[1]!, kernel, scope, line.number);
  if (pattern.tag !== "ctor") throw new SurfaceError(line.number, "an induction case must start with a constructor");
  const constructor = datatype.constructors.find(item => item.name === pattern.name);
  if (!constructor) throw new SurfaceError(line.number, `${pattern.name} is not a constructor of ${datatype.predicate}`);
  if (pattern.args.some(item => item.tag !== "bind")) throw new SurfaceError(line.number, "induction constructor fields must be distinct variables");
  const fields = pattern.args.map(item => (item as Extract<Pattern, { tag: "bind" }>).name);
  if (new Set(fields).size !== fields.length) throw new SurfaceError(line.number, "induction constructor fields must be distinct variables");
  const hypotheses = match[2]?.trim() ? splitTopLevel(match[2]!, ",").map(item => item.trim()) : [];
  if (hypotheses.length !== constructor.recursiveFields.length || hypotheses.some(item => !SIMPLE_IDENTIFIER.test(item))) {
    throw new SurfaceError(line.number,
      `case ${pattern.name} needs ${constructor.recursiveFields.length} induction ${constructor.recursiveFields.length === 1 ? "hypothesis" : "hypotheses"}`);
  }
  const inline = match[3]?.trim() || undefined;
  return { constructor, fields, hypotheses, inline, ...(successor ? { successorSugar: true } : {}) };
}

/**
 * The goal of a `| k + 1 =>` case: the induction variable replaced by k + 1,
 * with a transport from a proof of that goal to the constructor form the
 * induction rule checks, through add.right_one : k + 1 = succ(k) at k.
 */
function successorCasePresentation(
  kernel: Kernel, line: number, scope: SurfaceScope, goal: Formula, inductionVariable: string, field: string, natPredicate: string,
): { readonly goal: Formula; readonly transport: (proof: Proof) => Proof } {
  // The `+` of natural numbers is the visible notation's target, so the
  // case is available wherever n + 1 can be written.
  const plus = visibleInfixNotationGroups(kernel, scope, line, "function").get("+")
    ?.find(item => item.operandType?.split(".").at(-1) === natPredicate.split(".").at(-1) || !item.operandType)?.target ??
    resolveOptional("add", scope, candidate => kernel.functions.get(candidate) === 2);
  if (!plus) throw new SurfaceError(line, "a `| k + 1 =>` case needs the + notation of natural numbers; import Grace.Core.Nat");
  const rightOne = resolveOptional("add.right_one", scope, candidate => kernel.theorems.has(candidate)) ??
    (kernel.theorems.has("Grace.Core.Nat.Algebra.add.right_one") ? "Grace.Core.Nat.Algebra.add.right_one" : undefined);
  if (!rightOne) throw new SurfaceError(line, "a `| k + 1 =>` case needs add.right_one; import Grace.Core.Nat.Algebra");
  const presented = substituteFormula(goal, inductionVariable, app(plus, v(field), nat(1)));
  const equality = impElim(at(theorem(rightOne), v(field)), assume(pred(natPredicate, v(field))));
  return { goal: presented, transport: proof => eqElim(equality, inductionVariable, goal, proof) };
}

function inductionCaseState(
  kernel: Kernel,
  line: SourceLine,
  goal: Formula,
  motive: Formula,
  inductionVariable: string,
  outerAssumptions: readonly Formula[],
  datatype: DatatypeRecord,
  parameters: readonly Term[],
  scope: SurfaceScope,
  requirements: readonly ParsedRequirement[],
): TacticStateSnapshot["goals"][number] {
  const branch = parseInductionBranch(kernel, line, datatype, scope);
  const branchTerm = app(branch.constructor.name, ...branch.fields.map(v));
  const branchGoal = branch.successorSugar
    ? successorCasePresentation(kernel, line.number, scope, goal, inductionVariable, branch.fields[0]!, datatype.predicate).goal
    : substituteFormula(goal, inductionVariable, branchTerm);
  const recursive = branch.constructor.recursiveFields.map((fieldIndex, index) => ({
    field: branch.fields[fieldIndex]!, name: branch.hypotheses[index]!,
  }));
  const inductionAssumptions = branch.fields.flatMap((field, fieldIndex) => {
    const recursiveIndex = branch.constructor.recursiveFields.indexOf(fieldIndex);
    if (recursiveIndex >= 0) return [
      pred(datatype.predicate, ...parameters, v(field)),
      substituteFormula(motive, inductionVariable, v(field)),
    ];
    const parameterField = branch.constructor.parameterFields?.find(item => item.field === fieldIndex);
    return parameterField ? [pred("in", v(field), parameters[parameterField.parameter]!)] : [];
  });
  // Mirror the context seeded by elaborateCase, including discharged outer
  // premises in the IH and the names of independent requirements.
  const locals = new Map<string, Formula>();
  requirements.forEach((requirement, index) => {
    locals.set(requirement.name ?? `requirement${index + 1}`, requirement.formula);
  });
  recursive.forEach(item => {
    let formula = substituteFormula(motive, inductionVariable, v(item.field));
    for (const assumption of outerAssumptions) {
      if (formula.tag !== "imp" || !formulaEquals(formula.left, assumption)) {
        throw new SurfaceError(line.number, `internal induction motive mismatch for ${item.name}`);
      }
      formula = formula.right;
    }
    locals.set(item.name, formula);
  });
  branch.fields.forEach(field => {
    const typeFormula = inductionAssumptions.find(formula => formula.tag === "pred" &&
      formula.args.some(argument => argument.tag === "var" && argument.name === field));
    if (typeFormula) {
      let localName = `h_${field}`;
      while (locals.has(localName)) localName += "_";
      locals.set(localName, typeFormula);
    }
  });
  return {
    goal: branchGoal,
    assumptions: [...inductionAssumptions, ...outerAssumptions],
    locals: [...locals].map(([name, formula]) => ({ name, formula })),
  };
}

/** Elaborate a sequential tactic script into an ordinary primitive proof term. */
function elaborateTacticTheorem(
  kernel: Kernel,
  name: string,
  binders: readonly Binder[],
  requirements: readonly Formula[],
  requirementNames: readonly (string | undefined)[],
  goal: Formula,
  lines: readonly SourceLine[],
  outerScope: SurfaceScope,
  seed?: TacticScriptSeed,
  narrative: readonly ProofNarrativeEntry[] = [],
  scopeEntries: readonly TacticScopeEntry[] = [],
): TacticScriptResult | void {
  const captureTrace = surfaceEnvironments.get(kernel)?.captureTacticTraces ?? true;
  const assumptions = seed ? [...seed.assumptions] : [...binderAssumptions(binders), ...requirements];
  const namedRequirements = requirementNames.filter((item): item is string => item !== undefined);
  if (new Set(namedRequirements).size !== namedRequirements.length) {
    throw new SurfaceError(lines[0]!.number, "requirement names must be distinct");
  }
  let variables = new Set(seed ? seed.variables : binders.map(item => item.name));
  let rootProof: Proof | undefined;
  const pending: TacticGoal[] = [{
    variables,
    goal,
    assumptions,
    locals: seed ? new Map(seed.locals) :
      new Map(requirements.map((formula, index) => [requirementNames[index] ?? `requirement${index + 1}`, { formula, proof: assume(formula) }])),
    close: proof => { rootProof = proof; },
  }];
  let resolutionLine = outerScope.line;
  const scope: SurfaceScope = {
    ...outerScope,
    get line() { return resolutionLine; },
    localFormulas: () => {
      const current = pending[0];
      return current
        ? [...current.assumptions, ...[...current.locals.values()].map(item => item.formula)]
        : [];
    },
    goal: () => pending[0]?.goal,
  };
  const visibility = scopeVisibility(kernel, scope);
  const snapshot = (): TacticStateSnapshot => !captureTrace ? { goals: [] } : ({
    goals: pending.map(item => ({
      goal: item.goal,
      assumptions: [...item.assumptions],
      locals: [...item.locals].map(([localName, local]) => ({ name: localName, formula: local.formula })),
    })),
  });
  const initial = snapshot();
  const traceSteps: TacticTraceStep[] = [];
  const localProofFrames: {
    readonly indent: number;
    readonly name: string;
    readonly continuation: TacticGoal;
  }[] = [];
  let calculation: { readonly indent: number } | undefined;
  // Bullet branches. A step written in a branch whose goal is already
  // closed, and that does not apply to the goal it reaches instead, is
  // reported with the line that closed the branch. A branch is closed once
  // the goals pending when its bullet was read, less its own, are all that
  // remain.
  const branchFrames: { readonly indent: number; readonly remaining: number; closedAt?: SourceLine }[] = [];

  interface CalculationRelation {
    readonly key: string;
    readonly left: Term;
    readonly right: Term;
    readonly rebuild: (left: Term, right: Term) => Formula;
  }
  const calculationRelation = (formula: Formula): CalculationRelation | undefined => {
    if (formula.tag === "eq") return {
      key: "=", left: formula.left, right: formula.right, rebuild: eq,
    };
    if (formula.tag !== "pred") return undefined;
    if (formula.args.length === 2) return {
      key: `predicate:${formula.pred}`,
      left: formula.args[0]!, right: formula.args[1]!,
      rebuild: (left, right) => pred(formula.pred, left, right),
    };
    if (formula.args.length === 3 && formula.pred.endsWith("relates")) {
      const relation = formula.args[0]!;
      return {
        key: `relation:${termCanonical(relation)}`,
        left: formula.args[1]!, right: formula.args[2]!,
        rebuild: (left, right) => pred(formula.pred, relation, left, right),
      };
    }
    return undefined;
  };
  const parseCalculationFormula = (text: string, endpoint: Term, line: number): Formula => {
    const carried = /^_\s*(=|<|≤)\s*(.+)$/u.exec(text);
    if (!carried) return parseFormula(text, kernel, variables, line, scope);
    // The endpoint is written into the step as printed for reading back,
    // which lets the right side take its notation from it; an endpoint whose
    // text still reads as a different term is put in place of a hole.
    const printed = parseFormula(`${formatTerm(endpoint, { reparse: true })} ${carried[1]} ${carried[2]}`, kernel, variables, line, scope);
    const relation = calculationRelation(printed);
    if (relation && termEquals(relation.left, endpoint)) return printed;
    let hole = "_endpoint";
    while (variables.has(hole) || freeTermVariables(endpoint).has(hole)) hole += "_";
    const parsed = parseFormula(`${hole} ${carried[1]} ${carried[2]}`, kernel, new Set([...variables, hole]), line, scope);
    return substituteFormula(parsed, hole, endpoint);
  };
  const relationKind = (relation: CalculationRelation): "eq" | "less" | "lessEqual" | undefined => {
    if (relation.key === "=") return "eq";
    if (relation.key.endsWith("LessEqual") || relation.key.includes("realLe")) return "lessEqual";
    if (relation.key.endsWith("Less") || relation.key.includes("rationalLess") || relation.key.includes("realLess")) return "less";
    return undefined;
  };
  const calculationTransitivity = (
    line: number,
    first: CalculationRelation,
    second: CalculationRelation,
    result: CalculationRelation,
    firstProof: Proof,
    secondProof: Proof,
    assumptions: readonly Formula[],
    facts: readonly Proof[],
  ): Proof => {
    if (first.key === "=" && second.key === "=" && result.key === "=") return calc(firstProof, secondProof);
    // Equality steps transport either endpoint of any registered relation,
    // so calculations such as `x ≤ y < z = w` stay mathematical without
    // requiring a separate transitivity theorem for every equality placement.
    if (first.key === "=" && second.key === result.key) {
      let variable = "__calc";
      const forbidden = new Set([
        ...freeTermVariables(first.left), ...freeTermVariables(first.right),
        ...freeTermVariables(second.right),
      ]);
      while (forbidden.has(variable)) variable += "_";
      return eqElim(firstProof, variable, second.rebuild(v(variable), second.right), secondProof, true);
    }
    if (second.key === "=" && first.key === result.key) {
      let variable = "__calc";
      const forbidden = new Set([
        ...freeTermVariables(first.left), ...freeTermVariables(second.left),
        ...freeTermVariables(second.right),
      ]);
      while (forbidden.has(variable)) variable += "_";
      return eqElim(secondProof, variable, first.rebuild(first.left, v(variable)), firstProof);
    }
    const firstKind = relationKind(first);
    const secondKind = relationKind(second);
    const resultKind = relationKind(result);
    let theoremName: string | undefined;
    if (first.key === second.key && second.key === result.key && firstKind === "less") {
      if (first.key.includes("rationalLess")) theoremName = "Grace.Cumulus.Rat.OrderedOperations.rationalLess.transitive";
      else if (first.key.includes("realLess")) theoremName = "Grace.Cumulus.Real.Core.realLess.transitive";
      else if (first.key.endsWith("Less")) theoremName = "Grace.Cumulus.Nat.Order.Less.transitive";
    } else if (first.key === second.key && second.key === result.key && firstKind === "lessEqual") {
      theoremName = first.key.includes("realLe")
        ? "Grace.Cumulus.Real.Ring.realLe.transitive"
        : "Grace.Core.Nat.Order.LessEqual.transitive";
    } else if (first.key.includes("realLe") && second.key.includes("realLess") && result.key.includes("realLess")) {
      theoremName = "Grace.Cumulus.Real.Ring.realLe.transitive_less";
    } else if (first.key.includes("realLess") && second.key.includes("realLe") && result.key.includes("realLess")) {
      theoremName = "Grace.Cumulus.Real.Ring.realLess.transitive_le";
    } else if (first.key.endsWith("Less") && second.key.endsWith("LessEqual") && result.key.endsWith("Less")) {
      theoremName = "Grace.Cumulus.Nat.Order.Less.transitive_LessEqual";
    } else if (first.key.endsWith("LessEqual") && second.key.endsWith("Less") && result.key.endsWith("Less")) {
      theoremName = "Grace.Cumulus.Nat.Order.LessEqual.transitive_Less";
    }
    if (!theoremName || !firstKind || !secondKind || !resultKind) {
      throw new SurfaceError(line,
        `calc has no checked composition rule for ${firstKind ?? first.key}, ${secondKind ?? second.key} ⟹ ${resultKind ?? result.key}`);
    }
    let proof = at(resolveProof(kernel, theoremName, line, scope), first.left, first.right, second.right);
    const refinements = prepareRefinementProver(kernel, assumptions, facts, visibility);
    let usedFirst = false;
    let usedSecond = false;
    while (true) {
      const formula = kernel.checkProof(proof, assumptions);
      if (formula.tag !== "imp") break;
      if (!usedFirst && formulaEquals(formula.left, first.rebuild(first.left, first.right))) {
        proof = impElim(proof, firstProof); usedFirst = true; continue;
      }
      if (!usedSecond && formulaEquals(formula.left, second.rebuild(second.left, second.right))) {
        proof = impElim(proof, secondProof); usedSecond = true; continue;
      }
      if (formula.left.tag === "pred" && formula.left.args.length === 1) {
        const evidence = refinements.prove(formula.left.args[0]!, formula.left.pred);
        if (evidence) { proof = impElim(proof, evidence); continue; }
      }
      throw new SurfaceError(line, `calc could not establish transitivity premise ${formatFormula(formula.left)}`);
    }
    return proof;
  };

  const focused = (line: SourceLine): TacticGoal => {
    const current = pending[0];
    if (!current) throw new SurfaceError(line.number, "no goals remain");
    return current;
  };
  const close = (line: SourceLine, given: Proof): void => {
    const current = focused(line);
    let proof = given;
    let actual: Formula;
    try { actual = kernel.checkProof(proof, current.assumptions); }
    catch (error) { throw new SurfaceError(line.number, error instanceof Error ? error.message : String(error)); }
    if (!formulaEquals(actual, current.goal)) {
      const bridged = bridgeDefinition(kernel, scope, line.number, proof, actual, current.goal, current.assumptions, current.locals);
      if (!bridged) {
        throw new SurfaceError(line.number, `proof establishes ${formatFormula(actual)}, but the goal is ${formatFormula(current.goal)}`);
      }
      proof = bridged;
    }
    pending.shift();
    current.close(proof);
  };
  const replaceWith = (
    line: SourceLine,
    specifications: readonly { goal: Formula; assumptions?: readonly Formula[]; locals?: Map<string, LocalProof> }[],
    combine: (proofs: readonly Proof[]) => Proof,
  ): void => {
    const current = focused(line);
    pending.shift();
    const proofs: (Proof | undefined)[] = specifications.map(() => undefined);
    let remaining = proofs.length;
    const children = specifications.map((specification, index): TacticGoal => ({
      variables: new Set(variables),
      goal: specification.goal,
      assumptions: specification.assumptions ?? current.assumptions,
      locals: specification.locals ?? new Map(current.locals),
      close: proof => {
        proofs[index] = proof;
        remaining -= 1;
        if (remaining === 0) current.close(combine(proofs as Proof[]));
      },
    }));
    pending.unshift(...children);
  };

  const destructureProof = (
    line: SourceLine,
    current: TacticGoal,
    pattern: DestructurePattern,
    sourceFormula: Formula,
    sourceProof: Proof,
    replaceableName?: string,
    shadowLocals = false,
  ): void => {
    let assumptions = [...current.assumptions];
    const locals = new Map(current.locals);
    let goal = current.goal;
    if (replaceableName) locals.delete(replaceableName);
    let wrap = (proof: Proof): Proof => proof;

    const match = (activePattern: DestructurePattern, formula: Formula, proof: Proof): void => {
      if (activePattern.tag === "substitute") {
        if (formula.tag !== "eq") {
          throw new SurfaceError(line.number, `rfl pattern needs an equality, not ${formatFormula(formula)}`);
        }
        const leftVariable = formula.left.tag === "var" && !freeTermVariables(formula.right).has(formula.left.name);
        const rightVariable = formula.right.tag === "var" && !freeTermVariables(formula.left).has(formula.right.name);
        if (!leftVariable && !rightVariable) {
          throw new SurfaceError(line.number,
            `rfl pattern needs an equality with a substitutable variable, not ${formatFormula(formula)}`);
        }
        const reverse = !leftVariable && rightVariable;
        const eliminated = (leftVariable ? formula.left : formula.right) as Extract<Term, { tag: "var" }>;
        const facts = [...locals.values()].map(item => item.proof);
        if (freeFormulaVariables(goal).has(eliminated.name)) {
          const rewrittenGoal = rewriteGoal(kernel, goal, proof, assumptions, facts, reverse, true, undefined, visibility);
          goal = rewrittenGoal.goal;
          const previousWrap = wrap;
          wrap = body => previousWrap(rewrittenGoal.lift(body));
        }
        for (const [name, local] of [...locals]) {
          if (local.proof === proof) { locals.delete(name); continue; }
          if (!freeFormulaVariables(local.formula).has(eliminated.name)) continue;
          try {
            locals.set(name, rewriteFact(kernel, local.proof, proof, assumptions,
              [...locals.values()].filter(item => item !== local).map(item => item.proof), reverse, true, undefined, visibility));
          } catch {
            // A fact not mentioning the eliminated variable remains valid.
          }
        }
        return;
      }
      if (activePattern.tag === "bind") {
        if (activePattern.name === "_") return;
        if (variables.has(activePattern.name) || (!shadowLocals && locals.has(activePattern.name))) {
          throw new SurfaceError(line.number, `${activePattern.name} is already in scope`);
        }
        locals.set(activePattern.name, { formula, proof });
        return;
      }
      if (formula.tag === "pred") {
        try {
          let unfolded = unfoldFormula(kernel, resolveProof(kernel, formula.pred, line.number, scope),
            { formula, proof }, assumptions, line.number);
          const generatedGuards = predicateSoftGuardCount(formula.pred, kernel, scope);
          for (let index = 0; index < generatedGuards && unfolded.formula.tag === "and"; index += 1) {
            unfolded = { formula: unfolded.formula.right, proof: andElimRight(unfolded.proof) };
          }
          if (unfolded.formula.tag === "exists" || unfolded.formula.tag === "and" || unfolded.formula.tag === "pred") {
            match(activePattern, unfolded.formula, unfolded.proof);
            return;
          }
        } catch {
          // The structural diagnostic below is clearer when the
          // predicate is primitive or does not expose a matching shape.
        }
      }
      const [first, ...tail] = activePattern.items;
      if (!first || tail.length === 0) throw new SurfaceError(line.number, "incomplete destructuring pattern");
      const remainder: DestructurePattern = tail.length === 1 ? tail[0]! : { tag: "tuple", items: tail };
      if (formula.tag === "exists") {
        if (first.tag !== "bind") {
          throw new SurfaceError(line.number, "an existential witness needs a name or _");
        }
        const forbidden = new Set([...variables, ...locals.keys()]);
        assumptions.forEach(item => freeFormulaVariables(item).forEach(name => forbidden.add(name)));
        const witness = first.name === "_" ? freshSurfaceVariable("witness", forbidden) : first.name;
        if (forbidden.has(witness)) throw new SurfaceError(line.number, `witness ${witness} is already in scope`);
        variables.add(witness);
        const instance = substituteFormula(formula.body, formula.variable, v(witness));
        const previousWrap = wrap;
        wrap = body => previousWrap(existsElim(proof, witness, body));
        assumptions = [...assumptions, instance];
        match(remainder, instance, assume(instance));
        return;
      }
      if (formula.tag === "and") {
        match(first, formula.left, andElimLeft(proof));
        match(remainder, formula.right, andElimRight(proof));
        return;
      }
      throw new SurfaceError(line.number,
        `pattern has more entries than ${formatFormula(formula)} can provide`);
    };

    match(pattern, sourceFormula, sourceProof);
    replaceWith(line, [{ goal, assumptions, locals }], ([body]) => wrap(body!));
  };

  for (let lineIndex = 0; lineIndex < lines.length; lineIndex += 1) {
    const line = lines[lineIndex]!;
    resolutionLine = line.number;
    const tacticProfileStart = globalThis.performance?.now();
    if (calculation && line.indent <= calculation.indent) {
      throw new SurfaceError(line.number,
        `calc chain is incomplete; next is ${formatFormula(pending[0]!.goal)}`,
        captureTrace ? { initial, steps: traceSteps, ...(narrative.length ? { narrative } : {}), ...(scopeEntries.length ? { scope: scopeEntries } : {}) } : undefined);
    }
    while (localProofFrames.length && line.indent <= localProofFrames.at(-1)!.indent) {
      const frame = localProofFrames.at(-1)!;
      if (pending[0] !== frame.continuation) {
        throw new SurfaceError(line.number,
          `local proof ${frame.name} is incomplete; next is ${formatFormula(pending[0]!.goal)}`,
          captureTrace ? { initial, steps: traceSteps, ...(narrative.length ? { narrative } : {}), ...(scopeEntries.length ? { scope: scopeEntries } : {}) } : undefined);
      }
      localProofFrames.pop();
    }
    const completedFrame = localProofFrames.at(-1);
    if (completedFrame && pending[0] === completedFrame.continuation) {
      throw new SurfaceError(line.number, `dedent after completing local proof ${completedFrame.name}`,
        captureTrace ? { initial, steps: traceSteps, ...(narrative.length ? { narrative } : {}), ...(scopeEntries.length ? { scope: scopeEntries } : {}) } : undefined);
    }
    while (branchFrames.length && (line.indent < branchFrames.at(-1)!.indent ||
      (line.bullet === true && line.indent <= branchFrames.at(-1)!.indent))) branchFrames.pop();
    const closedBranch = line.bullet !== true && branchFrames.at(-1)?.indent === line.indent
      ? branchFrames.at(-1)!.closedAt : undefined;
    if (line.bullet === true) branchFrames.push({ indent: line.indent, remaining: pending.length - 1 });
    const before = snapshot();
    let stepInfo: TacticTraceStep["info"];
    let stepFailed = false;
    try {
    let command = expandUserTactic(kernel, line.text, scope, line.number);
    // Explicit bounds are required; omission never enables recursive relief.
    const backchainConfig = /^(simp|simpa)\s+\(backchain\s*:=\s*(\d+),\s*work\s*:=\s*(\d+)\)(.*)$/u.exec(command);
    const backchain = backchainConfig
      ? { depth: Number(backchainConfig[2]), work: Number(backchainConfig[3]) } : false;
    if (backchainConfig) command = backchainConfig[1]! + backchainConfig[4]!;
    const current = focused(line);
    // Local lemmas and split goals restore their own term namespace.
    variables = current.variables;
    if (calculation) {
      const target = calculationRelation(current.goal);
      if (!target) throw new SurfaceError(line.number, "calc needs an equality or registered binary relation goal");
      const assignment = findTopLevel(command, ":=");
      if (assignment < 0) {
        throw new SurfaceError(line.number, "calc step needs `left = right := proof` or `_ = right := proof`");
      }
      const relationText = command.slice(0, assignment).trim();
      const proofText = command.slice(assignment + 2).trim();
      if (!relationText || !proofText) throw new SurfaceError(line.number, "incomplete calc step");
      const step = parseCalculationFormula(relationText, target.left, line.number);
      const stepRelation = calculationRelation(step);
      if (!stepRelation) throw new SurfaceError(line.number, "calc steps need an equality or registered binary relation");
      if (!termEquals(stepRelation.left, target.left)) {
        throw new SurfaceError(line.number,
          `calc step starts at ${formatTerm(stepRelation.left)}, but the current endpoint is ${formatTerm(target.left)}`);
      }
      let stepProof: Proof;
      if (/^by\s+/u.test(proofText)) {
        const tacticText = proofText.replace(/^by\s+/u, "");
        const script = splitTacticLine({
          number: line.number, text: tacticText, indent: line.indent,
          columnStart: (line.columnStart ?? 1) + assignment + 2 + proofText.indexOf(tacticText),
          columnEnd: line.columnEnd,
        });
        const run = (tactics: typeof script) => elaborateTacticTheorem(kernel, name, [], [], [], step, tactics, scope, {
          assumptions: current.assumptions,
          locals: current.locals,
          variables,
        });
        let nested: ReturnType<typeof run>;
        try {
          nested = run(script);
        } catch (error) {
          // A step justified by one rewrite is complete once the rewrite
          // makes its two sides the same term: `_ = (g ∘ f) ∘ k := by rw assoc`.
          if (!(error instanceof SurfaceError) || !/^(rw|rewrite)\s/u.test(tacticText)) throw error;
          try {
            nested = run([...script, { ...script[0]!, text: "rfl" }]);
          } catch {
            throw error;
          }
        }
        if (!nested) throw new SurfaceError(line.number, "calc step tactic did not produce a proof");
        stepProof = nested.proof;
      } else {
        stepProof = parseProofExpression(kernel, proofText, current, variables, line.number, scope,
          { expectedConclusion: step });
      }
      const actual = kernel.checkProof(stepProof, current.assumptions);
      if (!formulaEquals(actual, step)) {
        throw new SurfaceError(line.number,
          `calc justification proves ${formatFormula(actual)}, not ${formatFormula(step)}`);
      }
      const next = lines[lineIndex + 1];
      const finalStep = !next || next.indent <= calculation.indent;
      if (finalStep) {
        if (stepRelation.key !== target.key || !termEquals(stepRelation.right, target.right)) {
          if (stepRelation.key === "=" && target.key === "=") {
            throw new SurfaceError(line.number,
              `calc chain ends at ${formatTerm(stepRelation.right)}, but the goal ends at ${formatTerm(target.right)}`);
          }
          throw new SurfaceError(line.number, `calc chain ends at ${formatFormula(step)}, but the goal is ${formatFormula(current.goal)}`);
        }
        calculation = undefined;
        close(line, stepProof);
      } else {
        const expandedNext = expandUserTactic(kernel, next.text, scope, next.number);
        const nextAssignment = findTopLevel(expandedNext, ":=");
        if (nextAssignment < 0) throw new SurfaceError(next.number, "calc step needs `left relation right := proof`");
        const nextFormula = parseCalculationFormula(expandedNext.slice(0, nextAssignment).trim(), stepRelation.right, next.number);
        const nextRelation = calculationRelation(nextFormula);
        if (!nextRelation) throw new SurfaceError(next.number, "calc steps need an equality or registered binary relation");
        const residual = nextRelation.rebuild(stepRelation.right, target.right);
        const residualRelation = calculationRelation(residual)!;
        replaceWith(line, [{ goal: residual }], ([rest]) => calculationTransitivity(
          line.number, stepRelation, residualRelation, target, stepProof, rest!, current.assumptions,
          [...current.locals.values()].map(item => item.proof),
        ));
      }
      continue;
    }
    if (command === "calc") {
      if (!calculationRelation(current.goal)) throw new SurfaceError(line.number, "calc needs an equality or registered binary relation goal");
      const next = lines[lineIndex + 1];
      if (!next || next.indent <= line.indent) {
        throw new SurfaceError(line.number, "calc needs an indented relation chain");
      }
      calculation = { indent: line.indent };
      continue;
    }
    if (command === "exact?") {
      const suggestions = exactSuggestions(kernel, current, scope);
      if (suggestions.length === 0) throw new SurfaceError(line.number, "exact? found no proof that closes this goal");
      stepInfo = { title: "exact?", items: suggestions.map(item => item.command), suggestions: suggestions.map(item => describeSuggestion(kernel, item, "exact")) };
      close(line, suggestions[0]!.proof);
      continue;
    }
    if (command === "apply?") {
      const suggestions = applySuggestions(kernel, current, scope);
      if (suggestions.length === 0) throw new SurfaceError(line.number, "apply? found no lemma whose conclusion matches this goal");
      stepInfo = { title: "apply?", items: suggestions.map(item => item.command), suggestions: suggestions.map(item => describeSuggestion(kernel, item, "apply")) };
      let proof = suggestions[0]!.proof;
      const premises = suggestions[0]!.premises;
      if (premises.length === 0) {
        close(line, proof);
        continue;
      }
      replaceWith(line, premises.map(goal => ({ goal })), arguments_ => {
        arguments_.forEach(argument => { proof = impElim(proof, argument); });
        return proof;
      });
      continue;
    }
    if (command === "sorry") {
      close(line, admitSorry(kernel, name, line.number, current));
      continue;
    }
    if (command === "rw?") {
      const suggestions = rewriteSuggestions(kernel, current, scope);
      if (suggestions.length === 0) throw new SurfaceError(line.number, "rw? found no rewrite rule that changes this goal");
      stepInfo = { title: "rw?", items: suggestions.map(item => item.command), suggestions: suggestions.map(item => item.suggestion) };
      const rewritten = suggestions[0]!.rewrite;
      replaceWith(line, [{ goal: rewritten.goal }], ([proof]) => rewritten.lift(proof!));
      continue;
    }
    if (command === "decide") {
      // Closed statements about finite sets: evaluate, then certify with a
      // generated script over the Cumulus membership lemmas.
      const functionName = (name: string): string | undefined =>
        resolveOptional(name, scope, candidate => kernel.functions.has(candidate));
      const names: FiniteNames = {
        empty: functionName("empty") ?? "empty", pair: functionName("pair") ?? "pair",
        powerset: functionName("powerset") ?? "powerset", succ: functionName("succ") ?? "succ",
        singleton: functionName("singleton"), union2: functionName("union2"), insert: functionName("insert"),
        intersection: functionName("intersection"), difference: functionName("difference"),
        subset: resolveOptional("Subset", scope, candidate => kernel.predicates.has(candidate)),
        cardinality: functionName("cardinality"),
      };
      let script: string[];
      try {
        script = decideFiniteSet(current.goal, names, new Set([...current.variables, ...current.locals.keys()]));
      } catch (error) {
        if (error instanceof FiniteDecideError) throw new SurfaceError(line.number, `decide: ${error.message}`);
        throw error;
      }
      if (typeof process !== "undefined" && process.env?.G17_DECIDE_DEBUG) console.error(script.join("\n"));
      const scriptLines = script.map(text => ({
        number: line.number, text: text.trim(), indent: line.indent + 2 + (text.length - text.trimStart().length),
      })).flatMap(splitTacticLine);
      const nested = elaborateTacticTheorem(kernel, "", [], [], [], current.goal, scriptLines, scope,
        { assumptions: current.assumptions, locals: current.locals, variables: current.variables })!;
      close(line, nested.proof);
      continue;
    }
    if (command === "typecheck") {
      if (current.goal.tag !== "pred" || current.goal.args.length === 0) {
        throw new SurfaceError(line.number, "typecheck requires a soft-type or refinement goal");
      }
      // Unary predicate goals are Tau soft-type queries.  The same certified
      // proof search generalizes to P(parameters..., term); it is
      // independent of mathematical `class` syntax and future type classes.
      const facts = [...current.locals.values()].map(item => item.proof);
      const evidence = proveRefinement(kernel, current.goal.args.at(-1)!, current.goal.pred,
        current.goal.args.slice(0, -1), current.assumptions, facts, visibility) ??
        proveRingConstantMembership(kernel, current.goal, current.assumptions, facts) ??
        proveNumeralMembership(kernel, current.goal, current, line, scope);
      if (!evidence) {
        throw new SurfaceError(line.number, `typecheck could not infer ${formatFormula(current.goal)}`);
      }
      close(line, evidence);
      continue;
    }
    if (command === "synthesize") {
      if (current.goal.tag !== "pred" || current.goal.args.length === 0) {
        throw new SurfaceError(line.number, "synthesize requires a predicate goal");
      }
      try {
        const instances = prepareInstanceProver(kernel, visibleInstanceNames(kernel, scope),
          current.assumptions, [...current.locals.values()].map(item => item.proof), {}, visibility);
        const evidence = instances.prove(current.goal.args.at(-1)!, current.goal.pred,
          current.goal.args.slice(0, -1));
        if (!evidence) throw new SurfaceError(line.number,
          `synthesize found no instance for ${formatFormula(current.goal)}`);
        close(line, evidence);
      } catch (error) {
        if (error instanceof InstanceResolutionError || error instanceof InstanceResolutionLimitError) {
          throw new SurfaceError(line.number, error.message);
        }
        throw error;
      }
      continue;
    }
    const ext = /^ext\s+([\p{L}_][\p{L}\p{M}\p{N}_]*)$/u.exec(command);
    if (ext) {
      const variable = ext[1]!;
      if (current.goal.tag !== "eq") throw new SurfaceError(line.number, "ext requires a set equality goal");
      if (variables.has(variable) || current.locals.has(variable)) {
        throw new SurfaceError(line.number, `${variable} is already in scope; choose a fresh extensionality variable`);
      }
      if (current.assumptions.some(item => freeFormulaVariables(item).has(variable))) {
        throw new SurfaceError(line.number, `${variable} occurs in an outer assumption; choose a fresh extensionality variable`);
      }
      variables.add(variable);
      const membership = iff(
        pred("in", v(variable), current.goal.left),
        pred("in", v(variable), current.goal.right),
      );
      const extensionality = at(resolveProof(kernel, "set.extensionality", line.number, scope), current.goal.left, current.goal.right);
      replaceWith(line, [{ goal: membership }], ([proof]) =>
        impElim(extensionality, forallIntro(variable, proof!)));
      continue;
    }
    const simpa = /^simpa(?:\s+with\s+(.+?)|\s*\[(.*?)\])?\s+using\s+(.+)$/u.exec(command);
    if (simpa) {
      const ruleText = simpa[1] ?? simpa[2] ?? "";
      const names = ruleText.trim() ? splitTopLevel(ruleText, ",").map(item => item.trim()) : [];
      const selectedLocals = new Map(names.map(item => [item, resolveLocalProof(current.locals, item, line.number, { kernel, scope, assumptions: current.assumptions })]));
      const localRules = [...selectedLocals.values()].flatMap(item => item ? [item.proof] : []);
      const external = names.filter(item => !selectedLocals.get(item));
      const sourceProof = parseProofExpression(kernel, simpa[3]!, current, variables, line.number, scope);
      const rules = [...defaultSimpRules(kernel, line.number, scope),
        ...resolveRules(kernel, external, line.number, scope), ...localRules];
      const options = createSimpSession({
        backchain, visibility,
        underBinders: true,
        using: rules,
        assumptions: current.assumptions,
        facts: [...current.locals.values()].map(item => item.proof).filter(item => item !== sourceProof),
        ground: defaultGroundRules(kernel, line.number, scope),
      });
      const sourceFormula = kernel.checkProof(sourceProof, current.assumptions);
      const simplified = sourceFormula.tag === "eq"
        ? simplifyEqualityFact(kernel, sourceProof, options)
        : simplifyFormulaFact(kernel, sourceProof, options);
      // Normalize the target before logical search. In particular a definition
      // beneath an existential must not trigger guesses for its witnesses.
      let target = current.goal;
      const lifts: Array<(proof: Proof) => Proof> = [];
      const seen = new Set<string>();
      for (let step = 0; step < 256 && !formulaEquals(simplified.formula, target); step += 1) {
        const key = canonical(target);
        if (seen.has(key)) break;
        seen.add(key);
        let rewritten;
        try {
          rewritten = target.tag === "eq"
            ? simplifyEqualityGoal(kernel, target, options)
            : simplifyFormulaGoal(kernel, target, options);
        } catch { break; }
        if (formulaEquals(rewritten.goal, target)) break;
        target = rewritten.goal;
        lifts.push(rewritten.lift);
      }
      let proof = formulaEquals(simplified.formula, target) ? simplified.proof : settle(kernel, target, {
        ...options,
        facts: [...current.locals.values()].map(item => item.proof).concat(simplified.proof),
      });
      for (let index = lifts.length - 1; index >= 0; index -= 1) proof = lifts[index]!(proof);
      close(line, proof);
      continue;
    }
    const simpAt = /^simp(?:\s+with\s+(.+?)|\s*\[(.*?)\])?\s+at\s+([\p{L}_][\p{L}\p{M}\p{N}_]*)$/u.exec(command);
    if (simpAt) {
      const localName = simpAt[3]!;
      const local = current.locals.get(localName);
      if (!local) throw new SurfaceError(line.number, `unknown local proof ${localName}`);
      const ruleText = simpAt[1] ?? simpAt[2] ?? "";
      const names = ruleText.trim() ? splitTopLevel(ruleText, ",").map(item => item.trim()) : [];
      const selectedLocals = new Map(names.map(item => [item, resolveLocalProof(current.locals, item, line.number, { kernel, scope, assumptions: current.assumptions })]));
      const localRules = [...selectedLocals.values()].flatMap(item => item ? [item.proof] : []);
      const external = names.filter(item => !selectedLocals.get(item));
      const simplifyOptions = createSimpSession({
        backchain, visibility,
        using: [...defaultSimpRules(kernel, line.number, scope), ...resolveRules(kernel, external, line.number, scope), ...localRules],
        assumptions: current.assumptions,
        facts: [...current.locals.values()].filter(item => item !== local).map(item => item.proof),
      });
      const simplified = local.formula.tag === "eq"
        ? simplifyEqualityFact(kernel, local.proof, simplifyOptions)
        : simplifyFormulaFact(kernel, local.proof, simplifyOptions);
      current.locals.set(localName, simplified);
      continue;
    }
    const simp = command === "simp" ? "" :
      (/^simp\s+with\s+(.+)$/.exec(command)?.[1] ?? /^simp\s*\[(.*)\]$/.exec(command)?.[1]);
    if (simp !== undefined) {
      const names = simp.trim() ? splitTopLevel(simp, ",").map(item => item.trim()) : [];
      const selectedLocals = new Map(names.map(item => [item, resolveLocalProof(current.locals, item, line.number, { kernel, scope, assumptions: current.assumptions })]));
      const localRules = [...selectedLocals.values()].flatMap(item => item ? [item.proof] : []);
      const external = names.filter(item => !selectedLocals.get(item));
      const rules = [...defaultSimpRules(kernel, line.number, scope), ...resolveRules(kernel, external, line.number, scope), ...localRules];
      if (current.goal.tag !== "eq") {
        const options = createSimpSession({
          backchain, visibility,
          // A bare simp unfolds subset goals by itself, as settle does.
          using: names.length ? rules : [...rules, ...defaultSettleRules(kernel, line.number, scope)],
          assumptions: current.assumptions, facts: [...current.locals.values()].map(item => item.proof),
          ground: defaultGroundRules(kernel, line.number, scope),
          // `simp` closes a logical goal with the full search when it can,
          // and otherwise falls back to a deterministic checked rewrite.
          fuel: 1_000,
        });
        try {
          close(line, settle(kernel, current.goal, options));
        } catch (closingError) {
          // A guard goal such as `F(f) : F(a) ⟶ F(b)` is rewritten to a
          // fixpoint and then closed by the search or the instance registry;
          // otherwise the rewritten guard is the remaining goal.
          if (current.goal.tag === "pred" && isTransparentPredicate(kernel, current.goal.pred, visibility)) {
            let target: Formula = current.goal;
            const lifts: Array<(proof: Proof) => Proof> = [];
            const seen = new Set<string>();
            for (let step = 0; step < 256; step += 1) {
              const key = canonical(target);
              if (seen.has(key)) break;
              seen.add(key);
              let rewritten: GoalRewrite;
              try { rewritten = simplifyFormulaGoal(kernel, target, options); } catch { break; }
              if (formulaEquals(rewritten.goal, target)) break;
              target = rewritten.goal;
              lifts.push(rewritten.lift);
            }
            const finish = (proof: Proof): Proof => {
              for (let index = lifts.length - 1; index >= 0; index -= 1) proof = lifts[index]!(proof);
              return proof;
            };
            let evidence: Proof | undefined;
            if (lifts.length) { try { evidence = settle(kernel, target, options); } catch {} }
            if (!evidence && target.tag === "pred" && target.args.length) {
              try {
                const instances = prepareInstanceProver(kernel, visibleInstanceNames(kernel, scope),
                  current.assumptions, [...current.locals.values()].map(item => item.proof), {}, visibility);
                evidence = instances.prove(target.args.at(-1)!, target.pred, target.args.slice(0, -1)) ?? undefined;
              } catch {}
            }
            if (evidence) { close(line, finish(evidence)); continue; }
            if (lifts.length) { replaceWith(line, [{ goal: target }], ([proof]) => finish(proof!)); continue; }
            throw closingError;
          }
          try {
            const simplified = simplifyFormulaGoal(kernel, current.goal, options);
            replaceWith(line, [{ goal: simplified.goal }], ([proof]) => simplified.lift(proof!));
          } catch {
            throw closingError;
          }
        }
        continue;
      }
      if (freeFormulaVariables(current.goal).size === 0) {
        try { close(line, kernel.proveComputation(current.goal.left, current.goal.right)); continue; } catch {}
      }
      const simplified = simplifyEqualityGoal(kernel, current.goal, {
        backchain, visibility,
        using: rules, assumptions: current.assumptions, facts: [...current.locals.values()].map(item => item.proof),
      });
      if (simplified.goal.tag === "eq" && formulaEquals(simplified.goal, eq(simplified.goal.left, simplified.goal.left))) {
        close(line, simplified.lift(refl(simplified.goal.left)));
      } else {
        replaceWith(line, [{ goal: simplified.goal }], ([proof]) => simplified.lift(proof!));
      }
      continue;
    }
    // rwa h is rw h followed by closing the rewritten goal from the context;
    // rwa h at fact rewrites the fact and then uses it.
    const rewriteAndClose = /^rwa\s+(.+)$/u.exec(command);
    if (rewriteAndClose) {
      const target = /\s+at\s+([\p{L}_][\p{L}\p{M}\p{N}_']*)$/u.exec(rewriteAndClose[1]!)?.[1];
      const scriptLines = [
        { number: line.number, text: `rw ${rewriteAndClose[1]}`, indent: line.indent + 2 },
        { number: line.number, text: target ? `exact ${target}` : "assumption", indent: line.indent + 2 },
      ].flatMap(splitTacticLine);
      const nested = elaborateTacticTheorem(kernel, "", [], [], [], current.goal, scriptLines, scope,
        { assumptions: current.assumptions, locals: current.locals, variables: current.variables })!;
      close(line, nested.proof);
      continue;
    }
    const rewriteHead = /^(?:rewrite|rw)\s+(.+)$/u.exec(command);
    let rewrite: readonly [string, string | undefined, string, string | undefined, boolean] | undefined;
    if (rewriteHead) {
      let payload = rewriteHead[1]!.trim();
      const underBinders = payload.startsWith("under ");
      if (underBinders) payload = payload.slice(6).trim();
      let target: string | undefined;
      const targetMatch = /^(.*?)\s+at\s+([\p{L}_][\p{L}\p{M}\p{N}_]*)$/u.exec(payload);
      if (targetMatch) { payload = targetMatch[1]!.trim(); target = targetMatch[2]!; }
      if (payload.startsWith("[") && payload.endsWith("]")) payload = payload.slice(1, -1).trim();
      const direction = /^(←|<-)\s*(.+)$/u.exec(payload);
      rewrite = [rewriteHead[0], direction?.[1], (direction?.[2] ?? payload).trim(), target, underBinders];
    }
    if (rewrite) {
      const reverse = Boolean(rewrite[1]);
      const reference = rewrite[2]!.trim();
      const localRule = resolveLocalProof(current.locals, reference, line.number, { kernel, scope, assumptions: current.assumptions });
      // `rw moves with p, hp` rewrites with the instance the application
      // names, as `have inst := moves with p, hp` followed by `rw inst` does.
      const applied = !localRule && findTopLevelWord(reference, "with") >= 0;
      let candidates: readonly Proof[];
      if (applied) {
        const head = reference.slice(0, findTopLevelWord(reference, "with")).trim();
        const ruleName = /^(.*?)(?:\s+at\s.*)?$/u.exec(head)?.[1]?.trim() ?? head;
        try {
          candidates = [parseProofExpression(kernel, reference, current, variables, line.number, scope)];
        } catch (error) {
          if (!(error instanceof SurfaceError)) throw error;
          throw new SurfaceError(line.number,
            `rw takes a fact or rule, optionally applied with \`at terms\` and \`with facts\`, ` +
            `and \`at hypothesis\` after it names the hypothesis to rewrite; ` +
            `\`rw ${reference}${rewrite[3] ? ` at ${rewrite[3]}` : ""}\` rewrites with ${ruleName} applied to ` +
            `${reference.slice(findTopLevelWord(reference, "with") + 4).trim()}, which failed: ${error.message}`);
        }
      } else candidates = localRule ? [localRule.proof] : resolveRules(kernel, [reference], line.number, scope);
      let rewritten: ReturnType<typeof rewriteGoal> | undefined;
      let lastError: unknown;
      for (const candidate of candidates) {
        try {
          if (rewrite[3]) {
            const local = current.locals.get(rewrite[3]!);
            if (!local) throw new SurfaceError(line.number, `unknown local proof ${rewrite[3]}`);
            const transformed = rewriteFact(kernel, local.proof, candidate, current.assumptions,
              [...current.locals.values()].filter(item => item !== local).map(item => item.proof), reverse, rewrite[4], undefined, visibility);
            current.locals.set(rewrite[3]!, transformed);
            rewritten = { goal: current.goal, lift: proof => proof };
            break;
          }
          rewritten = rewriteGoal(kernel, current.goal, candidate, current.assumptions,
            [...current.locals.values()].map(item => item.proof), reverse, rewrite[4], undefined, visibility);
          break;
        } catch (error) { lastError = error; }
      }
      if (!rewritten) {
        // The rule and its target are shown as the goal panel shows them,
        // with the notation the hypotheses in scope supply.
        if (lastError instanceof RewriteMismatch) {
          const facts = [...current.assumptions, ...[...current.locals.values()].map(item => item.formula)];
          const options = goalDisplayOptions(kernel, scope, facts, [current.goal, lastError.target]);
          const where = rewrite[3]
            ? `${rewrite[3]} : ${formatFormula(lastError.target, options)}`
            : `the goal ${formatFormula(lastError.target, options)}`;
          throw new SurfaceError(line.number,
            `rewrite rule ${reference} (${formatFormula(lastError.rule, options)}) does not match ${where}`);
        }
        throw new SurfaceError(line.number, lastError instanceof Error ? lastError.message : "rewrite rule did not match");
      }
      if (rewrite[3]) continue;
      // A goal the rewrite makes reflexive is closed when the rewrite ends
      // its branch: the script ends, the next step is dedented, or it begins
      // a sibling bullet. A step that follows in the same branch, `rfl` or
      // a further step of the proof, still finds the goal as written.
      const next = lines[lineIndex + 1];
      const endsBranch = !next || next.indent < line.indent || (next.bullet === true && next.indent <= line.indent);
      if (endsBranch && rewritten.goal.tag === "eq" && termEquals(rewritten.goal.left, rewritten.goal.right)) {
        close(line, rewritten.lift(refl(rewritten.goal.left)));
        continue;
      }
      replaceWith(line, [{ goal: rewritten.goal }], ([proof]) => rewritten!.lift(proof!));
      continue;
    }
    const unfold = /^unfold\s+(\S+)(?:\s+at\s+([\p{L}_][\p{L}\p{M}\p{N}_]*))?$/u.exec(command);
    if (unfold) {
      const targetFormula = unfold[2] ? current.locals.get(unfold[2]!)?.formula : current.goal;
      const notationCandidates = visibleInfixNotationGroups(kernel, scope, line.number).get(unfold[1]!);
      const matchingNotation = notationCandidates?.filter(item =>
        targetFormula && formulaMentionsSymbol(targetFormula, item.target)) ?? [];
      if (notationCandidates && notationCandidates.length > 1 && matchingNotation.length !== 1) {
        const alternatives = notationCandidates.map(item =>
          `${notationTypeLabel(item)}: ${item.target}`).join(", ");
        throw new SurfaceError(line.number,
          `unfold ${unfold[1]} is overloaded and the selected proposition does not determine one definition; use ${alternatives}`);
      }
      const definitionReference = matchingNotation[0]?.target ?? notationCandidates?.[0]?.target ?? unfold[1]!;
      // The formula being unfolded decides among declarations of one name.
      const rule = resolveProof(kernel, definitionReference, line.number,
        targetFormula ? { ...scope, goal: () => targetFormula } : scope, true);
      const generatedGuards = predicateSoftGuardCount(definitionReference, kernel, scope);
      if (unfold[2]) {
        const local = current.locals.get(unfold[2]!);
        if (!local) throw new SurfaceError(line.number, `unknown local proof ${unfold[2]}`);
        try {
          let unfolded = unfoldFormula(kernel, rule, local, current.assumptions, line.number);
          // Generated domain guards are recoverable from the original
          // predicate fact, but old-style proofs expect `unfold P at h` to
          // expose P's authored body. Peel exactly those generated conjuncts.
          for (let index = 0; index < generatedGuards && unfolded.formula.tag === "and"; index += 1) {
            unfolded = { formula: unfolded.formula.right, proof: andElimRight(unfolded.proof) };
          }
          current.locals.set(unfold[2]!, unfolded);
        } catch {
          current.locals.set(unfold[2]!, rewriteFact(kernel, local.proof, rule, current.assumptions,
            [...current.locals.values()].filter(item => item !== local).map(item => item.proof), false, false, undefined, visibility));
        }
      } else {
        if (current.goal.tag === "pred") {
          try {
            const unfolded = unfoldGoal(kernel, rule, current.goal, current.assumptions, line.number);
            let reduced = unfolded.formula;
            let rebuild: (proof: Proof) => Proof = proof => proof;
            const facts = [
              ...current.assumptions.map(formula => ({ formula, proof: assume(formula) })),
              ...current.locals.values(),
            ];
            for (let index = 0; index < generatedGuards && reduced.tag === "and"; index += 1) {
              const evidence = facts.find(item => formulaEquals(item.formula, reduced.left))?.proof ??
                (reduced.left.tag === "pred" && reduced.left.args.length > 0
                  ? proveRefinement(kernel, reduced.left.args.at(-1)!, reduced.left.pred,
                    reduced.left.args.slice(0, -1), current.assumptions,
                    [...current.locals.values()].map(item => item.proof), visibility)
                  : undefined);
              if (!evidence) break;
              const previous = rebuild;
              rebuild = proof => previous(andIntro(evidence, proof));
              reduced = reduced.right;
            }
            replaceWith(line, [{ goal: reduced }], ([proof]) => impElim(unfolded.fold, rebuild(proof!)));
          } catch {
            const rewritten = rewriteGoal(kernel, current.goal, rule, current.assumptions,
              [...current.locals.values()].map(item => item.proof), false, false, undefined, visibility);
            replaceWith(line, [{ goal: rewritten.goal }], ([proof]) => rewritten.lift(proof!));
          }
        } else if (current.goal.tag === "eq") {
          const unfolded = simplifyEqualityGoal(kernel, current.goal, {
            using: resolveRules(kernel, [definitionReference], line.number, scope), assumptions: current.assumptions,
            facts: [...current.locals.values()].map(item => item.proof), visibility,
          });
          replaceWith(line, [{ goal: unfolded.goal }], ([proof]) => unfolded.lift(proof!));
        } else {
          // A defined predicate under ∧, ∨, →, ¬, ∀, or ∃: every instance in
          // the goal is unfolded, through the connectives and the binders.
          const unfolded = unfoldThroughout(kernel, current.goal, rule, current.assumptions,
            [...current.locals.values()].map(item => item.proof), visibility, variables);
          if (!unfolded) {
            throw new SurfaceError(line.number,
              `unfold ${unfold[1]} finds nothing to unfold in the goal ${formatFormula(current.goal)}`);
          }
          replaceWith(line, [{ goal: unfolded.goal }], ([proof]) => unfolded.lift(proof!));
        }
      }
      continue;
    }
    const relationInduction = /^induction\s+([\p{L}_][\p{L}\p{M}\p{N}_]*)\s+over\s+(.+?)\s+ordered\s+by\s+(.+?)\s+certified\s+by\s+(.+)$/u.exec(command);
    if (relationInduction) {
      const targetName = relationInduction[1]!;
      if (variables.has(targetName)) {
        throw new SurfaceError(line.number,
          `well-founded induction binder ${targetName} is already in scope; use it before introducing the quantified variable`);
      }
      const domain = parseTerm(relationInduction[2]!, kernel, variables, line.number, scope);
      const relation = parseTerm(relationInduction[3]!, kernel, variables, line.number, scope);
      const certificate = parseProofExpression(
        kernel, relationInduction[4]!, current, variables, line.number, scope,
      );
      const expectedCertificate = pred("wellFoundedOn", relation, domain);
      const actualCertificate = kernel.checkProof(certificate, current.assumptions);
      if (!formulaEquals(actualCertificate, expectedCertificate)) {
        throw new SurfaceError(line.number,
          `induction certificate proves ${formatFormula(actualCertificate)}, expected ${formatFormula(expectedCertificate)}`);
      }
      if (current.goal.tag !== "forall" || current.goal.variable !== targetName ||
          current.goal.body.tag !== "imp" ||
          !formulaEquals(current.goal.body.left, pred("in", v(targetName), domain))) {
        throw new SurfaceError(line.number,
          `well-founded induction expects a goal of the form ∀ ${targetName}, ${targetName} ∈ ${formatTerm(domain)} → P(${targetName})`);
      }
      const motive = current.goal.body.right;
      const forbidden = new Set<string>(variables);
      freeFormulaVariables(current.goal).forEach(item => forbidden.add(item));
      current.assumptions.forEach(item => freeFormulaVariables(item).forEach(variable => forbidden.add(variable)));
      const predecessorName = freshSurfaceVariable(`${targetName}Predecessor`, forbidden);
      const predecessorMotive = substituteFormula(motive, targetName, v(predecessorName));
      const inductionHypothesis = forall(predecessorName, imp(
        and(
          pred("in", v(predecessorName), domain),
          pred("relates", relation, v(predecessorName), v(targetName)),
        ),
        predecessorMotive,
      ));
      const stepGoal = forall(targetName, imp(
        pred("in", v(targetName), domain),
        imp(inductionHypothesis, motive),
      ));
      replaceWith(line, [{ goal: stepGoal }], ([step]) => wellFoundedInduction(
        relation, domain, targetName, predecessorName, motive, certificate, step!,
      ));
      continue;
    }
    const membershipInduction = /^induction\s+([\p{L}_][\p{L}\p{M}\p{N}_]*)\s+using\s+membership$/u.exec(command);
    if (membershipInduction) {
      const targetName = membershipInduction[1]!;
      if (!variables.has(targetName)) throw new SurfaceError(line.number, `unknown induction variable ${targetName}`);
      if (current.assumptions.some(item => freeFormulaVariables(item).has(targetName))) {
        throw new SurfaceError(line.number,
          `membership induction cannot keep an assumption depending on ${targetName}; revert it first`);
      }
      const forbidden = new Set<string>(variables);
      freeFormulaVariables(current.goal).forEach(item => forbidden.add(item));
      current.assumptions.forEach(item => freeFormulaVariables(item).forEach(variable => forbidden.add(variable)));
      const currentName = freshSurfaceVariable(`${targetName}MemberSet`, forbidden); forbidden.add(currentName);
      const predecessorName = freshSurfaceVariable(`${targetName}Member`, forbidden);
      const target = v(targetName);
      const currentTerm = v(currentName);
      const predecessor = v(predecessorName);
      const motive = substituteFormula(current.goal, targetName, currentTerm);
      const predecessorMotive = substituteFormula(motive, currentName, predecessor);
      const memberPremise = pred("in", predecessor, currentTerm);
      const plainHypothesis = forall(predecessorName, imp(memberPremise, predecessorMotive));
      const stepGoal = forall(currentName, imp(plainHypothesis, motive));

      const closureName = resolveExisting("closure", scope,
        candidate => kernel.functions.get(candidate) === 1, line.number, "transitive-closure function");
      const membershipName = resolveExisting("membershipOn", scope,
        candidate => kernel.functions.get(candidate) === 1, line.number, "restricted-membership relation");
      const contains = resolveProof(kernel, "closure.contains", line.number, scope);
      const transitive = resolveProof(kernel, "closure.transitive", line.number, scope);
      const relates = resolveProof(kernel, "membershipOn.relates", line.number, scope);
      const wellFounded = resolveProof(kernel, "membershipOn.wellFounded", line.number, scope);
      const domain = app(closureName, target);
      const relation = app(membershipName, domain);
      const inDomainCurrent = pred("in", currentTerm, domain);
      const inDomainPredecessor = pred("in", predecessor, domain);
      const relationPremise = pred("relates", relation, predecessor, currentTerm);
      const restrictedHypothesis = forall(predecessorName, imp(
        and(inDomainPredecessor, relationPremise), predecessorMotive,
      ));

      replaceWith(line, [{ goal: stepGoal }], ([userStep]) => {
        const currentInDomain = assume(inDomainCurrent);
        const predecessorInCurrent = assume(memberPremise);
        let predecessorInDomain: Proof = at(transitive, target, currentTerm);
        predecessorInDomain = impElim(predecessorInDomain, currentInDomain);
        predecessorInDomain = forallElim(predecessorInDomain, predecessor);
        predecessorInDomain = impElim(predecessorInDomain, predecessorInCurrent);

        let restrictedRelation: Proof = at(relates, predecessor, currentTerm, domain);
        restrictedRelation = impElim(restrictedRelation, predecessorInDomain);
        restrictedRelation = impElim(restrictedRelation, currentInDomain);
        restrictedRelation = impElim(iffElimRight(restrictedRelation), predecessorInCurrent);

        let predecessorResult: Proof = forallElim(assume(restrictedHypothesis), predecessor);
        predecessorResult = impElim(predecessorResult, andIntro(predecessorInDomain, restrictedRelation));
        const plainProof = forallIntro(predecessorName, impIntro(memberPremise, predecessorResult));
        const branch = impElim(forallElim(userStep!, currentTerm), plainProof);
        const restrictedStep = forallIntro(currentName, impIntro(inDomainCurrent,
          impIntro(restrictedHypothesis, branch)));
        const certificate = at(wellFounded, domain);
        const induction = wellFoundedInduction(
          relation, domain, currentName, predecessorName, motive, certificate, restrictedStep,
        );
        const atTarget = forallElim(induction, target);
        return impElim(atTarget, at(contains, target));
      });
      continue;
    }
    const obtain = /^obtain\s+(.+?)\s*:=\s*(.+)$/u.exec(command);
    if (obtain) {
      const sourceProof = parseProofExpression(kernel, obtain[2]!, current, variables, line.number, scope);
      const sourceFormula = kernel.checkProof(sourceProof, current.assumptions);
      destructureProof(line, current, parseDestructurePattern(obtain[1]!, line.number), sourceFormula, sourceProof);
      continue;
    }
    // Named implicit arguments may contain := inside the proposition. Only
    // an assignment outside all delimiters starts the local proof expression.
    const haveAssignment = /^have\s/u.test(command) ? findTopLevel(command, ":=") : -1;
    const have = haveAssignment < 0 ? null
      : /^have\s+([\p{L}_][\p{L}\p{M}\p{N}_]*)(?:\s*:\s*(.+))?\s*$/u.exec(command.slice(0, haveAssignment));
    if (have) {
      if (current.locals.has(have[1]!)) throw new SurfaceError(line.number, `local proof ${have[1]} already exists`);
      const stated = have[2] ? parseFormula(have[2], kernel, variables, line.number, scope) : undefined;
      let proof = parseProofExpression(kernel, command.slice(haveAssignment + 2).trim(), current, variables, line.number, scope,
        { expectedConclusion: stated });
      let actual = kernel.checkProof(proof, current.assumptions);
      if (stated && !formulaEquals(stated, actual)) {
        // The stated form may be the proof's through a definition, as
        // `have h : (x, y) ∈ r := related` restates `relates(r, x, y)`.
        const bridged = bridgeDefinition(kernel, scope, line.number, proof, actual, stated, current.assumptions, current.locals);
        if (!bridged) {
          throw new SurfaceError(line.number,
            `local proof ${have[1]} states ${formatFormula(stated)}, but its proof establishes ${formatFormula(actual)}`);
        }
        proof = bridged;
        actual = stated;
      }
      current.locals.set(have[1]!, { proof, formula: actual });
      continue;
    }
    const localHave = /^have\s+([\p{L}_][\p{L}\p{M}\p{N}_]*)\s*:\s*(.+)$/u.exec(command);
    // `have h : P by tactic` runs the one tactic on P in a nested script and
    // keeps the result as a local proof, like a one-line indented body.
    const byClause = localHave ? findTopLevelWord(localHave[2]!, "by") : -1;
    const propositionText = localHave ? (byClause >= 0 ? localHave[2]!.slice(0, byClause) : localHave[2]!).trim() : "";
    const byTactic = localHave && byClause >= 0 ? localHave[2]!.slice(byClause + 2).trim() : "";
    if (localHave && byTactic) {
      const localName = localHave[1]!;
      if (current.locals.has(localName)) throw new SurfaceError(line.number, `local proof ${localName} already exists`);
      const proposition = parseFormula(propositionText, kernel, variables, line.number, scope);
      const tactic = byTactic;
      const scriptLines = [{ number: line.number, text: tactic, indent: line.indent + 2 }].flatMap(splitTacticLine);
      const nested = elaborateTacticTheorem(kernel, "", [], [], [], proposition, scriptLines, scope,
        { assumptions: current.assumptions, locals: current.locals, variables: current.variables })!;
      current.locals.set(localName, { proof: nested.proof, formula: proposition });
      continue;
    }
    if (localHave) {
      const localName = localHave[1]!;
      if (current.locals.has(localName)) throw new SurfaceError(line.number, `local proof ${localName} already exists`);
      const next = lines[lineIndex + 1];
      if (!next || next.indent <= line.indent) {
        throw new SurfaceError(line.number, `local proof ${localName} needs an indented tactic body`);
      }
      const proposition = parseFormula(propositionText, kernel, variables, line.number, scope);
      const continuationLocals = new Map(current.locals);
      let established: Proof | undefined;
      const continuation: TacticGoal = {
        variables: new Set(variables),
        goal: current.goal,
        assumptions: [...current.assumptions, proposition],
        locals: continuationLocals,
        close: proof => {
          if (!established) throw new SurfaceError(line.number, `local proof ${localName} is incomplete`);
          current.close(impElim(impIntro(proposition, proof), established));
        },
      };
      const subgoal: TacticGoal = {
        variables: new Set(variables),
        goal: proposition,
        assumptions: current.assumptions,
        locals: new Map(current.locals),
        close: proof => {
          established = proof;
          // A checked local lemma is a scoped cut. Its eigenvariables stay in
          // its original scope.
          continuationLocals.set(localName, { proof: assume(proposition), formula: proposition });
        },
      };
      pending.shift();
      pending.unshift(subgoal, continuation);
      localProofFrames.push({ indent: line.indent, name: localName, continuation });
      continue;
    }
    const specialize = /^specialize\s+([\p{L}_][\p{L}\p{M}\p{N}_]*)\s+with\s+(.+)$/u.exec(command);
    if (specialize) {
      const name = specialize[1]!;
      const local = current.locals.get(name);
      if (!local) throw new SurfaceError(line.number, `unknown local proof ${name}`);
      const proof = parseProofExpression(kernel, `${name} with ${specialize[2]!}`,
        current, variables, line.number, scope);
      const formula = kernel.checkProof(proof, current.assumptions);
      current.locals.set(name, { proof, formula });
      continue;
    }
    const applyMatch = /^apply\s+(.+)$/.exec(command);
    if (applyMatch) {
      let proof = parseProofExpression(kernel, applyMatch[1]!, current, variables, line.number, scope,
        { expectedConclusion: current.goal, applicationGoal: true });
      let formula = kernel.checkProof(proof, current.assumptions);
      const premises: Formula[] = [];
      while (formula.tag === "imp" && !formulaEquals(formula, current.goal)) {
        premises.push(formula.left);
        formula = formula.right;
      }
      if (!formulaEquals(formula, current.goal)) {
        throw new SurfaceError(line.number, `applied proof concludes ${formatFormula(formula)}, not ${formatFormula(current.goal)}`);
      }
      if (premises.length === 0) { close(line, proof); continue; }
      replaceWith(line, premises.map(premise => ({ goal: premise })), arguments_ => {
        arguments_.forEach(argument => { proof = impElim(proof, argument); });
        return proof;
      });
      continue;
    }
    const show = /^show\s+(.+?)\s*:=\s*(.+)$/u.exec(command);
    if (show) {
      const stated = parseFormula(show[1]!, kernel, variables, line.number, scope);
      if (!formulaEquals(stated, current.goal)) {
        throw new SurfaceError(line.number,
          `show states ${formatFormula(stated)}, but the goal is ${formatFormula(current.goal)}`);
      }
      close(line, parseProofExpression(kernel, show[2]!, current, variables, line.number, scope, { expectedConclusion: current.goal }));
      continue;
    }
    const exact = /^exact\s+(?!⟨)(.+)$/u.exec(command);
    if (exact) {
      close(line, parseProofExpression(kernel, exact[1]!, current, variables, line.number, scope, { expectedConclusion: current.goal }));
      continue;
    }
    // `intro` and `intros` on a defined predicate goal such as `A ⊆ B` work
    // through its definition when that is a universal or an implication, as
    // an `intro` on a reducible head does.
    const introduceThroughDefinition = (goal: TacticGoal, at: SourceLine): boolean => {
      const unfolded = unfoldPredicateGoal(kernel, scope, at.number, goal.goal, goal.assumptions, goal.locals, ["forall", "imp"]);
      if (!unfolded) return false;
      replaceWith(at, [{ goal: unfolded.formula }], ([proof]) => unfolded.fold(proof!));
      return true;
    };
    const intros = /^intros\s+(.+)$/u.exec(command);
    if (intros) {
      const names = intros[1]!.split(/[\s,]+/u).filter(Boolean);
      if (names.length === 0 || names.some(item => !SIMPLE_IDENTIFIER.test(item))) {
        throw new SurfaceError(line.number, "intros expects names separated by spaces or commas");
      }
      for (const name of names) {
        let goal = focused(line);
        if (goal.goal.tag === "pred" && introduceThroughDefinition(goal, line)) goal = focused(line);
        if (goal.goal.tag === "forall") {
          variables.add(name);
          const body = substituteFormula(goal.goal.body, goal.goal.variable, v(name));
          replaceWith(line, [{ goal: body }], ([proof]) => forallIntro(name, proof!));
          continue;
        }
        if (goal.goal.tag !== "imp") {
          throw new SurfaceError(line.number,
            `intros reached ${formatFormula(goal.goal)} before it could introduce ${name}`);
        }
        if (goal.locals.has(name)) throw new SurfaceError(line.number, `local proof ${name} already exists`);
        const locals = new Map(goal.locals);
        locals.set(name, { formula: goal.goal.left, proof: assume(goal.goal.left) });
        replaceWith(line, [{
          goal: goal.goal.right,
          assumptions: [...goal.assumptions, goal.goal.left],
          locals,
        }], ([body]) => impIntro(goal.goal.left, body!));
      }
      continue;
    }
    const intro = /^intro(?:\s+([\p{L}_][\p{L}\p{M}\p{N}_]*))?(?:\s+at\s+([\p{L}_][\p{L}\p{M}\p{N}_]*))?$/u.exec(command);
    if (intro) {
      if (intro[2]) {
        const local = current.locals.get(intro[2]!);
        if (!local) throw new SurfaceError(line.number, `unknown local proof ${intro[2]}`);
        if (!intro[1]) throw new SurfaceError(line.number, `intro at ${intro[2]} needs an instantiating term`);
        if (!variables.has(intro[1]!)) throw new SurfaceError(line.number, `${intro[1]} is not an in-scope term`);
        if (local.formula.tag !== "forall") {
          throw new SurfaceError(line.number, `intro at ${intro[2]} requires a universally quantified hypothesis`);
        }
        const term = v(intro[1]!);
        current.locals.set(intro[2]!, {
          proof: forallElim(local.proof, term),
          formula: substituteFormula(local.formula.body, local.formula.variable, term),
        });
        continue;
      }
      if (current.goal.tag === "pred") introduceThroughDefinition(current, line);
      if (current.goal.tag === "forall") {
        const variable = intro[1] ?? current.goal.variable;
        variables.add(variable);
        const body = substituteFormula(current.goal.body, current.goal.variable, v(variable));
        replaceWith(line, [{ goal: body }], ([proof]) => forallIntro(variable, proof!));
        continue;
      }
      if (current.goal.tag !== "imp") throw new SurfaceError(line.number, "intro requires a universal or implication goal");
      const localName = intro[1] ?? `assumption${current.assumptions.length + 1}`;
      if (current.locals.has(localName)) throw new SurfaceError(line.number, `local proof ${localName} already exists`);
      const locals = new Map(current.locals);
      locals.set(localName, { formula: current.goal.left, proof: assume(current.goal.left) });
      replaceWith(line, [{ goal: current.goal.right, assumptions: [...current.assumptions, current.goal.left], locals }],
        ([body]) => impIntro(current.goal.left, body!));
      continue;
    }
    // A defined predicate goal whose body has the shape a tactic needs is
    // opened through its definition first, the way a constructor or a left
    // step unfolds a reducible head.
    const goalThroughDefinition = (wanted: readonly Formula["tag"][]): TacticGoal => {
      if (current.goal.tag !== "pred") return current;
      const unfolded = unfoldPredicateGoal(kernel, scope, line.number, current.goal, current.assumptions, current.locals, wanted);
      if (!unfolded) return current;
      replaceWith(line, [{ goal: unfolded.formula }], ([proof]) => unfolded.fold(proof!));
      return focused(line);
    };
    if (command === "left" || command === "right") {
      const target = goalThroughDefinition(["or"]).goal;
      if (target.tag !== "or") throw new SurfaceError(line.number, `${command} requires a disjunction goal`);
      const chooseLeft = command === "left";
      replaceWith(line, [{ goal: chooseLeft ? target.left : target.right }], ([proof]) =>
        chooseLeft ? orIntroLeft(proof!, target.right) : orIntroRight(target.left, proof!));
      continue;
    }
    if (command === "constructor" || command === "split") {
      const target = goalThroughDefinition(["and", "iff"]).goal;
      if (target.tag === "and") {
        replaceWith(line, [{ goal: target.left }, { goal: target.right }], ([left, right]) => andIntro(left!, right!));
      } else if (target.tag === "iff") {
        replaceWith(line,
          [{ goal: imp(target.left, target.right) }, { goal: imp(target.right, target.left) }],
          ([forward, backward]) => iffIntro(forward!, backward!));
      } else throw new SurfaceError(line.number, `${command} requires a conjunction or equivalence goal`);
      continue;
    }
    // `exact ⟨a, b⟩` is `refine` with every component supplied.
    const refine = /^(?:refine|exact)\s+⟨(.*)⟩$/u.exec(command);
    if (refine) {
      let entries = splitTopLevel(refine[1]!, ",").map(item => item.trim());
      if (entries.length === 0 || entries.some(item => item.length === 0)) {
        throw new SurfaceError(line.number, "refine expects a comma-separated constructor pattern");
      }
      let refineGoal = current.goal;
      let foldRefinement = (proof: Proof): Proof => proof;
      if (refineGoal.tag === "pred") {
        try {
          const predicateName = refineGoal.pred;
          const unfolded = unfoldGoal(kernel,
            resolveProof(kernel, predicateName, line.number, scope), refineGoal,
            current.assumptions, line.number);
          let reduced = unfolded.formula;
          let rebuild = (proof: Proof): Proof => proof;
          const facts = [
            ...current.assumptions.map(formula => ({ formula, proof: assume(formula) })),
            ...current.locals.values(),
          ];
          for (let index = 0;
            index < predicateSoftGuardCount(predicateName, kernel, scope) && reduced.tag === "and";
            index += 1) {
            const evidence = facts.find(item => formulaEquals(item.formula, reduced.left))?.proof ??
              (reduced.left.tag === "pred" && reduced.left.args.length > 0
                ? proveRefinement(kernel, reduced.left.args.at(-1)!, reduced.left.pred,
                  reduced.left.args.slice(0, -1), current.assumptions,
                  [...current.locals.values()].map(item => item.proof), visibility)
                : undefined);
            if (!evidence) break;
            const previous = rebuild;
            rebuild = proof => previous(andIntro(evidence, proof));
            reduced = reduced.right;
          }
          if (reduced.tag === "exists" || reduced.tag === "and" || reduced.tag === "iff") {
            refineGoal = reduced;
            foldRefinement = proof => impElim(unfolded.fold, rebuild(proof));
          }
        } catch {
          // Keep the authored goal when it is not a transparent constructor.
        }
      }
      let cursor = 0;
      const holes: Formula[] = [];
      const build = (formula: Formula, entryPosition = true): ((proofs: readonly Proof[]) => Proof) => {
        const next = entries[cursor];
        // A hole at a conjunction with entries still to come stands for the
        // first conjunct; the entries after it fill the rest, as ⟨a, ?_, c⟩
        // for A ∧ B ∧ C reads. A final hole stands for everything left.
        const descends = formula.tag === "and" && cursor < entries.length - 1;
        if (entryPosition && next === "?_" && !descends) {
          cursor += 1;
          const index = holes.length;
          holes.push(formula);
          return proofs => proofs[index]!;
        }
        // A nested constructor for a predicate definition is assembled as its
        // own exact ⟨…⟩, which unfolds the definition at its top level.
        if (entryPosition && next?.startsWith("⟨") && next.endsWith("⟩") && formula.tag === "pred") {
          const proof = parseProofExpression(kernel, next, current, variables, line.number, scope,
            { expectedConclusion: formula });
          cursor += 1;
          return () => proof;
        }
        if (entryPosition && next?.startsWith("⟨") && next.endsWith("⟩")) {
          const outerEntries = entries, outerCursor = cursor;
          entries = splitTopLevel(next.slice(1, -1), ",").map(item => item.trim());
          if (entries.length < 2 || entries.some(item => !item)) {
            throw new SurfaceError(line.number, "nested refine expects at least two constructor entries");
          }
          cursor = 0;
          const nested = build(formula, false);
          if (cursor !== entries.length) {
            throw new SurfaceError(line.number, "nested refine has unused constructor entries");
          }
          entries = outerEntries;
          cursor = outerCursor + 1;
          return nested;
        }
        // A final existential component may already have a complete proof.
        // Try it before treating the entry as a witness; earlier entries keep
        // their established witness/constructor interpretation.
        if (entryPosition && formula.tag === "exists" && cursor === entries.length - 1 && next !== "_") {
          try {
            const proof = parseProofExpression(kernel, next!, current, variables, line.number, scope,
              { expectedConclusion: formula });
            if (formulaEquals(kernel.checkProof(proof, current.assumptions), formula)) {
              cursor += 1;
              return () => proof;
            }
          } catch {
            // A term witness is not necessarily a proof reference.
          }
        }
        if (formula.tag === "exists") {
          const entry = entries[cursor];
          if (entry === undefined) {
            throw new SurfaceError(line.number,
              `refine needs a witness for ${formatFormula(formula)}`);
          }
          if (entry === "_") {
            throw new SurfaceError(line.number,
              "refine cannot infer an existential witness; write the witness explicitly");
          }
          cursor += 1;
          const witness = parseTerm(entry, kernel, variables, line.number, scope);
          const instance = substituteFormula(formula.body, formula.variable, witness);
          const evidence = build(instance);
          return proofs => existsIntro(formula.variable, formula.body, witness, evidence(proofs));
        }
        if ((formula.tag === "and" || formula.tag === "iff") && entries[cursor] !== "_") {
          try {
            const proof = parseProofExpression(kernel, entries[cursor]!, current, variables, line.number, scope,
              { expectedConclusion: formula });
            if (formulaEquals(kernel.checkProof(proof, current.assumptions), formula)) {
              cursor += 1;
              return () => proof;
            }
          } catch {
            // If the next entry is not evidence for the whole connective,
            // interpret the pattern structurally below.
          }
        }
        if (formula.tag === "and") {
          const left = build(formula.left);
          const right = build(formula.right);
          return proofs => andIntro(left(proofs), right(proofs));
        }
        if (formula.tag === "iff") {
          const forward = build(imp(formula.left, formula.right));
          const backward = build(imp(formula.right, formula.left));
          return proofs => iffIntro(forward(proofs), backward(proofs));
        }
        const entry = entries[cursor];
        if (entry === undefined) {
          throw new SurfaceError(line.number,
            `refine needs evidence for ${formatFormula(formula)}`);
        }
        cursor += 1;
        if (entry === "_") {
          const index = holes.length;
          holes.push(formula);
          return proofs => proofs[index]!;
        }
        const proof = entry === "rfl" || entry === "reflexivity"
          ? (() => {
              if (formula.tag !== "eq" || !termEquals(formula.left, formula.right)) {
                throw new SurfaceError(line.number,
                  `${entry} cannot establish ${formatFormula(formula)}`);
              }
              return refl(formula.left);
            })()
          : entry === "assumption"
            ? (() => {
                const local = [...current.locals.values()].find(item => formulaEquals(item.formula, formula));
                const assumed = current.assumptions.find(item => formulaEquals(item, formula));
                if (!local && !assumed) {
                  throw new SurfaceError(line.number,
                    `no assumption proves ${formatFormula(formula)}`);
                }
                return local?.proof ?? assume(assumed!);
              })()
            : parseProofExpression(kernel, entry, current, variables, line.number, scope,
              { expectedConclusion: formula });
        const actual = kernel.checkProof(proof, current.assumptions);
        if (!formulaEquals(actual, formula)) {
          const bridged = bridgeDefinition(kernel, scope, line.number, proof, actual, formula, current.assumptions, current.locals);
          if (!bridged) {
            throw new SurfaceError(line.number,
              `${entry} proves ${formatFormula(actual)}, but refine needs ${formatFormula(formula)}`);
          }
          return () => bridged;
        }
        return () => proof;
      };
      const assemble = build(refineGoal, false);
      if (cursor !== entries.length) {
        throw new SurfaceError(line.number,
          `refine has ${entries.length - cursor} unused constructor ${entries.length - cursor === 1 ? "entry" : "entries"}`);
      }
      if (holes.length === 0) close(line, foldRefinement(assemble([])));
      else replaceWith(line, holes.map(goal => ({ goal })), proofs => foldRefinement(assemble(proofs)));
      continue;
    }
    const disjunctionCases = /^(?:cases|rcases)\s+(\S+)\s+with\s+(.+\|.+)$/u.exec(command);
    if (disjunctionCases) {
      const source = disjunctionCases[1]!;
      const names = disjunctionCases[2]!.split("|").map(item => item.trim());
      if (names.length < 2 || !names.every(name => SIMPLE_IDENTIFIER.test(name))) {
        throw new SurfaceError(line.number, "malformed disjunction case names");
      }
      let local = current.locals.get(source);
      if (!local) throw new SurfaceError(line.number, `unknown local proof ${source}`);
      // A defined predicate splits through its definition.
      if (local.formula.tag === "pred") {
        const unfolded = unfoldPredicateFact(kernel, scope, line.number, local, current.assumptions, ["or"]);
        if (unfolded) local = unfolded;
      }
      const alternatives: Formula[] = [];
      const collectAlternatives = (formula: Formula): void => {
        if (formula.tag === "or") {
          collectAlternatives(formula.left);
          collectAlternatives(formula.right);
        } else alternatives.push(formula);
      };
      if (names.length === 2 && local.formula.tag === "or") {
        alternatives.push(local.formula.left, local.formula.right);
      } else collectAlternatives(local.formula);
      if (alternatives.length !== names.length) {
        throw new SurfaceError(line.number,
          `cases has ${names.length} names but ${source} has ${alternatives.length} alternatives`);
      }
      const specifications = alternatives.map((alternative, index) => {
        const locals = new Map(current.locals);
        locals.set(names[index]!, { formula: alternative, proof: assume(alternative) });
        return { goal: current.goal, assumptions: [...current.assumptions, alternative], locals };
      });
      replaceWith(line, specifications, proofs => {
        if (names.length === 2) {
          if (local.formula.tag !== "or") throw new Error("malformed disjunction");
          return orElim(local.proof, proofs[0]!, proofs[1]!);
        }
        let cursor = 0;
        const assemble = (formula: Formula, disjunction: Proof): Proof => {
          if (formula.tag !== "or") return proofs[cursor++]!;
          return orElim(disjunction,
            assemble(formula.left, assume(formula.left)),
            assemble(formula.right, assume(formula.right)));
        };
        return assemble(local.formula, local.proof);
      });
      continue;
    }
    const recursiveCases = /^rcases\s+(\S+)\s+with\s+(.+)$/u.exec(command);
    if (recursiveCases) {
      const source = recursiveCases[1]!;
      const local = current.locals.get(source);
      if (!local) throw new SurfaceError(line.number, `unknown local proof ${source}`);
      destructureProof(line, current, parseDestructurePattern(recursiveCases[2]!, line.number), local.formula, local.proof, source, true);
      continue;
    }
    const casesConjunction = /^cases\s+(\S+)\s+with\s+(\S+)\s+(?:and|∧)\s+(\S+)$/u.exec(command);
    if (casesConjunction) {
      const source = casesConjunction[1]!;
      const leftName = casesConjunction[2]!.trim();
      const rightName = casesConjunction[3]!.trim();
      if (![leftName, rightName].every(name => SIMPLE_IDENTIFIER.test(name))) throw new SurfaceError(line.number, "malformed conjunction case names");
      const local = current.locals.get(source);
      if (!local) throw new SurfaceError(line.number, `unknown local proof ${source}`);
      if (local.formula.tag !== "and") throw new SurfaceError(line.number, `cases requires ${source} to prove a conjunction`);
      const locals = new Map(current.locals);
      locals.set(leftName, { formula: local.formula.left, proof: andElimLeft(local.proof) });
      locals.set(rightName, { formula: local.formula.right, proof: andElimRight(local.proof) });
      replaceWith(line, [{ goal: current.goal, locals }], ([proof]) => proof!);
      continue;
    }
    const clear = /^clear\s+(\S+)$/.exec(command);
    if (clear) {
      const local = current.locals.get(clear[1]!);
      if (!local) throw new SurfaceError(line.number, `unknown local proof ${clear[1]}`);
      const locals = new Map(current.locals);
      locals.delete(clear[1]!);
      const index = current.assumptions.findIndex(item => formulaEquals(item, local.formula));
      const assumptions = index < 0 ? current.assumptions : current.assumptions.filter((_, itemIndex) => itemIndex !== index);
      replaceWith(line, [{ goal: current.goal, assumptions, locals }], ([proof]) => proof!);
      continue;
    }
    const rename = /^rename\s+(\S+)\s*(?:=>|⇒)\s*(\S+)$/.exec(command);
    if (rename) {
      const local = current.locals.get(rename[1]!);
      if (!local) throw new SurfaceError(line.number, `unknown local proof ${rename[1]}`);
      if (!SIMPLE_IDENTIFIER.test(rename[2]!)) throw new SurfaceError(line.number, "malformed local proof name");
      if (current.locals.has(rename[2]!)) throw new SurfaceError(line.number, `local proof ${rename[2]} already exists`);
      current.locals.delete(rename[1]!);
      current.locals.set(rename[2]!, local);
      continue;
    }
    const revert = /^revert\s+(\S+)$/.exec(command);
    if (revert) {
      const local = current.locals.get(revert[1]!);
      if (!local) throw new SurfaceError(line.number, `unknown local proof ${revert[1]}`);
      const index = current.assumptions.findIndex(item => formulaEquals(item, local.formula));
      if (index < 0) throw new SurfaceError(line.number, `cannot revert derived fact ${revert[1]}; only assumptions can be reverted`);
      const locals = new Map(current.locals);
      locals.delete(revert[1]!);
      const assumptions = current.assumptions.filter((_, itemIndex) => itemIndex !== index);
      replaceWith(line, [{ goal: imp(local.formula, current.goal), assumptions, locals }],
        ([proof]) => impElim(proof!, assume(local.formula)));
      continue;
    }
    if (command === "exfalso") {
      replaceWith(line, [{ goal: bottom }], ([absurdity]) => falseElim(current.goal, absurdity!));
      continue;
    }
    // `by_contra` or `by_contra h` assumes the negation of the goal under
    // the given name, `this` by default, and asks for ⊥.
    const byContra = /^by_contra(?:\s+([\p{L}_][\p{L}\p{M}\p{N}_']*))?$/u.exec(command);
    if (byContra) {
      const name = byContra[1] ?? "this";
      if (current.locals.has(name)) throw new SurfaceError(line.number, `local proof ${name} already exists`);
      const negated = not(current.goal);
      const locals = new Map(current.locals);
      locals.set(name, { formula: negated, proof: assume(negated) });
      const goal = current.goal;
      replaceWith(line, [{ goal: bottom, assumptions: [...current.assumptions, negated], locals }],
        ([body]) => dne(goal, impIntro(negated, body!)));
      continue;
    }
    // `by_cases h : P` splits on P by excluded middle: the first goal has
    // h : P, the second h : ¬P, with a bullet for each as after `cases`.
    const byCases = /^by_cases\s+(?:([\p{L}_][\p{L}\p{M}\p{N}_']*)\s*:\s*)?(.+)$/u.exec(command);
    if (byCases) {
      const name = byCases[1] ?? "h";
      if (current.locals.has(name)) throw new SurfaceError(line.number, `local proof ${name} already exists`);
      const proposition = parseFormula(byCases[2]!, kernel, variables, line.number, scope);
      const branch = (formula: Formula) => {
        const locals = new Map(current.locals);
        locals.set(name, { formula, proof: assume(formula) });
        return { goal: current.goal, assumptions: [...current.assumptions, formula], locals };
      };
      replaceWith(line, [branch(proposition), branch(not(proposition))],
        ([positive, negative]) => orElim(excludedMiddle(proposition), positive!, negative!));
      continue;
    }
    if (command === "contradiction") {
      const absurdity = settle(kernel, bottom, {
        using: [], assumptions: current.assumptions, facts: [...current.locals.values()].map(item => item.proof), visibility,
      });
      close(line, falseElim(current.goal, absurdity));
      continue;
    }
    if (command === "tauto") {
      close(line, proveTautology(
        kernel, current.goal, current.assumptions, [...current.locals.values()].map(item => item.proof),
      ));
      continue;
    }
    if (command === "cc" || command === "congruence") {
      close(line, proveCongruence(
        kernel, current.goal, current.assumptions, [
          ...[...current.locals.values()].map(item => item.proof),
          ...openedGuardFacts(kernel, current.assumptions, current.locals.values(), visibility).map(item => item.proof),
        ],
      ));
      continue;
    }
    const witness = /^(?:witness|use)\s+(.+)$/.exec(command);
    if (witness) {
      const target = goalThroughDefinition(["exists"]).goal;
      if (target.tag !== "exists") throw new SurfaceError(line.number, "witness requires an existential goal");
      const term = parseTerm(witness[1]!, kernel, variables, line.number, scope);
      const instance = substituteFormula(target.body, target.variable, term);
      // A carrier guard conjunct on the witness, such as the `Nat(k)` of
      // `∃ k, Nat(k) ∧ …`, is routine: it is discharged from the context or
      // by soft typing, and the proof continues with the mathematical part.
      let remaining = instance;
      let rebuild: (inner: Proof) => Proof = inner => inner;
      while (remaining.tag === "and" && remaining.left.tag === "pred" && remaining.left.args.length > 0 &&
          routineGuardPredicate(kernel, remaining.left.pred)) {
        const guard = remaining.left;
        const evidence = [...current.locals.values()].find(item => formulaEquals(item.formula, guard))?.proof
          ?? (current.assumptions.some(item => formulaEquals(item, guard)) ? assume(guard) : undefined)
          ?? proveRefinement(kernel, guard.args.at(-1)!, guard.pred, guard.args.slice(0, -1), current.assumptions,
            [...current.locals.values()].map(item => item.proof), visibility);
        if (!evidence) break;
        const previous = rebuild;
        rebuild = inner => previous(andIntro(evidence, inner));
        remaining = remaining.right;
      }
      replaceWith(line, [{ goal: remaining }], ([evidence]) =>
        existsIntro(target.variable, target.body, term, rebuild(evidence!)));
      continue;
    }
    if (command === "assumption") {
      const local = [...current.locals.values()].find(item => formulaEquals(item.formula, current.goal));
      const formula = current.assumptions.find(item => formulaEquals(item, current.goal));
      const opened = local || formula ? undefined
        : openedGuardFacts(kernel, current.assumptions, current.locals.values(), visibility).find(item => formulaEquals(item.formula, current.goal));
      if (!local && !formula && !opened) throw new SurfaceError(line.number, `no assumption proves ${formatFormula(current.goal)}`);
      close(line, local?.proof ?? opened?.proof ?? assume(formula!));
      continue;
    }
    const symmAt = /^symm at ([\p{L}_][\p{L}\p{M}\p{N}_]*)$/u.exec(command);
    if (symmAt) {
      const name = symmAt[1]!;
      const local = current.locals.get(name);
      if (!local) throw new SurfaceError(line.number, `unknown local proof ${name}`);
      if (local.formula.tag !== "eq") throw new SurfaceError(line.number, `symm at ${name} requires an equality`);
      const proof = symm(local.proof);
      current.locals.set(name, { proof, formula: eq(local.formula.right, local.formula.left) });
      continue;
    }
    if (command === "symm") {
      if (current.goal.tag !== "eq") throw new SurfaceError(line.number, "symm requires an equality goal");
      replaceWith(line, [{ goal: eq(current.goal.right, current.goal.left) }], ([proof]) => symm(proof!));
      continue;
    }
    if (command === "reflexivity" || command === "rfl") {
      if (current.goal.tag !== "eq") throw new SurfaceError(line.number, "reflexivity requires an equality goal");
      close(line, refl(current.goal.left));
      continue;
    }
    if (command === "compute") {
      if (current.goal.tag !== "eq") {
        // A closed order goal over ℕ: both sides are evaluated and the
        // relation is certified through the order's definitions.
        const order = closedNaturalOrder(kernel, current.goal, line.number, scope);
        if (!order) {
          throw new SurfaceError(line.number,
            "compute requires an equality goal, or a closed natural-number order goal a < b, a ≤ b, or a ≠ b");
        }
        const nested = (goal: Formula, script: readonly string[]) => elaborateTacticTheorem(kernel, name, [], [], [], goal,
          script.map(text => ({ number: line.number, text, indent: line.indent + 2 })), scope,
          { assumptions: current.assumptions, locals: current.locals, variables })!.proof;
        if (order.relation !== "notEqual") {
          close(line, nested(current.goal, [`witness ${order.gap}`, "compute"]));
          continue;
        }
        // a ≠ b: the smaller side is below the larger, so a = b would put a
        // natural number below itself.
        const irreflexive = resolveOptional("Less.irreflexive", scope, candidate => kernel.theorems.has(candidate)) ??
          [...kernel.theorems.keys()].find(candidate => candidate.endsWith(".Less.irreflexive"));
        if (!irreflexive) {
          throw new SurfaceError(line.number,
            "compute needs Less.irreflexive in scope for a ≠ b; import Grace.Cumulus.Nat.Order");
        }
        const [small, large] = order.leftSmaller ? [order.left, order.right] : [order.right, order.left];
        const below = nested(pred(order.less, small, large), [`witness ${order.gap}`, "compute"]);
        const equal = eq(order.left, order.right);
        let variable = "__compute";
        while (freeTermVariables(large).has(variable)) variable += "_";
        // From small = large, the strict comparison becomes large < large.
        const motive = pred(order.less, v(variable), large);
        const reflexive = eqElim(order.leftSmaller ? assume(equal) : symm(assume(equal)), variable, motive, below);
        let absurd: Proof = at(theorem(irreflexive), large);
        for (;;) {
          const statement = kernel.checkProof(absurd, [...current.assumptions, equal]);
          if (statement.tag !== "imp") break;
          if (formulaEquals(statement.left, pred(order.less, large, large))) { absurd = impElim(absurd, reflexive); break; }
          const guard = statement.left.tag === "pred" && statement.left.args.length > 0
            ? proveRefinement(kernel, statement.left.args.at(-1)!, statement.left.pred, statement.left.args.slice(0, -1),
              current.assumptions, [...current.locals.values()].map(item => item.proof), visibility)
            : undefined;
          if (!guard) throw new SurfaceError(line.number, `compute could not establish ${formatFormula(statement.left)}`);
          absurd = impElim(absurd, guard);
        }
        close(line, impIntro(equal, absurd));
        continue;
      }
      const left = current.goal.left, right = current.goal.right;
      if (left.tag === "app" && right.tag === "app" &&
          left.fn === "Grace.Cumulus.Rat.Operations.rationalClass" && right.fn === left.fn) {
        kernel.checkRationalClassEquality(left, right);
        close(line, rationalClassCompute(left, right));
      } else {
        const certificate = cachedComputation(kernel, left, right);
        try { close(line, certificate.proof); }
        catch (error) {
          // A certificate from an earlier check of this process whose
          // definitions have changed since: rebuild it.
          if (!certificate.reused) throw error;
          computationCertificates.delete(certificate.key);
          close(line, kernel.proveComputation(left, right));
        }
      }
      continue;
    }
    const linearCombination = /^linear_combination\s+(.+)$/.exec(command);
    if (linearCombination) {
      if (current.goal.tag !== "eq") throw new SurfaceError(line.number, "linear_combination requires an equality goal");
      const expression = linearCombination[1]!.trim();
      const pieces: { text: string; negative: boolean }[] = [];
      let depth = 0;
      let start = 0;
      let negative = false;
      if (expression.startsWith("+") || expression.startsWith("-")) {
        negative = expression[0] === "-";
        start = 1;
      }
      for (let index = start; index < expression.length; index += 1) {
        const character = expression[index]!;
        if (character === "(") depth += 1;
        else if (character === ")") depth -= 1;
        else if (depth === 0 && (character === "+" || character === "-")) {
          const text = expression.slice(start, index).trim();
          if (!text) throw new SurfaceError(line.number, "malformed linear combination");
          pieces.push({ text, negative });
          negative = character === "-";
          start = index + 1;
        }
      }
      const finalPiece = expression.slice(start).trim();
      if (finalPiece) pieces.push({ text: finalPiece, negative });
      if (pieces.length === 0) throw new SurfaceError(line.number, "linear_combination requires at least one equality");
      const facts = [...current.locals.values()].map(item => item.proof);
      // Resolve the carrier from the goal and the named equations.
      // All algebra below produces congruence and ring-law proofs.
      const equationTerms = pieces.flatMap(piece => {
        const match = /^(?:(.+?)\s*\*\s*)?([\p{L}_][\p{L}\p{M}\p{N}_]*)$/u.exec(piece.text);
        const local = match && current.locals.get(match[2]!);
        return local?.formula.tag === "eq" ? [local.formula.left, local.formula.right] : [];
      });
      const ringSession = prepareCommutativeRing(kernel, [current.goal.left, current.goal.right, ...equationTerms],
        current.assumptions, facts, scope, line.number);
      if (ringSession) {
        const ops = ringSession.operations;
        const plus = (a: Term, b: Term) => app(ops.call2, ops.add, a, b);
        const minus = (a: Term) => app(ops.call1, ops.neg, a);
        const scaled = pieces.map(piece => {
          const match = /^(?:(.+?)\s*\*\s*)?([\p{L}_][\p{L}\p{M}\p{N}_]*)$/u.exec(piece.text);
          if (!match) throw new SurfaceError(line.number, `malformed linear combination term ${piece.text}`);
          const local = current.locals.get(match[2]!);
          if (!local) throw new SurfaceError(line.number, `unknown local proof ${match[2]}`);
          if (local.formula.tag !== "eq") throw new SurfaceError(line.number, `linear combination term ${match[2]} is not an equality`);
          let proof = piece.negative ? symm(local.proof) : local.proof;
          if (match[1]) {
            // A coefficient is read as the goal is; a bare numeral is the
            // carrier's, as `(2:R)` is, and a coefficient the notation in
            // scope cannot type is read in the selected ring.
            let parsed: Term;
            try { parsed = parseTerm(match[1].trim(), kernel, variables, line.number, scope); }
            catch (error) {
              if (!(error instanceof SurfaceError)) throw error;
              parsed = parseTerm(match[1].trim(), kernel, variables, line.number,
                { ...scope, rings: [ringSession.ring], ringAliases: scope.ringAliases ?? scope.rings ?? [] });
            }
            const coefficient = ringNumeral(kernel, scope, parsed, ringSession.ring, line.number);
            proof = congr(ops.call2, refl(ops.mul), refl(coefficient), proof);
          }
          return proof;
        });
        const combined = scaled.reduce((a, b) => congr(ops.call2, refl(ops.add), a, b));
        const equation = kernel.checkProof(combined, current.assumptions);
        if (equation.tag !== "eq") throw new SurfaceError(line.number, "internal linear combination is not an equality");
        const corrected = plus(current.goal.right, plus(equation.left, minus(equation.right)));
        const normalized = ringSession.normalize([current.goal.left, corrected]);
        if (!normalized || !termEquals(normalized[0]!.term, normalized[1]!.term))
          throw new SurfaceError(line.number, "linear_combination does not normalize to the current goal");
        const substitution = congr(ops.call2, refl(ops.add), refl(current.goal.right),
          congr(ops.call2, refl(ops.add), combined, refl(minus(equation.right))));
        close(line, calc(normalized[0]!.proof, symm(normalized[1]!.proof), substitution,
          ringSession.cancelDifference(current.goal.right, equation.right)));
        continue;
      }
      const scaled: Proof[] = pieces.map(piece => {
        const match = /^(?:(.+?)\s*\*\s*)?([\p{L}_][\p{L}\p{M}\p{N}_]*)$/u.exec(piece.text);
        if (!match) throw new SurfaceError(line.number, `malformed linear combination term ${piece.text}`);
        const local = current.locals.get(match[2]!);
        if (!local) throw new SurfaceError(line.number, `unknown local proof ${match[2]}`);
        if (local.formula.tag !== "eq") throw new SurfaceError(line.number, `linear combination term ${match[2]} is not an equality`);
        const equality = piece.negative ? symm(local.proof) : local.proof;
        if (!match[1]) return equality;
        const coefficient = parseTerm(match[1].trim(), kernel, variables, line.number, scope);
        const presentation = naturalLinearArithmeticPresentation(kernel, line.number, scope);
        return congr(presentation.mul, refl(coefficient), equality);
      });
      const presentation = naturalLinearArithmeticPresentation(kernel, line.number, scope);
      const combined = scaled.reduce((left, right) => congr(presentation.add, left, right));
      const combinedFormula = kernel.checkProof(combined, current.assumptions);
      if (combinedFormula.tag !== "eq") throw new SurfaceError(line.number, "internal linear combination did not produce an equality");
      const polynomialRefinements = prepareRefinementProver(kernel, current.assumptions, [], visibility);
      const combinedLeft = normalizeNaturalSemiring(kernel, combinedFormula.left, line.number, scope, current.assumptions, polynomialRefinements);
      const combinedRight = normalizeNaturalSemiring(kernel, combinedFormula.right, line.number, scope, current.assumptions, polynomialRefinements);
      const goalLeft = normalizeNaturalSemiring(kernel, current.goal.left, line.number, scope, current.assumptions, polynomialRefinements);
      const goalRight = normalizeNaturalSemiring(kernel, current.goal.right, line.number, scope, current.assumptions, polynomialRefinements);
      const normalizedCombination = calc(symm(combinedLeft.proof), combined, combinedRight.proof);
      if (termEquals(combinedLeft.term, goalLeft.term) && termEquals(combinedRight.term, goalRight.term)) {
        close(line, calc(goalLeft.proof, normalizedCombination, symm(goalRight.proof)));
        continue;
      }
      if (termEquals(combinedLeft.term, goalRight.term) && termEquals(combinedRight.term, goalLeft.term)) {
        close(line, calc(goalLeft.proof, symm(normalizedCombination), symm(goalRight.proof)));
        continue;
      }
      const monomialKey = (item: SemiringMonomial): string => item.factors.map(termCanonical).join("\u0000");
      const subtract = (whole: readonly SemiringMonomial[], part: readonly SemiringMonomial[]): SemiringMonomial[] | undefined => {
        const remainder = [...whole];
        for (const item of part) {
          const index = remainder.findIndex(candidate => monomialKey(candidate) === monomialKey(item));
          if (index < 0) return undefined;
          remainder.splice(index, 1);
        }
        return remainder;
      };
      const leftCommon = subtract(combinedLeft.monomials, goalLeft.monomials);
      const rightCommon = subtract(combinedRight.monomials, goalRight.monomials);
      if (leftCommon && rightCommon && leftCommon.length > 0 && leftCommon.length === rightCommon.length &&
          leftCommon.every((item, index) => monomialKey(item) === monomialKey(rightCommon[index]!))) {
        const productTerm = (factors: readonly Term[]): Term => factors.slice(0, -1).reduceRight<Term>(
          (tail, head) => app(presentation.mul, head, tail), factors.at(-1)!,
        );
        const commonTerms = leftCommon.map(item => productTerm(item.factors));
        const commonTerm = commonTerms.slice(0, -1).reduceRight<Term>(
          (tail, head) => app(presentation.add, head, tail), commonTerms.at(-1)!,
        );
        const augmentedLeft = app(presentation.add, commonTerm, goalLeft.term);
        const augmentedRight = app(presentation.add, commonTerm, goalRight.term);
        const augmentedLeftNormal = normalizeNaturalSemiring(kernel, augmentedLeft, line.number, scope, current.assumptions, polynomialRefinements);
        const augmentedRightNormal = normalizeNaturalSemiring(kernel, augmentedRight, line.number, scope, current.assumptions, polynomialRefinements);
        if (termEquals(augmentedLeftNormal.term, combinedLeft.term) &&
            termEquals(augmentedRightNormal.term, combinedRight.term)) {
          const augmentedEquality = calc(
            augmentedLeftNormal.proof, normalizedCombination, symm(augmentedRightNormal.proof),
          );
          const facts = [...current.locals.values()].map(item => item.proof);
          const refinements = prepareRefinementProver(kernel, current.assumptions, facts, visibility);
          let cancellation = at(
            resolveProof(kernel, "Grace.Cumulus.Nat.Core.add.left_cancel", line.number, scope),
            goalLeft.term, goalRight.term, commonTerm,
          );
          while (true) {
            const formula = kernel.checkProof(cancellation, current.assumptions);
            if (formula.tag !== "imp" || formula.left.tag !== "pred" || formula.left.args.length !== 1) break;
            const evidence = refinements.prove(formula.left.args[0]!, formula.left.pred);
            if (!evidence) throw new SurfaceError(line.number, `linear_combination could not establish ${formatFormula(formula.left)}`);
            cancellation = impElim(cancellation, evidence);
          }
          close(line, calc(goalLeft.proof, impElim(cancellation, augmentedEquality), symm(goalRight.proof)));
          continue;
        }
      }
      throw new SurfaceError(line.number, "linear_combination does not normalize to the current goal");
    }
    // `ring [h₁, …]` closes a natural-number equation using the named
    // equations as rewrite rules modulo the semiring axioms: a side is
    // normalized, a quotient monomial times a rule's normalized left side
    // that fits inside the normal form is exposed by ring and replaced by
    // the rule's right side, and this repeats until the sides agree by ring.
    const ringWith = /^ring\s*\[(.*)\]$/u.exec(command);
    if (ringWith) {
      if (current.goal.tag !== "eq") throw new SurfaceError(line.number, "ring [rules] requires an equality goal");
      const presentation = naturalLinearArithmeticPresentation(kernel, line.number, scope);
      const refinements = prepareRefinementProver(kernel, current.assumptions, [], visibility);
      const normalize = (term: Term): SemiringNormalForm =>
        normalizeNaturalSemiring(kernel, term, line.number, scope, current.assumptions, refinements);
      interface Monomial { coefficient: bigint; readonly atoms: Map<string, { readonly term: Term; power: number }> }
      interface Rule { readonly name: string; readonly left: SemiringNormalForm; readonly right: SemiringNormalForm; readonly proof: Proof }
      const monomialOf = (item: SemiringMonomial): Monomial => {
        const result: Monomial = { coefficient: 1n, atoms: new Map() };
        for (const factor of item.factors) {
          const value = factor.tag === "nat" ? naturalValue(factor) : undefined;
          if (value !== undefined) { result.coefficient *= value; continue; }
          const key = termCanonical(factor);
          const entry = result.atoms.get(key);
          if (entry) entry.power += 1; else result.atoms.set(key, { term: factor, power: 1 });
        }
        return result;
      };
      const atomsKey = (monomial: Monomial): string =>
        [...monomial.atoms.entries()].sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0)).map(([key, entry]) => `${key}^${entry.power}`).join("*");
      const divide = (divisor: Monomial, monomial: Monomial): Monomial | undefined => {
        if (monomial.coefficient % divisor.coefficient !== 0n) return undefined;
        const atoms = new Map([...monomial.atoms].map(([key, entry]) => [key, { term: entry.term, power: entry.power }]));
        for (const [key, entry] of divisor.atoms) {
          const have = atoms.get(key);
          if (!have || have.power < entry.power) return undefined;
          if (have.power === entry.power) atoms.delete(key); else have.power -= entry.power;
        }
        return { coefficient: monomial.coefficient / divisor.coefficient, atoms };
      };
      const times = (left: Monomial, right: Monomial): Monomial => {
        const atoms = new Map([...left.atoms].map(([key, entry]) => [key, { term: entry.term, power: entry.power }]));
        for (const [key, entry] of right.atoms) {
          const have = atoms.get(key);
          if (have) have.power += entry.power; else atoms.set(key, { term: entry.term, power: entry.power });
        }
        return { coefficient: left.coefficient * right.coefficient, atoms };
      };
      const subtract = (whole: readonly Monomial[], part: readonly Monomial[]): Monomial[] | undefined => {
        const result = new Map(whole.map(item => [atomsKey(item), { coefficient: item.coefficient, atoms: item.atoms }]));
        for (const item of part) {
          const have = result.get(atomsKey(item));
          if (!have || have.coefficient < item.coefficient) return undefined;
          if (have.coefficient === item.coefficient) result.delete(atomsKey(item)); else have.coefficient -= item.coefficient;
        }
        return [...result.values()];
      };
      const monomialTerm = (monomial: Monomial): Term => {
        const factors: Term[] = [];
        if (monomial.coefficient !== 1n || monomial.atoms.size === 0) factors.push(nat(monomial.coefficient));
        for (const entry of monomial.atoms.values()) for (let index = 0; index < entry.power; index += 1) factors.push(entry.term);
        return factors.slice(0, -1).reduceRight<Term>((tail, head) => app(presentation.mul, head, tail), factors.at(-1)!);
      };
      const sumTerm = (terms: readonly Term[]): Term =>
        terms.slice(0, -1).reduceRight<Term>((tail, head) => app(presentation.add, head, tail), terms.at(-1)!);
      let rules: Rule[] = splitTopLevel(ringWith[1]!, ",").map(item => item.trim()).filter(Boolean).map(name => {
        const proof = parseProofExpression(kernel, name, current, variables, line.number, scope);
        const formula = kernel.checkProof(proof, current.assumptions);
        if (formula.tag !== "eq") throw new SurfaceError(line.number, `ring rule ${name} must be an equation`);
        const left = normalize(formula.left);
        const right = normalize(formula.right);
        if (left.monomials.length === 0) throw new SurfaceError(line.number, `ring rule ${name} has a zero left side`);
        return { name, left, right, proof: calc(symm(left.proof), proof, right.proof) };
      });
      const reduce = (start: Term, using: readonly Rule[]): { readonly term: Term; readonly proof: Proof } => {
        let term = start;
        let chain: Proof | undefined;
        for (let fuel = 0; fuel < 64; fuel += 1) {
          const form = normalize(term);
          const polynomial = form.monomials.map(monomialOf);
          let found: { readonly rule: Rule; readonly quotient: Monomial; readonly rest: Monomial[] } | undefined;
          search: for (const rule of using) {
            const left = rule.left.monomials.map(monomialOf);
            for (const pivot of left) for (const monomial of polynomial) {
              const quotient = divide(pivot, monomial);
              if (!quotient) continue;
              const rest = subtract(polynomial, left.map(item => times(quotient, item)));
              if (rest) { found = { rule, quotient, rest }; break search; }
            }
          }
          if (!found) break;
          const product = app(presentation.mul, monomialTerm(found.quotient), found.rule.left.term);
          const exposed = found.rest.length ? app(presentation.add, product, sumTerm(found.rest.map(monomialTerm))) : product;
          const exposedForm = normalize(exposed);
          if (!termEquals(exposedForm.term, form.term)) throw new SurfaceError(line.number, `ring [rules] could not expose ${found.rule.name} in ${formatTerm(term)}`);
          let placeholder = "__ring_rule";
          const forbidden = new Set([...freeTermVariables(exposed), ...freeTermVariables(found.rule.right.term)]);
          while (forbidden.has(placeholder)) placeholder += "_";
          const hole = app(presentation.mul, monomialTerm(found.quotient), v(placeholder));
          const withHole = found.rest.length ? app(presentation.add, hole, sumTerm(found.rest.map(monomialTerm))) : hole;
          const rewritten = substituteTerm(withHole, placeholder, found.rule.right.term);
          const step = calc(form.proof, symm(exposedForm.proof), eqElim(found.rule.proof, placeholder, eq(exposed, withHole), refl(exposed)));
          chain = chain ? calc(chain, step) : step;
          term = rewritten;
        }
        return { term, proof: chain ?? refl(start) };
      };
      // The rules reduce one another first: a step law stated with (n + 1)!
      // is usable on a goal in terms of n! once the factorial law has been
      // applied inside it.
      for (let round = 0; round < 8; round += 1) {
        let changed = false;
        rules = rules.map((rule, index) => {
          const others = rules.filter((_, position) => position !== index);
          const leftReduced = reduce(rule.left.term, others);
          const rightReduced = reduce(rule.right.term, others);
          if (termEquals(leftReduced.term, rule.left.term) && termEquals(rightReduced.term, rule.right.term)) return rule;
          changed = true;
          const left = normalize(leftReduced.term);
          const right = normalize(rightReduced.term);
          if (left.monomials.length === 0) throw new SurfaceError(line.number, `ring rule ${rule.name} reduces to a zero left side`);
          return { name: rule.name, left, right, proof: calc(symm(left.proof), symm(leftReduced.proof), rule.proof, rightReduced.proof, right.proof) };
        });
        if (!changed) break;
      }
      const left = reduce(current.goal.left, rules);
      const right = reduce(current.goal.right, rules);
      const leftForm = normalize(left.term);
      const rightForm = normalize(right.term);
      if (!termEquals(leftForm.term, rightForm.term)) {
        throw new SurfaceError(line.number,
          `ring [rules] did not close the goal; the sides reduce to ${formatTerm(leftForm.term)} and ${formatTerm(rightForm.term)}`);
      }
      close(line, calc(left.proof, leftForm.proof, symm(rightForm.proof), symm(right.proof)));
      continue;
    }
    const ringNormalForm = /^ring_nf(?:\s+at\s+([\p{L}_][\p{L}\p{M}\p{N}_]*))?$/u.exec(command);
    if (ringNormalForm) {
      const normalizeTerms = (terms: readonly Term[]) =>
        normalizeCommutativeRing(kernel, terms, current.assumptions,
          [...current.locals.values()].map(item => item.proof), scope, line.number);
      const polynomialRefinements = prepareRefinementProver(kernel, current.assumptions, [], visibility);
      if (ringNormalForm[1]) {
        const local = current.locals.get(ringNormalForm[1]);
        if (!local) throw new SurfaceError(line.number, `unknown local proof ${ringNormalForm[1]}`);
        if (local.formula.tag === "eq") {
          const generic = normalizeTerms([local.formula.left, local.formula.right]);
          const left = generic?.[0] ?? normalizeNaturalSemiring(kernel, local.formula.left, line.number, scope, current.assumptions, polynomialRefinements);
          const right = generic?.[1] ?? normalizeNaturalSemiring(kernel, local.formula.right, line.number, scope, current.assumptions, polynomialRefinements);
          current.locals.set(ringNormalForm[1], {
            formula: eq(left.term, right.term),
            proof: calc(symm(left.proof), local.proof, right.proof),
          });
          continue;
        }
        if (local.formula.tag !== "pred") {
          throw new SurfaceError(line.number, "ring_nf at requires an equality or predicate hypothesis");
        }
        // Replace each argument in its own position: a rewrite rule for one
        // argument must not touch its occurrences inside the others.
        let normalizedFormula: Formula = local.formula;
        let normalizedProof = local.proof;
        const indices = polynomialArgumentIndices(local.formula);
        const generic = normalizeTerms(indices.map(index => local.formula.args[index]!));
        const forbidden = freeFormulaVariables(local.formula);
        let placeholder = "__ring_nf";
        while (forbidden.has(placeholder)) placeholder += "_";
        for (const [position, index] of indices.entries()) {
          const argument = local.formula.args[index]!;
          const result = generic?.[position] ??
            normalizeNaturalSemiring(kernel, argument, line.number, scope, current.assumptions, polynomialRefinements);
          if (termEquals(argument, result.term)) continue;
          if (normalizedFormula.tag !== "pred") break;
          const motive = pred(normalizedFormula.pred,
            ...normalizedFormula.args.map((item, slot) => slot === index ? v(placeholder) : item));
          normalizedProof = eqElim(result.proof, placeholder, motive, normalizedProof);
          normalizedFormula = pred(normalizedFormula.pred,
            ...normalizedFormula.args.map((item, slot) => slot === index ? result.term : item));
        }
        current.locals.set(ringNormalForm[1], { formula: normalizedFormula, proof: normalizedProof });
        continue;
      }
      if (current.goal.tag === "eq") {
        const generic = normalizeTerms([current.goal.left, current.goal.right]);
        const left = generic?.[0] ?? normalizeNaturalSemiring(kernel, current.goal.left, line.number, scope, current.assumptions, polynomialRefinements);
        const right = generic?.[1] ?? normalizeNaturalSemiring(kernel, current.goal.right, line.number, scope, current.assumptions, polynomialRefinements);
        // Sides with the same normal form close the goal outright.
        if (termEquals(left.term, right.term)) { close(line, calc(left.proof, symm(right.proof))); continue; }
        replaceWith(line, [{ goal: eq(left.term, right.term) }], ([proof]) =>
          calc(left.proof, proof!, symm(right.proof)));
        continue;
      }
      if (current.goal.tag !== "pred") {
        throw new SurfaceError(line.number, "ring_nf requires an equality or predicate goal");
      }
      let goal = current.goal as Formula;
      let lift = (proof: Proof): Proof => proof;
      const indices = polynomialArgumentIndices(current.goal);
      const generic = normalizeTerms(indices.map(index => current.goal.args[index]!));
      for (const [position, index] of indices.entries()) {
        const argument = current.goal.args[index]!;
        const result = generic?.[position] ??
          normalizeNaturalSemiring(kernel, argument, line.number, scope, current.assumptions, polynomialRefinements);
        if (termEquals(argument, result.term)) continue;
        const rewritten = rewriteGoal(kernel, goal, result.proof, current.assumptions,
          [...current.locals.values()].map(item => item.proof), false, false, undefined, visibility);
        goal = rewritten.goal;
        const previous = lift;
        lift = proof => previous(rewritten.lift(proof));
      }
      replaceWith(line, [{ goal }], ([proof]) => lift(proof!));
      continue;
    }
    const ring = /^ring(?:\s+at\s+([\p{L}_][\p{L}\p{M}\p{N}_]*))?$/u.exec(command);
    if (ring) {
      if (!ring[1] && current.goal.tag === "eq") {
        const generic = normalizeCommutativeRing(kernel, [current.goal.left, current.goal.right],
          current.assumptions, [...current.locals.values()].map(item => item.proof), scope, line.number);
        if (generic) {
          if (termEquals(generic[0]!.term, generic[1]!.term)) {
            close(line, calc(generic[0]!.proof, symm(generic[1]!.proof)));
            continue;
          }
          // Match an available equality modulo the same checked normalizer.
          // This mirrors Nat ring's existing contextual equality behavior;
          // it does not search for combinations of hypotheses.
          let matched: Proof | undefined;
          const goalVariables = freeFormulaVariables(current.goal);
          for (const local of current.locals.values()) {
            if (local.formula.tag !== "eq" ||
                ![...freeFormulaVariables(local.formula)].some(variable => goalVariables.has(variable))) continue;
            const normalized = normalizeCommutativeRing(kernel, [local.formula.left, local.formula.right],
              current.assumptions, [...current.locals.values()].map(item => item.proof), scope, line.number);
            if (!normalized) continue;
            const equality = calc(symm(normalized[0]!.proof), local.proof, normalized[1]!.proof);
            if (termEquals(generic[0]!.term, normalized[0]!.term) &&
                termEquals(generic[1]!.term, normalized[1]!.term)) matched = equality;
            else if (termEquals(generic[0]!.term, normalized[1]!.term) &&
                termEquals(generic[1]!.term, normalized[0]!.term)) matched = symm(equality);
            if (matched) break;
          }
          if (!matched) {
            throw new SurfaceError(line.number, `the two ring polynomials have different normal forms${
              quotientAtomNote(kernel, current.goal, scope)}`);
          }
          close(line, calc(generic[0]!.proof, matched, symm(generic[1]!.proof)));
          continue;
        }
      }
      const polynomialRefinements = prepareRefinementProver(kernel, current.assumptions, [], visibility);
      if (ring[1]) {
        const local = current.locals.get(ring[1]);
        if (!local) throw new SurfaceError(line.number, `unknown local proof ${ring[1]}`);
        if (local.formula.tag !== "eq") throw new SurfaceError(line.number, "ring at requires an equality hypothesis");
        const generic = normalizeCommutativeRing(kernel, [local.formula.left, local.formula.right],
          current.assumptions, [...current.locals.values()].map(item => item.proof), scope, line.number);
        const left = generic?.[0] ?? normalizeNaturalSemiring(kernel, local.formula.left, line.number, scope, current.assumptions, polynomialRefinements);
        const right = generic?.[1] ?? normalizeNaturalSemiring(kernel, local.formula.right, line.number, scope, current.assumptions, polynomialRefinements);
        current.locals.set(ring[1], {
          formula: eq(left.term, right.term),
          proof: calc(symm(left.proof), local.proof, right.proof),
        });
        continue;
      }
      if (current.goal.tag !== "eq") throw new SurfaceError(line.number, "ring requires an equality goal");
      const goalLeft = normalizeNaturalSemiring(kernel, current.goal.left, line.number, scope, current.assumptions, polynomialRefinements);
      const goalRight = normalizeNaturalSemiring(kernel, current.goal.right, line.number, scope, current.assumptions, polynomialRefinements);
      if (termEquals(goalLeft.term, goalRight.term)) {
        close(line, calc(goalLeft.proof, symm(goalRight.proof)));
        continue;
      }
      const goalVariables = freeFormulaVariables(current.goal);
      let closedFromEquality = false;
      for (const item of current.locals.values()) {
        if (item.formula.tag !== "eq" ||
            ![...freeFormulaVariables(item.formula)].some(variable => goalVariables.has(variable))) continue;
        const factLeft = normalizeNaturalSemiring(kernel, item.formula.left, line.number, scope, current.assumptions, polynomialRefinements);
        const factRight = normalizeNaturalSemiring(kernel, item.formula.right, line.number, scope, current.assumptions, polynomialRefinements);
        if (termEquals(goalLeft.term, factLeft.term) && termEquals(factRight.term, goalRight.term)) {
          close(line, calc(goalLeft.proof, symm(factLeft.proof), item.proof, factRight.proof, symm(goalRight.proof)));
          closedFromEquality = true;
          break;
        }
        if (termEquals(goalLeft.term, factRight.term) && termEquals(factLeft.term, goalRight.term)) {
          close(line, calc(goalLeft.proof, symm(factRight.proof), symm(item.proof), factLeft.proof, symm(goalRight.proof)));
          closedFromEquality = true;
          break;
        }
      }
      if (closedFromEquality) continue;
      const relevantEqualities: Proof[] = [];
      for (const item of current.locals.values()) {
        if (item.formula.tag === "eq" && !termEquals(item.formula.left, item.formula.right) &&
            [...freeFormulaVariables(item.formula)].some(variable => goalVariables.has(variable))) {
          relevantEqualities.push(item.proof);
        }
      }
      close(line, settle(kernel, current.goal, {
        using: preparedRingRules(kernel, line.number, scope), assumptions: current.assumptions, visibility,
        facts: relevantEqualities, useContextEqualities: false, fuel: 50_000,
      }));
      continue;
    }
    // arith on ⊥ refutes the local comparisons: it proves 0 < 0 from them
    // and closes with irreflexivity.
    // `arith` on a disequality introduces it and refutes; on a conjunction it
    // splits and settles each conjunct, so a list of index inequalities is
    // one line.
    if (command === "arith" && (current.goal.tag === "and" || (current.goal.tag === "imp" && current.goal.right.tag === "bottom"))) {
      const script = current.goal.tag === "and"
        ? ["constructor", ". arith", ". arith"]
        : ["intro __arithNegated", "arith"];
      const scriptLines = script.map(text => ({ number: line.number, text, indent: line.indent + 2 })).flatMap(splitTacticLine);
      const nested = elaborateTacticTheorem(kernel, "", [], [], [], current.goal, scriptLines, scope,
        { assumptions: current.assumptions, locals: current.locals, variables: current.variables })!;
      close(line, nested.proof);
      continue;
    }
    // On any other goal, arith first tries the goal itself and then, when
    // that fails, refutes the hypotheses: contradictory bounds close any goal.
    if (command === "arith" && current.goal.tag !== "bottom") {
      const attempt = (script: readonly string[]): Proof => elaborateTacticTheorem(kernel, "", [], [], [], current.goal,
        script.map(text => ({ number: line.number, text, indent: line.indent + 2 })).flatMap(splitTacticLine), scope,
        { assumptions: current.assumptions, locals: current.locals, variables: current.variables })!.proof;
      let direct: unknown;
      try { close(line, attempt(["__arith_direct"])); continue; }
      catch (error) { if (!(error instanceof SurfaceError)) throw error; direct = error; }
      try { close(line, attempt(["exfalso", "arith"])); continue; }
      catch (error) { if (!(error instanceof SurfaceError)) throw error; throw direct; }
    }
    if (command === "arith" && current.goal.tag === "bottom") {
      if (!resolveOptional("Less.irreflexive", scope, candidate => kernel.theorems.has(candidate))) {
        throw new SurfaceError(line.number, "arith on a ⊥ goal needs Less.irreflexive; import Grace.Cumulus.Nat.Order");
      }
      const scriptLines = [
        { number: line.number, text: "have __arithRefuted : 0 < 0 by arith", indent: line.indent + 2 },
        { number: line.number, text: "exact Less.irreflexive at 0 with *, __arithRefuted", indent: line.indent + 2 },
      ].flatMap(splitTacticLine);
      const nested = elaborateTacticTheorem(kernel, "", [], [], [], current.goal, scriptLines, scope,
        { assumptions: current.assumptions, locals: current.locals, variables: current.variables })!;
      close(line, nested.proof);
      continue;
    }
    if (command === "arith" || command === "__arith_direct" || command === "linarith") {
      const refinementFacts = [...current.locals.values()]
        .filter(item => item.formula.tag === "pred" || item.formula.tag === "and")
        .map(item => item.proof);
      const refinements = prepareRefinementProver(kernel, current.assumptions, refinementFacts, visibility);
      // Real linear arithmetic: Fourier-Motzkin elimination over the local
      // comparisons, emitted as a certificate of checked order laws and one
      // ring identity. Falls through to the other presentations when the
      // goal is not a real comparison or the facts do not entail it linearly.
      if (command === "linarith") {
        const realPredicate = resolveOptional("Real", scope, candidate => kernel.predicates.has(candidate));
        const lessName = resolveOptional("realLess", scope, candidate => kernel.functions.has(candidate));
        const leName = resolveOptional("realLe", scope, candidate => kernel.functions.has(candidate));
        if (realPredicate && lessName && leName) {
          const symbol = (name: string): string | undefined =>
            resolveOptional(name, scope, candidate => kernel.functions.has(candidate));
          const extraAssumptions: Formula[] = [];
          const activeAssumptions = (): Formula[] => [...current.assumptions, ...extraAssumptions];
          const dischargeReal = (proof: Proof): Proof | undefined => {
            let result = proof;
            while (true) {
              const formula = kernel.checkProof(result, activeAssumptions());
              if (formula.tag !== "imp" || formula.left.tag !== "pred" || formula.left.args.length !== 1 ||
                  !formula.left.pred.endsWith(".Real")) return result;
              const evidence = refinements.prove(formula.left.args[0]!, formula.left.pred);
              if (!evidence) return undefined;
              result = impElim(result, evidence);
            }
          };
          const rule = (name: string, terms: readonly Term[], premises: readonly Proof[]): Proof | undefined => {
            const resolved = resolveOptional(name, scope, candidate => kernel.theorems.has(candidate));
            if (!resolved) return undefined;
            try {
              let proof: Proof | undefined = at(theorem(resolved), ...terms);
              for (const premise of premises) {
                proof = dischargeReal(proof);
                if (!proof) return undefined;
                proof = impElim(proof, premise);
              }
              return dischargeReal(proof);
            } catch { return undefined; }
          };
          const localProofs = [...current.locals.values()].map(item => item.proof);
          const session = (terms: readonly Term[]): ReturnType<typeof prepareCommutativeRing> => {
            try { return prepareCommutativeRing(kernel, terms, current.assumptions, localProofs, scope, line.number); }
            catch { return undefined; }
          };
          const realAddName = symbol("realAdd");
          const realNegName = symbol("realNeg");
          const realZeroName = symbol("realZero");
          const realOneName = symbol("realOne");
          const realMulName = symbol("realMul");
          const realDivName = symbol("realDiv");
          const realInvName = symbol("realInvValue");
          const call2Name = symbol("call2") ?? [...kernel.functions.keys()].find(candidate => candidate.endsWith(".Algebra.call2"));
          const realNumeral = (term: Term): bigint | undefined => {
            const template = (visibleInfixNotationGroups(kernel, scope, line.number, "function", "numeral").get("_") ?? [])
              .find(item => item.operandType === realPredicate);
            if (template && term.tag === "app" && term.fn === template.target) {
              const leading = template.leadingArguments ?? [];
              if (term.args.length === leading.length + 1 && leading.every((arg, i) => termEquals(arg, term.args[i]!))) {
                const value = naturalValue(term.args.at(-1)!);
                if (value !== undefined) return value;
              }
            }
            return realAddName && realZeroName && realOneName
              ? ringNumeralValue(term, { add: app(realAddName), zero: app(realZeroName), one: app(realOneName) })
              : undefined;
          };
          const ringEquality = (left: Term, right: Term): Proof | undefined => {
            const ring = session([left, right]);
            if (!ring) return undefined;
            try {
              const normalized = ring.normalize([left, right]);
              if (!normalized || !termEquals(normalized[0]!.term, normalized[1]!.term)) return undefined;
              return calc(normalized[0]!.proof, symm(normalized[1]!.proof));
            } catch { return undefined; }
          };
          // t / k for a numeral k ≠ 0: t = k * (t / k), from t / k = t * inv(k)
          // (realDiv.eq_mul_inv) and k * inv(k) = 1 (realInvValue.mul_right
          // under k ≠ 0, which 0 < k gives through irreflexivity), with the
          // ring normalizer rearranging the products.
          const quotient = realDivName && realInvName && realMulName && realZeroName && realOneName && call2Name ? {
            parse: (term: Term) => {
              if (term.tag !== "app" || term.fn !== call2Name || term.args.length !== 3 ||
                  !termEquals(term.args[0]!, app(realDivName))) return undefined;
              const value = realNumeral(term.args[2]!);
              return value !== undefined && value !== 0n ? { numerator: term.args[1]!, divisor: term.args[2]! } : undefined;
            },
            identity: (numerator: Term, divisor: Term, quotientTerm: Term, positive: Proof): Proof | undefined => {
              const zero = app(realZeroName);
              const times = (a: Term, b: Term): Term => app(call2Name, app(realMulName), a, b);
              const trace = (message: string): undefined => {
                if (typeof process !== "undefined" && process.env?.G17_LINARITH_DEBUG) console.error(`[linarith] quotient: ${message}`);
                return undefined;
              };
              const unfolded = rule("realDiv.eq_mul_inv", [numerator, divisor], []);
              if (!unfolded) return trace("realDiv.eq_mul_inv");
              const equalZero = eq(divisor, zero);
              let variable = "__linarithDivisor";
              while (freeTermVariables(divisor).has(variable)) variable += "_";
              const atZero = eqElim(assume(equalZero), variable, pred("relates", app(lessName), zero, v(variable)), positive);
              // k = 0 is assumed while 0 < 0 is derived from it, and discharged.
              extraAssumptions.push(equalZero);
              const absurd = rule("realLess.not_self", [zero], [atZero]);
              const inverse = absurd && rule("realInvValue.mul_right", [divisor], [impIntro(equalZero, absurd)]);
              extraAssumptions.splice(extraAssumptions.lastIndexOf(equalZero), 1);
              if (!absurd) return trace("realLess.not_self");
              if (!inverse) return trace("realInvValue.mul_right");
              const inverseTerm = app(realInvName, divisor);
              const scaled = congr(call2Name, refl(app(realMulName)), refl(divisor), unfolded);
              const rearranged = ringEquality(times(divisor, times(numerator, inverseTerm)), times(numerator, times(divisor, inverseTerm)));
              const cancelled = congr(call2Name, refl(app(realMulName)), refl(numerator), inverse);
              const unit = ringEquality(times(numerator, app(realOneName)), numerator);
              if (!rearranged) return trace("rearrangement");
              if (!unit) return trace("unit");
              try {
                const proof = symm(calc(scaled, rearranged, cancelled, unit));
                const actual = kernel.checkProof(proof, activeAssumptions());
                return formulaEquals(actual, eq(numerator, times(divisor, quotientTerm))) ? proof
                  : trace(`proves ${formatFormula(actual)}`);
              } catch (error) { return trace(error instanceof Error ? error.message : String(error)); }
            },
          } : undefined;
          const realProof = proveRealLinearArithmetic({
            goal: current.goal,
            facts: [...current.locals.values()].map(item => ({ formula: item.formula, proof: item.proof })),
            symbols: { add: symbol("realAddValue"), sub: symbol("realSubValue"), neg: symbol("realNegValue"),
              zero: symbol("realZero"), one: symbol("realOne"),
              call2: symbol("call2") ?? [...kernel.functions.keys()].find(candidate => candidate.endsWith(".Algebra.call2")),
              addGraph: realAddName ? app(realAddName) : undefined,
              negGraph: realNegName ? app(realNegName) : undefined,
              mul: symbol("realMulValue"), mulGraph: realMulName ? app(realMulName) : undefined },
            // A numeral k of ℝ is k ones: the real numeral function declared by
            // a numeral template, or the ring embedding ringNat itself.
            numeral: term => {
              const template = (visibleInfixNotationGroups(kernel, scope, line.number, "function", "numeral").get("_") ?? [])
                .find(item => item.operandType === realPredicate);
              if (template && term.tag === "app" && term.fn === template.target) {
                const leading = template.leadingArguments ?? [];
                if (term.args.length === leading.length + 1 && leading.every((arg, i) => termEquals(arg, term.args[i]!))) {
                  const value = naturalValue(term.args.at(-1)!);
                  if (value !== undefined) return value;
                }
              }
              return realAddName && realZeroName && realOneName
                ? ringNumeralValue(term, { add: app(realAddName), zero: app(realZeroName), one: app(realOneName) })
                : undefined;
            },
            graphs: { less: app(lessName), le: app(leName) },
            rule,
            theoremFact: name => {
              const resolved = resolveOptional(name, scope, candidate => kernel.theorems.has(candidate));
              return resolved ? theorem(resolved) : undefined;
            },
            isReal: term => refinements.prove(term, realPredicate) !== undefined,
            ringEquality,
            quotient,
            check: proof => kernel.checkProof(proof, activeAssumptions()),
            extraAssumptions,
          });
          if (realProof) { close(line, realProof); continue; }
        }
      }
      // Rational linear arithmetic: the same elimination over the strict
      // rational order, with equalities as the non-strict comparisons and
      // trichotomy settling comparison and equality goals.
      if (command === "linarith") {
        const rationalPredicate = resolveOptional("Rational", scope, candidate => kernel.predicates.has(candidate));
        const lessName = resolveOptional("rationalLess", scope, candidate => kernel.functions.has(candidate));
        const trichotomyName = resolveOptional("rationalLess.trichotomy", scope, candidate => kernel.theorems.has(candidate));
        if (rationalPredicate && lessName && trichotomyName) {
          const symbol = (name: string): string | undefined =>
            resolveOptional(name, scope, candidate => kernel.functions.has(candidate));
          const extraAssumptions: Formula[] = [];
          const activeAssumptions = (): Formula[] => [...current.assumptions, ...extraAssumptions];
          const dischargeRational = (proof: Proof): Proof | undefined => {
            let result = proof;
            while (true) {
              const formula = kernel.checkProof(result, activeAssumptions());
              if (formula.tag !== "imp" || formula.left.tag !== "pred" || formula.left.args.length !== 1 ||
                  formula.left.pred !== rationalPredicate) return result;
              const evidence = refinements.prove(formula.left.args[0]!, formula.left.pred);
              if (!evidence) return undefined;
              result = impElim(result, evidence);
            }
          };
          const lemma = (name: string, terms: readonly Term[], premises: readonly Proof[]): Proof | undefined => {
            const resolved = resolveOptional(name, scope, candidate => kernel.theorems.has(candidate));
            if (!resolved) return undefined;
            try {
              let proof: Proof | undefined = at(theorem(resolved), ...terms);
              for (const premise of premises) {
                proof = dischargeRational(proof);
                if (!proof) return undefined;
                proof = impElim(proof, premise);
              }
              return dischargeRational(proof);
            } catch { return undefined; }
          };
          const localProofs = [...current.locals.values()].map(item => item.proof);
          const session = (terms: readonly Term[]): ReturnType<typeof prepareCommutativeRing> => {
            try { return prepareCommutativeRing(kernel, terms, current.assumptions, localProofs, scope, line.number); }
            catch { return undefined; }
          };
          const addName = symbol("rationalAdd");
          const negName = symbol("rationalNeg");
          const rationalProof = proveRationalLinearArithmetic({
            goal: current.goal,
            facts: [...current.locals.values()].map(item => ({ formula: item.formula, proof: item.proof })),
            symbols: { add: symbol("rationalAddValue"), sub: symbol("rationalSubValue"), neg: symbol("rationalNegValue"),
              zero: symbol("rationalZero"), one: symbol("rationalOne"),
              call2: symbol("call2") ?? [...kernel.functions.keys()].find(candidate => candidate.endsWith(".Algebra.call2")),
              addGraph: addName ? app(addName) : undefined,
              negGraph: negName ? app(negName) : undefined },
            less: app(lessName),
            lemma,
            theoremFact: name => {
              const resolved = resolveOptional(name, scope, candidate => kernel.theorems.has(candidate));
              return resolved ? theorem(resolved) : undefined;
            },
            isRational: term => refinements.prove(term, rationalPredicate) !== undefined,
            ringEquality: (left, right) => {
              const ring = session([left, right]);
              if (!ring) return undefined;
              try {
                const normalized = ring.normalize([left, right]);
                if (!normalized || !termEquals(normalized[0]!.term, normalized[1]!.term)) return undefined;
                return calc(normalized[0]!.proof, symm(normalized[1]!.proof));
              } catch { return undefined; }
            },
            check: proof => kernel.checkProof(proof, activeAssumptions()),
            extraAssumptions,
          });
          if (rationalProof) { close(line, rationalProof); continue; }
          const rationalGoal = current.goal.tag === "imp" && current.goal.right.tag === "bottom"
            ? current.goal.left : current.goal;
          if (rationalGoal.tag === "pred" && rationalGoal.pred === "relates" && rationalGoal.args.length === 3 &&
              termEquals(rationalGoal.args[0]!, app(lessName))) {
            throw new SurfaceError(line.number, "linarith found no checked rational-order derivation");
          }
        }
      }
      // An ordered ring's affine reasoning uses only its additive ordered
      // group. Resolve that checked interface from the visible instances (or
      // a local structure hypothesis), with no carrier names baked in.
      if (command === "linarith" && current.goal.tag === "pred" &&
          current.goal.pred === "relates" && current.goal.args.length === 3) {
        const className = resolveOptional("OrderedAdditiveGroup", scope, candidate => kernel.predicates.has(candidate));
        if (className) {
          const instanceProver = prepareInstanceProver(kernel, visibleInstanceNames(kernel, scope),
            current.assumptions, [], {}, visibility);
          const synthesis = instanceProver.resolve(className,
            [undefined, undefined, undefined, undefined, current.goal.args[0]!]);
          let structureProof = synthesis?.proof;
          if (!structureProof) {
            const ringName = resolveOptional("OrderedRing", scope, candidate => kernel.predicates.has(candidate));
            const projection = resolveOptional("OrderedRing.additive", scope,
              candidate => kernel.theorems.has(candidate));
            if (ringName && projection) {
              const ring = instanceProver.resolve(ringName,
                [undefined, undefined, undefined, undefined, undefined, undefined, current.goal.args[0]!]);
              if (ring) {
                const formula = kernel.checkProof(ring.proof, current.assumptions);
                if (formula.tag === "pred" && formula.args.length === 7) {
                  structureProof = impElim(at(theorem(projection), ...formula.args), ring.proof);
                }
              }
            }
          }
          if (structureProof) {
            const witness = kernel.checkProof(structureProof, current.assumptions);
            if (witness.tag !== "pred" || witness.args.length !== 5) throw new SurfaceError(line.number,
              "ordered additive instance returned a malformed certificate");
            const [carrier, add, zero, neg, relation] = witness.args;
            const memberCache = new Map<string, Proof | undefined>();
            const membership = (term: Term): Proof | undefined => {
              const key = termCanonical(term);
              if (memberCache.has(key)) return memberCache.get(key);
              const derive = (): Proof | undefined => {
              const goal = pred("in", term, carrier!);
              const local = [...current.locals.values()].find(item => formulaEquals(item.formula, goal));
              if (local) return local.proof;
              const assumed = current.assumptions.find(item => formulaEquals(item, goal));
              if (assumed) return assume(assumed);
              if (term.tag === "app" && term.fn === "apply" &&
                  term.args.length === 2 && termEquals(term.args[0]!, neg!)) {
                const input = membership(term.args[1]!);
                const law = resolveOptional("OrderedAdditiveGroup.neg_closed", scope,
                  candidate => kernel.theorems.has(candidate));
                if (input && law) return impElim(impElim(
                  at(theorem(law), carrier!, add!, zero!, neg!, relation!, term.args[1]!),
                  structureProof), input);
              }
              if (term.tag === "app" && term.fn.endsWith(".Algebra.call2") &&
                  term.args.length === 3 && termEquals(term.args[0]!, add!)) {
                const left = membership(term.args[1]!);
                const right = membership(term.args[2]!);
                const law = resolveOptional("OrderedAdditiveGroup.add_closed", scope,
                  candidate => kernel.theorems.has(candidate));
                if (left && right && law) return impElim(impElim(
                  at(theorem(law), carrier!, add!, zero!, neg!, relation!, term.args[1]!, term.args[2]!),
                  structureProof), andIntro(left, right));
              }
              try {
                return settle(kernel, goal, {
                  using: resolveRules(kernel, ["Real"], line.number, scope),
                  assumptions: current.assumptions, fuel: 100, visibility,
                });
              } catch { return undefined; }
              };
              const result = derive();
              memberCache.set(key, result);
              return result;
            };
            const conjunction = (proofs: readonly Proof[]): Proof =>
              proofs.slice(0, -1).reduceRight<Proof>((tail, proof) => andIntro(proof, tail), proofs.at(-1)!);
            const applyLaw = (name: string, terms: readonly Term[], ordered: readonly Proof[]): Proof | undefined => {
              const law = resolveOptional(`OrderedAdditiveGroup.${name}`, scope,
                candidate => kernel.theorems.has(candidate));
              if (!law) return undefined;
              try {
                let result = at(theorem(law), carrier!, add!, zero!, neg!, relation!, ...terms);
                result = impElim(result, structureProof);
                const formula = kernel.checkProof(result, current.assumptions);
                if (formula.tag === "imp" && formula.left.tag === "pred" && formula.left.pred === "in") {
                  const proof = membership(formula.left.args[0]!);
                  if (!proof) return undefined;
                  result = impElim(result, proof);
                } else if (formula.tag === "imp" && formula.left.tag === "and") {
                  const members = terms.map(membership);
                  if (members.some(proof => !proof)) return undefined;
                  result = impElim(result, conjunction(members as Proof[]));
                }
                for (const proof of ordered) result = impElim(result, proof);
                return result;
              } catch { return undefined; }
            };
            const goalLeft = current.goal.args[1]!;
            const goalRight = current.goal.args[2]!;
            const locals = [...current.locals.values()].filter(item => item.formula.tag === "pred" &&
              item.formula.pred === "relates" && termEquals(item.formula.args[0]!, relation!));
            const sameGoal = (proof: Proof | undefined): Proof | undefined =>
              proof && formulaEquals(kernel.checkProof(proof, current.assumptions), current.goal) ? proof : undefined;
            let genericProof: Proof | undefined;
            if (termEquals(goalLeft, goalRight)) genericProof = sameGoal(applyLaw("reflexive", [goalLeft], []));
            const sum = (term: Term): readonly [Term, Term] | undefined =>
              term.tag === "app" && term.fn.endsWith(".Algebra.call2") &&
              term.args.length === 3 && termEquals(term.args[0]!, add!)
                ? [term.args[1]!, term.args[2]!] : undefined;
            const opposite = (term: Term): Term | undefined =>
              term.tag === "app" && term.fn === "apply" &&
              term.args.length === 2 && termEquals(term.args[0]!, neg!)
                ? term.args[1]! : undefined;
            for (const local of locals.slice(0, 16)) {
              if (genericProof) break;
              if (formulaEquals(local.formula, current.goal)) { genericProof = local.proof; break; }
              const formula = local.formula;
              if (formula.tag !== "pred") continue;
              const x = formula.args[1]!;
              const y = formula.args[2]!;
              if (termEquals(opposite(goalLeft) ?? goalLeft, y) &&
                  termEquals(opposite(goalRight) ?? goalRight, x) &&
                  opposite(goalLeft) && opposite(goalRight)) {
                genericProof = sameGoal(applyLaw("neg_reverse", [x, y], [local.proof]));
              }
              for (const later of locals.slice(0, 16)) {
                if (genericProof || later.formula.tag !== "pred") continue;
                const z = later.formula.args[1]!;
                const w = later.formula.args[2]!;
                if (termEquals(y, z) && termEquals(x, goalLeft) && termEquals(w, goalRight)) {
                  genericProof = sameGoal(applyLaw("transitive", [x, y, w], [local.proof, later.proof]));
                }
                const leftParts = sum(goalLeft);
                const rightParts = sum(goalRight);
                if (leftParts && rightParts && termEquals(leftParts[0], x) &&
                    termEquals(rightParts[0], y) && termEquals(leftParts[1], z) &&
                    termEquals(rightParts[1], w)) {
                  genericProof = sameGoal(applyLaw("add", [x, y, z, w], [local.proof, later.proof]));
                }
                if (leftParts && rightParts && termEquals(leftParts[0], x) &&
                    termEquals(rightParts[0], y) && termEquals(opposite(leftParts[1]) ?? leftParts[1], w) &&
                    termEquals(opposite(rightParts[1]) ?? rightParts[1], z) &&
                    opposite(leftParts[1]) && opposite(rightParts[1])) {
                  const reversed = applyLaw("neg_reverse", [z, w], [later.proof]);
                  if (reversed) genericProof = sameGoal(applyLaw("add", [x, y,
                    leftParts[1], rightParts[1]], [local.proof, reversed]));
                }
              }
              if (genericProof) break;
              if (termEquals(goalLeft, zero!) && goalRight.tag === "app" &&
                  goalRight.fn.endsWith(".Algebra.call2") && termEquals(goalRight.args[0]!, add!) &&
                  termEquals(goalRight.args[1]!, y) && goalRight.args[2]?.tag === "app" &&
                  goalRight.args[2].fn === "apply" &&
                  termEquals(goalRight.args[2].args[0]!, neg!) &&
                  termEquals(goalRight.args[2].args[1]!, x)) {
                genericProof = sameGoal(applyLaw("nonnegative_sub", [x, y], [local.proof]));
              }
              const leftSum = goalLeft.tag === "app" && goalLeft.fn.endsWith(".Algebra.call2") &&
                termEquals(goalLeft.args[0]!, add!) ? goalLeft.args : undefined;
              const rightSum = goalRight.tag === "app" && goalRight.fn.endsWith(".Algebra.call2") &&
                termEquals(goalRight.args[0]!, add!) ? goalRight.args : undefined;
              if (!genericProof && leftSum && rightSum && termEquals(leftSum[1]!, x) &&
                  termEquals(rightSum[1]!, y) && termEquals(leftSum[2]!, rightSum[2]!)) {
                const z = leftSum[2]!;
                const reflexive = applyLaw("reflexive", [z], []);
                if (reflexive) genericProof = sameGoal(applyLaw("add", [x, y, z, z], [local.proof, reflexive]));
              }
              if (genericProof) break;
            }
            if (!genericProof && locals.length > 0) {
              type AffineForm = Map<string, bigint>;
              const atomTerms = new Map<string, Term>();
              const affine = (term: Term): AffineForm => {
                if (termEquals(term, zero!)) return new Map();
                const parts = sum(term);
                const negated = opposite(term);
                if (parts || negated) {
                  const result = new Map<string, bigint>();
                  const merge = (source: AffineForm, sign: bigint): void => {
                    for (const [key, value] of source) {
                      const next = (result.get(key) ?? 0n) + sign * value;
                      if (next === 0n) result.delete(key); else result.set(key, next);
                    }
                  };
                  if (parts) { merge(affine(parts[0]), 1n); merge(affine(parts[1]), 1n); }
                  else merge(affine(negated!), -1n);
                  return result;
                }
                const key = termCanonical(term);
                atomTerms.set(key, term);
                return new Map([[key, 1n]]);
              };
              const combineForms = (left: AffineForm, right: AffineForm, sign = 1n): AffineForm => {
                const result = new Map(left);
                for (const [key, value] of right) {
                  const next = (result.get(key) ?? 0n) + sign * value;
                  if (next === 0n) result.delete(key); else result.set(key, next);
                }
                return result;
              };
              const formKey = (form: AffineForm): string => [...form].sort(([a], [b]) => a.localeCompare(b))
                .map(([key, value]) => `${key}:${value}`).join("|");
              const sameAffine = (left: Term, right: Term): boolean => {
                const a = affine(left);
                const b = affine(right);
                return a.size === b.size && [...a].every(([key, value]) => b.get(key) === value);
              };
              const addFunction = [...kernel.functions.keys()].find(name => name.endsWith(".Algebra.call2"));
              const negFunction = "apply";
              const addTerm = (left: Term, right: Term): Term => app(addFunction!, add!, left, right);
              const negTerm = (term: Term): Term => app(negFunction!, neg!, term);
              const equation = (name: string, terms: readonly Term[], left: Term, right: Term): Proof | undefined => {
                const proof = applyLaw(name, terms, []);
                if (!proof) return undefined;
                const formula = kernel.checkProof(proof, current.assumptions);
                if (formulaEquals(formula, eq(left, right))) return proof;
                if (formulaEquals(formula, eq(right, left))) return symm(proof);
                return undefined;
              };
              const neighbors = (term: Term, depth: number): Array<{ term: Term; proof: Proof }> => {
                if (depth > 5) return [];
                const result: Array<{ term: Term; proof: Proof }> = [];
                const push = (target: Term, proof: Proof | undefined): void => {
                  if (proof && !termEquals(term, target)) result.push({ term: target, proof });
                };
                const parts = sum(term);
                if (parts) {
                  const [x, y] = parts;
                  push(addTerm(y, x), equation("add_comm", [x, y], term, addTerm(y, x)));
                  if (termEquals(x, zero!)) push(y, equation("zero_left", [y], term, y));
                  if (termEquals(y, zero!)) push(x, equation("zero_right", [x], term, x));
                  if (termEquals(opposite(y) ?? y, x) && opposite(y))
                    push(zero!, equation("add_neg", [x], term, zero!));
                  if (termEquals(opposite(x) ?? x, y) && opposite(x))
                    push(zero!, equation("neg_add", [y], term, zero!));
                  const lhs = sum(x);
                  if (lhs) {
                    const [a, b] = lhs;
                    const target = addTerm(a, addTerm(b, y));
                    push(target, equation("add_assoc", [a, b, y], term, target));
                    if (opposite(y) && termEquals(opposite(y)!, a))
                      push(b, equation("add_cancel_left", [a, b], term, b));
                  }
                  const rhs = sum(y);
                  if (rhs) {
                    const [b, c] = rhs;
                    const target = addTerm(addTerm(x, b), c);
                    push(target, equation("add_assoc", [x, b, c], term, target));
                    const exchanged = addTerm(b, addTerm(x, c));
                    push(exchanged, equation("add_swap", [x, b, c], term, exchanged));
                  }
                  for (const child of neighbors(x, depth + 1))
                    push(addTerm(child.term, y), congr(addFunction!, refl(add!), child.proof, refl(y)));
                  for (const child of neighbors(y, depth + 1))
                    push(addTerm(x, child.term), congr(addFunction!, refl(add!), refl(x), child.proof));
                }
                const inner = opposite(term);
                if (inner) {
                  const doubled = opposite(inner);
                  if (doubled) push(doubled, equation("neg_neg", [doubled], term, doubled));
                  for (const child of neighbors(inner, depth + 1))
                    push(negTerm(child.term), congr(negFunction!, refl(neg!), child.proof));
                }
                return result;
              };
              interface AdditiveNormal { readonly leaves: readonly Term[]; readonly term: Term; readonly proof: Proof }
              const additiveTerm = (leaves: readonly Term[]): Term => leaves.slice(0, -1)
                .reduceRight<Term>((tail, head) => addTerm(head, tail), leaves.at(-1)!);
              const appendAdditive = (left: readonly Term[], right: readonly Term[]): Proof => {
                if (left.length === 1) return refl(addTerm(left[0]!, additiveTerm(right)));
                const head = left[0]!;
                const tail = additiveTerm(left.slice(1));
                const end = additiveTerm(right);
                const associated = equation("add_assoc", [head, tail, end],
                  addTerm(addTerm(head, tail), end), addTerm(head, addTerm(tail, end)));
                if (!associated) throw new Error("ordered additive association certificate unavailable");
                return calc(associated, congr(addFunction!, refl(add!), refl(head),
                  appendAdditive(left.slice(1), right)));
              };
              const swapAdditive = (leaves: readonly Term[], index: number): Proof => {
                if (index > 0) return congr(addFunction!, refl(add!), refl(leaves[0]!),
                  swapAdditive(leaves.slice(1), index - 1));
                const [first, second] = leaves;
                const target = [second!, first!, ...leaves.slice(2)];
                const rule = leaves.length === 2
                  ? equation("add_comm", [first!, second!], additiveTerm(leaves), additiveTerm(target))
                  : equation("add_swap", [first!, second!, additiveTerm(leaves.slice(2))],
                    additiveTerm(leaves), additiveTerm(target));
                if (!rule) throw new Error("ordered additive exchange certificate unavailable");
                return rule;
              };
              const additiveOrder = (term: Term): string => {
                const inner = opposite(term);
                return `${termCanonical(inner ?? term)}:${inner ? "1" : "0"}`;
              };
              const reduceAdditive = (leaves: readonly Term[], index: number,
                  law: Proof): Proof => {
                if (index > 0) return congr(addFunction!, refl(add!), refl(leaves[0]!),
                  reduceAdditive(leaves.slice(1), index - 1, law));
                if (leaves.length === 2) return law;
                const rest = additiveTerm(leaves.slice(2));
                const pair = addTerm(leaves[0]!, leaves[1]!);
                const associated = symm(equation("add_assoc", [leaves[0]!, leaves[1]!, rest],
                  addTerm(pair, rest), additiveTerm(leaves))!);
                const reduced = calc(associated,
                  congr(addFunction!, refl(add!), law, refl(rest)));
                return calc(reduced, equation("zero_left", [rest], addTerm(zero!, rest), rest)!);
              };
              const flattenAdditive = (term: Term): AdditiveNormal => {
                const parts = sum(term);
                if (!parts) return { leaves: [term], term, proof: refl(term) };
                const left = flattenAdditive(parts[0]);
                const right = flattenAdditive(parts[1]);
                const leaves = [...left.leaves, ...right.leaves];
                const proof = calc(congr(addFunction!, refl(add!), left.proof, right.proof),
                  appendAdditive(left.leaves, right.leaves));
                return { leaves, term: additiveTerm(leaves), proof };
              };
              const normalizeAdditive = (term: Term): AdditiveNormal => {
                const flat = flattenAdditive(term);
                const leaves = [...flat.leaves];
                let proof = flat.proof;
                const keys = leaves.map(additiveOrder);
                for (let target = 0; target < leaves.length; target += 1) {
                  let selected = target;
                  for (let candidate = target + 1; candidate < leaves.length; candidate += 1)
                    if (keys[candidate]! < keys[selected]!) selected = candidate;
                  while (selected > target) {
                    proof = calc(proof, swapAdditive(leaves, selected - 1));
                    [leaves[selected - 1], leaves[selected]] = [leaves[selected]!, leaves[selected - 1]!];
                    [keys[selected - 1], keys[selected]] = [keys[selected]!, keys[selected - 1]!];
                    selected -= 1;
                  }
                }
                for (let index = 0; index < leaves.length;) {
                  const first = leaves[index]!;
                  const next = leaves[index + 1];
                  const atom = opposite(first) ?? first;
                  const cancel = next && (termEquals(next, negTerm(atom)) && termEquals(first, atom)
                    ? equation("add_neg", [atom], addTerm(first, next), zero!)
                    : termEquals(first, negTerm(atom)) && termEquals(next, atom)
                      ? equation("neg_add", [atom], addTerm(first, next), zero!) : undefined);
                  if (cancel) {
                    proof = calc(proof, reduceAdditive(leaves, index, cancel));
                    if (index > 0 && index + 2 === leaves.length) {
                      const prefix = additiveTerm(leaves.slice(0, index));
                      const withoutZero = equation("zero_right", [prefix],
                        addTerm(prefix, zero!), prefix);
                      // The prefix is right associated, so move its final
                      // zero to the outer level before removing it.
                      if (index === 1 && withoutZero) proof = calc(proof, withoutZero);
                      else if (index > 1) {
                        const removeLast = (items: readonly Term[]): Proof => {
                          if (items.length === 1) return equation("zero_right", [items[0]!],
                            addTerm(items[0]!, zero!), items[0]!)!;
                          return congr(addFunction!, refl(add!), refl(items[0]!),
                            removeLast(items.slice(1)));
                        };
                        proof = calc(proof, removeLast(leaves.slice(0, index)));
                      }
                    }
                    leaves.splice(index, 2);
                    if (leaves.length === 0) leaves.push(zero!);
                    continue;
                  }
                  index += 1;
                }
                return { leaves, term: additiveTerm(leaves), proof };
              };
              const proveEquality = (left: Term, right: Term): Proof | undefined => {
                if (termEquals(left, right)) return refl(left);
                if (!sameAffine(left, right) || !addFunction || !negFunction) return undefined;
                try {
                  const normalLeft = normalizeAdditive(left);
                  const normalRight = normalizeAdditive(right);
                  if (termEquals(normalLeft.term, normalRight.term))
                    return calc(normalLeft.proof, symm(normalRight.proof));
                } catch { /* Signed cancellation may still need local rewriting. */ }
                const queue: Array<{ term: Term; proof: Proof; depth: number }> = [
                  { term: left, proof: refl(left), depth: 0 },
                ];
                const visited = new Set([termCanonical(left)]);
                for (let index = 0; index < queue.length && queue.length < 512; index += 1) {
                  const item = queue[index]!;
                  if (item.depth >= 8) continue;
                  for (const next of neighbors(item.term, 0)) {
                    const key = termCanonical(next.term);
                    if (visited.has(key)) continue;
                    const proof = calc(item.proof, next.proof);
                    if (termEquals(next.term, right)) return proof;
                    visited.add(key);
                    queue.push({ term: next.term, proof, depth: item.depth + 1 });
                    if (queue.length >= 512) break;
                  }
                }
                return undefined;
              };
              const align = (candidate: Proof): Proof | undefined => {
                const formula = kernel.checkProof(candidate, current.assumptions);
                if (formula.tag !== "pred" || formula.pred !== "relates" ||
                    !termEquals(formula.args[0]!, relation!)) return undefined;
                const left = formula.args[1]!;
                const right = formula.args[2]!;
                if (!sameAffine(left, goalLeft) || !sameAffine(right, goalRight)) return undefined;
                const leftEquality = proveEquality(left, goalLeft);
                const rightEquality = proveEquality(right, goalRight);
                if (!leftEquality || !rightEquality) return undefined;
                let variable = "__orderedAffine";
                const forbidden = new Set([...freeTermVariables(left), ...freeTermVariables(right),
                  ...freeTermVariables(goalLeft), ...freeTermVariables(goalRight)]);
                while (forbidden.has(variable)) variable += "_";
                const replacedLeft = eqElim(leftEquality, variable,
                  pred("relates", relation!, v(variable), right), candidate);
                const replacedRight = eqElim(rightEquality, variable,
                  pred("relates", relation!, goalLeft, v(variable)), replacedLeft);
                return sameGoal(replacedRight);
              };
              const terms = new Map<string, Term>();
              const collect = (term: Term): void => {
                if (terms.size > 20) return;
                terms.set(termCanonical(term), term);
                const parts = sum(term);
                if (parts) { collect(parts[0]); collect(parts[1]); }
                const inner = opposite(term);
                if (inner) collect(inner);
              };
              collect(goalLeft);
              collect(goalRight);
              const bases: Proof[] = locals.map(item => item.proof);
              // Small goals benefit from immediate two-fact certificates.
              // For larger contexts the directed sparse solver below chooses
              // facts first; eagerly checking every pair is quadratic work.
              if (locals.length <= 2) for (const first of locals) for (const second of locals) {
                if (first.formula.tag !== "pred" || second.formula.tag !== "pred") continue;
                const combined = applyLaw("add", [first.formula.args[1]!, first.formula.args[2]!,
                  second.formula.args[1]!, second.formula.args[2]!], [first.proof, second.proof]);
                if (combined) bases.push(combined);
              }
              for (const base of bases) {
                genericProof = align(base);
                if (genericProof) break;
                const formula = kernel.checkProof(base, current.assumptions);
                if (formula.tag !== "pred") continue;
                for (const shift of terms.values()) {
                  const left = addTerm(formula.args[1]!, shift);
                  const right = addTerm(formula.args[2]!, shift);
                  if (!sameAffine(left, goalLeft) || !sameAffine(right, goalRight)) continue;
                  const reflexive = applyLaw("reflexive", [shift], []);
                  if (!reflexive) continue;
                  const translated = applyLaw("add", [formula.args[1]!, formula.args[2]!, shift, shift],
                    [base, reflexive]);
                  if (translated && (genericProof = align(translated))) break;
                }
                if (genericProof) break;
              }
              if (!genericProof && locals.length > 1) {
                const targetGap = combineForms(affine(goalRight), affine(goalLeft), -1n);
                const localGaps = locals.map(item => item.formula.tag === "pred"
                  ? combineForms(affine(item.formula.args[2]!), affine(item.formula.args[1]!), -1n)
                  : new Map<string, bigint>());
                const factsByAtom = new Map<string, number[]>();
                localGaps.forEach((gap, index) => {
                  for (const atom of gap.keys()) {
                    const facts = factsByAtom.get(atom) ?? [];
                    facts.push(index);
                    factsByAtom.set(atom, facts);
                  }
                });
                interface Combination { readonly indices: readonly number[]; readonly gap: AffineForm }
                const queue: Combination[] = [];
                const visited = new Set<string>();
                for (let index = 0; index < locals.length; index += 1) {
                  const gap = localGaps[index]!;
                  const key = formKey(gap);
                  if (visited.has(key)) continue;
                  visited.add(key);
                  queue.push({ indices: [index], gap });
                }
                const certificate = (indices: readonly number[]): Proof | undefined => {
                  let result = locals[indices[0]!]!.proof;
                  for (const index of indices.slice(1)) {
                    const left = kernel.checkProof(result, current.assumptions);
                    const right = locals[index]!.formula;
                    if (left.tag !== "pred" || right.tag !== "pred") return undefined;
                    const combined = applyLaw("add", [left.args[1]!, left.args[2]!,
                      right.args[1]!, right.args[2]!], [result, locals[index]!.proof]);
                    if (!combined) return undefined;
                    result = combined;
                  }
                  return result;
                };
                const shiftTerm = (form: AffineForm): Term | undefined => {
                  const leaves: Term[] = [];
                  for (const [key, coefficient] of [...form].sort(([a], [b]) => a.localeCompare(b))) {
                    if (coefficient > 16n || coefficient < -16n) return undefined;
                    const atom = atomTerms.get(key);
                    if (!atom) return undefined;
                    const item = coefficient < 0n ? negTerm(atom) : atom;
                    for (let count = 0; count < Number(coefficient < 0n ? -coefficient : coefficient); count += 1)
                      leaves.push(item);
                  }
                  return leaves.length === 0 ? zero! : leaves.slice(1)
                    .reduce<Term>((left, right) => addTerm(left, right), leaves[0]!);
                };
                // Solve the common independent-bound case directly. Choose a
                // remaining coordinate and subtract a bound that moves it
                // toward zero; the breadth-first search below handles cases
                // that require temporary movement away from the target.
                const failed = new Set<string>();
                let directedNodes = 0;
                const directed = (remaining: AffineForm, budget: number,
                    active: Set<string>): readonly number[] | undefined => {
                  if (remaining.size === 0) return [];
                  if (budget === 0 || ++directedNodes > 2048) return undefined;
                  const key = formKey(remaining);
                  if (active.has(key) || failed.has(`${budget}|${key}`)) return undefined;
                  active.add(key);
                  const candidates = [...remaining].map(([atom, value]) => ({
                    atom, value,
                    options: (factsByAtom.get(atom) ?? []).map(index => ({ gap: localGaps[index]!, index }))
                      .filter(({ gap }) => {
                        const contribution = gap.get(atom) ?? 0n;
                        return contribution !== 0n &&
                          (contribution > 0n) === (value > 0n) &&
                          (contribution < 0n ? -contribution : contribution) <=
                          (value < 0n ? -value : value);
                      }),
                  })).sort((a, b) => a.options.length - b.options.length);
                  for (const { options } of candidates) {
                    for (const { gap, index } of options) {
                      const next = combineForms(remaining, gap, -1n);
                      const solution = directed(next, budget - 1, active);
                      if (solution) { active.delete(key); return [index, ...solution]; }
                    }
                    if (options.length === 0) break;
                  }
                  active.delete(key);
                  failed.add(`${budget}|${key}`);
                  return undefined;
                };
                const directIndices = directed(targetGap, 64, new Set());
                if (directIndices?.length) {
                  const base = certificate(directIndices);
                  if (base) {
                    const formula = kernel.checkProof(base, current.assumptions);
                    if (formula.tag === "pred") {
                      const shift = shiftTerm(combineForms(affine(goalLeft), affine(formula.args[1]!), -1n));
                      if (shift && !termEquals(shift, zero!)) {
                        const reflexive = applyLaw("reflexive", [shift], []);
                        const translated = reflexive && applyLaw("add", [formula.args[1]!,
                          formula.args[2]!, shift, shift], [base, reflexive]);
                        if (translated) genericProof = align(translated);
                      } else if (shift) genericProof = align(base);
                    }
                  }
                }
                for (let head = 0; !genericProof && head < queue.length && queue.length < 512; head += 1) {
                  const item = queue[head]!;
                  if (formKey(item.gap) === formKey(targetGap)) {
                    const base = certificate(item.indices);
                    if (base) {
                      const formula = kernel.checkProof(base, current.assumptions);
                      if (formula.tag === "pred") {
                        const shift = shiftTerm(combineForms(affine(goalLeft), affine(formula.args[1]!), -1n));
                        if (shift && !termEquals(shift, zero!)) {
                          const reflexive = applyLaw("reflexive", [shift], []);
                          const translated = reflexive && applyLaw("add", [formula.args[1]!,
                            formula.args[2]!, shift, shift], [base, reflexive]);
                          if (translated) genericProof = align(translated);
                        } else genericProof = align(base);
                      }
                    }
                    if (genericProof) break;
                  }
                  if (item.indices.length >= 12) continue;
                  for (let index = item.indices.at(-1)!; index < locals.length; index += 1) {
                    const gap = combineForms(item.gap, localGaps[index]!);
                    const key = formKey(gap);
                    if (visited.has(key)) continue;
                    visited.add(key);
                    queue.push({ indices: [...item.indices, index], gap });
                    if (queue.length >= 512) break;
                  }
                }
              }
            }
            if (genericProof) { close(line, genericProof); continue; }
            if (relation?.tag === "var" || (relation?.tag === "app" &&
                !relation.fn.endsWith(".realLe") && !relation.fn.endsWith(".realLess"))) {
              throw new SurfaceError(line.number, "linarith found no checked ordered-additive derivation");
            }
          }
        }
      }
      // A bounded real-order slice of linarith: use the checked order laws
      // before entering the Nat-specific affine procedure. Each candidate is
      // instantiated and replayed by the kernel.
      if (command === "linarith" && current.goal.tag === "pred" && current.goal.args.length === 3) {
        const realKind = (formula: Formula): "realLess" | "realLe" | undefined => {
          if (formula.tag !== "pred" || formula.pred !== "relates" || formula.args.length !== 3) return undefined;
          const graph = formula.args[0]!;
          if (graph.tag !== "app" || graph.args.length !== 0) return undefined;
          return graph.fn.endsWith(".realLess") ? "realLess"
            : graph.fn.endsWith(".realLe") ? "realLe" : undefined;
        };
        const goalRealKind = realKind(current.goal);
        if (goalRealKind) {
          const localOrders = [...current.locals.values()].filter(item =>
            realKind(item.formula));
          const rules = [
            { name: "realLess.implies_le", inputs: ["realLess"], output: "realLe" },
            { name: "realLess.transitive", inputs: ["realLess", "realLess"], output: "realLess" },
            { name: "realLe.transitive", inputs: ["realLe", "realLe"], output: "realLe" },
            { name: "realLe.transitive_less", inputs: ["realLe", "realLess"], output: "realLess" },
            { name: "realLess.transitive_le", inputs: ["realLess", "realLe"], output: "realLess" },
            { name: "realLess.add", inputs: ["realLess", "realLess"], output: "realLess" },
            { name: "realLe.add", inputs: ["realLe", "realLe"], output: "realLe" },
          ];
          let realProof: Proof | undefined;
          for (const rule of rules) {
            if (rule.output !== goalRealKind) continue;
            const name = resolveOptional(rule.name, scope, candidate => kernel.theorems.has(candidate));
            if (!name) continue;
            const choices = localOrders.filter(item => realKind(item.formula) === rule.inputs[0]).slice(0, 32);
            const later = rule.inputs.length === 2
              ? localOrders.filter(item => realKind(item.formula) === rule.inputs[1]).slice(0, 32)
              : [];
            for (const first of choices) {
              const candidates = rule.inputs.length === 1 ? [undefined] : later;
              for (const second of candidates) {
                if (first.formula.tag !== "pred" || (second && second.formula.tag !== "pred")) continue;
                const terms = second && second.formula.tag === "pred"
                  ? rule.name.endsWith(".add")
                    ? [first.formula.args[1]!, first.formula.args[2]!,
                      second.formula.args[1]!, second.formula.args[2]!]
                    : [first.formula.args[1]!, first.formula.args[2]!, second.formula.args[2]!]
                  : [first.formula.args[1]!, first.formula.args[2]!];
                try {
                  let proof = at(theorem(name), ...terms);
                  while (true) {
                    const formula = kernel.checkProof(proof, current.assumptions);
                    if (formula.tag !== "imp" || formula.left.tag !== "pred" ||
                        formula.left.args.length !== 1 || !formula.left.pred.endsWith(".Real")) break;
                    const evidence = refinements.prove(formula.left.args[0]!, formula.left.pred);
                    if (!evidence) break;
                    proof = impElim(proof, evidence);
                  }
                  proof = impElim(proof, first.proof);
                  if (second) proof = impElim(proof, second.proof);
                  if (formulaEquals(kernel.checkProof(proof, current.assumptions), current.goal)) {
                    realProof = proof;
                    break;
                  }
                } catch { /* This candidate does not fit the checked goal. */ }
              }
              if (realProof) break;
            }
            if (realProof) break;
          }
          // Prove affine real goals by composing checked order laws. The
          // decomposition follows the expression tree, so subtraction may
          // occur on either side and at any depth. The kernel checks every
          // instantiated law and every intermediate order proof.
          if (!realProof) {
            const binary = (term: Term, suffix: string): readonly [Term, Term] | undefined =>
              term.tag === "app" && term.fn.endsWith(`.${suffix}`) && term.args.length === 2
                ? [term.args[0]!, term.args[1]!]
                : suffix === "realAddValue" && term.tag === "app" && term.fn.endsWith(".Algebra.call2") &&
                  term.args.length === 3 && term.args[0]?.tag === "app" &&
                  term.args[0].fn.endsWith(".realAdd")
                  ? [term.args[1]!, term.args[2]!] : undefined;
            const unary = (term: Term, suffix: string): Term | undefined =>
              term.tag === "app" && term.fn.endsWith(`.${suffix}`) && term.args.length === 1
                ? term.args[0]!
                : suffix === "realNegValue" && term.tag === "app" && term.fn === "apply" &&
                  term.args.length === 2 && term.args[0]?.tag === "app" &&
                  term.args[0].fn.endsWith(".realNeg")
                  ? term.args[1]! : undefined;
            const checkedRule = (name: string, terms: readonly Term[], premises: readonly Proof[]): Proof | undefined => {
              const resolved = resolveOptional(name, scope, candidate => kernel.theorems.has(candidate));
              if (!resolved) return undefined;
              try {
                let proof: Proof = at(theorem(resolved), ...terms);
                for (const premise of premises) {
                  while (true) {
                    const formula = kernel.checkProof(proof, current.assumptions);
                    if (formula.tag !== "imp" || formula.left.tag !== "pred" ||
                        formula.left.args.length !== 1 || !formula.left.pred.endsWith(".Real")) break;
                    const evidence = refinements.prove(formula.left.args[0]!, formula.left.pred);
                    if (!evidence) return undefined;
                    proof = impElim(proof, evidence);
                  }
                  proof = impElim(proof, premise);
                }
                while (true) {
                  const formula = kernel.checkProof(proof, current.assumptions);
                  if (formula.tag !== "imp" || formula.left.tag !== "pred" ||
                      formula.left.args.length !== 1 || !formula.left.pred.endsWith(".Real")) break;
                  const evidence = refinements.prove(formula.left.args[0]!, formula.left.pred);
                  if (!evidence) return undefined;
                  proof = impElim(proof, evidence);
                }
                return proof;
              } catch { return undefined; }
            };
            const graphs = new Map<"realLess" | "realLe", Term>();
            for (const local of localOrders) {
              const kind = realKind(local.formula);
              if (kind && local.formula.tag === "pred") graphs.set(kind, local.formula.args[0]!);
            }
            graphs.set(goalRealKind, current.goal.args[0]!);
            for (const kind of ["realLess", "realLe"] as const) if (!graphs.has(kind)) {
              const name = resolveOptional(kind, scope, candidate => kernel.functions.has(candidate));
              if (name) graphs.set(kind, app(name));
            }
            const order = (kind: "realLess" | "realLe", left: Term, right: Term): Formula =>
              pred("relates", graphs.get(kind) ?? current.goal.args[0]!, left, right);
            const visiting = new Set<string>();
            const proveOrder = (kind: "realLess" | "realLe", left: Term, right: Term, depth: number): Proof | undefined => {
              if (depth > 5) return undefined;
              const target = order(kind, left, right);
              const key = `${kind}|${termCanonical(left)}|${termCanonical(right)}`;
              if (visiting.has(key)) return undefined;
              visiting.add(key);
              try {
                for (const local of localOrders) {
                  if (formulaEquals(local.formula, target) && realKind(local.formula) === kind) return local.proof;
                }
                const rightDifference = binary(right, "realSubValue");
                if (kind === "realLess" && rightDifference && left.tag === "app" &&
                    left.args.length === 0 && left.fn.endsWith(".realZero")) {
                  const premise = proveOrder("realLess", rightDifference[1], rightDifference[0], depth + 1);
                  const equivalence = checkedRule("realLess.iff_pos_sub", [rightDifference[1], rightDifference[0]], []);
                  if (premise && equivalence) {
                    const result = impElim(iffElimLeft(equivalence), premise);
                    if (formulaEquals(kernel.checkProof(result, current.assumptions), target)) return result;
                  }
                }
                if (kind === "realLe" && termEquals(left, right)) {
                  const reflexive = checkedRule("realLe.reflexive", [left], []);
                  if (reflexive && formulaEquals(kernel.checkProof(reflexive, current.assumptions), target)) return reflexive;
                }
                if (kind === "realLe") {
                  const rightSub = binary(right, "realSubValue");
                  const leftSub = binary(left, "realSubValue");
                  if (rightSub && left.tag === "app" && left.args.length === 0 && left.fn.endsWith(".realZero")) {
                    const premise = proveOrder("realLe", rightSub[1], rightSub[0], depth + 1);
                    if (premise) {
                      const result = checkedRule("realSubValue.nonnegative_of_le", [rightSub[1], rightSub[0]], [premise]);
                      if (result && formulaEquals(kernel.checkProof(result, current.assumptions), target)) return result;
                    }
                  }
                  if (leftSub && rightSub) {
                    const first = proveOrder("realLe", leftSub[0], rightSub[0], depth + 1);
                    const second = termEquals(leftSub[1], rightSub[1])
                      ? proveOrder("realLe", leftSub[1], leftSub[1], depth + 1)
                      : proveOrder("realLe", rightSub[1], leftSub[1], depth + 1);
                    if (first && second) {
                      const result = checkedRule("realSubValue.le",
                        [leftSub[0], leftSub[1], rightSub[0], rightSub[1]], [first, second]);
                      if (result && formulaEquals(kernel.checkProof(result, current.assumptions), target)) return result;
                    }
                  }
                  const negLeft = unary(left, "realNegValue");
                  const negRight = unary(right, "realNegValue");
                  if (negLeft && negRight) {
                    const premise = proveOrder("realLe", negRight, negLeft, depth + 1);
                    if (premise) {
                      const result = checkedRule("realLe.neg_reverse", [negRight, negLeft], [premise]);
                      if (result && formulaEquals(kernel.checkProof(result, current.assumptions), target)) return result;
                    }
                  }
                }
                if (kind === "realLess") {
                  const leftSub = binary(left, "realSubValue");
                  const rightSub = binary(right, "realSubValue");
                  if (leftSub && rightSub && termEquals(leftSub[1], rightSub[1])) {
                    const premise = proveOrder("realLess", leftSub[0], rightSub[0], depth + 1);
                    if (premise) {
                      const result = checkedRule("realSubValue.lt_left",
                        [leftSub[0], rightSub[0], leftSub[1]], [premise]);
                      if (result && formulaEquals(kernel.checkProof(result, current.assumptions), target)) return result;
                    }
                  }
                }
                const leftAdd = binary(left, "realAddValue");
                const rightAdd = binary(right, "realAddValue");
                if (leftAdd && rightAdd) {
                  const first = proveOrder(kind, leftAdd[0], rightAdd[0], depth + 1);
                  const second = proveOrder(kind, leftAdd[1], rightAdd[1], depth + 1);
                  if (first && second) {
                    const rule = kind === "realLe" ? "realLe.add" : "realLess.add";
                    const result = checkedRule(rule,
                      [leftAdd[0], rightAdd[0], leftAdd[1], rightAdd[1]], [first, second]);
                    if (result && formulaEquals(kernel.checkProof(result, current.assumptions), target)) return result;
                  }
                }
                for (const local of localOrders) {
                  if (local.formula.tag !== "pred" || !termEquals(local.formula.args[1]!, left)) continue;
                  const middle = local.formula.args[2]!;
                  const firstKind = realKind(local.formula);
                  const rule = kind === "realLe" && firstKind === "realLe" ? "realLe.transitive"
                    : kind === "realLess" && firstKind === "realLe" ? "realLe.transitive_less"
                      : kind === "realLess" && firstKind === "realLess" ? "realLess.transitive_le" : undefined;
                  if (!rule) continue;
                  const second = proveOrder(kind === "realLe" ? "realLe" : firstKind === "realLe" ? "realLess" : "realLe",
                    middle, right, depth + 1);
                  if (!second) continue;
                  const result = checkedRule(rule, [left, middle, right], [local.proof, second]);
                  if (result && formulaEquals(kernel.checkProof(result, current.assumptions), target)) return result;
                }
                return undefined;
              } finally { visiting.delete(key); }
            };
            realProof = proveOrder(goalRealKind, current.goal.args[1]!, current.goal.args[2]!, 0);
            if (!realProof && goalRealKind === "realLe") {
              // Search a small collection of checked consequences, comparing
              // their affine forms before attempting algebraic equality proof.
              // This permits associative/commutative rearrangement and
              // cancellation without asking the kernel to trust normalization.
              const goalLeft = current.goal.args[1]!;
              const goalRight = current.goal.args[2]!;
              type Affine = Map<string, bigint>;
              const affine = (term: Term): Affine => {
                const add = (left: Affine, right: Affine, sign = 1n): Affine => {
                  const result = new Map(left);
                  for (const [key, value] of right) {
                    const next = (result.get(key) ?? 0n) + sign * value;
                    if (next === 0n) result.delete(key); else result.set(key, next);
                  }
                  return result;
                };
                if (term.tag === "app" && term.args.length === 0 && term.fn.endsWith(".realZero")) return new Map();
                const sum = binary(term, "realAddValue");
                if (sum) return add(affine(sum[0]), affine(sum[1]));
                const sub = binary(term, "realSubValue");
                if (sub) return add(affine(sub[0]), affine(sub[1]), -1n);
                const neg = unary(term, "realNegValue");
                if (neg) return add(new Map(), affine(neg), -1n);
                return new Map([[termCanonical(term), 1n]]);
              };
              const sameAffine = (left: Term, right: Term): boolean => {
                const a = affine(left);
                const b = affine(right);
                return a.size === b.size && [...a].every(([key, value]) => b.get(key) === value);
              };
              const realRewriteNames = [
                "realAddValue.associative", "realAddValue.commutative",
                "realAddValue.zero_left", "realAddValue.zero_right",
                "realAddValue.neg_left", "realAddValue.neg_right",
                "realNegValue.involutive", "realNegValue.add", "realNegValue.zero",
                "realSubValue.add_cancel_left", "realSubValue.add_cancel_right",
                "realSubValue.add_right_cancel", "realSubValue.zero_left", "realSubValue.zero_right",
              ];
              let realRewrites: PreparedRewrites | undefined;
              const proveAffineEquality = (left: Term, right: Term): Proof | undefined => {
                if (termEquals(left, right)) return refl(left);
                if (!sameAffine(left, right)) return undefined;
                try {
                  realRewrites ??= prepareRewrites(kernel, resolveRules(kernel, realRewriteNames, line.number, scope));
                  return settle(kernel, eq(left, right), {
                    using: realRewrites, assumptions: current.assumptions, visibility,
                    useContextEqualities: false, fuel: 4_000,
                  });
                } catch { return undefined; }
              };
              const align = (candidate: Proof): Proof | undefined => {
                const formula = kernel.checkProof(candidate, current.assumptions);
                if (formula.tag !== "pred" || realKind(formula) !== "realLe") return undefined;
                const left = formula.args[1]!;
                const right = formula.args[2]!;
                if (!sameAffine(left, goalLeft) || !sameAffine(right, goalRight)) return undefined;
                const leftEq = proveAffineEquality(left, goalLeft);
                const rightEq = proveAffineEquality(right, goalRight);
                if (!leftEq || !rightEq) return undefined;
                let variable = "__realAffine";
                const forbidden = new Set([...freeTermVariables(left), ...freeTermVariables(right),
                  ...freeTermVariables(goalLeft), ...freeTermVariables(goalRight)]);
                while (forbidden.has(variable)) variable += "_";
                const shiftedLeft = eqElim(leftEq, variable,
                  order("realLe", v(variable), right), candidate);
                const shiftedRight = eqElim(rightEq, variable,
                  order("realLe", goalLeft, v(variable)), shiftedLeft);
                return formulaEquals(kernel.checkProof(shiftedRight, current.assumptions), current.goal)
                  ? shiftedRight : undefined;
              };
              const parts = new Map<string, Term>();
              const collect = (term: Term, depth: number): void => {
                if (depth > 5 || parts.size > 24) return;
                parts.set(termCanonical(term), term);
                const pair = binary(term, "realAddValue") ?? binary(term, "realSubValue");
                if (pair) { collect(pair[0], depth + 1); collect(pair[1], depth + 1); }
              };
              collect(goalLeft, 0);
              collect(goalRight, 0);
              const addition = [...parts.values()].find(item => binary(item, "realAddValue") &&
                item.tag === "app" && item.fn.endsWith(".Algebra.call2"));
              const addGraph = addition?.tag === "app" ? addition.args[0] : undefined;
              const addFn = addition?.tag === "app" ? addition.fn : undefined;
              const realAdd = resolveOptional("realAdd", scope, candidate => kernel.functions.has(candidate));
              const addTerm = (left: Term, right: Term): Term | undefined =>
                addFn && (addGraph ?? realAdd) ? app(addFn, addGraph ?? app(realAdd!), left, right) : undefined;
              const subName = resolveOptional("realSubValue", scope, candidate => kernel.functions.has(candidate));
              const subTerm = (left: Term, right: Term): Term | undefined => subName ? app(subName, left, right) : undefined;
              const available = localOrders.filter(item => realKind(item.formula) === "realLe" && item.formula.tag === "pred").slice(0, 16);
              const bases: Proof[] = available.map(item => item.proof);
              for (const first of available) for (const second of available) {
                if (first.formula.tag !== "pred" || second.formula.tag !== "pred") continue;
                const combined = checkedRule("realLe.add", [first.formula.args[1]!, first.formula.args[2]!,
                  second.formula.args[1]!, second.formula.args[2]!], [first.proof, second.proof]);
                if (combined) bases.push(combined);
              }
              for (const base of bases) {
                realProof = align(base);
                if (realProof) break;
                const formula = kernel.checkProof(base, current.assumptions);
                if (formula.tag !== "pred") continue;
                for (const part of parts.values()) {
                  const leftSum = addTerm(formula.args[1]!, part);
                  const rightSum = addTerm(formula.args[2]!, part);
                  if (leftSum && rightSum && sameAffine(leftSum, goalLeft) && sameAffine(rightSum, goalRight)) {
                    const translated = checkedRule("realLe.add_right",
                      [formula.args[1]!, formula.args[2]!, part], [base]);
                    if (translated && (realProof = align(translated))) break;
                  }
                  const leftSub = subTerm(formula.args[1]!, part);
                  const rightSub = subTerm(formula.args[2]!, part);
                  if (leftSub && rightSub && sameAffine(leftSub, goalLeft) && sameAffine(rightSub, goalRight)) {
                    const translated = checkedRule("realSubValue.le_left",
                      [formula.args[1]!, formula.args[2]!, part], [base]);
                    if (translated && (realProof = align(translated))) break;
                  }
                }
                if (realProof) break;
              }
            }
          }
          if (realProof) { close(line, realProof); continue; }
          throw new SurfaceError(line.number, "linarith found no checked real-order derivation");
        }
      }
      const presentation = naturalLinearArithmeticPresentation(kernel, line.number, scope);
      const dischargeArithmeticTypes = (proof: Proof, terms: readonly Term[]): Proof | undefined => {
        let result = at(proof, ...terms);
        while (true) {
          const formula = kernel.checkProof(result, current.assumptions);
          if (formula.tag !== "imp" || formula.left.tag !== "pred" || formula.left.args.length !== 1) break;
          const evidence = refinements.prove(formula.left.args[0]!, formula.left.pred);
          if (!evidence) return undefined;
          result = impElim(result, evidence);
        }
        return result;
      };
      const comparisonKind = (formula: Formula): "lt" | "le" | undefined =>
        formula.tag === "pred" && formula.args.length === 2
          ? formula.pred === presentation.less ? "lt"
            : formula.pred === presentation.lessEqual ? "le" : undefined
          : undefined;
      const goalKind = comparisonKind(current.goal);
      if (goalKind && current.goal.tag === "pred") {
        interface LinearForm { readonly coefficients: Map<string, bigint>; readonly constant: bigint }
        const atomTerms = new Map<string, Term>();
        const plus = (left: LinearForm, right: LinearForm): LinearForm => {
          const coefficients = new Map(left.coefficients);
          for (const [atom, coefficient] of right.coefficients) {
            const sum = (coefficients.get(atom) ?? 0n) + coefficient;
            if (sum === 0n) coefficients.delete(atom); else coefficients.set(atom, sum);
          }
          return { coefficients, constant: left.constant + right.constant };
        };
        const scale = (coefficient: bigint, form: LinearForm): LinearForm => ({
          coefficients: new Map([...form.coefficients].flatMap(([atom, value]) => coefficient * value === 0n
            ? [] : [[atom, coefficient * value] as const])),
          constant: coefficient * form.constant,
        });
        const negate = (form: LinearForm): LinearForm => scale(-1n, form);
        const linearize = (term: Term): LinearForm => {
          const value = naturalValue(term);
          if (value !== undefined) return { coefficients: new Map(), constant: value };
          if (term.tag === "app" && term.fn === presentation.add && term.args.length === 2) {
            return plus(linearize(term.args[0]!), linearize(term.args[1]!));
          }
          if (term.tag === "app" && term.fn === presentation.successor && term.args.length === 1) {
            return plus(linearize(term.args[0]!), { coefficients: new Map(), constant: 1n });
          }
          if (term.tag === "app" && term.fn === presentation.mul && term.args.length === 2) {
            const leftValue = naturalValue(term.args[0]!);
            if (leftValue !== undefined) return scale(leftValue, linearize(term.args[1]!));
            const rightValue = naturalValue(term.args[1]!);
            if (rightValue !== undefined) return scale(rightValue, linearize(term.args[0]!));
          }
          const key = termCanonical(term);
          atomTerms.set(key, term);
          return { coefficients: new Map([[key, 1n]]), constant: 0n };
        };
        const difference = (left: Term, right: Term): LinearForm =>
          plus(linearize(right), negate(linearize(left)));
        const formKey = (form: LinearForm): string => [
          `#:${form.constant}`,
          ...[...form.coefficients].sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0)
            .map(([atom, coefficient]) => `${atom}:${coefficient}`),
        ].join("|");
        const goalLeft = current.goal.args[0]!;
        const goalRight = current.goal.args[1]!;
        const goalVariables = freeFormulaVariables(current.goal);
        const equalityFacts: Proof[] = [];
        for (const local of current.locals.values()) {
          if (local.formula.tag === "eq" && !termEquals(local.formula.left, local.formula.right) &&
              [...freeFormulaVariables(local.formula)].some(variable => goalVariables.has(variable))) {
            equalityFacts.push(local.proof);
          }
        }
        const ringRules = preparedRingRules(kernel, line.number, scope);
        const dischargeTypes = dischargeArithmeticTypes;
        const addAssociative = resolveProof(kernel, "Grace.Core.Nat.Algebra.add.associative", line.number, scope);
        const addCommutative = resolveProof(kernel, "Grace.Core.Nat.Algebra.add.commutative", line.number, scope);
        const mulCommutative = resolveProof(kernel, "Grace.Core.Nat.Algebra.mul.commutative", line.number, scope);
        const scalarRules = resolveRules(kernel, [
          "mul", "Grace.Core.Nat.Algebra.add.right_unit",
        ], line.number, scope);
        interface AdditiveNormalForm { readonly leaves: readonly Term[]; readonly term: Term; readonly proof: Proof }
        const additiveTerm = (leaves: readonly Term[]): Term => leaves.length === 0 ? nat(0)
          : leaves.slice(0, -1).reduceRight<Term>((tail, head) => app(presentation.add, head, tail), leaves.at(-1)!);
        const appendAdditive = (left: readonly Term[], right: readonly Term[]): Proof => {
          const rightTerm = additiveTerm(right);
          const visit = (leaves: readonly Term[]): Proof => {
            if (leaves.length <= 1) return refl(app(presentation.add, leaves[0]!, rightTerm));
            const head = leaves[0]!;
            const tail = leaves.slice(1);
            const tailTerm = additiveTerm(tail);
            const associative = dischargeTypes(addAssociative, [tailTerm, rightTerm, head]);
            if (!associative) throw new SurfaceError(line.number, "arith could not type additive reassociation");
            const rest = visit(tail);
            return calc(associative, congr(presentation.add, refl(head), rest));
          };
          return visit(left);
        };
        const swapAdditive = (leaves: readonly Term[], index: number): Proof => {
          if (index > 0) return congr(
            presentation.add, refl(leaves[0]!), swapAdditive(leaves.slice(1), index - 1),
          );
          const first = leaves[0]!;
          const second = leaves[1]!;
          if (leaves.length === 2) {
            const commutative = dischargeTypes(addCommutative, [second, first]);
            if (!commutative) throw new SurfaceError(line.number, "arith could not type additive commutativity");
            return commutative;
          }
          const tail = additiveTerm(leaves.slice(2));
          const swap = dischargeTypes(
            resolveProof(kernel, "Grace.Core.Nat.Algebra.add.swap", line.number, scope),
            [second, tail, first],
          );
          if (!swap) throw new SurfaceError(line.number, "arith could not type additive exchange");
          return swap;
        };
        const compareLeaves = (left: Term, right: Term): number => {
          const leftValue = naturalValue(left);
          const rightValue = naturalValue(right);
          if (leftValue !== undefined && rightValue !== undefined) return leftValue < rightValue ? -1 : leftValue > rightValue ? 1 : 0;
          if (leftValue !== undefined) return -1;
          if (rightValue !== undefined) return 1;
          const leftKey = termCanonical(left);
          const rightKey = termCanonical(right);
          return leftKey < rightKey ? -1 : leftKey > rightKey ? 1 : 0;
        };
        const sortAdditive = (input: readonly Term[]): AdditiveNormalForm => {
          const leaves = [...input];
          let term = additiveTerm(leaves);
          let proof: Proof = refl(term);
          for (let target = 0; target < leaves.length; target += 1) {
            let selected = target;
            for (let candidate = target + 1; candidate < leaves.length; candidate += 1) {
              if (compareLeaves(leaves[candidate]!, leaves[selected]!) < 0) selected = candidate;
            }
            while (selected > target) {
              const exchange = swapAdditive(leaves, selected - 1);
              proof = calc(proof, exchange);
              [leaves[selected - 1], leaves[selected]] = [leaves[selected]!, leaves[selected - 1]!];
              selected -= 1;
            }
          }
          term = additiveTerm(leaves);
          return { leaves, term, proof };
        };
        const collapseAdditiveConstants = (input: AdditiveNormalForm): AdditiveNormalForm => {
          const leaves = [...input.leaves];
          let proof = input.proof;
          let count = 0;
          while (count < leaves.length && naturalValue(leaves[count]!) !== undefined) count += 1;
          while (count > 1) {
            const first = leaves[0]!;
            const second = leaves[1]!;
            const rest = leaves.slice(2);
            const restTerm = additiveTerm(rest);
            const sum = (naturalValue(first)! + naturalValue(second)!).toString();
            const computed = kernel.proveComputation(app(presentation.add, first, second), nat(sum));
            if (rest.length === 0) proof = calc(proof, computed);
            else {
              const associative = dischargeTypes(addAssociative, [second, restTerm, first]);
              if (!associative) throw new SurfaceError(line.number, "arith could not type constant reassociation");
              const grouped = symm(associative);
              const folded = congr(presentation.add, computed, refl(restTerm));
              proof = calc(proof, grouped, folded);
            }
            leaves.splice(0, 2, nat(sum));
            count -= 1;
          }
          // The search linearizer discards zero constants. Its certificate
          // normalizer must do the same, using the checked additive identity.
          if (leaves.length > 1 && naturalValue(leaves[0]!) === 0n) {
            const rest = additiveTerm(leaves.slice(1));
            const identity = dischargeTypes(
              resolveProof(kernel, "Grace.Core.Nat.Rec.add.left_unit", line.number, scope), [rest],
            );
            if (!identity) throw new SurfaceError(line.number, "arith could not type additive identity");
            proof = calc(proof, identity);
            leaves.shift();
          }
          return { leaves, term: additiveTerm(leaves), proof };
        };
        const normalizeAdditive = (term: Term): AdditiveNormalForm => {
          if (term.tag === "app" && term.fn === presentation.successor && term.args.length === 1) {
            const argument = term.args[0]!;
            const expansion = dischargeTypes(
              resolveProof(kernel, "Grace.Core.Nat.Algebra.add.right_one", line.number, scope), [argument],
            );
            if (!expansion) throw new SurfaceError(line.number, "arith could not type successor expansion");
            const normalized = normalizeAdditive(app(presentation.add, argument, nat(1)));
            return { ...normalized, proof: calc(symm(expansion), normalized.proof) };
          }
          if (term.tag === "app" && term.fn === presentation.mul && term.args.length === 2) {
            const leftValue = naturalValue(term.args[0]!);
            const rightValue = naturalValue(term.args[1]!);
            if (leftValue !== undefined || rightValue !== undefined) {
              const coefficient = leftValue ?? rightValue!;
              if (coefficient > 4_096n) throw new SurfaceError(line.number, "arith scalar expansion exceeds 4,096");
              const atom = leftValue !== undefined ? term.args[1]! : term.args[0]!;
              const repeated = Array.from({ length: Number(coefficient) }, () => atom);
              const expanded = additiveTerm(repeated);
              let expansion: Proof;
              if (leftValue !== undefined) {
                expansion = settle(kernel, eq(term, expanded), {
                  using: scalarRules, assumptions: current.assumptions, facts: equalityFacts, fuel: 50_000, visibility,
                });
              } else {
                const commute = dischargeTypes(mulCommutative, [term.args[1]!, term.args[0]!]);
                if (!commute) throw new SurfaceError(line.number, "arith could not type scalar commutativity");
                const unfolded = settle(kernel, eq(app(presentation.mul, term.args[1]!, term.args[0]!), expanded), {
                  using: scalarRules, assumptions: current.assumptions, facts: equalityFacts, fuel: 50_000, visibility,
                });
                expansion = calc(commute, unfolded);
              }
              const normalized = normalizeAdditive(expanded);
              return { leaves: normalized.leaves, term: normalized.term, proof: calc(expansion, normalized.proof) };
            }
          }
          if (term.tag !== "app" || term.fn !== presentation.add || term.args.length !== 2) {
            return { leaves: [term], term, proof: refl(term) };
          }
          const left = normalizeAdditive(term.args[0]!);
          const right = normalizeAdditive(term.args[1]!);
          const congruence = congr(presentation.add, left.proof, right.proof);
          const reassociated = appendAdditive(left.leaves, right.leaves);
          const sorted = sortAdditive([...left.leaves, ...right.leaves]);
          const collapsed = collapseAdditiveConstants(sorted);
          return {
            leaves: collapsed.leaves, term: collapsed.term,
            proof: calc(congruence, reassociated, collapsed.proof),
          };
        };
        const proveTermEquality = (left: Term, right: Term): Proof => {
          if (termEquals(left, right)) return refl(left);
          if (freeTermVariables(left).size === 0 && freeTermVariables(right).size === 0) {
            try { return kernel.proveComputation(left, right); } catch {}
          }
          try {
            return settle(kernel, eq(left, right), {
              using: ringRules, assumptions: current.assumptions, facts: equalityFacts, visibility,
              useContextEqualities: false, fuel: 50_000,
            });
          } catch {
            const normalizedLeft = normalizeAdditive(left);
            const normalizedRight = normalizeAdditive(right);
            if (!termEquals(normalizedLeft.term, normalizedRight.term)) throw new SurfaceError(line.number, "arith certificate normalization disagrees with its linear form");
            return calc(normalizedLeft.proof, symm(normalizedRight.proof));
          }
        };
        const typed = (proof: Proof, terms: readonly Term[]): Proof | undefined => {
          return dischargeTypes(proof, terms);
        };
        interface LinearComparison {
          readonly left: Term;
          readonly right: Term;
          readonly form: LinearForm;
          readonly proof: Proof;
        }
        const comparison = (left: Term, right: Term, proof: Proof): LinearComparison =>
          ({ left, right, form: difference(left, right), proof });
        const strictToWeak = (left: Term, right: Term, proof: Proof): LinearComparison | undefined => {
          const gap = typed(presentation.strictGap, [left, right]);
          if (!gap) return undefined;
          const gapLeft = app(presentation.add, left, nat(1));
          return comparison(gapLeft, right, impElim(iffElimLeft(gap), proof));
        };
        const originals: LinearComparison[] = [];
        for (const local of current.locals.values()) {
          const kind = comparisonKind(local.formula);
          if (!kind || local.formula.tag !== "pred") continue;
          const left = local.formula.args[0]!;
          const right = local.formula.args[1]!;
          const item = kind === "le" ? comparison(left, right, local.proof) : strictToWeak(left, right, local.proof);
          if (item) originals.push(item);
        }
        const equalityToComparison = (left: Term, right: Term, proof: Proof): LinearComparison | undefined => {
          const reflexive = typed(presentation.lessEqualReflexive, [left]);
          if (!reflexive) return undefined;
          let variable = "__arithEquality";
          const forbidden = new Set([...freeTermVariables(left), ...freeTermVariables(right)]);
          while (forbidden.has(variable)) variable += "_";
          return comparison(left, right, eqElim(
            proof, variable, pred(presentation.lessEqual, left, v(variable)), reflexive,
          ));
        };
        for (const local of current.locals.values()) {
          if (local.formula.tag !== "eq") continue;
          const forward = equalityToComparison(local.formula.left, local.formula.right, local.proof);
          const backward = equalityToComparison(local.formula.right, local.formula.left, symm(local.proof));
          if (forward) originals.push(forward);
          if (backward) originals.push(backward);
        }
        const negatedGoal = assume(not(current.goal));
        let opposite: LinearComparison | undefined;
        if (goalKind === "le") {
          const theoremProof = typed(presentation.lessOfNotLessEqual, [goalLeft, goalRight]);
          if (theoremProof) opposite = strictToWeak(goalRight, goalLeft, impElim(theoremProof, negatedGoal));
        } else {
          const theoremProof = typed(presentation.lessEqualOfNotLess, [goalLeft, goalRight]);
          if (theoremProof) opposite = comparison(goalRight, goalLeft, impElim(theoremProof, negatedGoal));
        }
        if (!opposite) throw new SurfaceError(line.number, "arith could not construct the negated comparison");
        originals.push(opposite);

        const addComparisons = (left: LinearComparison, right: LinearComparison): LinearComparison | undefined => {
          const terms = [left.left, left.right, right.left, right.right] as const;
          let proof = typed(presentation.addLessEqualLessEqual, terms);
          if (!proof) return undefined;
          proof = impElim(impElim(proof, left.proof), right.proof);
          return {
            left: app(presentation.add, left.left, right.left),
            right: app(presentation.add, left.right, right.right),
            form: plus(left.form, right.form), proof,
          };
        };
        const scaleComparison = (source: LinearComparison, coefficient: bigint): LinearComparison | undefined => {
          if (coefficient <= 0n) return undefined;
          let remaining = coefficient;
          let power = source;
          let result: LinearComparison | undefined;
          while (remaining > 0n) {
            if (remaining & 1n) {
              result = result ? addComparisons(result, power) : power;
              if (!result) return undefined;
            }
            remaining >>= 1n;
            if (remaining > 0n) {
              power = addComparisons(power, power)!;
              if (!power) return undefined;
            }
          }
          return result;
        };
        const gcd = (left: bigint, right: bigint): bigint => {
          let a = left < 0n ? -left : left;
          let b = right < 0n ? -right : right;
          while (b) [a, b] = [b, a % b];
          return a;
        };
        const deduplicate = (items: readonly LinearComparison[]): LinearComparison[] => {
          const unique = new Map<string, LinearComparison>();
          for (const item of items) if (!unique.has(formKey(item.form))) unique.set(formKey(item.form), item);
          return [...unique.values()];
        };
        // Integer tightening: when every atom coefficient of a comparison
        // shares a factor g, divide through and round the constant, which is
        // what makes the elimination exact over the naturals. The certificate
        // cancels the common atom part, then applies the floor or ceiling
        // quotient lemma with a computed quotient.
        const quotientFloor = resolveOptional("LessEqual.quotient_floor", scope, candidate => kernel.theorems.has(candidate));
        const quotientCeiling = resolveOptional("LessEqual.quotient_ceiling", scope, candidate => kernel.theorems.has(candidate));
        const quotientName = resolveOptional("quotientNat", scope, candidate => kernel.functions.has(candidate));
        const scaledSum = (entries: readonly (readonly [string, bigint])[]): Term => {
          const parts = [...entries].sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0).map(([atom, coefficient]) => {
            const term = atomTerms.get(atom)!;
            return coefficient === 1n ? term : app(presentation.mul, nat(coefficient.toString()), term);
          });
          return parts.length === 0 ? nat(0) : parts.slice(1).reduce<Term>((sum, term) => app(presentation.add, sum, term), parts[0]!);
        };
        const tighten = (item: LinearComparison): LinearComparison | undefined => {
          if (!quotientFloor || !quotientCeiling || !quotientName) return undefined;
          const entries = [...item.form.coefficients].filter(([, coefficient]) => coefficient !== 0n);
          if (entries.length === 0) return undefined;
          let g = 0n;
          for (const [, coefficient] of entries) g = gcd(g, coefficient);
          if (g <= 1n || item.form.constant % g === 0n) return undefined;
          try {
            const leftForm = linearize(item.left);
            const rightForm = linearize(item.right);
            const atoms = new Set([...leftForm.coefficients.keys(), ...rightForm.coefficients.keys()]);
            const common: [string, bigint][] = [];
            const lower: [string, bigint][] = [];
            const upper: [string, bigint][] = [];
            for (const atom of atoms) {
              const a = leftForm.coefficients.get(atom) ?? 0n;
              const b = rightForm.coefficients.get(atom) ?? 0n;
              const shared = a < b ? a : b;
              if (shared > 0n) common.push([atom, shared]);
              if (a > b) lower.push([atom, (a - b) / g]);
              if (b > a) upper.push([atom, (b - a) / g]);
            }
            const C = scaledSum(common);
            const Q = scaledSum(lower);
            const P = scaledSum(upper);
            const k = app(presentation.successor, nat((g - 1n).toString()));
            const cL = leftForm.constant;
            const cR = rightForm.constant;
            const add = (x: Term, y: Term): Term => app(presentation.add, x, y);
            const mul = (x: Term, y: Term): Term => app(presentation.mul, x, y);
            const transport = (left: Term, right: Term): Proof => {
              // item.left ≤ item.right becomes left ≤ right through two term equalities.
              const leftEquality = proveTermEquality(item.left, left);
              const rightEquality = proveTermEquality(item.right, right);
              let variable = "__arithTighten";
              const forbidden = new Set([...freeTermVariables(left), ...freeTermVariables(right)]);
              while (forbidden.has(variable)) variable += "_";
              const first = eqElim(leftEquality, variable, pred(presentation.lessEqual, v(variable), item.right), item.proof);
              return eqElim(rightEquality, variable, pred(presentation.lessEqual, left, v(variable)), first);
            };
            const cancelTwice = (innerLeft: Term, innerRight: Term, constant: Term, proof: Proof): Proof | undefined => {
              const outer = typed(presentation.lessEqualAddLeftCancel, [add(constant, innerLeft), add(constant, innerRight), C]);
              if (!outer) return undefined;
              const inner = typed(presentation.lessEqualAddLeftCancel, [innerLeft, innerRight, constant]);
              if (!inner) return undefined;
              return impElim(inner, impElim(outer, proof));
            };
            let variable = "__arithQuotient";
            const forbidden = new Set([...freeTermVariables(Q), ...freeTermVariables(P)]);
            while (forbidden.has(variable)) variable += "_";
            if (cL <= cR) {
              const d = nat((cR - cL).toString());
              const innerLeft = mul(k, Q);
              const innerRight = add(mul(k, P), d);
              const constant = nat(cL.toString());
              const moved = transport(add(C, add(constant, innerLeft)), add(C, add(constant, innerRight)));
              const cancelled = cancelTwice(innerLeft, innerRight, constant, moved);
              if (!cancelled) return undefined;
              const lemma = typed(theorem(quotientFloor), [Q, P, nat((g - 1n).toString()), d]);
              if (!lemma) return undefined;
              const bounded = impElim(lemma, cancelled);
              const quotientValue = (cR - cL) / g;
              const computed = kernel.proveComputation(app(quotientName, d, k), nat(quotientValue.toString()));
              const result = eqElim(computed, variable, pred(presentation.lessEqual, Q, add(P, v(variable))), bounded);
              return comparison(Q, add(P, nat(quotientValue.toString())), result);
            }
            const e = cL - cR - 1n;
            const eTerm = nat(e.toString());
            const innerLeft = add(mul(k, Q), add(eTerm, nat(1)));
            const innerRight = mul(k, P);
            const constant = nat(cR.toString());
            const moved = transport(add(C, add(constant, innerLeft)), add(C, add(constant, innerRight)));
            const cancelled = cancelTwice(innerLeft, innerRight, constant, moved);
            if (!cancelled) return undefined;
            const lemma = typed(theorem(quotientCeiling), [Q, P, nat((g - 1n).toString()), eTerm]);
            if (!lemma) return undefined;
            const bounded = impElim(lemma, cancelled);
            const quotientValue = e / g;
            const computed = kernel.proveComputation(app(quotientName, eTerm, k), nat(quotientValue.toString()));
            const result = eqElim(computed, variable,
              pred(presentation.lessEqual, add(Q, add(v(variable), nat(1))), P), bounded);
            return comparison(add(Q, add(nat(quotientValue.toString()), nat(1))), P, result);
          } catch {
            return undefined;
          }
        };
        const tightened = (item: LinearComparison): LinearComparison => tighten(item) ?? item;
        const eliminate = (input: readonly LinearComparison[]): LinearComparison | undefined => {
          let constraints = deduplicate(input.map(tightened));
          const variables = new Set(constraints.flatMap(item => [...item.form.coefficients.keys()]));
          while (variables.size > 0) {
          let selected: string | undefined;
          let selectedCost: bigint | undefined;
          for (const variable of variables) {
            let positive = 0n;
            let negative = 0n;
            let unitPositive = true;
            let unitNegative = true;
            for (const item of constraints) {
              const coefficient = item.form.coefficients.get(variable) ?? 0n;
              if (coefficient > 0n) { positive += 1n; if (coefficient !== 1n) unitPositive = false; }
              else if (coefficient < 0n) { negative += 1n; if (coefficient !== -1n) unitNegative = false; }
            }
            // An elimination is exact when one side's coefficients are all
            // units; prefer it, then the cheapest projection.
            const exact = unitPositive || unitNegative;
            const cost = (exact ? 0n : 1n << 40n) + positive * negative;
            if (selectedCost === undefined || cost < selectedCost || (cost === selectedCost && variable < selected!)) {
              selected = variable;
              selectedCost = cost;
            }
          }
          const variable = selected!;
          variables.delete(variable);
          const positive = constraints.filter(item => (item.form.coefficients.get(variable) ?? 0n) > 0n);
          const negative = constraints.filter(item => (item.form.coefficients.get(variable) ?? 0n) < 0n);
          const next = constraints.filter(item => !item.form.coefficients.has(variable));
          for (const upper of positive) for (const lower of negative) {
            const upperCoefficient = upper.form.coefficients.get(variable)!;
            const lowerCoefficient = -lower.form.coefficients.get(variable)!;
            const divisor = gcd(upperCoefficient, lowerCoefficient);
            const scaledUpper = scaleComparison(upper, lowerCoefficient / divisor);
            const scaledLower = scaleComparison(lower, upperCoefficient / divisor);
            if (!scaledUpper || !scaledLower) continue;
            const combined = addComparisons(scaledUpper, scaledLower);
            if (combined) next.push(tightened(combined));
            if (next.length > 16_384) {
              throw new SurfaceError(line.number, "arith linear elimination exceeded 16,384 projected constraints");
            }
          }
            constraints = deduplicate(next);
          }
          return constraints.find(item => item.form.coefficients.size === 0 && item.form.constant < 0n);
        };

        // Independent atom components cannot contribute to one another during
        // Fourier-Motzkin elimination. Search the goal component first, then
        // the remaining components for an unrelated contradiction, which keeps
        // explosion valid while avoiding quadratic work on large contexts.
        interface ConstraintComponent {
          readonly items: LinearComparison[];
          readonly atoms: Set<string>;
          containsGoal: boolean;
        }
        const components: ConstraintComponent[] = [];
        for (const item of originals) {
          const atoms = new Set(item.form.coefficients.keys());
          const touching = components.filter(component =>
            [...atoms].some(atom => component.atoms.has(atom)));
          if (touching.length === 0) {
            components.push({ items: [item], atoms, containsGoal: item === opposite });
            continue;
          }
          const target = touching[0]!;
          target.items.push(item);
          atoms.forEach(atom => target.atoms.add(atom));
          target.containsGoal ||= item === opposite;
          for (const merged of touching.slice(1)) {
            target.items.push(...merged.items);
            merged.atoms.forEach(atom => target.atoms.add(atom));
            target.containsGoal ||= merged.containsGoal;
            components.splice(components.indexOf(merged), 1);
          }
        }
        components.sort((left, right) => Number(right.containsGoal) - Number(left.containsGoal));
        let contradiction: LinearComparison | undefined;
        for (const component of components) {
          const constraints = [...component.items];
          // Nat atoms are nonnegative. These constraints make each projection
          // faithful to the carrier's lower bound without coupling components.
          for (const key of component.atoms) {
            const term = atomTerms.get(key)!;
            const zero = typed(presentation.lessEqualZero, [term]);
            if (zero) constraints.push({
              left: nat(0), right: term,
              form: { coefficients: new Map([[key, 1n]]), constant: 0n }, proof: zero,
            });
          }
          contradiction = eliminate(constraints);
          if (contradiction) break;
        }
        if (!contradiction) throw new SurfaceError(line.number, "arith found no linear arithmetic contradiction");

        const leftForm = linearize(contradiction.left);
        const rightForm = linearize(contradiction.right);
        const atoms = [...new Set([...leftForm.coefficients.keys(), ...rightForm.coefficients.keys()])].sort();
        const commonParts: Term[] = [];
        for (const atom of atoms) {
          const coefficient = leftForm.coefficients.get(atom) ?? 0n;
          if (coefficient !== (rightForm.coefficients.get(atom) ?? 0n) || coefficient < 0n) {
            throw new SurfaceError(line.number, "arith produced a malformed ground projection");
          }
          if (coefficient === 0n) continue;
          const term = atomTerms.get(atom)!;
          commonParts.push(coefficient === 1n ? term : app(presentation.mul, nat(coefficient.toString()), term));
        }
        const common = commonParts.length === 0 ? nat(0) : commonParts.slice(1)
          .reduce<Term>((sum, term) => app(presentation.add, sum, term), commonParts[0]!);
        const normalizedLeft = app(presentation.add, common, nat(leftForm.constant.toString()));
        const normalizedRight = app(presentation.add, common, nat(rightForm.constant.toString()));
        const leftEquality = proveTermEquality(contradiction.left, normalizedLeft);
        const rightEquality = proveTermEquality(contradiction.right, normalizedRight);
        let variable = "__arithGround";
        const forbidden = new Set([...freeTermVariables(contradiction.left), ...freeTermVariables(contradiction.right)]);
        while (forbidden.has(variable)) variable += "_";
        const leftTransport = eqElim(
          leftEquality, variable, pred(presentation.lessEqual, v(variable), contradiction.right), contradiction.proof,
        );
        const normalized = eqElim(
          rightEquality, variable, pred(presentation.lessEqual, normalizedLeft, v(variable)), leftTransport,
        );
        let cancel = typed(presentation.lessEqualAddLeftCancel,
          [nat(leftForm.constant.toString()), nat(rightForm.constant.toString()), common]);
        if (!cancel) throw new SurfaceError(line.number, "arith could not type its ground projection");
        const impossible = impElim(cancel, normalized);
        const smaller = rightForm.constant;
        const larger = leftForm.constant;
        const gapStart = app(presentation.add, nat(smaller.toString()), nat(1));
        const gap = larger - smaller - 1n;
        let groundLe = typed(presentation.lessEqualAddRight, [gapStart, nat(gap.toString())]);
        if (!groundLe) throw new SurfaceError(line.number, "arith could not type its ground witness");
        const groundRight = app(presentation.add, gapStart, nat(gap.toString()));
        groundLe = eqElim(
          kernel.proveComputation(groundRight, nat(larger.toString())), variable,
          pred(presentation.lessEqual, gapStart, v(variable)), groundLe,
        );
        const groundGap = typed(presentation.strictGap, [nat(smaller.toString()), nat(larger.toString())]);
        if (!groundGap) throw new SurfaceError(line.number, "arith could not type its strict ground witness");
        const groundLess = impElim(iffElimRight(groundGap), groundLe);
        let cycle = typed(presentation.lessTransitiveLessEqual,
          [nat(smaller.toString()), nat(larger.toString()), nat(smaller.toString())]);
        if (!cycle) throw new SurfaceError(line.number, "arith could not type its contradiction certificate");
        cycle = impElim(impElim(cycle, groundLess), impossible);
        const irreflexive = typed(presentation.lessIrreflexive, [nat(smaller.toString())]);
        if (!irreflexive) throw new SurfaceError(line.number, "arith could not type irreflexivity");
        const absurdity = impElim(irreflexive, cycle);
        close(line, dne(current.goal, impIntro(not(current.goal), absurdity)));
        continue;
      }
      if (current.goal.tag !== "eq") throw new SurfaceError(line.number, "arith requires a linear equality or comparison goal");
      const goalVariables = freeFormulaVariables(current.goal);
      const relevantEqualities = [...current.locals.values()].filter(item =>
        item.formula.tag === "eq" && !termEquals(item.formula.left, item.formula.right) &&
        [...freeFormulaVariables(item.formula)].some(variable => goalVariables.has(variable)));
      let normalizedEquality: Proof | undefined;
      const equalityDirections = [
        relevantEqualities.map(item => item.proof),
        relevantEqualities.map(item => symm(item.proof)),
      ];
      for (const facts of equalityDirections) {
        try {
          normalizedEquality = settle(kernel, current.goal, {
            using: preparedRingRules(kernel, line.number, scope), assumptions: current.assumptions, visibility,
            facts, useContextEqualities: false, fuel: 50_000,
          });
          break;
        } catch {}
      }
      if (normalizedEquality) {
        close(line, normalizedEquality);
        continue;
      }
      const forwardBound = [...current.locals.values()].find(item => item.formula.tag === "pred" &&
        item.formula.pred === presentation.lessEqual && item.formula.args.length === 2 &&
        termEquals(item.formula.args[0]!, current.goal.left) && termEquals(item.formula.args[1]!, current.goal.right));
      const backwardBound = [...current.locals.values()].find(item => item.formula.tag === "pred" &&
        item.formula.pred === presentation.lessEqual && item.formula.args.length === 2 &&
        termEquals(item.formula.args[0]!, current.goal.right) && termEquals(item.formula.args[1]!, current.goal.left));
      if (forwardBound && backwardBound) {
        const antisymmetric = dischargeArithmeticTypes(
          presentation.lessEqualAntisymmetric, [current.goal.left, current.goal.right],
        );
        if (antisymmetric) {
          close(line, impElim(impElim(antisymmetric, forwardBound.proof), backwardBound.proof));
          continue;
        }
      }
      const binary = (term: Term): readonly [string, Term, Term] | undefined =>
        term.tag === "app" && term.args.length === 2 ? [term.fn, term.args[0]!, term.args[1]!] : undefined;
      const isAddition = (name: string): boolean => name === "add" || name.endsWith(".add");
      let cancellation = arithmeticCancellation.get(kernel);
      if (!cancellation) {
        cancellation = {
          left: resolveProof(kernel, "Grace.Cumulus.Nat.Core.add.left_cancel", line.number, scope),
          right: resolveProof(kernel, "Grace.Cumulus.Nat.Core.add.right_cancel", line.number, scope),
        };
        arithmeticCancellation.set(kernel, cancellation);
      }
      interface ArithmeticEdge { readonly term: Term; readonly proof: Proof }
      const graph = new Map<string, ArithmeticEdge[]>();
      const knownEdges = new Set<string>();
      const addEdge = (from: Term, to: Term, proof: Proof): void => {
        const fromKey = termCanonical(from);
        const toKey = termCanonical(to);
        const key = `${fromKey}\u0000${toKey}`;
        if (knownEdges.has(key)) return;
        knownEdges.add(key);
        const edges = graph.get(fromKey) ?? [];
        edges.push({ term: to, proof });
        graph.set(fromKey, edges);
      };
      const addEquality = (formula: Extract<Formula, { readonly tag: "eq" }>, proof: Proof): void => {
        addEdge(formula.left, formula.right, proof);
        addEdge(formula.right, formula.left, symm(proof));
      };
      for (const fact of current.locals.values()) {
        if (fact.formula.tag !== "eq") continue;
        let derivedFormula = fact.formula;
        let derivedProof = fact.proof;
        addEquality(derivedFormula, derivedProof);
        while (true) {
          const left = binary(derivedFormula.left);
          const right = binary(derivedFormula.right);
          if (!left || !right || left[0] !== right[0] || !isAddition(left[0])) break;
          if (termEquals(left[2], right[2])) {
            let candidate = at(cancellation.right, left[1], right[1], left[2]);
            let typedArguments = true;
            for (const term of [left[1], right[1], left[2]]) {
              const typed = refinements.prove(term, "Nat");
              if (!typed) { typedArguments = false; break; }
              candidate = impElim(candidate, typed);
            }
            if (!typedArguments) break;
            derivedProof = impElim(candidate, derivedProof);
            derivedFormula = eq(left[1], right[1]);
            addEquality(derivedFormula, derivedProof);
            continue;
          }
          if (!termEquals(left[1], right[1])) break;
          const typed = refinements.prove(left[1], "Nat");
          if (!typed) break;
          derivedProof = impElim(impElim(at(cancellation.left, left[2], right[2], left[1]), typed), derivedProof);
          derivedFormula = eq(left[2], right[2]);
          addEquality(derivedFormula, derivedProof);
        }
      }
      const targetKey = termCanonical(current.goal.right);
      const startKey = termCanonical(current.goal.left);
      let arithmeticProof: Proof | undefined = startKey === targetKey ? refl(current.goal.left) : undefined;
      const queue: { readonly term: Term; readonly path?: Proof }[] = [{ term: current.goal.left }];
      const visited = new Set([startKey]);
      for (let cursor = 0; !arithmeticProof && cursor < queue.length; cursor += 1) {
        const current = queue[cursor]!;
        for (const edge of graph.get(termCanonical(current.term)) ?? []) {
          const edgeKey = termCanonical(edge.term);
          if (visited.has(edgeKey)) continue;
          const path = current.path ? calc(current.path, edge.proof) : edge.proof;
          if (edgeKey === targetKey) { arithmeticProof = path; break; }
          visited.add(edgeKey);
          queue.push({ term: edge.term, path });
        }
      }
      if (!arithmeticProof) throw new SurfaceError(line.number, "arith found no supported linear arithmetic step");
      close(line, arithmeticProof);
      continue;
    }
    const settleMatch = /^settle(?:\s+with\s+(.+))?$/.exec(command);
    if (settleMatch) {
      const names = settleMatch[1] ? splitTopLevel(settleMatch[1], ",").map(item => item.trim()) : [];
      const localRules = names.flatMap(item => current.locals.has(item) ? [current.locals.get(item)!.proof] : []);
      const externalNames = names.filter(item => !current.locals.has(item));
      close(line, settle(kernel, current.goal, {
        using: names.length ? [...resolveRules(kernel, externalNames, line.number, scope), ...localRules] : defaultSettleRules(kernel, line.number, scope),
        assumptions: current.assumptions, visibility,
        facts: [...current.locals.values()].map(item => item.proof),
        ground: defaultGroundRules(kernel, line.number, scope),
      }));
      continue;
    }
    throw new SurfaceError(line.number, "unknown tactic");
    } catch (error) {
      stepFailed = true;
      const message = (error instanceof Error ? error.message : String(error)).replace(/^line \d+: /u, "");
      const failure = closedBranch
        ? new SurfaceError(line.number,
          `no goals remain in this case; line ${closedBranch.number} (${closedBranch.text}) closed it, ` +
          `and the step does not apply to the next goal: ${message}`)
        : error instanceof SurfaceError ? error : new SurfaceError(line.number, message);
      // `traceSteps` is retained by reference: the finally block
      // below appends the failing command and its unchanged/partial goal state.
      if (captureTrace) failure.partialTrace ??= { initial, steps: traceSteps, ...(narrative.length ? { narrative } : {}), ...(scopeEntries.length ? { scope: scopeEntries } : {}) };
      throw failure;
    } finally {
      if (!stepFailed) {
        for (const frame of branchFrames) if (!frame.closedAt && pending.length <= frame.remaining) frame.closedAt = line;
      }
      const tacticProfileThreshold = Number((globalThis as typeof globalThis & {
        process?: { env?: Record<string, string | undefined> };
      }).process?.env?.GRACE_PROFILE_TACTICS_MS ?? "0");
      if (tacticProfileStart !== undefined && tacticProfileThreshold > 0) {
        const elapsed = globalThis.performance.now() - tacticProfileStart;
        if (elapsed >= tacticProfileThreshold) {
          console.error(`${elapsed.toFixed(2)} ms\t${name || "<nested>"}:${line.number}\t${line.text}`);
        }
      }
      if (captureTrace) traceSteps.push({
        line: line.number, columnStart: line.columnStart, columnEnd: line.columnEnd,
        command: line.text, ...(stepInfo ? { info: stepInfo } : {}), before, after: snapshot(),
      });
    }
  }

  if (calculation) {
    throw new SurfaceError(lines.at(-1)!.number,
      `calc chain is incomplete; next is ${formatFormula(pending[0]!.goal)}`,
      captureTrace ? { initial, steps: traceSteps, ...(narrative.length ? { narrative } : {}), ...(scopeEntries.length ? { scope: scopeEntries } : {}) } : undefined);
  }

  if (pending.length !== 0) {
    throw new SurfaceError(
      lines.at(-1)!.number,
      `${pending.length} ${pending.length === 1 ? "goal remains" : "goals remain"}; next is ${formatFormula(pending[0]!.goal)}`,
      captureTrace ? { initial, steps: traceSteps, ...(narrative.length ? { narrative } : {}), ...(scopeEntries.length ? { scope: scopeEntries } : {}) } : undefined,
    );
  }
  if (!rootProof) throw new SurfaceError(lines.at(-1)!.number, "proof did not produce a term");
  if (seed) return { proof: rootProof, trace: { initial, steps: traceSteps, ...(narrative.length ? { narrative } : {}), ...(scopeEntries.length ? { scope: scopeEntries } : {}) } };
  let proof = assumptions.reduceRight<Proof>((result, assumption) => impIntro(assumption, result), rootProof);
  for (const binder of [...binders].reverse()) proof = forallIntro(binder.name, proof);
  let statement = assumptions.reduceRight<Formula>((result, assumption) => imp(assumption, result), goal);
  for (const binder of [...binders].reverse()) statement = forall(binder.name, statement);
  try {
    kernel.addTheorem(name, statement, proof);
    if (captureTrace) kernel.setTheoremTacticTrace(name, { initial, steps: traceSteps, ...(narrative.length ? { narrative } : {}), ...(scopeEntries.length ? { scope: scopeEntries } : {}) });
  }
  catch (error) { throw new SurfaceError(lines[0]!.number, error instanceof Error ? error.message : String(error)); }
}

function formulaMentionsSymbol(formula: Formula, name: string): boolean {
  switch (formula.tag) {
    case "bottom": return false;
    case "eq": return containsFunction(formula.left, name) || containsFunction(formula.right, name);
    case "pred": return formula.pred === name || formula.args.some(argument => containsFunction(argument, name));
    case "imp":
    case "and":
    case "or":
    case "iff": return formulaMentionsSymbol(formula.left, name) || formulaMentionsSymbol(formula.right, name);
    case "forall":
    case "exists": return formulaMentionsSymbol(formula.body, name);
  }
}

/**
 * Theorem propositions follow layout rather than physical lines. A `requires`
 * or `shows` marker owns every more-indented non-command line up to the next
 * theorem clause, so tactics stay line-oriented while formulas can be
 * arranged as mathematics instead of serialized into one long row.
 */
/**
 * Unfold every instance of a definition's equivalence `rule` in `goal`: the
 * instances a rewrite reaches through the connectives first, then those
 * under a ∀ or ∃ whose bound variable they mention, by descending into the
 * binder with its variable free and closing the binder again. The result is
 * the unfolded goal with the transport of its proof back to `goal`, or
 * undefined when nothing unfolds.
 */
function unfoldThroughout(
  kernel: Kernel, goal: Formula, rule: Proof, assumptions: readonly Formula[], facts: readonly Proof[],
  visibility: ScopeVisibility | undefined, taken: ReadonlySet<string>,
): { readonly goal: Formula; readonly lift: (proof: Proof) => Proof } | undefined {
  type Transport = { readonly goal: Formula; readonly lift: (proof: Proof) => Proof };
  const compose = (outer: Transport | undefined, inner: Transport | undefined): Transport | undefined =>
    !inner ? outer : !outer ? inner : { goal: inner.goal, lift: proof => outer.lift(inner.lift(proof)) };
  const reserved = new Set(taken);
  assumptions.forEach(item => freeFormulaVariables(item).forEach(name => reserved.add(name)));
  const repeat = (formula: Formula): Transport | undefined => {
    let result: Transport | undefined;
    for (let round = 0; round < 64; round += 1) {
      const current = result?.goal ?? formula;
      let rewritten: Transport;
      try { rewritten = rewriteGoal(kernel, current, rule, assumptions, facts, false, true, undefined, visibility); }
      catch { break; }
      if (formulaEquals(rewritten.goal, current)) break;
      result = compose(result, rewritten);
    }
    return result;
  };
  const descend = (formula: Formula): Transport | undefined => {
    const flat = repeat(formula);
    return compose(flat, under(flat?.goal ?? formula));
  };
  const under = (formula: Formula): Transport | undefined => {
    switch (formula.tag) {
      case "forall":
      case "exists": {
        const bound = formula.variable;
        const variable = reserved.has(bound) ? freshSurfaceVariable(bound, new Set([...reserved, ...freeFormulaVariables(formula)])) : bound;
        const body = variable === bound ? formula.body : substituteFormula(formula.body, bound, v(variable));
        reserved.add(variable);
        const inner = descend(body);
        if (!inner) return undefined;
        if (formula.tag === "forall") {
          return { goal: forall(variable, inner.goal),
            lift: proof => forallIntro(variable, inner.lift(forallElim(proof, v(variable)))) };
        }
        return { goal: exists(variable, inner.goal),
          lift: proof => existsElim(proof, variable, existsIntro(variable, body, v(variable), inner.lift(assume(inner.goal)))) };
      }
      case "and": {
        const left = descend(formula.left);
        const right = descend(formula.right);
        if (!left && !right) return undefined;
        return { goal: and(left?.goal ?? formula.left, right?.goal ?? formula.right),
          lift: proof => andIntro(left ? left.lift(andElimLeft(proof)) : andElimLeft(proof),
            right ? right.lift(andElimRight(proof)) : andElimRight(proof)) };
      }
      case "or": {
        const left = descend(formula.left);
        const right = descend(formula.right);
        if (!left && !right) return undefined;
        const leftGoal = left?.goal ?? formula.left;
        const rightGoal = right?.goal ?? formula.right;
        return { goal: or(leftGoal, rightGoal),
          lift: proof => orElim(proof,
            orIntroLeft(left ? left.lift(assume(leftGoal)) : assume(leftGoal), formula.right),
            orIntroRight(formula.left, right ? right.lift(assume(rightGoal)) : assume(rightGoal))) };
      }
      case "imp": {
        // The consequent only: an antecedent needs the other direction.
        const right = descend(formula.right);
        if (!right) return undefined;
        return { goal: imp(formula.left, right.goal),
          lift: proof => impIntro(formula.left, right.lift(impElim(proof, assume(formula.left)))) };
      }
      default:
        return undefined;
    }
  };
  return descend(goal);
}

function joinTheoremClauseContinuations(block: readonly SourceLine[]): readonly SourceLine[] {
  const result: SourceLine[] = [];
  const boundary = (line: SourceLine): boolean =>
    /^(?:requires|shows)(?:\s|$)/.test(line.text) || line.text === "proof" ||
    /^induction\s+/.test(line.text) || line.text.startsWith("|");
  for (let index = 0; index < block.length;) {
    const line = block[index]!;
    const clause = /^(requires|shows)(?:\s+(.*))?$/.exec(line.text);
    if (!clause) {
      result.push(line);
      index += 1;
      continue;
    }
    const pieces = clause[2]?.trim() ? [clause[2]!.trim()] : [];
    const narratives: SourceLine[] = [];
    let cursor = index + 1;
    while (cursor < block.length && !boundary(block[cursor]!)) {
      const continuation = block[cursor]!;
      if (continuation.narrative) {
        narratives.push(continuation);
        cursor += 1;
        continue;
      }
      if (continuation.indent <= line.indent) {
        throw new SurfaceError(continuation.number,
          `${clause[1]} continuation must be indented beneath line ${line.number}`);
      }
      pieces.push(continuation.text);
      cursor += 1;
    }
    if (pieces.length === 0) {
      throw new SurfaceError(line.number, `${clause[1]} needs an indented proposition`);
    }
    result.push({ ...line, text: `${clause[1]} ${pieces.join(" ")}` }, ...narratives);
    index = cursor;
  }
  return result;
}

function instantiateUnfoldRule(
  kernel: Kernel,
  rule: Proof,
  target: Formula,
  assumptions: readonly Formula[],
  line: number,
): { readonly proof: Proof; readonly equivalence: Extract<Formula, { tag: "iff" }> } {
  if (target.tag !== "pred") throw new SurfaceError(line, "unfold currently targets a defined predicate");
  let proof = rule;
  let formula = kernel.checkProof(proof, assumptions);
  for (const argument of target.args) {
    if (formula.tag !== "forall") break;
    proof = at(proof, argument);
    formula = kernel.checkProof(proof, assumptions);
  }
  if (formula.tag !== "iff") throw new SurfaceError(line, "unfold requires a predicate definition");
  return { proof, equivalence: formula };
}

function unfoldFormula(
  kernel: Kernel,
  rule: Proof,
  local: LocalProof,
  assumptions: readonly Formula[],
  line: number,
): LocalProof {
  const instantiated = instantiateUnfoldRule(kernel, rule, local.formula, assumptions, line);
  if (formulaEquals(instantiated.equivalence.left, local.formula)) {
    return { formula: instantiated.equivalence.right, proof: impElim(iffElimLeft(instantiated.proof), local.proof) };
  }
  if (formulaEquals(instantiated.equivalence.right, local.formula)) {
    return { formula: instantiated.equivalence.left, proof: impElim(iffElimRight(instantiated.proof), local.proof) };
  }
  throw new SurfaceError(line, "definition does not unfold the selected local proposition");
}

function unfoldGoal(
  kernel: Kernel,
  rule: Proof,
  goal: Formula,
  assumptions: readonly Formula[],
  line: number,
): { readonly formula: Formula; readonly fold: Proof } {
  const instantiated = instantiateUnfoldRule(kernel, rule, goal, assumptions, line);
  if (formulaEquals(instantiated.equivalence.left, goal)) {
    return { formula: instantiated.equivalence.right, fold: iffElimRight(instantiated.proof) };
  }
  if (formulaEquals(instantiated.equivalence.right, goal)) {
    return { formula: instantiated.equivalence.left, fold: iffElimLeft(instantiated.proof) };
  }
  throw new SurfaceError(line, "definition does not unfold the current goal");
}

/**
 * A fact through a defined predicate, as its body with the definition's
 * generated carrier guards peeled; undefined when the predicate has no
 * definition or the fact is not an instance of it.
 */
function unfoldPredicateFact(
  kernel: Kernel,
  scope: SurfaceScope,
  line: number,
  fact: LocalProof,
  assumptions: readonly Formula[],
  until?: readonly Formula["tag"][],
): LocalProof | undefined {
  // With `until`, nested definitions are opened until the body has one of
  // the wanted shapes, as `Less(a, b)` opens to `LessEqual(succ(a), b)`
  // and on to its existential.
  if (until) {
    let current: LocalProof | undefined = fact;
    for (let depth = 0; depth < 4 && current; depth += 1) {
      const next = unfoldPredicateFact(kernel, scope, line, current, assumptions);
      if (!next) return undefined;
      if (until.includes(next.formula.tag)) return next;
      current = next.formula.tag === "pred" ? next : undefined;
    }
    return undefined;
  }
  if (fact.formula.tag !== "pred" || fact.formula.args.length === 0) return undefined;
  try {
    const rule = resolveProof(kernel, fact.formula.pred, line, scope);
    let unfolded = unfoldFormula(kernel, rule, fact, assumptions, line);
    const guards = predicateSoftGuardCount(fact.formula.pred, kernel, scope);
    for (let index = 0; index < guards && unfolded.formula.tag === "and"; index += 1) {
      unfolded = { formula: unfolded.formula.right, proof: andElimRight(unfolded.proof) };
    }
    return unfolded;
  } catch {
    return undefined;
  }
}

/**
 * A goal through a defined predicate, as its body: the definition's
 * generated carrier guards are supplied from the context or by soft typing,
 * and `fold` turns a proof of the body into a proof of the goal. Undefined
 * when the predicate has no definition or a guard cannot be supplied.
 */
function unfoldPredicateGoal(
  kernel: Kernel,
  scope: SurfaceScope,
  line: number,
  goal: Formula,
  assumptions: readonly Formula[],
  locals: ReadonlyMap<string, LocalProof>,
  until?: readonly Formula["tag"][],
): { readonly formula: Formula; readonly fold: (proof: Proof) => Proof } | undefined {
  if (until) {
    let formula = goal;
    let fold: (proof: Proof) => Proof = proof => proof;
    for (let depth = 0; depth < 4; depth += 1) {
      const next = unfoldPredicateGoal(kernel, scope, line, formula, assumptions, locals);
      if (!next) return undefined;
      const outer = fold;
      fold = proof => outer(next.fold(proof));
      formula = next.formula;
      if (until.includes(formula.tag)) return { formula, fold };
      if (formula.tag !== "pred") return undefined;
    }
    return undefined;
  }
  if (goal.tag !== "pred" || goal.args.length === 0) return undefined;
  try {
    const rule = resolveProof(kernel, goal.pred, line, scope);
    const unfolded = unfoldGoal(kernel, rule, goal, assumptions, line);
    let reduced = unfolded.formula;
    let rebuild: (inner: Proof) => Proof = inner => inner;
    const guards = predicateSoftGuardCount(goal.pred, kernel, scope);
    for (let index = 0; index < guards; index += 1) {
      if (reduced.tag !== "and") return undefined;
      const guard = reduced.left;
      const evidence = [...locals.values()].find(item => formulaEquals(item.formula, guard))?.proof
        ?? (assumptions.some(item => formulaEquals(item, guard)) ? assume(guard) : undefined)
        ?? (guard.tag === "pred" && guard.args.length > 0
          ? proveRefinement(kernel, guard.args.at(-1)!, guard.pred, guard.args.slice(0, -1), assumptions,
            [...locals.values()].map(item => item.proof), scopeVisibility(kernel, scope))
          : undefined);
      if (!evidence) return undefined;
      const previous = rebuild;
      rebuild = inner => previous(andIntro(evidence, inner));
      reduced = reduced.right;
    }
    return { formula: reduced, fold: proof => impElim(unfolded.fold, rebuild(proof)) };
  } catch {
    return undefined;
  }
}

/**
 * A fact stated through a defined predicate meets a goal stated by the
 * predicate's body, or the other way round: the definition's equivalence
 * bridges the two, so `x : ℚ` closes `x ∈ ℚ` and `x ∈ ℚ` closes `x : ℚ`.
 * Returns undefined when no bridge applies.
 */
function bridgeDefinition(
  kernel: Kernel,
  scope: SurfaceScope,
  line: number,
  proof: Proof,
  actual: Formula,
  wanted: Formula,
  assumptions: readonly Formula[],
  locals: ReadonlyMap<string, LocalProof>,
): Proof | undefined {
  const forward = unfoldPredicateFact(kernel, scope, line, { formula: actual, proof }, assumptions);
  if (forward && formulaEquals(forward.formula, wanted)) return forward.proof;
  const backward = unfoldPredicateGoal(kernel, scope, line, wanted, assumptions, locals);
  if (backward && formulaEquals(backward.formula, actual)) return backward.fold(proof);
  return undefined;
}

/**
 * A premise that only types a term is routine: a carrier sort such as
 * `Nat(n)`, or any declared class such as `Ordinal(α)`. Such a guard is
 * discharged from the context or by soft typing without being named.
 */
function routineGuardPredicate(kernel: Kernel, predicate: string): boolean {
  const leaf = predicate.slice(predicate.lastIndexOf(".") + 1);
  if (["Nat", "Integer", "Rational", "Real"].includes(leaf)) return true;
  return surfaceEnvironments.get(kernel)?.classes.has(predicate) ?? false;
}

/**
 * The printing options the goal panel uses at a proof state: the notation
 * table, the ring scopes, and the operations, predicates, functors,
 * carriers, and function forms the facts in scope supply. Built only for
 * a message, since the goal panel derives the same from the trace.
 */
function goalDisplayOptions(
  kernel: Kernel, scope: SurfaceScope, facts: readonly Formula[], conclusions: readonly Formula[],
): PrettyOptions {
  const classNames = new Set(classReport(kernel).map(item => item.name));
  return {
    classPredicate: name => classNames.has(name),
    notations: notationReport(kernel),
    ...(scope.rings?.length ? { rings: scope.rings } : {}),
    operations: displayOperations(kernel, scope, facts, conclusions),
    predicates: displayPredicates(kernel, scope, facts),
    functors: displayFunctors(facts),
    carriers: displayCarriers(kernel, scope, facts, conclusions),
    functions: displayFunctions(kernel, scope, facts),
  };
}

function tacticState(goal: Formula, assumptions: readonly Formula[], locals: ReadonlyMap<string, LocalProof>): TacticStateSnapshot {
  return {
    goals: [{
      goal,
      assumptions: [...assumptions],
      locals: [...locals].map(([name, local]) => ({ name, formula: local.formula })),
    }],
  };
}

interface ProofExpressionContext {
  expectedConclusion?: Formula;
  /** Infer bare apply parameters while retaining its proof obligations. */
  applicationGoal?: boolean;
  localProofs?: Proof[];
  instanceProver?: InstanceProver;
  /** The conjuncts of transparent guard facts in scope, each with its proof. */
  openedGuards?: GuardFact[];
}

/**
 * The conjuncts that transparent guards among the assumptions and local
 * facts expose: from `f : a ⟶ b`, the facts `f ∈ M`, `dom(f) = a`, and
 * `cod(f) = b`, each proved through the guard's definition.
 */
function openedGuardFacts(
  kernel: Kernel, assumptions: readonly Formula[], locals: Iterable<LocalProof>, visibility: ScopeVisibility | undefined,
): GuardFact[] {
  return [
    ...assumptions.map(formula => ({ formula, proof: assume(formula) })),
    ...[...locals].map(item => ({ formula: item.formula, proof: item.proof })),
  ].flatMap(fact => openGuardFact(kernel, fact, visibility));
}

/** A counted star is syntax for an exact, bounded sequence of assumptions. */
function expandCountedPremises(text: string, line: number): string {
  if (!text.includes("*{")) return text;
  return text.replace(/(\bwith\s+|,\s*)\*\{([^}]*)\}/g, (_, prefix: string, digits: string) => {
    const count = /^[0-9]+$/.test(digits) ? Number(digits) : NaN;
    if (!Number.isSafeInteger(count) || count < 1 || count > 256)
      throw new SurfaceError(line, "with *{n} expects a premise count from 1 to 256");
    return prefix + Array.from({ length: count }, () => "assumption").join(", ");
  });
}

// Containers and relation graphs are parameters, not polynomial operands.
function polynomialArgumentIndices(formula: Extract<Formula, { tag: "pred" }>): number[] {
  if (formula.pred === "in" && formula.args.length === 2) return [0];
  if (formula.pred === "relates" && formula.args.length === 3) return [1, 2];
  return formula.args.map((_, index) => index);
}

function resolveLocalProof(
  locals: ReadonlyMap<string, LocalProof>,
  name: string,
  line: number,
  through?: { kernel: Kernel; scope: SurfaceScope; assumptions: readonly Formula[] },
): LocalProof | undefined {
  let localReference = locals.get(name);
  if (!localReference) {
    for (let dot = name.lastIndexOf("."); dot > 0; dot = name.lastIndexOf(".", dot - 1)) {
      const root = locals.get(name.slice(0, dot));
      if (!root) continue;
      const path = name.slice(dot + 1).split(".");
      if (!path.every(part => part === "left" || part === "right")) break;
      let formula = root.formula, projected = root.proof;
      for (const part of path) {
        // A defined predicate projects through its definition.
        if (formula.tag === "pred" && through) {
          const unfolded = unfoldPredicateFact(through.kernel, through.scope, line, { formula, proof: projected }, through.assumptions, ["and"]);
          if (unfolded) { formula = unfolded.formula; projected = unfolded.proof; }
        }
        if (formula.tag !== "and") {
          throw new SurfaceError(line, `${name}: .${part} requires a conjunction, found ${formatFormula(formula)}`);
        }
        projected = part === "left" ? andElimLeft(projected) : andElimRight(projected);
        formula = part === "left" ? formula.left : formula.right;
      }
      localReference = { formula, proof: projected };
      break;
    }
  }
  return localReference;
}

/** Match only the explicitly supplied premise, with rigid quantified variables.
 * No premise search, unfolding, or cross-application substitution cache. */
/** A requirement term with the parameters inferred so far substituted. */
function substituteNamedTerm(term: Term, inferred: ReadonlyMap<string, Term>): Term {
  if (term.tag === "var") return inferred.get(term.name) ?? term;
  if (term.tag === "nat") return term;
  return app(term.fn, ...term.args.map(argument => substituteNamedTerm(argument, inferred)));
}

/** The conjuncts of a right-nested conjunction, as `⟨a, b, c⟩` lists them. */
function conjunctionParts(formula: Formula): Formula[] {
  return formula.tag === "and" ? [formula.left, ...conjunctionParts(formula.right)] : [formula];
}

function matchNamedPremise(pattern: Formula, actual: Formula,
  parameters: ReadonlySet<string>, inferred: Map<string, Term>,
  bound: ReadonlySet<string> = new Set()): boolean {
  const term = (left: Term, right: Term): boolean => {
    if (left.tag === "var" && parameters.has(left.name)) {
      if ([...freeTermVariables(right)].some(name => bound.has(name))) return false;
      const previous = inferred.get(left.name);
      if (previous) return termEquals(previous, right);
      inferred.set(left.name, right);
      return true;
    }
    if (left.tag !== right.tag) return false;
    if (left.tag === "var" && right.tag === "var") return left.name === right.name;
    if (left.tag === "nat" && right.tag === "nat") return left.value === right.value;
    return left.tag === "app" && right.tag === "app" && left.fn === right.fn &&
      left.args.length === right.args.length && left.args.every((arg, i) => term(arg, right.args[i]!));
  };
  if (pattern.tag !== actual.tag) return false;
  switch (pattern.tag) {
    case "bottom": return true;
    case "eq": return actual.tag === "eq" && term(pattern.left, actual.left) && term(pattern.right, actual.right);
    case "pred": return actual.tag === "pred" && pattern.pred === actual.pred &&
      pattern.args.length === actual.args.length && pattern.args.every((arg, i) => term(arg, actual.args[i]!));
    case "and": case "or": case "imp": case "iff":
      return actual.tag === pattern.tag &&
        matchNamedPremise(pattern.left, actual.left, parameters, inferred, bound) &&
        matchNamedPremise(pattern.right, actual.right, parameters, inferred, bound);
    case "forall": case "exists": {
      if (actual.tag !== pattern.tag) return false;
      const forbidden = new Set([...parameters, ...bound,
        ...freeFormulaVariables(pattern.body), ...freeFormulaVariables(actual.body)]);
      for (const value of inferred.values()) for (const name of freeTermVariables(value)) forbidden.add(name);
      const fresh = freshSurfaceVariable("__premise_bound", forbidden);
      return matchNamedPremise(substituteFormula(pattern.body, pattern.variable, v(fresh)),
        substituteFormula(actual.body, actual.variable, v(fresh)), parameters, inferred, new Set([...bound, fresh]));
    }
  }
}

function parseProofExpression(
  kernel: Kernel,
  text: string,
  current: TacticGoal,
  variables: ReadonlySet<string>,
  line: number,
  scope: SurfaceScope,
  expressionContext: ProofExpressionContext = {},
): Proof {
  text = expandCountedPremises(text, line);
  const visibility = scopeVisibility(kernel, scope);
  // A parenthesized proof expression groups an application, as inside the
  // components of refine ⟨…⟩ where commas separate components.
  while (outerParenthesized(text.trim())) text = text.trim().slice(1, -1);
  // An anonymous constructor ⟨a, b⟩ is a proof of the expected proposition,
  // assembled as refine would assemble it; it needs that proposition, which
  // exact, show, an annotated have, and a with position all supply.
  if (/^⟨.*⟩$/su.test(text.trim())) {
    const wanted = expressionContext.expectedConclusion;
    if (!wanted) throw new SurfaceError(line, "an anonymous constructor ⟨…⟩ needs an expected proposition here; name the fact or use refine");
    const scriptLines = [{ number: line, text: `exact ${text.trim()}`, indent: 2 }].flatMap(splitTacticLine);
    const nested = elaborateTacticTheorem(kernel, "", [], [], [], wanted, scriptLines, scope,
      { assumptions: current.assumptions, locals: current.locals, variables: current.variables })!;
    return nested.proof;
  }
  const withMatch = /^(.*?)\s+with\s+(.+)$/u.exec(text.trim());
  const applicationText = (withMatch?.[1] ?? text).trim();
  const supplied = withMatch?.[2]
    ? splitTopLevel(withMatch[2], ",").map(item => item.trim()).filter(Boolean)
    : [];
  const atMatch = /^(.+?)(?:\s+at\s+(.+))?$/.exec(applicationText)!;
  const reference = atMatch[1]!.trim();
  const direction = reference.endsWith(".forward") ? "forward" : reference.endsWith(".backward") ? "backward" : undefined;
  const undirected = direction ? reference.slice(0, -(direction.length + 1)) : reference;
  const referenceMatch = /^([^\s{]+)(?:\{(.*)\})?$/.exec(undirected);
  if (!referenceMatch) throw new SurfaceError(line, `malformed proof reference ${reference}`);
  const baseName = referenceMatch[1]!;
  if (!QUALIFIED_IDENTIFIER.test(baseName) && /[\p{L}\p{M}\p{N}_]-[\p{L}\p{M}\p{N}_]|-[\p{L}\p{N}_]/u.test(baseName)) {
    throw new SurfaceError(line, malformedIdentifier("proof", baseName));
  }
  const localReference = resolveLocalProof(current.locals, baseName, line, { kernel, scope, assumptions: current.assumptions });
  let proof = localReference?.proof ?? resolveProof(kernel, baseName, line, scope);
  // A local fact that is a transparent predicate application, such as
  // subset : A ⊆ B, applies to arguments through its definition: the body
  // is exposed once, as unfold … at would, when arguments are supplied.
  const throughDefinition = (fact: LocalProof): Proof | undefined => {
    if (fact.formula.tag !== "pred") return undefined;
    try {
      const rule = resolveProof(kernel, fact.formula.pred, line, scope);
      let unfolded = unfoldFormula(kernel, rule, fact, current.assumptions, line);
      const generatedGuards = predicateSoftGuardCount(fact.formula.pred, kernel, scope);
      for (let index = 0; index < generatedGuards && unfolded.formula.tag === "and"; index += 1) {
        unfolded = { formula: unfolded.formula.right, proof: andElimRight(unfolded.proof) };
      }
      return unfolded.formula.tag === "forall" || unfolded.formula.tag === "imp" ? unfolded.proof : undefined;
    } catch {
      // Not a transparent predicate: the fact is applied as it stands.
      return undefined;
    }
  };
  if (localReference && localReference.formula.tag === "pred" && (atMatch[2] || supplied.length > 0)) {
    proof = throughDefinition(localReference) ?? proof;
  }
  const resolvedName = localReference ? undefined
    : proof.rule === "theorem" ? proof.name
    : resolutionCandidates(baseName, scope).find(candidate => surfaceEnvironments.get(kernel)?.signatures.has(candidate));
  const signature = resolvedName ? surfaceEnvironments.get(kernel)?.signatures.get(resolvedName) : undefined;
  const parameters = signature?.parameters ?? [];
  const guardCount = parameters.filter(isGuardBinder).length;
  // Only source declarations distinguish requirements from an implication in
  // the conclusion. This is untrusted elaboration metadata, never proof evidence.
  let remainingPremises = signature?.kind === "theorem" && signature.requirementCount !== undefined
    ? guardCount + signature.requirementCount : undefined;
  let remainingBinders = parameters.length;
  const consumedPremise = (): void => {
    if (remainingPremises !== undefined && remainingPremises > 0) remainingPremises -= 1;
  };
  let generatedGuardCount = 0;
  let inferredApplyGuards = false;
  let inferGuardsWithoutWith = false;
  if (atMatch[2]) {
    const terms = splitTopLevel(atMatch[2]!, ",").map(term => parseTerm(term, kernel, variables, line, scope));
    const overrides: ImplicitOverride[] = referenceMatch[2]?.trim()
      ? splitTopLevel(referenceMatch[2]!, ",").map(item => {
          const assignment = findTopLevel(item, ":=");
          if (assignment < 0) return { value: parseTerm(item, kernel, variables, line, scope) };
          const name = item.slice(0, assignment).trim();
          if (!SIMPLE_IDENTIFIER.test(name)) throw new SurfaceError(line, `malformed implicit argument name ${name}`);
          return { name, value: parseTerm(item.slice(assignment + 2), kernel, variables, line, scope) };
        }) : [];
    const arguments_ = resolvedName
      ? elaborateApplicationArguments(kernel, resolvedName, terms, overrides, variables, scope, line)
      : terms;
    // Terms fill the binders in order; a carrier guard standing between two
    // binders is discharged on the way, as one after the last is. The
    // statement is walked alongside, so no proof is checked per term.
    const guardEvidence = (wanted: Formula): Proof | undefined => {
      const local = [...current.locals.values()].find(item => formulaEquals(item.formula, wanted));
      if (local) return local.proof;
      if (current.assumptions.some(item => formulaEquals(item, wanted))) return assume(wanted);
      if (wanted.tag !== "pred" || wanted.args.length === 0) return undefined;
      return proveRefinement(kernel, wanted.args.at(-1)!, wanted.pred, wanted.args.slice(0, -1),
        current.assumptions, [...current.locals.values()].map(item => item.proof), visibility);
    };
    let shape: Formula | undefined = kernel.checkProof(proof, current.assumptions);
    for (const term of arguments_) {
      if (shape?.tag === "imp" && shape.left.tag === "pred" && shape.left.args.length > 0 &&
          routineGuardPredicate(kernel, shape.left.pred)) {
        const guard = guardEvidence(shape.left);
        if (guard) { proof = impElim(proof, guard); consumedPremise(); shape = shape.right; }
      }
      proof = at(proof, term);
      shape = shape?.tag === "forall" ? substituteFormula(shape.body, shape.variable, term) : undefined;
    }
    remainingBinders = Math.max(0, parameters.length - arguments_.length);
    generatedGuardCount = remainingBinders === 0 ? guardCount : 0;
    inferGuardsWithoutWith = parameters.some(item => item.implicit);
  }
  // Named implicit arguments without an at list seed the inference below
  // with those bindings; positional implicit arguments still need at.
  const implicitSeed = new Map<string, Term>();
  if (!atMatch[2] && referenceMatch[2]?.trim()) {
    for (const item of splitTopLevel(referenceMatch[2]!, ",")) {
      const assignment = findTopLevel(item, ":=");
      if (assignment < 0) throw new SurfaceError(line, `implicit proof arguments require an explicit \`at\` argument list`);
      const name = item.slice(0, assignment).trim();
      if (!SIMPLE_IDENTIFIER.test(name)) throw new SurfaceError(line, `malformed implicit argument name ${name}`);
      implicitSeed.set(name, parseTerm(item.slice(assignment + 2), kernel, variables, line, scope));
    }
  }

  // Goal-directed inference. Without an `at` list, every parameter is found
  // by matching the conclusion against the goal, the named premises against
  // the requirements, and finally the remaining requirements against local
  // facts with a bounded, syntactic, unique-match search. Bare `exact thm`
  // then discharges the requirements from local facts as `with *` does.
  let autoDischarge = false;
  let reorderedPremises: string[] | undefined;
  const starIndex = supplied.indexOf("*");
  const namedPrefix = starIndex >= 0 ? supplied.slice(0, starIndex) : supplied;
  // Premise evidence is a local fact, a closed theorem, or the assumption
  // wildcard (null). Entries that are none of these are positional terms or
  // nested proofs and keep their explicit meaning, so inference needs every
  // entry to be evidence.
  const evidenceFormula = (name: string): Formula | null | undefined => {
    // The wildcard and an anonymous constructor are evidence whose formula
    // is the premise it will be checked against.
    if (name === "assumption" || /^⟨.*⟩$/su.test(name)) return null;
    // A parenthesized entry is evidence unless it reads as a term, such as an
    // ordered pair; its statement is found by checking the inner expression.
    if (/^\(.*\)$/su.test(name)) {
      try { parseTerm(name, kernel, variables, line, scope); return undefined; } catch { /* not a term */ }
      try {
        return kernel.checkProof(parseProofExpression(kernel, name, current, variables, line, scope, expressionContext.localProofs !== undefined ? { localProofs: expressionContext.localProofs } : {}), current.assumptions);
      } catch { return null; }
    }
    const local = resolveLocalProof(current.locals, name, line, { kernel, scope, assumptions: current.assumptions });
    if (local) return local.formula;
    if (!/^[\p{L}_][\p{L}\p{M}\p{N}_.]*$/u.test(name) || variables.has(name) ||
        resolveLocalProof(current.locals, name.split(".")[0]!, line, { kernel, scope, assumptions: current.assumptions })) return undefined;
    // A name that also denotes a term, such as a constant, stays a term.
    try { parseTerm(name, kernel, variables, line, scope); return undefined; } catch { /* not a term */ }
    try {
      const closed = kernel.checkProof(resolveProof(kernel, name, line, scope), current.assumptions);
      return closed.tag === "forall" ? undefined : closed;
    } catch { return undefined; }
  };
  const namedEvidence = namedPrefix.map(evidenceFormula);
  const allLocal = namedEvidence.every(item => item !== undefined);
  const trailingEvidence = starIndex >= 0 ? supplied.slice(starIndex + 1).filter(name => evidenceFormula(name) !== undefined).length : 0;
  // A proof without source metadata (an axiom, a definition property, a
  // local fact) infers over its leading quantifiers with no declared
  // requirements; named premises then match implications in its body.
  // A theorem whose binders all sit inside its statement, such as the
  // bootstrap `pair.membership`, is inferred over like a metadata-free proof.
  const metadataFree = signature?.kind !== "theorem" || signature.requirementCount === undefined ||
    (parameters.length === 0 && signature.requirementCount === 0);
  // A bare `with *` on a source theorem also infers: its requirements are
  // matched against local facts, and unique matches fix the parameters.
  if (!atMatch[2] && allLocal &&
      (metadataFree ? kernel.checkProof(proof, current.assumptions).tag === "forall" : remainingBinders > 0) &&
      (expressionContext.expectedConclusion || namedPrefix.length > 0 || implicitSeed.size > 0 ||
        (starIndex >= 0 && !metadataFree))) {
    const goal = expressionContext.expectedConclusion;
    const statement = kernel.checkProof(proof, current.assumptions);
    if (!(goal && namedPrefix.length === 0 && formulaEquals(statement, goal))) {
      const inferenceMode = expressionContext.applicationGoal && supplied.length === 0 ? "apply" : "application";
      let pattern = statement;
      const names = new Set<string>();
      if (metadataFree) {
        while (pattern.tag === "forall") { names.add(pattern.variable); pattern = pattern.body; }
      } else {
        for (let i = 0; i < parameters.length; i++) {
          if (pattern.tag !== "forall") throw new SurfaceError(line, "theorem parameter metadata does not match its checked statement");
          names.add(pattern.variable);
          pattern = pattern.body;
        }
      }
      const requirements: Formula[] = [];
      const declaredRequirements = metadataFree ? 0 : guardCount + signature!.requirementCount!;
      for (let i = 0; i < declaredRequirements; i++) {
        if (pattern.tag !== "imp") throw new SurfaceError(line, "theorem requirement metadata does not match its checked statement");
        requirements.push(pattern.left);
        pattern = pattern.right;
      }
      if (direction) {
        // The equivalence may sit beneath further implications, which stay
        // open requirements. Infer from the selected conclusion and its
        // antecedent, but leave proof construction to projectDirection and
        // consume below.
        while (pattern.tag === "imp") { requirements.push(pattern.left); pattern = pattern.right; }
        if (pattern.tag !== "iff") throw new SurfaceError(line, `${baseName} is not an equivalence`);
        requirements.push(direction === "forward" ? pattern.left : pattern.right);
        pattern = direction === "forward" ? pattern.right : pattern.left;
      }
      const inferred = new Map<string, Term>();
      for (const [name, value] of implicitSeed) {
        if (!names.has(name)) throw new SurfaceError(line, `${baseName} has no parameter ${name}`);
        inferred.set(name, value);
      }
      // Evidence entries beyond the declared requirements consume implications
      // inside the conclusion, so the goal may sit beneath some of them; a
      // bare apply leaves any such implication as a subgoal.
      const extra: Formula[] = [];
      const allowance = expressionContext.applicationGoal && supplied.length === 0 ? Infinity : namedPrefix.length + trailingEvidence;
      if (goal) {
        let conclusion = pattern;
        let matched = false;
        for (let stripped = 0; ; stripped++) {
          const candidate = new Map(inferred);
          if (matchNamedPremise(conclusion, goal, names, candidate)) {
            for (const [name, value] of candidate) inferred.set(name, value);
            matched = true;
            break;
          }
          if (stripped >= allowance || conclusion.tag !== "imp") break;
          extra.push(conclusion.left);
          conclusion = conclusion.right;
        }
        if (!matched) {
          if (namedPrefix.length === 0) throw new SurfaceError(line, `${baseName}: conclusion does not match the goal for ${inferenceMode}; supply an explicit at list`);
          // Named premises can still fix every parameter; the conclusion
          // then meets the goal through a definition when the fact closes.
          extra.length = 0;
          let fallback = pattern;
          for (let stripped = 0; stripped < allowance && fallback.tag === "imp"; stripped++) {
            extra.push(fallback.left);
            fallback = fallback.right;
          }
        }
      } else {
        // Without a goal, evidence entries still match the leading
        // implications of the statement, as for a bootstrap theorem whose
        // requirements carry no source metadata.
        let conclusion = pattern;
        for (let stripped = 0; stripped < allowance && conclusion.tag === "imp"; stripped++) {
          extra.push(conclusion.left);
          conclusion = conclusion.right;
        }
      }
      const targets = [...requirements, ...extra];
      const claimed = new Map<number, string>();
      for (let position = 0; position < namedPrefix.length; position += 1) {
        const name = namedPrefix[position]!;
        const formula = namedEvidence[position];
        if (formula === null || formula === undefined) continue;
        let found = false;
        for (let i = 0; i < targets.length && !found; i++) {
          if (claimed.has(i)) continue;
          const candidate = new Map(inferred);
          if (!matchNamedPremise(targets[i]!, formula, names, candidate)) continue;
          for (const [parameter, value] of candidate) inferred.set(parameter, value);
          claimed.set(i, name);
          found = true;
        }
        // Entries listed in order may be the conjuncts of one requirement,
        // `with inSpace, notInjective` for `x ∈ A ∧ x ∉ B`: they are
        // combined into the constructor ⟨inSpace, notInjective⟩.
        for (let i = 0; i < targets.length && !found; i++) {
          if (claimed.has(i) || targets[i]!.tag !== "and") continue;
          const parts = conjunctionParts(targets[i]!);
          if (position + parts.length > namedPrefix.length) continue;
          const candidate = new Map(inferred);
          const matched = parts.every((part, offset) => {
            const evidence = namedEvidence[position + offset];
            return evidence !== null && evidence !== undefined && matchNamedPremise(part, evidence, names, candidate);
          });
          if (!matched) continue;
          for (const [parameter, value] of candidate) inferred.set(parameter, value);
          claimed.set(i, `⟨${namedPrefix.slice(position, position + parts.length).join(", ")}⟩`);
          position += parts.length - 1;
          found = true;
        }
        if (!found) {
          const expected = targets.findIndex((_, index) => !claimed.has(index));
          const wanted = expected < 0
            ? "every requirement is already matched by an earlier premise"
            : `requirement ${expected + 1} is ${formatFormula(targets[expected]!)}`;
          throw new SurfaceError(line,
            `${baseName}: named premise ${name} (${formatFormula(formula)}) matches no requirement; ${wanted}; supply an explicit at list if needed`);
        }
      }
      // Named premises are consumed where they matched, whatever their order
      // in the list; unnamed positions before the last named one come from
      // local evidence. A wildcard entry keeps the list positional.
      if (claimed.size > 0 && !namedEvidence.includes(null)) {
        const last = Math.max(...claimed.keys());
        reorderedPremises = [];
        for (let i = 0; i <= last; i++) reorderedPremises.push(claimed.get(i) ?? "assumption");
        if (starIndex >= 0) reorderedPremises.push("*", ...supplied.slice(starIndex + 1));
      }
      if (inferred.size < names.size) {
        const key = (formula: Formula): string => formula.tag === "pred" ? `pred:${formula.pred}` : formula.tag;
        const indexed = new Map<string, Formula[]>();
        const openedFacts = openedGuardFacts(kernel, current.assumptions, current.locals.values(), visibility).map(item => item.formula);
        for (const fact of [...current.assumptions, ...[...current.locals.values()].map(item => item.formula), ...openedFacts]) {
          const bucket = indexed.get(key(fact));
          if (bucket) bucket.push(fact); else indexed.set(key(fact), [fact]);
        }
        let attempts = 0;
        let changed = true;
        while (changed && inferred.size < names.size) {
          changed = false;
          for (const requirement of targets) {
            if (![...freeFormulaVariables(requirement)].some(name => names.has(name) && !inferred.has(name))) continue;
            let unique: Map<string, Term> | undefined;
            let ambiguous = false;
            for (const fact of indexed.get(key(requirement)) ?? []) {
              if (++attempts > 2048)
                throw new SurfaceError(line, `${baseName}: ${inferenceMode} parameter inference reached its 2048-match limit; supply an explicit at list`);
              const candidate = new Map(inferred);
              if (!matchNamedPremise(requirement, fact, names, candidate)) continue;
              if (!unique) unique = candidate;
              else if (candidate.size !== unique.size || [...candidate].some(([name, value]) =>
                !unique!.has(name) || !termEquals(value, unique!.get(name)!))) {
                ambiguous = true;
                break;
              }
            }
            if (!ambiguous && unique && unique.size > inferred.size) {
              for (const [name, value] of unique) inferred.set(name, value);
              changed = true;
            }
          }
          // A guard such as (g ∘ f : a ⟶ b) with an open endpoint and no
          // local fact of its shape is completed by the certified rules: the
          // guards of the factors determine the endpoints of the composite.
          if (!changed && inferred.size < names.size) {
            for (const requirement of targets) {
              if (requirement.tag !== "pred" || !isBindingPredicate(kernel, requirement.pred, visibility)) continue;
              const open = (term: Term): boolean => [...freeTermVariables(term)].some(name => names.has(name) && !inferred.has(name));
              if (!requirement.args.some(open)) continue;
              const request = requirement.args.map(argument => open(argument) ? undefined : substituteNamedTerm(argument, inferred));
              if (request.every(argument => argument === undefined)) continue;
              const completed = prepareRefinementProver(kernel, current.assumptions,
                [...current.locals.values()].map(item => item.proof), visibility).complete(requirement.pred, request);
              if (!completed) continue;
              const candidate = new Map(inferred);
              if (!matchNamedPremise(requirement, pred(requirement.pred, ...completed.arguments), names, candidate)) continue;
              for (const [name, value] of candidate) inferred.set(name, value);
              changed = true;
              break;
            }
          }
        }
      }
      const missing = [...names].filter(name => !inferred.has(name));
      if (missing.length)
        throw new SurfaceError(line, `${baseName}: cannot uniquely infer parameters ${missing.join(", ")} from the goal and local premises; supply an explicit at list`);
      for (const value of inferred.values()) if ([...freeTermVariables(value)].some(name => !variables.has(name)))
        throw new SurfaceError(line, `${baseName}: inferred parameter escapes the local scope`);
      proof = at(proof, ...[...names].map(name => inferred.get(name)!));
      remainingBinders = 0;
      generatedGuardCount = metadataFree ? 0 : guardCount;
      inferredApplyGuards = Boolean(expressionContext.applicationGoal && supplied.length === 0);
      autoDischarge = Boolean(goal && !expressionContext.applicationGoal && supplied.length === 0);
    }
  }

  const localProofs = (): Proof[] => expressionContext.localProofs ??=
    [...current.locals.values()].map(item => item.proof);
  const openedGuards = (): GuardFact[] => expressionContext.openedGuards ??=
    openedGuardFacts(kernel, current.assumptions, current.locals.values(), visibility);
  const instances = (): InstanceProver => expressionContext.instanceProver ??= prepareInstanceProver(
    kernel, visibleInstanceNames(kernel, scope), current.assumptions, localProofs(), {}, visibility);
  const inferredEvidence = (wanted: Formula): Proof | undefined => {
    const local = [...current.locals.values()].find(item => formulaEquals(item.formula, wanted));
    if (local) return local.proof;
    const assumed = current.assumptions.find(item => formulaEquals(item, wanted));
    if (assumed) return assume(assumed);
    const opened = openedGuards().find(item => formulaEquals(item.formula, wanted));
    if (opened) return opened.proof;
    // An equation between endpoints, such as the composability condition
    // dom(g) = cod(f) under the guards g : b ⟶ c and f : a ⟶ b, follows by
    // congruence closure over the opened guards and the local equalities.
    if (wanted.tag === "eq" && openedGuards().length) {
      try { return proveCongruence(kernel, wanted, current.assumptions, [...localProofs(), ...openedGuards().map(item => item.proof)]); }
      catch { return undefined; }
    }
    if (wanted.tag !== "pred" || wanted.args.length === 0) return undefined;
    try {
      const instance = instances().prove(wanted.args.at(-1)!, wanted.pred, wanted.args.slice(0, -1));
      if (instance) return instance;
    } catch (error) {
      if (error instanceof InstanceResolutionError || error instanceof InstanceResolutionLimitError) {
        throw new SurfaceError(line, error.message);
      }
      throw error;
    }
    return proveRefinement(kernel, wanted.args.at(-1)!, wanted.pred, wanted.args.slice(0, -1),
      current.assumptions, localProofs(), visibility);
  };
  const explicitEvidence = (argument: string, wanted: Formula): Proof | undefined => {
    if (argument === "assumption") return inferredEvidence(wanted);
    try {
      const evidence = parseProofExpression(kernel, argument, current, variables, line, scope,
        { ...expressionContext, expectedConclusion: wanted, applicationGoal: false });
      return formulaEquals(kernel.checkProof(evidence, current.assumptions), wanted) ? evidence : undefined;
    } catch {
      return undefined;
    }
  };
  const remaining = autoDischarge ? ["*"] : reorderedPremises ?? [...supplied];
  let inferredGuards = 0;
  // Binder types are checked implications in the kernel statement,
  // but their evidence is reconstructible from Tau once the explicit terms
  // are known. Preserve a supplied proof when it matches, and
  // otherwise fill only the generated leading guards. A supplied list fills
  // every leading guard, whichever position its named guard evidence takes.
  while (generatedGuardCount > 0 && (supplied.length > 0 || inferGuardsWithoutWith || inferredApplyGuards)) {
    const formula = kernel.checkProof(proof, current.assumptions);
    if (formula.tag !== "imp") break;
    const explicit = remaining[0] && remaining[0] !== "*"
      ? explicitEvidence(remaining[0]!, formula.left) : undefined;
    const evidence = explicit ?? inferredEvidence(formula.left);
    if (!evidence) break;
    if (explicit) remaining.shift();
    else inferredGuards += 1;
    proof = impElim(proof, evidence);
    generatedGuardCount -= 1;
    consumedPremise();
  }
  // An implicit theorem parameter is a request to reconstruct the routine
  // application boundary. Existing Cumulus proofs rely on that boundary also
  // consuming immediately available named requirements after the generated
  // soft-type guard (for example membership.successor_forward{n := k} at x).
  if (inferGuardsWithoutWith && supplied.length === 0) {
    for (;;) {
      const formula = kernel.checkProof(proof, current.assumptions);
      if (formula.tag !== "imp") break;
      const evidence = inferredEvidence(formula.left);
      if (!evidence) break;
      proof = impElim(proof, evidence);
      consumedPremise();
    }
  }

  // A bare apply discharges the section hypotheses in scope among the
  // declared requirements of the applied theorem, as `with *` does, so a
  // section theorem applied under its own hypotheses opens only the goals
  // they leave; the first requirement that is not one, and everything
  // after it, stay open as goals.
  if (inferredApplyGuards && remainingPremises !== undefined) {
    const hypotheses = scope.sectionHypotheses?.() ?? [];
    while (remainingPremises > 0 && hypotheses.length) {
      const formula = kernel.checkProof(proof, current.assumptions);
      if (formula.tag !== "imp") break;
      const wanted = formula.left;
      if (!hypotheses.some(item => formulaEquals(item, wanted)) ||
          !current.assumptions.some(item => formulaEquals(item, wanted))) break;
      proof = impElim(proof, assume(wanted));
      consumedPremise();
    }
  }

  let pendingDirection = direction;
  const projectDirection = (): void => {
    if (!pendingDirection) return;
    const formula = kernel.checkProof(proof, current.assumptions);
    if (formula.tag !== "iff") return;
    proof = pendingDirection === "forward" ? iffElimLeft(proof) : iffElimRight(proof);
    pendingDirection = undefined;
    // Selecting an equivalence direction adds precisely its antecedent,
    // even when the selected consequent is itself an implication or negation.
    if (remainingPremises !== undefined) remainingPremises += 1;
  };
  const consume = (argument: string): void => {
    projectDirection();
    if (argument === "*") {
      let consumed = 0;
      for (;;) {
        projectDirection();
        if (remainingBinders === 0 && remainingPremises === 0) break;
        const formula = kernel.checkProof(proof, current.assumptions);
        if (formula.tag !== "imp") break;
        if (autoDischarge && expressionContext.expectedConclusion && formulaEquals(formula, expressionContext.expectedConclusion)) break;
        const evidence = inferredEvidence(formula.left);
        if (!evidence) {
          throw new SurfaceError(line, autoDischarge
            ? `${baseName} needs evidence for ${formatFormula(formula.left)}; supply it with \`with\``
            : `with * cannot find evidence for ${formatFormula(formula.left)}`);
        }
        proof = impElim(proof, evidence);
        consumedPremise();
        consumed += 1;
      }
      // A known declaration boundary also permits an already-complete application.
      if (consumed === 0 && inferredGuards === 0 && !autoDischarge &&
          !(remainingBinders === 0 && remainingPremises === 0)) {
        throw new SurfaceError(line, `${baseName} has no inferred premises for with *`);
      }
      inferredGuards = 0;
      return;
    }
    const formula = kernel.checkProof(proof, current.assumptions);
    if (formula.tag === "forall") {
      // Evidence in a binder's position instantiates the leading binders by
      // matching the first premise beneath them, so a mixed list such as
      // `transitive with hbInY, z, hzInB` needs no at list.
      const evidence = argument === "assumption" ? undefined : evidenceFormula(argument);
      if (evidence) {
        const names = new Set<string>();
        let pattern: Formula = formula;
        while (pattern.tag === "forall") { names.add(pattern.variable); pattern = pattern.body; }
        const candidate = new Map<string, Term>();
        if (pattern.tag === "imp" && matchNamedPremise(pattern.left, evidence, names, candidate) && candidate.size === names.size) {
          let instantiated: Formula = formula;
          while (instantiated.tag === "forall") {
            proof = forallElim(proof, candidate.get(instantiated.variable)!);
            instantiated = instantiated.body;
            remainingBinders = Math.max(0, remainingBinders - 1);
          }
          consume(argument);
          return;
        }
      }
      try {
        proof = forallElim(proof, parseTerm(argument, kernel, variables, line, scope));
      } catch (error) {
        // A fact named where a binder wants a term: say which entries of the
        // list are facts and which are terms, and where the terms belong.
        if (!(error instanceof SurfaceError) || evidenceFormula(argument) === undefined) throw error;
        const entries = supplied.filter(item => item !== "*");
        const facts = entries.filter(item => evidenceFormula(item) !== undefined);
        const terms = entries.filter(item => evidenceFormula(item) === undefined);
        const list = (items: readonly string[], kind: string): string =>
          `${items.map(item => `${item} (${entries.indexOf(item) + 1})`).join(", ")} ${items.length === 1 ? "is a" : "are"} ${kind}${items.length === 1 ? "" : "s"}`;
        throw new SurfaceError(line,
          `${argument} is a local fact, not a variable in scope, and ${baseName} takes a term for its binder ${formula.variable} here; ` +
          `in the with list ${list(facts, "fact")}${terms.length ? ` and ${list(terms, "term")}` : ""}; ` +
          `write the terms in an at list: ${baseName} at ${terms.join(", ") || "…"} with ${facts.join(", ")}`);
      }
      remainingBinders = Math.max(0, remainingBinders - 1);
      return;
    }
    if (formula.tag === "imp") {
      // A carrier guard such as Nat(n + m) is routine: when the supplied
      // entry is not evidence for it, the guard is discharged from the
      // context or by soft typing and the entry goes to the premise after it.
      const dischargeGuard = (): boolean => {
        if (formula.left.tag !== "pred" || formula.left.args.length === 0) return false;
        const guard = inferredEvidence(formula.left);
        if (!guard) return false;
        proof = impElim(proof, guard);
        consumedPremise();
        return true;
      };
      let evidence: Proof | undefined;
      try {
        evidence = argument === "assumption"
          ? inferredEvidence(formula.left)
          : parseProofExpression(kernel, argument, current, variables, line, scope,
            { ...expressionContext, expectedConclusion: formula.left, applicationGoal: false });
      } catch (error) {
        if (!(error instanceof SurfaceError) || argument === "assumption" || !dischargeGuard()) throw error;
        consume(argument);
        return;
      }
      if (!evidence) throw new SurfaceError(line,
        `no assumption matches ${formatFormula(formula.left)}`);
      const actual = kernel.checkProof(evidence, current.assumptions);
      if (!formulaEquals(actual, formula.left)) {
        const bridged = bridgeDefinition(kernel, scope, line, evidence, actual, formula.left, current.assumptions, current.locals);
        if (bridged) { proof = impElim(proof, bridged); consumedPremise(); return; }
        if (argument !== "assumption" && dischargeGuard()) { consume(argument); return; }
        // The entry and those that follow it may be the conjuncts of the
        // premise, supplied in order; they combine as ⟨a, b⟩ does.
        const parts = formula.left.tag === "and" ? conjunctionParts(formula.left) : [];
        const followers = remaining.slice(0, parts.length - 1);
        if (parts.length > 1 && argument !== "assumption" && followers.length === parts.length - 1 &&
            followers.every(item => item !== "*")) {
          let combined: Proof | undefined;
          try {
            combined = parseProofExpression(kernel, `⟨${[argument, ...followers].join(", ")}⟩`, current, variables, line, scope,
              { ...expressionContext, expectedConclusion: formula.left, applicationGoal: false });
            if (!formulaEquals(kernel.checkProof(combined, current.assumptions), formula.left)) combined = undefined;
          } catch { combined = undefined; }
          if (combined) {
            remaining.splice(0, followers.length);
            proof = impElim(proof, combined);
            consumedPremise();
            return;
          }
        }
        throw new SurfaceError(line,
          `${argument} proves ${formatFormula(actual)}, but application needs ${formatFormula(formula.left)}`);
      }
      proof = impElim(proof, evidence);
      consumedPremise();
      return;
    }
    // A derived predicate fact, such as the b ⊆ y that a transitivity
    // fact yields, takes further arguments through its definition too.
    const unfolded = throughDefinition({ formula, proof });
    if (unfolded) {
      proof = unfolded;
      remainingPremises = undefined;
      consume(argument);
      return;
    }
    throw new SurfaceError(line, `${baseName} has no remaining argument at ${argument}`);
  };

  while (remaining.length) consume(remaining.shift()!);
  // Carrier guards left after an at list or a with list are routine too:
  // they are discharged from the context or by soft typing while that
  // succeeds, so `choose.factorial at n with n` is the equation and
  // `add.commutative at a, b` needs no `with *` for its guards. A guard
  // that cannot be discharged stays, and apply leaves it as a goal.
  if ((atMatch[2] || supplied.length > 0) && starIndex < 0) {
    for (;;) {
      const formula = kernel.checkProof(proof, current.assumptions);
      if (formula.tag !== "imp" || formula.left.tag !== "pred" || formula.left.args.length === 0) break;
      if (!routineGuardPredicate(kernel, formula.left.pred)) break;
      const guard = inferredEvidence(formula.left);
      if (!guard) break;
      proof = impElim(proof, guard);
      consumedPremise();
    }
  }
  projectDirection();
  if (pendingDirection && expressionContext.applicationGoal && remainingBinders === 0) {
    // Project the equivalence beneath still-open requirements. The temporary
    // assumptions are discharged again, so apply receives subgoals.
    let formula = kernel.checkProof(proof, current.assumptions);
    const premises: Formula[] = [];
    while (formula.tag === "imp") {
      premises.push(formula.left);
      formula = formula.right;
    }
    if (formula.tag === "iff") {
      for (const premise of premises) proof = impElim(proof, assume(premise));
      proof = pendingDirection === "forward" ? iffElimLeft(proof) : iffElimRight(proof);
      for (let i = premises.length - 1; i >= 0; i--) proof = impIntro(premises[i]!, proof);
      pendingDirection = undefined;
    }
  }
  if (pendingDirection) throw new SurfaceError(line, `${baseName} is not an equivalence`);
  return proof;
}

function resolveProof(kernel: Kernel, rawName: string, line: number, scope: SurfaceScope, affinity = false): Proof {
  const symbol = surfaceSymbol(rawName);
  const notationTarget = QUALIFIED_IDENTIFIER.test(symbol)
    ? undefined
    : visibleInfixNotations(kernel, scope, line).get(rawName)?.target;
  const name = notationTarget ?? resolveOptional(symbol, scope, candidate =>
    kernel.theorems.has(candidate) || kernel.axioms.has(candidate) ||
    kernel.definitions.has(candidate) || Boolean(definitionProperty(kernel, candidate)), affinity);
  if (name) {
    if (kernel.theorems.has(name)) return theorem(name);
    if (kernel.axioms.has(name)) return axiom(name);
    if (kernel.definitions.has(name)) return preferredDefinitionProof(name, kernel.definitions.get(name)!);
    const property = definitionProperty(kernel, name);
    if (property) return definition(property.definition, property.property);
  }
  throw new SurfaceError(line, describeUnknownProof(kernel, rawName, scope));
}

/** The note `ring` adds when the goal divides by a numeral, which it reads
 * as an atom. */
function quotientAtomNote(kernel: Kernel, goal: Formula, scope: SurfaceScope): string {
  const divide = resolveOptional("realDiv", scope, candidate => kernel.functions.has(candidate));
  if (!divide) return "";
  let found = false;
  const visit = (term: Term): void => {
    if (found || term.tag !== "app") return;
    if (term.fn.endsWith(".Algebra.call2") && term.args.length === 3 && termEquals(term.args[0]!, app(divide))) { found = true; return; }
    term.args.forEach(visit);
  };
  if (goal.tag === "eq") { visit(goal.left); visit(goal.right); }
  return found ? "; a quotient t / k is an atom for ring: for a linear goal use linarith, which reads t / k as " +
    "the k-th part of t, or rewrite with realDiv.eq_mul_inv or a named constant such as oneHalf" : "";
}

/** A library index consulted for the module declaring a name the loaded
 * environment does not know, installed by the loader that knows the roots. */
let libraryDeclarationLocator: ((short: string) => readonly { readonly module: string; readonly name: string }[]) | undefined;
export function setLibraryDeclarationLocator(
  locator?: (short: string) => readonly { readonly module: string; readonly name: string }[],
): void {
  libraryDeclarationLocator = locator;
}

/**
 * `unknown proof X`, and where X is declared when some module declares it:
 * a loaded module outside the import closure, read off the surface
 * environment, or a library module the locator knows.
 */
function describeUnknownProof(kernel: Kernel, rawName: string, scope: SurfaceScope): string {
  const symbol = surfaceSymbol(rawName).replace(/\.(forward|backward)$/u, "");
  const base = `unknown proof ${rawName}`;
  const environment = surfaceEnvironments.get(kernel);
  const declared = (name: string): boolean => name === symbol || name.endsWith(`.${symbol}`);
  const loaded = environment ? [...environment.modules.values()].flatMap(module =>
    [...module.theorems, ...module.definitions].filter(declared).map(name => ({ module: module.name, name }))) : [];
  const visible = (module: string): boolean => module === scope.moduleName || Boolean(scope.visibleModules?.has(module));
  const outside = loaded.filter(item => !visible(item.module));
  if (outside.length) {
    return `${base}; ${outside.map(item => `${item.name} is declared in module ${item.module}`).join(", ")}, ` +
      `which this module does not import`;
  }
  if (loaded.length) return `${base}; did you mean ${loaded.map(item => item.name).join(" or ")}?`;
  const library = libraryDeclarationLocator?.(symbol) ?? [];
  if (library.length) {
    return `${base}; the library declares ${library.map(item => `${item.name} in module ${item.module}`).join(", ")}, ` +
      `which this module does not import`;
  }
  return base;
}

// A property is a suffix of one definition name: direct map probes replace
// the former full-definition scan, including on unsuccessful lookups.
function definitionProperty(kernel: Kernel, name: string): { definition: string; property: string } | undefined {
  for (let dot = name.lastIndexOf("."); dot >= 0; dot = name.lastIndexOf(".", dot - 1)) {
    const base = name.slice(0, dot), property = name.slice(dot + 1);
    if (kernel.definitions.get(base)?.properties.has(property)) return { definition: base, property };
  }
  return undefined;
}

interface SuggestedApplication {
  /** Ordering key of an exact? result: premises discharged, plus a penalty for a name only reachable as _root_. */
  readonly rank?: number;
  readonly command: string;
  readonly proof: Proof;
  readonly premises: readonly Formula[];
  /** The declaration applied (a full name) or the local fact used. */
  readonly name: string;
  readonly reference: string;
  readonly local?: boolean;
  readonly arguments: readonly Term[];
  /** How exact? discharged each premise, parallel to the premises it closed. */
  readonly evidence?: readonly { readonly formula: Formula; readonly text: string; readonly routine: boolean }[];
}

/** Where a named proof comes from, for a suggestion's structured record. */
function suggestionSource(kernel: Kernel, name: string): TacticSuggestion["source"] {
  const base = name.replace(/\.(forward|backward)$/, "");
  for (const candidate of [name, base]) {
    if (kernel.theorems.has(candidate)) return "theorem";
    if (kernel.axioms.has(candidate)) return "axiom";
  }
  return "definition";
}

function describeSuggestion(kernel: Kernel, item: SuggestedApplication, tactic: "exact" | "apply"): TacticSuggestion {
  return {
    command: item.command, tactic, name: item.name, reference: item.reference,
    source: item.local ? "local" : suggestionSource(kernel, item.name),
    arguments: item.arguments,
    premises: item.evidence
      ? item.evidence.map(entry => ({ formula: entry.formula, evidence: entry.text, routine: entry.routine }))
      : item.premises.map(formula => ({ formula })),
    closes: tactic === "exact" || item.premises.length === 0,
  };
}

function exactSuggestions(kernel: Kernel, current: TacticGoal, scope: SurfaceScope): readonly SuggestedApplication[] {
  const result: SuggestedApplication[] = [];
  for (const [name, local] of current.locals) {
    if (formulaEquals(local.formula, current.goal)) result.push({ command: `exact ${name}`, proof: local.proof, premises: [], name, reference: name, local: true, arguments: [] });
  }
  for (const candidate of orderedProofsForSuggestions(kernel, scope)) {
    const application = suggestApplication(kernel, candidate, current.goal, current.assumptions, scope,
      [...current.locals.values()].map(item => item.formula));
    if (!application) continue;
    let proof = application.proof;
    let solved = true;
    const spelled: string[] = [];
    const discharged: { formula: Formula; text: string; routine: boolean }[] = [];
    let routine = 0;
    for (const premise of application.premises) {
      const evidence = premiseEvidence(kernel, current, premise, true, scopeVisibility(kernel, scope));
      if (!evidence) { solved = false; break; }
      proof = impElim(proof, evidence.proof);
      spelled.push(evidence.text);
      discharged.push({ formula: premise, text: evidence.text, routine: evidence.routine });
      if (evidence.routine) routine += 1;
    }
    if (solved && formulaEquals(kernel.checkProof(proof, current.assumptions), current.goal)) {
      // The premises are written out as the search discharged them: a local
      // fact by name, a specialized one as `(fact at terms with guards)`, and
      // a routine typing fact as `assumption`.
      const command = application.command.replace(/^apply /, "exact ") + (spelled.length ? ` with ${spelled.join(", ")}` : "");
      // A result whose premises are the mathematics in scope ranks above one
      // the typing closes for it, and a short name above a _root_ one.
      result.push({ command, proof, premises: [], name: application.name, reference: application.reference, arguments: application.arguments,
        evidence: discharged, rank: routine * 4 + spelled.length + (command.includes("_root_.") ? 16 : 0) });
    }
    if (result.length >= 24) break;
  }
  // A result that needs no premises and has a short name comes first, and a
  // theorem only reachable as `_root_.…` is offered only when nothing the
  // module can name closes the goal.
  const ranked = result.sort((left, right) => (left.rank ?? 0) - (right.rank ?? 0));
  const reachable = ranked.filter(item => !item.command.includes("_root_."));
  return (reachable.length ? reachable : ranked).slice(0, 8).map(({ rank: _rank, ...item }) => item);
}

/**
 * Evidence for a premise of a suggested application, with how it is written:
 * a local fact by name, an assumption or a routine typing fact as
 * `assumption`, or, one level deep, a universally quantified local fact
 * specialized at the terms that match and its guards discharged in turn.
 */
function premiseEvidence(
  kernel: Kernel, current: TacticGoal, premise: Formula, specialize: boolean, visibility: ScopeVisibility | undefined,
): { proof: Proof; text: string; routine: boolean } | undefined {
  for (const [name, local] of current.locals) {
    if (formulaEquals(local.formula, premise)) return { proof: local.proof, text: name, routine: false };
  }
  const assumption = current.assumptions.find(item => formulaEquals(item, premise));
  if (assumption) return { proof: assume(assumption), text: "assumption", routine: true };
  if (specialize) {
    for (const [name, local] of current.locals) {
      const variables: string[] = [];
      let body = local.formula;
      while (body.tag === "forall") { variables.push(body.variable); body = body.body; }
      if (variables.length === 0) continue;
      const guards: Formula[] = [];
      for (;;) {
        const attempt = new Map<string, Term>();
        if (matchSuggestionFormula(body, premise, new Set(variables), attempt) && variables.every(item => attempt.has(item))) {
          const terms = variables.map(item => attempt.get(item)!);
          let proof: Proof = at(local.proof, ...terms);
          const spelled: string[] = [];
          let discharged = true;
          for (const guard of guards) {
            const evidence = premiseEvidence(kernel, current, substituteManySurface(guard, attempt), false, visibility);
            if (!evidence) { discharged = false; break; }
            proof = impElim(proof, evidence.proof);
            spelled.push(evidence.text);
          }
          if (!discharged) break;
          try {
            if (!formulaEquals(kernel.checkProof(proof, current.assumptions), premise)) break;
          } catch { break; }
          const text = `(${name} at ${terms.map(formatTerm).join(", ")}${spelled.length ? ` with ${spelled.join(", ")}` : ""})`;
          return { proof, text, routine: false };
        }
        if (body.tag !== "imp") break;
        guards.push(body.left);
        body = body.right;
      }
    }
  }
  if (premise.tag === "pred" && premise.args.length) {
    const proof = proveRefinement(kernel, premise.args.at(-1)!, premise.pred, premise.args.slice(0, -1),
      current.assumptions, [...current.locals.values()].map(item => item.proof), visibility);
    if (proof) return { proof, text: "assumption", routine: true };
  }
  return undefined;
}

function applySuggestions(kernel: Kernel, current: TacticGoal, scope: SurfaceScope): readonly SuggestedApplication[] {
  const result: SuggestedApplication[] = [];
  for (const candidate of orderedProofsForSuggestions(kernel, scope)) {
    const application = suggestApplication(kernel, candidate, current.goal, current.assumptions, scope);
    if (application) result.push(application);
    if (result.length >= 8) break;
  }
  return result;
}

function orderedTheoremsForSuggestions(kernel: Kernel, scope: SurfaceScope): readonly [string, Formula][] {
  const entries = [...kernel.theorems].filter(([name]) => visibleDeclaration(name, scope));
  if (!scope.moduleName) return entries;
  return entries.sort(([left], [right]) => {
    const leftLocal = scope.resolution?.owner(left) === scope.moduleName;
    const rightLocal = scope.resolution?.owner(right) === scope.moduleName;
    return leftLocal === rightLocal ? 0 : leftLocal ? -1 : 1;
  });
}

interface SuggestionProof {
  readonly name: string;
  readonly proof: Proof;
  readonly formula: Formula;
  readonly instantiate?: (arguments_: readonly Term[]) => Proof;
}

function orderedProofsForSuggestions(kernel: Kernel, scope: SurfaceScope): readonly SuggestionProof[] {
  const entries: SuggestionProof[] = [];
  for (const [name, formula] of kernel.theorems)
    if (visibleDeclaration(name, scope)) entries.push(...expandSuggestionProof(name, theorem(name), formula));
  for (const [name, formula] of kernel.axioms) {
    if (!name.startsWith("sorry.") && visibleDeclaration(name, scope)) entries.push(...expandSuggestionProof(name, axiom(name), formula));
  }
  for (const [name, record] of kernel.definitions) {
    if (!visibleDeclaration(name, scope)) continue;
    for (const [property, formula] of record.properties) {
      const proof = definition(name, property);
      const propertyName = `${name}.${property}`;
      entries.push(...expandSuggestionProof(propertyName, proof, formula));
    }
  }
  if (!scope.moduleName) return entries;
  return entries.sort((left, right) => {
    const leftLocal = scope.resolution?.owner(left.name) === scope.moduleName;
    const rightLocal = scope.resolution?.owner(right.name) === scope.moduleName;
    return leftLocal === rightLocal ? 0 : leftLocal ? -1 : 1;
  });
}

function expandSuggestionProof(name: string, proof: Proof, formula: Formula): readonly SuggestionProof[] {
  const entries: SuggestionProof[] = [{ name, proof, formula }];
  const variables: string[] = [];
  let conclusion = formula;
  while (conclusion.tag === "forall") {
    variables.push(conclusion.variable);
    conclusion = conclusion.body;
  }
  if (conclusion.tag !== "iff") return entries;
  const direction = (
    suffix: "forward" | "backward", eliminate: (equivalence: Proof) => Proof, left: Formula, right: Formula,
  ): SuggestionProof => {
    let directedFormula = imp(left, right);
    for (const variable of [...variables].reverse()) {
      directedFormula = forall(variable, directedFormula);
    }
    return {
      name: `${name}.${suffix}`, proof, formula: directedFormula,
      instantiate: arguments_ => eliminate(arguments_.length ? at(proof, ...arguments_) : proof),
    };
  };
  entries.push(direction("forward", iffElimLeft, conclusion.left, conclusion.right));
  entries.push(direction("backward", iffElimRight, conclusion.right, conclusion.left));
  return entries;
}

function rewriteSuggestions(
  kernel: Kernel, current: TacticGoal, scope: SurfaceScope,
): readonly { command: string; rewrite: ReturnType<typeof rewriteGoal>; suggestion: TacticSuggestion }[] {
  const result: { command: string; rewrite: ReturnType<typeof rewriteGoal>; suggestion: TacticSuggestion }[] = [];
  const facts = [...current.locals.values()].map(item => item.proof);
  const candidates: { name: string; proof: Proof; formula: Formula; local?: boolean }[] = [];
  for (const [name, local] of current.locals) candidates.push({ name, proof: local.proof, formula: local.formula, local: true });
  for (const [name, formula] of orderedTheoremsForSuggestions(kernel, scope)) {
    candidates.push({ name, proof: theorem(name), formula });
  }
  for (const [name, record] of kernel.definitions) {
    for (const property of record.properties.keys()) {
      const proof = definition(name, property);
      candidates.push({ name: `${name}.${property}`, proof, formula: kernel.checkProof(proof) });
    }
  }
  // A rewrite that closes the goal comes first, then the ones that shrink
  // it most; a direction whose pattern is a bare variable matches every
  // term and is never a suggestion (`← union.singleton` would wrap any term
  // in ⋃{·}).
  const closes = (goal: Formula): boolean => (goal.tag === "eq" && termEquals(goal.left, goal.right)) ||
    (goal.tag === "iff" && formulaEquals(goal.left, goal.right)) ||
    current.assumptions.some(item => formulaEquals(item, goal)) ||
    [...current.locals.values()].some(item => formulaEquals(item.formula, goal));
  const scored: { command: string; rewrite: ReturnType<typeof rewriteGoal>; score: number; suggestion: TacticSuggestion }[] = [];
  for (const candidate of candidates) {
    let conclusion = candidate.formula;
    const bound = new Set<string>();
    while (conclusion.tag === "forall") { bound.add(conclusion.variable); conclusion = conclusion.body; }
    while (conclusion.tag === "imp") conclusion = conclusion.right;
    if (conclusion.tag !== "eq") continue;
    for (const reverse of [false, true]) {
      const pattern = reverse ? conclusion.right : conclusion.left;
      if (pattern.tag === "var" && bound.has(pattern.name)) continue;
      try {
        const rewrite = rewriteGoal(kernel, current.goal, candidate.proof, current.assumptions, facts, reverse, false, undefined, scopeVisibility(kernel, scope));
        if (formulaEquals(rewrite.goal, current.goal)) continue;
        const reference = candidate.local ? candidate.name : surfaceReference(candidate.name, kernel, scope);
        const closed = closes(rewrite.goal);
        const score = closed ? 0 : 1 + formulaSize(rewrite.goal);
        const command = `rw ${reverse ? "← " : ""}${reference}`;
        scored.push({ command, rewrite, score, suggestion: {
          command, tactic: "rw", name: candidate.name, reference,
          source: candidate.local ? "local" : suggestionSource(kernel, candidate.name),
          arguments: [], premises: [], closes: closed, reverse, goal: rewrite.goal,
        } });
      } catch {}
      if (scored.length >= 48) break;
    }
    if (scored.length >= 48) break;
  }
  scored.sort((left, right) => left.score - right.score);
  for (const { command, rewrite, suggestion } of scored.slice(0, 8)) result.push({ command, rewrite, suggestion });
  return result;
}

/** The number of nodes in a formula, the measure `rw?` ranks its suggestions by. */
function formulaSize(formula: Formula): number {
  const termSize = (term: Term): number => term.tag === "app" ? 1 + term.args.reduce((sum, item) => sum + termSize(item), 0) : 1;
  switch (formula.tag) {
    case "bottom": return 1;
    case "eq": return 1 + termSize(formula.left) + termSize(formula.right);
    case "pred": return 1 + formula.args.reduce((sum, item) => sum + termSize(item), 0);
    case "imp": case "and": case "or": case "iff": return 1 + formulaSize(formula.left) + formulaSize(formula.right);
    case "forall": case "exists": return 1 + formulaSize(formula.body);
  }
}

function suggestApplication(
  kernel: Kernel, candidate: SuggestionProof, goal: Formula, assumptions: readonly Formula[], scope: SurfaceScope,
  localFormulas: readonly Formula[] = [],
): SuggestedApplication | undefined {
  const { name, formula: statement } = candidate;
  const reference = surfaceReference(name, kernel, scope);
  // Test the authored statement before exposing implication premises. Negation
  // is represented as P -> false, so peeling first would miss an exact theorem
  // such as `omega.infinite : not Finite(omega)`.
  if (formulaEquals(statement, goal)) {
    try {
      if (formulaEquals(kernel.checkProof(candidate.proof, assumptions), goal)) {
        return { command: `apply ${reference}`, proof: candidate.proof, premises: [], name, reference, arguments: [] };
      }
    } catch {}
  }
  const variables: string[] = [];
  let conclusion = statement;
  while (conclusion.tag === "forall") { variables.push(conclusion.variable); conclusion = conclusion.body; }
  const premises: Formula[] = [];
  const matchVariables = new Set(variables);
  let substitution: Map<string, Term> | undefined;
  for (;;) {
    const attempt = new Map<string, Term>();
    if (matchSuggestionFormula(conclusion, goal, matchVariables, attempt)) {
      // A variable the conclusion leaves open, the carrier `A` of
      // `f : A → B → x ∈ A → f(x) ∈ B`, is fixed by a premise that matches
      // a fact in scope.
      for (const premise of premises) {
        if (variables.every(variable => attempt.has(variable))) break;
        for (const fact of [...localFormulas, ...assumptions]) {
          const extended = new Map(attempt);
          if (matchSuggestionFormula(premise, fact, matchVariables, extended)) { for (const [k, v] of extended) attempt.set(k, v); break; }
        }
      }
      if (variables.every(variable => attempt.has(variable))) { substitution = attempt; break; }
    }
    if (conclusion.tag !== "imp") return undefined;
    premises.push(conclusion.left);
    conclusion = conclusion.right;
  }
  const arguments_ = variables.map(variable => substitution.get(variable)!);
  const proof = candidate.instantiate?.(arguments_) ?? at(candidate.proof, ...arguments_);
  const instantiatedPremises = premises.map(premise => substituteManySurface(premise, substitution));
  const expected = instantiatedPremises.reduceRight<Formula>((result, premise) => imp(premise, result), goal);
  try {
    if (!formulaEquals(kernel.checkProof(proof, assumptions), expected)) return undefined;
  } catch {
    return undefined;
  }
  const signature = surfaceEnvironments.get(kernel)?.signatures.get(name);
  const displayedArguments = signature?.parameters.length === arguments_.length
    ? arguments_.filter((_, index) => !signature.parameters[index]!.implicit)
    : arguments_;
  return {
    command: `apply ${reference}${displayedArguments.length ? ` at ${displayedArguments.map(formatTerm).join(", ")}` : ""}`,
    proof,
    premises: instantiatedPremises,
    name, reference, arguments: displayedArguments,
  };
}

function surfaceReference(name: string, kernel: Kernel, scope: SurfaceScope): string {
  const parts = name.split(".");
  for (let length = 1; length <= parts.length; length += 1) {
    const candidate = parts.slice(-length).join(".");
    try {
      if (resolveOptional(candidate, scope, item => hasNamedProof(kernel, item)) === name) return candidate;
    } catch (error) {
      if (!(error instanceof SurfaceError && error.message.includes("ambiguous name"))) throw error;
    }
  }
  return `_root_.${name}`;
}

function hasNamedProof(kernel: Kernel, name: string): boolean {
  if (kernel.theorems.has(name) || kernel.axioms.has(name) || kernel.definitions.has(name)) return true;
  return Boolean(definitionProperty(kernel, name));
}

function substituteManySurface(formula: Formula, substitution: ReadonlyMap<string, Term>): Formula {
  let result = formula;
  for (const [name, value] of substitution) result = substituteFormula(result, name, value);
  return result;
}

function matchSuggestionTerm(
  pattern: Term, actual: Term, variables: ReadonlySet<string>, substitution: Map<string, Term>,
): boolean {
  if (pattern.tag === "var" && variables.has(pattern.name)) {
    const previous = substitution.get(pattern.name);
    if (previous) return termEquals(previous, actual);
    substitution.set(pattern.name, actual);
    return true;
  }
  if (pattern.tag !== actual.tag) return false;
  if (pattern.tag === "var" && actual.tag === "var") return pattern.name === actual.name;
  if (pattern.tag === "nat" && actual.tag === "nat") return pattern.value === actual.value;
  return pattern.tag === "app" && actual.tag === "app" && pattern.fn === actual.fn && pattern.args.length === actual.args.length &&
    pattern.args.every((argument, index) => matchSuggestionTerm(argument, actual.args[index]!, variables, substitution));
}

function matchSuggestionFormula(
  pattern: Formula, actual: Formula, variables: ReadonlySet<string>, substitution: Map<string, Term>,
): boolean {
  if (pattern.tag !== actual.tag) return false;
  switch (pattern.tag) {
    case "bottom": return true;
    case "eq": return actual.tag === "eq" && matchSuggestionTerm(pattern.left, actual.left, variables, substitution) &&
      matchSuggestionTerm(pattern.right, actual.right, variables, substitution);
    case "pred": return actual.tag === "pred" && pattern.pred === actual.pred && pattern.args.length === actual.args.length &&
      pattern.args.every((argument, index) => matchSuggestionTerm(argument, actual.args[index]!, variables, substitution));
    case "imp": case "and": case "or": case "iff":
      return actual.tag === pattern.tag && matchSuggestionFormula(pattern.left, actual.left, variables, substitution) &&
        matchSuggestionFormula(pattern.right, actual.right, variables, substitution);
    case "forall": case "exists":
      return actual.tag === pattern.tag && matchSuggestionFormula(
        substituteFormula(pattern.body, pattern.variable, v(actual.variable)), actual.body, variables, substitution);
  }
}

function elaborateCase(
  kernel: Kernel,
  line: SourceLine,
  scriptLines: readonly SourceLine[],
  goal: Formula,
  motive: Formula,
  inductionVariable: string,
  outerAssumptions: readonly Formula[],
  requirements: readonly ParsedRequirement[],
  outerBinders: readonly Binder[],
  datatype: DatatypeRecord,
  parameters: readonly Term[],
  scope: SurfaceScope,
): { readonly case: Extract<Proof, { rule: "induction" }>["cases"][number]; readonly trace: TacticTrace } {
  const branch = parseInductionBranch(kernel, line, datatype, scope);
  const branchTerm = app(branch.constructor.name, ...branch.fields.map(v));
  const constructorGoal = substituteFormula(goal, inductionVariable, branchTerm);
  const sugar = branch.successorSugar
    ? successorCasePresentation(kernel, line.number, scope, goal, inductionVariable, branch.fields[0]!, datatype.predicate) : undefined;
  const branchGoal = sugar?.goal ?? constructorGoal;
  const recursive = branch.constructor.recursiveFields.map((fieldIndex, index) => ({
    field: branch.fields[fieldIndex]!, name: branch.hypotheses[index]!,
    formula: substituteFormula(motive, inductionVariable, v(branch.fields[fieldIndex]!)),
  }));
  const inductionAssumptions = branch.fields.flatMap((field, fieldIndex) => {
    const recursiveIndex = branch.constructor.recursiveFields.indexOf(fieldIndex);
    if (recursiveIndex >= 0) {
      const hypothesis = recursive[recursiveIndex]!;
      return [pred(datatype.predicate, ...parameters, v(field)), hypothesis.formula];
    }
    const parameterField = branch.constructor.parameterFields?.find(item => item.field === fieldIndex);
    return parameterField ? [pred("in", v(field), parameters[parameterField.parameter]!)] : [];
  });
  const assumptions = [...inductionAssumptions, ...outerAssumptions];
  const locals = new Map<string, LocalProof>();
  requirements.forEach((requirement, index) => {
    const name = requirement.name ?? `requirement${index + 1}`;
    locals.set(name, { formula: requirement.formula, proof: assume(requirement.formula) });
  });
  recursive.forEach(item => {
    let proof: Proof = assume(item.formula);
    let formula = item.formula;
    for (const assumption of outerAssumptions) {
      if (formula.tag !== "imp" || !formulaEquals(formula.left, assumption)) {
        throw new SurfaceError(line.number, `internal induction motive mismatch for ${item.name}`);
      }
      proof = impElim(proof, assume(assumption));
      formula = formula.right;
    }
    locals.set(item.name, { formula, proof });
  });
  branch.fields.forEach((field, fieldIndex) => {
    const typeFormula = inductionAssumptions.find(formula => formula.tag === "pred" &&
      formula.args.some(argument => argument.tag === "var" && argument.name === field));
    if (typeFormula) {
      let localName = `h_${field}`;
      while (locals.has(localName)) localName += "_";
      locals.set(localName, { formula: typeFormula, proof: assume(typeFormula) });
    }
  });
  try {
    const script = elaborateTacticTheorem(kernel, "", [], [], [], branchGoal, scriptLines, scope, {
      assumptions,
      locals,
      variables: new Set([...outerBinders.map(item => item.name), ...branch.fields]),
    })!;
    return { case: {
      constructor: branch.constructor.name,
      fields: [...branch.fields],
      proof: outerAssumptions.reduceRight<Proof>(
        (result, assumption) => impIntro(assumption, result),
        sugar ? sugar.transport(script.proof) : script.proof,
      ),
    }, trace: script.trace };
  } catch (error) {
    if (error instanceof SurfaceError) throw error;
    throw new SurfaceError(line.number, error instanceof Error ? error.message : String(error));
  }
}

function preparedRingRules(kernel: Kernel, line: number, scope: SurfaceScope): PreparedRewrites {
  let rules = ringPrograms.get(kernel);
  if (rules) return rules;
  rules = prepareRewrites(kernel, resolveRules(kernel, [
    "Grace.Core.Nat.Algebra.add.right_unit",
    "Grace.Core.Nat.Algebra.mul.right_zero",
    "Grace.Core.Nat.Algebra.mul.left_unit",
    "Grace.Core.Nat.Algebra.mul.right_unit",
    "Grace.Core.Nat.Algebra.mul.commutative",
    "Grace.Core.Nat.Algebra.mul.distributes_right",
    "Grace.Core.Nat.Algebra.mul.distributes_left",
    "Grace.Core.Nat.Algebra.mul.associative",
    "Grace.Cumulus.Nat.Core.add.four_shuffle",
  ], line, scope));
  ringPrograms.set(kernel, rules);
  return rules;
}

/** Constant membership from an already checked local ring certificate.
 * Tau cannot infer operation parameters absent from the membership conclusion.
 * Inspect only local evidence, with fixed projections and no recursive search.
 */
/**
 * `m ∈ n` for literal naturals with m < n, decided by simplification with
 * the successor membership laws of the ordinals, as the library proves
 * `2 ∈ 5`; undefined when the goal is not of that shape or the laws are
 * not loaded.
 */
function proveNumeralMembership(
  kernel: Kernel, goal: Formula, current: TacticGoal, line: SourceLine, scope: SurfaceScope,
): Proof | undefined {
  if (goal.tag !== "pred" || goal.pred !== "in" || goal.args.length !== 2) return undefined;
  const member = naturalValue(goal.args[0]!);
  const bound = naturalValue(goal.args[1]!);
  if (member === undefined || bound === undefined || member >= bound) return undefined;
  const laws = ["next.natural", "next.membership"].map(name =>
    resolveOptional(name, scope, candidate => kernel.theorems.has(candidate)) ??
    [...kernel.theorems.keys()].find(candidate => candidate.endsWith(`.${name}`)));
  if (laws.some(law => law === undefined)) return undefined;
  const script = [{ number: line.number, text: `simp [${laws.join(", ")}]`, indent: line.indent + 2 }];
  try {
    const nested = elaborateTacticTheorem(kernel, "", [], [], [], goal, script, scope,
      { assumptions: current.assumptions, locals: current.locals, variables: current.variables });
    return nested?.proof;
  } catch {
    return undefined;
  }
}

function proveRingConstantMembership(kernel: Kernel, goal: Formula,
  assumptions: readonly Formula[], facts: readonly Proof[]): Proof | undefined {
  if (goal.tag !== "pred" || goal.pred !== "in" || goal.args.length !== 2) return undefined;
  const [value, carrier] = goal.args;
  const core = "Grace.Cumulus.Algebra.Ring.Core.";
  const project = (name: string, args: readonly Term[], evidence: Proof): Proof | undefined =>
    kernel.theorems.has(name) ? impElim(at(theorem(name), ...args), evidence) : undefined;
  const candidates = function* () {
    for (const formula of assumptions) yield { formula, proof: assume(formula) };
    for (const proof of facts) yield { formula: kernel.checkProof(proof, assumptions), proof };
  };
  for (const { formula, proof } of candidates()) {
    if (formula.tag !== "pred" || formula.args.length !== 6 ||
        !termEquals(formula.args[0]!, carrier!)) continue;
    const commutative = formula.pred === "Grace.Cumulus.Algebra.Ring.Defs.IsCommRing";
    if (!commutative && formula.pred !== "Grace.Cumulus.Algebra.Foundation.Algebra.IsRing") continue;
    const isZero = termEquals(value!, formula.args[2]!);
    const isOne = termEquals(value!, formula.args[5]!);
    if (!isZero && !isOne) continue;
    const ordinary = commutative ? project(core + "IsCommRing.ring", formula.args, proof) : proof;
    if (!ordinary) continue;
    if (isZero) {
      const result = project(core + "IsRing.zero_in_carrier", formula.args, ordinary);
      if (result) return result;
    }
    if (isOne) {
      const monoid = project(core + "IsRing.multiplicative", formula.args, ordinary);
      const result = monoid && project("Grace.Cumulus.Algebra.Group.Core.IsMonoid.unit_in_carrier",
        [carrier!, formula.args[4]!, formula.args[5]!], monoid);
      if (result) return result;
    }
  }
  return undefined;
}

/** An untrusted polynomial computation accompanied by ordinary ring-law proofs. */
function normalizeCommutativeRing(kernel: Kernel, terms: readonly Term[],
  assumptions: readonly Formula[], facts: readonly Proof[], scope: SurfaceScope, line: number
): readonly { term: Term; proof: Proof }[] | undefined {
  return prepareCommutativeRing(kernel, terms, assumptions, facts, scope, line)?.normalize(terms);
}

// All caches belong to this one fixed kernel/context/carrier. No evidence is
// retained across tactic invocations or changes to assumptions.
function prepareCommutativeRing(kernel: Kernel, terms: readonly Term[],
  assumptions: readonly Formula[], facts: readonly Proof[], scope: SurfaceScope, line: number) {
  // The six-place IsCommRing over separate pieces; the bundled CommRing(R)
  // of a ring structure reaches this path through the instance
  // CommRing.parts, which reads the pieces off the projections.
  const className = resolveOptional("IsCommRing", scope, candidate => kernel.predicates.get(candidate) === 6) ??
    [...kernel.predicates.keys()].find(name => name.endsWith(".IsCommRing") && kernel.predicates.get(name) === 6);
  if (!className) return undefined;
  // A locally constructed ring (for example a polynomial or quotient ring)
  // is checked evidence just like a structure hypothesis. Keep it in this
  // tactic's context-local instance index; do not register it globally.
  const visibility = scopeVisibility(kernel, scope);
  const instances = prepareInstanceProver(kernel, visibleInstanceNames(kernel, scope), assumptions, facts, {}, visibility);
  // A checked `.notation` equation may present an operation through a value
  // function instead of a definitionally equal graph application. Look up only
  // the alias being used; never search the theorem database for rewrites.
  interface NotationBridge { name: string; operation: Term; arity: number }
  const notationBridges = new Map<string, NotationBridge | undefined>();
  const notationBridge = (fn: string): NotationBridge | undefined => {
    if (notationBridges.has(fn)) return notationBridges.get(fn);
    notationBridges.set(fn, undefined);
    const short = `${fn.split(".").at(-1)}.notation`;
    const name = resolveOptional(short, scope, name => kernel.theorems.has(name));
    if (!name) return undefined;
    let statement = kernel.theorems.get(name)!;
    const variables: string[] = [];
    while (statement.tag === "forall") { variables.push(statement.variable); statement = statement.body; }
    while (statement.tag === "imp") statement = statement.right;
    if (statement.tag !== "eq") return undefined;
    for (const [alias, graph] of [[statement.left, statement.right], [statement.right, statement.left]]) {
      if (alias!.tag !== "app" || alias!.fn !== fn || alias!.args.length !== variables.length ||
          !alias!.args.every((arg, i) => arg.tag === "var" && arg.name === variables[i]) ||
          graph!.tag !== "app" || !(graph!.fn.endsWith(".Algebra.call2") || graph!.fn === "apply") ||
          graph!.args.length !== variables.length + 1 || !graph!.args[0] ||
          freeTermVariables(graph!.args[0]).size ||
          !graph!.args.slice(1).every((arg, i) => arg.tag === "var" && arg.name === variables[i])) continue;
      const result = { name, operation: graph!.args[0], arity: variables.length };
      notationBridges.set(fn, result);
      return result;
    }
    return undefined;
  };
  const operations: Term[] = [];
  const seenOperations = new Set<string>();
  // Prefer the shallowest polynomial operations across all goal/equation
  // roots. A depth-first walk of f(-x) = -f(x) would pick the source ring
  // hidden inside f's argument before the target ring governing the equality.
  // Keep deeper operations as fallbacks; this is a linear traversal and does
  // not add proof search or retain evidence across contexts.
  const operationQueue = [...terms];
  for (let index = 0; index < operationQueue.length; index++) {
    const term = operationQueue[index]!;
    if (term.tag !== "app") continue;
    // An operation graph applied to arguments: call2(op, a, b), or a unary
    // operation applied as a function, op(a), with a variable or constant
    // graph. A sequence applied to an index also matches; when no candidate
    // resolves, the alias ranking below still finds the ring.
    if ((term.fn.endsWith(".Algebra.call2") || (term.fn === "apply" && term.args.length === 2 &&
        (term.args[0]!.tag === "var" || (term.args[0]!.tag === "app" && term.args[0]!.args.length === 0)))) && term.args[0]) {
      const key = termCanonical(term.args[0]);
      if (!seenOperations.has(key)) { seenOperations.add(key); operations.push(term.args[0]); }
    }
    const bridge = notationBridge(term.fn);
    if (bridge && bridge.arity === term.args.length) {
      const key = termCanonical(bridge.operation);
      if (!seenOperations.has(key)) { seenOperations.add(key); operations.push(bridge.operation); }
    }
    operationQueue.push(...term.args);
  }
  // A goal written only with a carrier's own numerals and value functions,
  // as realNumeral(2) = realAddValue(1, 1), names no operation graph; the
  // numeral's bridge theorem `<numeral>.numeral` does, through ringNat.
  if (operations.length === 0) {
    const templates = visibleInfixNotationGroups(kernel, scope, line, "function", "numeral").get("_") ?? [];
    const seen = new Set<string>();
    const seed = (term: Term): void => {
      if (term.tag !== "app") return;
      const template = templates.find(item => item.target === term.fn);
      if (template && !seen.has(term.fn)) {
        seen.add(term.fn);
        let statement = kernel.theorems.get(`${term.fn}.numeral`);
        while (statement?.tag === "forall") statement = statement.body;
        while (statement?.tag === "imp") statement = statement.right;
        if (statement?.tag === "eq" && statement.right.tag === "app" && statement.right.args.length === 4 &&
            statement.right.fn.endsWith(".ringNat")) {
          const key = termCanonical(statement.right.args[0]!);
          if (!seenOperations.has(key)) { seenOperations.add(key); operations.push(statement.right.args[0]!); }
        }
      }
      term.args.forEach(seed);
    };
    terms.forEach(seed);
  }
  if (operations.length === 0 && !terms.some(term => term.tag === "app" &&
      [...(kernel.definitions.get(term.fn)?.properties.values() ?? [])].some(property =>
        /\.Algebra\.call[12]"/.test(JSON.stringify(property))))) return undefined;
  let certificate: Proof | undefined;
  for (const operation of operations) {
    for (const position of [1, 3, 4]) {
      const requested: Array<Term | undefined> = Array(6).fill(undefined);
      requested[position] = operation;
      const found = instances.resolve(className, requested);
      if (found) { certificate = found.proof; break; }
    }
    if (certificate) break;
  }
  if (!certificate) {
    const aliases = new Set<string>();
    const collectAliases = (term: Term): void => {
      if (term.tag !== "app") return;
      if (kernel.definitions.has(term.fn)) aliases.add(term.fn);
      term.args.forEach(collectAliases);
    };
    terms.forEach(collectAliases);
    const ranked = [...visibleInstanceNames(kernel, scope)].flatMap(name => {
      const formula = kernel.theorems.get(name);
      if (formula?.tag !== "pred" || formula.pred !== className || formula.args.length !== 6) return [];
      const symbols = [formula.args[1], formula.args[3], formula.args[4]]
        .filter((item): item is Term & { tag: "app" } => item?.tag === "app" && item.args.length === 0)
        .map(item => `"fn":"${item.fn}"`);
      const score = [...aliases].filter(alias => {
        const record = kernel.definitions.get(alias);
        return record && symbols.some(symbol => JSON.stringify([...record.properties.values()]).includes(symbol));
      }).length;
      return score ? [{ name, score }] : [];
    }).sort((left, right) => right.score - left.score);
    if (ranked.length && (ranked.length === 1 || ranked[0]!.score > ranked[1]!.score))
      certificate = theorem(ranked[0]!.name);
    try {
      certificate ??= instances.resolve(className, Array(6).fill(undefined))?.proof;
    } catch (error) {
      // An unconstrained polynomial must not select an arbitrary carrier.
      // Let the natural-number path handle it if several rings are visible.
      if (!(error instanceof InstanceResolutionError)) throw error;
    }
  }
  if (!certificate) {
    const orderedName = resolveOptional("OrderedRing", scope, candidate => kernel.predicates.get(candidate) === 7);
    const projection = resolveOptional("OrderedRing.comm_ring", scope, candidate => kernel.theorems.has(candidate)) ??
      [...kernel.theorems.keys()].find(name => name.endsWith(".OrderedRing.comm_ring"));
    if (orderedName && projection) {
      const requests: Array<Array<Term | undefined>> = [];
      for (const operation of operations) for (const position of [1, 3, 4]) {
        const requested: Array<Term | undefined> = Array(7).fill(undefined);
        requested[position] = operation;
        requests.push(requested);
      }
      if (operations.length === 0) requests.push(Array(7).fill(undefined));
      for (const requested of requests) {
        const ordered = instances.resolve(orderedName, requested);
        if (!ordered) continue;
        const orderedFormula = kernel.checkProof(ordered.proof, assumptions);
        if (orderedFormula.tag !== "pred" || orderedFormula.args.length !== 7) continue;
        certificate = impElim(at(theorem(projection), ...orderedFormula.args), ordered.proof);
        break;
      }
    }
  }
  if (!certificate) return undefined;
  const formula = kernel.checkProof(certificate, assumptions);
  if (formula.tag !== "pred" || formula.args.length !== 6) return undefined;
  const [carrier, add, zero, neg, mul, one] = formula.args as [Term, Term, Term, Term, Term, Term];
  const ringTheoremCache = new Map<string, string | undefined>();
  const ringTheorem = (name: string): string | undefined => {
    if (!ringTheoremCache.has(name)) ringTheoremCache.set(name,
      resolveOptional(name, scope, item => kernel.theorems.has(item)) ??
      [...kernel.theorems.keys()].find(item => item.endsWith(`.${name}`)));
    return ringTheoremCache.get(name);
  };
  const projection = ringTheorem("IsCommRing.ring");
  if (!projection) return undefined;
  const ordinary = impElim(at(theorem(projection), ...formula.args), certificate);
  const call2 = [...kernel.functions.keys()].find(name => name.endsWith(".Algebra.call2"));
  const call1 = "apply";
  if (!call2) return undefined;
  // Compact structural keys retain sharing after AST-interning eviction
  // without serializing each polynomial suffix as a complete source tree.
  // IDs and evidence are local to this fixed carrier and assumption context.
  const termIds = new WeakMap<Term, number>();
  const structuralIds = new Map<string, number>();
  const termId = (term: Term): number => {
    const known = termIds.get(term);
    if (known !== undefined) return known;
    const numeral = term.tag === "nat" || term.tag === "app" &&
      (term.fn === "zero" || term.fn === "succ") ? naturalValue(term) : undefined;
    const shape = numeral !== undefined ? ["nat", numeral.toString()] :
      term.tag === "nat" ? ["nat", term.value] :
      term.tag === "var" ? ["var", term.name] : ["app", term.fn, ...term.args.map(termId)];
    const key = JSON.stringify(shape);
    let id = structuralIds.get(key);
    if (id === undefined) { id = structuralIds.size; structuralIds.set(key, id); }
    termIds.set(term, id);
    return id;
  };
  // Compact proof assembly is untrusted: final equality certificates are
  // still replayed by the kernel and both export checkers.
  const identities = new WeakMap<Term, Proof>();
  const identity = (term: Term): Proof => {
    let proof = identities.get(term);
    if (!proof) { proof = refl(term); identities.set(term, proof); }
    return proof;
  };
  const reverse = (proof: Proof): Proof => proof.rule === "refl" ? proof :
    proof.rule === "symm" ? proof.proof : symm(proof);
  const chain = (first: Proof, ...rest: Proof[]): Proof => {
    const steps = [first, ...rest].filter(proof => proof.rule !== "refl");
    return steps.length ? calc(steps[0]!, ...steps.slice(1)) : first;
  };
  const lift = (fn: string, ...proofs: Proof[]): Proof => {
    if (proofs.every(proof => proof.rule === "refl"))
      return identity(app(fn, ...proofs.map(proof => proof.term)));
    return congr(fn, ...proofs);
  };
  const plus = (a: Term, b: Term): Term => app(call2, add, a, b);
  const times = (a: Term, b: Term): Term => app(call2, mul, a, b);
  const minus = (a: Term): Term => app(call1, neg, a);
  const sum = (term: Term): readonly [Term, Term] | undefined => term.tag === "app" &&
    term.fn === call2 && termEquals(term.args[0]!, add) ? [term.args[1]!, term.args[2]!] : undefined;
  const product = (term: Term): readonly [Term, Term] | undefined => term.tag === "app" &&
    term.fn === call2 && termEquals(term.args[0]!, mul) ? [term.args[1]!, term.args[2]!] : undefined;
  const opposite = (term: Term): Term | undefined => term.tag === "app" &&
    term.fn === call1 && termEquals(term.args[0]!, neg) ? term.args[1] : undefined;
  const refinements = prepareRefinementProver(kernel, assumptions, facts, visibility);
  const memberCache = new Map<number, Proof | undefined>();
  const carrierSoftType = boundedCarrierType(kernel, carrier);
  let localFacts: Map<number, Proof> | undefined;
  const member = (term: Term): Proof | undefined => {
    const key = termId(term);
    if (memberCache.has(key)) return memberCache.get(key);
    const goal = pred("in", term, carrier);
    let proof = assumptions.find(item => formulaEquals(item, goal));
    let result: Proof | undefined = proof ? assume(proof) : undefined;
    if (!result) {
      localFacts ??= new Map(facts.flatMap(item => {
        const statement = kernel.checkProof(item, assumptions);
        return statement.tag === "pred" && statement.pred === "in" && statement.args.length === 2 &&
          termEquals(statement.args[1]!, carrier) ? [[termId(statement.args[0]!), item] as const] : [];
      }));
      result = localFacts.get(key);
    }
    if (!result && termEquals(term, zero)) {
      const name = ringTheorem("IsRing.zero_in_carrier");
      if (name) {
        result = impElim(at(theorem(name), ...formula.args), ordinary);
      }
    }
    if (!result && termEquals(term, one)) {
      const monoid = impElim(at(theorem(ringTheorem("IsRing.multiplicative")!), ...formula.args), ordinary);
      const name = ringTheorem("IsMonoid.unit_in_carrier");
      if (name) result = impElim(at(theorem(name), carrier, mul, one), monoid);
    }
    if (!result && numeralValue(term) !== undefined && term.tag === "app") {
      result = numeralLaw("IsRing.numeral_closed", [term.args[3]!]);
    }
    if (!result) {
      const parts = sum(term) ?? product(term);
      const inner = opposite(term);
      if (parts || inner) {
        const name = ringTheorem(parts ? sum(term) ? "IsRing.add_closed" : "IsRing.mul_closed" :
          "IsRing.neg_closed");
        const premises = parts ? parts.map(member) : [member(inner!)];
        if (name && premises.every(Boolean)) {
          result = at(theorem(name), ...formula.args, ...(parts ?? [inner!]));
          result = impElim(result, ordinary);
          for (const premise of premises) result = impElim(result, premise!);
        }
      }
    }
    if (!result) {
      // Ask Tau for the atom's soft type, then use its checked carrier
      // definition. This avoids requiring users to name x.real, y.real, etc.
      const softType = carrierSoftType;
      const evidence = softType && refinements.prove(term, softType);
      if (softType && evidence) {
        try {
          result = settle(kernel, goal, { using: resolveRules(kernel, [softType], line, scope),
            assumptions, facts: [evidence], fuel: 100, visibility });
        } catch { /* Keep the ordinary checked membership fallbacks. */ }
      }
    }
    if (!result) {
      const alias = unfoldAlias(term);
      const evidence = alias && member(alias.term);
      if (alias && evidence) {
        let variable = "__ring_member";
        const used = new Set([...freeTermVariables(term), ...freeTermVariables(carrier)]);
        while (used.has(variable)) variable += "_";
        result = eqElim(alias.proof, variable, pred("in", v(variable), carrier), evidence, true);
      }
    }
    if (!result) {
      try {
        result = settle(kernel, goal, { using: resolveRules(kernel, ["Real"], line, scope),
          assumptions, facts, fuel: 100, visibility });
      } catch { /* An untyped atom cannot enter the polynomial. */ }
    }
    if (result && !formulaEquals(kernel.checkProof(result, assumptions), goal)) result = undefined;
    memberCache.set(key, result);
    return result;
  };
  interface LawNode { children: Map<number, LawNode>; proof?: Proof }
  const lawCache = new Map<string, LawNode>();
  const specializedLaws = new Map<string, Proof>();
  const law = (name: string, args: readonly Term[]): Proof => {
    let node = lawCache.get(name);
    if (!node) { node = { children: new Map() }; lawCache.set(name, node); }
    for (const arg of args) {
      const key = termId(arg);
      let child = node.children.get(key);
      if (!child) { child = { children: new Map() }; node.children.set(key, child); }
      node = child;
    }
    if (node.proof) return node.proof;
    const theoremName = ringTheorem(name);
    if (!theoremName) throw new Error(`missing checked ring law ${name}`);
    let specialized = specializedLaws.get(theoremName);
    if (!specialized) {
      // Discharge the fixed structure hypothesis once, before substituting
      // polynomial operands into the law. Re-quantification is first-order logic;
      // the kernel checks freshness and the resulting proof like any other.
      const used = new Set(assumptions.flatMap(item => [...freeFormulaVariables(item)]));
      for (const arg of formula.args) for (const variable of freeTermVariables(arg)) used.add(variable);
      const variables = args.map((_, index) => {
        let variable = `__ring_arg${index}`;
        while (used.has(variable)) variable += "_";
        used.add(variable);
        return variable;
      });
      const fixed = impElim(at(theorem(theoremName), ...formula.args, ...variables.map(v)),
        name.startsWith("IsRing.") ? ordinary : certificate!);
      specialized = variables.reduceRight<Proof>((proof, variable) => forallIntro(variable, proof), fixed);
      specializedLaws.set(theoremName, specialized);
    }
    let proof = at(specialized, ...args);
    for (const arg of args) {
      const evidence = member(arg);
      if (!evidence) throw new Error(`ring could not establish ${formatTerm(arg)} ∈ ${formatTerm(carrier)}`);
      proof = impElim(proof, evidence);
    }
    node.proof = proof;
    return proof;
  };
  const equation = (name: string, args: readonly Term[], a: Term, b: Term): Proof => {
    const proof = law(name, args);
    const actual = kernel.checkProof(proof, assumptions);
    if (formulaEquals(actual, eq(a, b))) return proof;
    if (formulaEquals(actual, eq(b, a))) return reverse(proof);
    throw new Error(`ring law ${name} has a different conclusion`);
  };
  // Scoped-ring numerals: ringNat(add, zero, one, k) is the k-fold sum of one.
  // A numeral is an ordinary factor that sorts first inside a product, so a
  // monomial carries at most one, in front, as its coefficient; the numeral
  // laws of Algebra.Ring.Numeral add and multiply coefficients, with the
  // arithmetic on the naturals closed by a computation certificate.
  const ringNatName = [...kernel.functions.keys()].find(name => name.endsWith(".ringNat") && kernel.functions.get(name) === 4);
  const numeralValue = (term: Term): bigint | undefined =>
    ringNatName === undefined ? undefined : ringNumeralValue(term, { add, zero, one });
  const numeralTerm = (value: bigint): Term => value === 1n ? one : app(ringNatName!, add, zero, one, nat(value));
  // Without the numeral module, like monomials of one sign stay side by side,
  // as x + x, and only opposite monomials cancel.
  const numeralsAvailable = ringNatName !== undefined && ["IsRing.numeral_closed", "IsRing.numeral_one",
    "IsCommRing.numeral_add", "IsCommRing.numeral_mul"].every(name => ringTheorem(name) !== undefined);
  const numeralLaw = (name: string, naturals: readonly Term[]): Proof => {
    const theoremName = ringTheorem(name);
    if (!theoremName) throw new Error(`missing checked ring law ${name}`);
    let proof: Proof = at(theorem(theoremName), ...formula.args, ...naturals);
    while (true) {
      const statement = kernel.checkProof(proof, assumptions);
      if (statement.tag !== "imp" || statement.left.tag !== "pred") return proof;
      const premise = statement.left;
      if (premise.args.length === 6) { proof = impElim(proof, name.startsWith("IsRing.") ? ordinary : certificate!); continue; }
      if (premise.args.length !== 1) return proof;
      const evidence = refinements.prove(premise.args[0]!, premise.pred);
      if (!evidence) throw new Error(`ring could not establish ${formatFormula(premise)}`);
      proof = impElim(proof, evidence);
    }
  };
  // num(a) ⊕ num(b) = num(a ⊕ b) for ⊕ the ring's addition or multiplication,
  // where num(1) is the ring's one.
  const numeralCombine = (operation: "add" | "mul", a: bigint, b: bigint): Proof => {
    const lawName = operation === "add" ? "IsCommRing.numeral_add" : "IsCommRing.numeral_mul";
    const total = operation === "add" ? a + b : a * b;
    const raw = numeralLaw(lawName, [nat(a), nat(b)]);
    const statement = kernel.checkProof(raw, assumptions);
    if (statement.tag !== "eq" || statement.left.tag !== "app") throw new Error(`ring law ${lawName} has a different conclusion`);
    const computed = kernel.proveComputation(statement.left.args[3]!, nat(total));
    const literal = lift(ringNatName!, identity(add), identity(zero), identity(one), computed);
    const bridge = (value: bigint): Proof => value === 1n ? numeralLaw("IsRing.numeral_one", []) : identity(numeralTerm(value));
    const operands = lift(call2, identity(operation === "add" ? add : mul), bridge(a), bridge(b));
    return chain(reverse(operands), reverse(raw), literal, bridge(total));
  };
  // A concrete carrier may spell its numerals through its own function, as
  // realNat(k) for ℝ, declared by a numeral template; the theorem
  // `<function>.numeral` bridges it to ringNat for normalization.
  const carrierType = boundedCarrierType(kernel, carrier);
  const numeralTemplate = carrierType
    ? (visibleInfixNotationGroups(kernel, scope, line, "function", "numeral").get("_") ?? [])
      .find(item => item.operandType === carrierType)
    : undefined;
  const aliasBridge = numeralTemplate && kernel.theorems.has(`${numeralTemplate.target}.numeral`)
    ? `${numeralTemplate.target}.numeral` : undefined;
  const aliasValue = (term: Term): bigint | undefined => {
    if (!numeralTemplate || term.tag !== "app" || term.fn !== numeralTemplate.target) return undefined;
    const leading = numeralTemplate.leadingArguments ?? [];
    if (term.args.length !== leading.length + 1 || !leading.every((arg, i) => termEquals(arg, term.args[i]!))) return undefined;
    return naturalValue(term.args.at(-1)!);
  };
  const factorKey = (term: Term): string => {
    const value = numeralValue(term);
    return value === undefined ? termCanonical(term) : `\u0000${value.toString().padStart(40, "0")}`;
  };
  interface Mono { readonly factors: readonly Term[]; readonly negative: boolean }
  type Poly = readonly Mono[];
  const productTerm = (factors: readonly Term[]): Term => factors.length === 0 ? one :
    factors.slice(0, -1).reduceRight<Term>((tail, head) => times(head, tail), factors.at(-1)!);
  const coefficientOf = (item: Mono): bigint =>
    item.factors.length ? numeralValue(item.factors[0]!) ?? 1n : 1n;
  const bodyOf = (item: Mono): readonly Term[] =>
    item.factors.length && numeralValue(item.factors[0]!) !== undefined ? item.factors.slice(1) : item.factors;
  const scaled = (coefficient: bigint, body: readonly Term[], negative: boolean): Mono =>
    ({ factors: coefficient === 1n ? body : [numeralTerm(coefficient), ...body], negative });
  const monoTerm = (item: Mono): Term => item.negative ? minus(productTerm(item.factors)) : productTerm(item.factors);
  const polynomialTerms = new WeakMap<Poly, Term>();
  const polyTerm = (items: Poly): Term => {
    const cached = polynomialTerms.get(items);
    if (cached) return cached;
    const term = items.length === 0 ? zero : items.slice(0, -1)
      .reduceRight<Term>((tail, item) => plus(monoTerm(item), tail), monoTerm(items.at(-1)!));
    polynomialTerms.set(items, term);
    return term;
  };
  const append = (a: Poly, b: Poly): Proof => {
    if (a.length === 0) return equation("IsRing.add_left_identity", [polyTerm(b)], plus(zero, polyTerm(b)), polyTerm(b));
    if (b.length === 0) return equation("IsRing.add_right_identity", [polyTerm(a)], plus(polyTerm(a), zero), polyTerm(a));
    if (a.length === 1) return identity(plus(monoTerm(a[0]!), polyTerm(b)));
    const head = monoTerm(a[0]!);
    const tail = polyTerm(a.slice(1));
    const end = polyTerm(b);
    return chain(equation("IsCommRing.add_assoc", [head, tail, end],
      plus(plus(head, tail), end), plus(head, plus(tail, end))),
      lift(call2, identity(add), identity(head), append(a.slice(1), b)));
  };
  const bodyKey = (item: Mono): string => bodyOf(item).map(termCanonical).join("\u0000");
  const monoKey = (item: Mono): string => `${bodyKey(item)}\u0001${item.negative ? 1 : 0}`;
  // Two monomials over the same factors combine into one: coefficients of one
  // sign add, opposite signs subtract or cancel. Every step is an application
  // of a checked ring law or numeral law.
  const combineLike = (a: Mono, b: Mono): { items: Mono[]; proof: Proof } => {
    const body = bodyOf(a);
    const [c1, c2] = [coefficientOf(a), coefficientOf(b)];
    const body0 = productTerm(body);
    const positive = (coefficient: bigint): Term => productTerm(scaled(coefficient, body, false).factors);
    // positive(c) = num(c) * body0, as a scaled product even when c = 1.
    const unscale = (coefficient: bigint): Proof => coefficient === 1n && body.length
      ? reverse(equation("IsCommRing.one_left", [body0], times(one, body0), body0))
      : identity(positive(coefficient));
    // num(x) * body0 + num(y) * body0 = num(x + y) * body0 for a nonempty body.
    const addScaled = (x: bigint, y: bigint): Proof => body.length === 0 ? numeralCombine("add", x, y) : chain(
      lift(call2, identity(add), unscale(x), unscale(y)),
      reverse(equation("IsCommRing.add_mul", [numeralTerm(x), numeralTerm(y), body0],
        times(plus(numeralTerm(x), numeralTerm(y)), body0), plus(times(numeralTerm(x), body0), times(numeralTerm(y), body0)))),
      lift(call2, identity(mul), numeralCombine("add", x, y), identity(body0)));
    if (a.negative === b.negative) {
      const item = scaled(c1 + c2, body, a.negative);
      if (!a.negative) return { items: [item], proof: addScaled(c1, c2) };
      return { items: [item], proof: chain(
        reverse(equation("IsCommRing.neg_add", [positive(c1), positive(c2)],
          minus(plus(positive(c1), positive(c2))), plus(minus(positive(c1)), minus(positive(c2))))),
        lift(call1, identity(neg), addScaled(c1, c2))) };
    }
    // Put the positive monomial first.
    if (a.negative) {
      const swapped = combineLike(b, a);
      return { items: swapped.items, proof: chain(equation("IsCommRing.add_comm", [monoTerm(a), monoTerm(b)],
        plus(monoTerm(a), monoTerm(b)), plus(monoTerm(b), monoTerm(a))), swapped.proof) };
    }
    const [x, y] = [positive(c1), positive(c2)];
    if (c1 === c2) return { items: [], proof: equation("IsRing.add_inverse_right", [x], plus(x, minus(x)), zero) };
    if (c1 > c2) {
      // x = d + y, so x + -y = d + (y + -y) = d.
      const d = positive(c1 - c2);
      return { items: [scaled(c1 - c2, body, false)], proof: chain(
        lift(call2, identity(add), chain(reverse(addScaled(c1 - c2, c2))), identity(minus(y))),
        equation("IsCommRing.add_assoc", [d, y, minus(y)], plus(plus(d, y), minus(y)), plus(d, plus(y, minus(y)))),
        lift(call2, identity(add), identity(d), equation("IsRing.add_inverse_right", [y], plus(y, minus(y)), zero)),
        equation("IsRing.add_right_identity", [d], plus(d, zero), d)) };
    }
    // y = x + d, so x + -y = (x + -x) + -d = -d.
    const d = positive(c2 - c1);
    return { items: [scaled(c2 - c1, body, true)], proof: chain(
      lift(call2, identity(add), identity(x), lift(call1, identity(neg), reverse(addScaled(c1, c2 - c1)))),
      lift(call2, identity(add), identity(x), equation("IsCommRing.neg_add", [x, d], minus(plus(x, d)), plus(minus(x), minus(d)))),
      reverse(equation("IsCommRing.add_assoc", [x, minus(x), minus(d)], plus(plus(x, minus(x)), minus(d)), plus(x, plus(minus(x), minus(d))))),
      lift(call2, identity(add), equation("IsRing.add_inverse_right", [x], plus(x, minus(x)), zero), identity(minus(d))),
      equation("IsRing.add_left_identity", [minus(d)], plus(zero, minus(d)), minus(d))) };
  };
  // Merge already normalized pieces instead of bubbling each monomial through
  // a growing sum. Opposite heads cancel immediately, before we construct
  // certificates for moving them across unrelated terms. Every rearrangement
  // below is still an application of an existing checked ring law.
  const mergePolynomial = (a: Poly, b: Poly): { items: Mono[]; proof: Proof } => {
    if (a.length === 0) return { items: [...b], proof: equation("IsRing.add_left_identity",
      [polyTerm(b)], plus(zero, polyTerm(b)), polyTerm(b)) };
    if (b.length === 0) return { items: [...a], proof: equation("IsRing.add_right_identity",
      [polyTerm(a)], plus(polyTerm(a), zero), polyTerm(a)) };
    const aKey = monoKey(a[0]!);
    const bKey = monoKey(b[0]!);
    const headA = monoTerm(a[0]!);
    const headB = monoTerm(b[0]!);
    const likeHeads = bodyKey(a[0]!) === bodyKey(b[0]!) && (numeralsAvailable || a[0]!.negative !== b[0]!.negative);
    // A singleton followed by a later normalized sum is already in normal
    // form. Do not manufacture x + 0 and then prove the zero disappears.
    if (!likeHeads && a.length === 1 && aKey <= bKey)
      return { items: [...a, ...b], proof: identity(plus(headA, polyTerm(b))) };
    if (a.length === 1 && b.length === 1) {
      if (likeHeads) return combineLike(a[0]!, b[0]!);
      return { items: [b[0]!, a[0]!], proof: equation("IsCommRing.add_comm", [headA, headB],
        plus(headA, headB), plus(headB, headA)) };
    }
    const tailA = polyTerm(a.slice(1));
    const tailB = polyTerm(b.slice(1));
    const split = (items: Poly): Proof => items.length === 1
      ? reverse(equation("IsRing.add_right_identity", [monoTerm(items[0]!)],
        plus(monoTerm(items[0]!), zero), monoTerm(items[0]!)))
      : identity(polyTerm(items));
    if (likeHeads) {
      const rest = mergePolynomial(a.slice(1), b.slice(1));
      const tails = plus(tailA, tailB);
      const like = combineLike(a[0]!, b[0]!);
      const likeTerm = polyTerm(like.items);
      const restTerm = polyTerm(rest.items);
      return { items: [...like.items, ...rest.items], proof: chain(
        lift(call2, identity(add), split(a), split(b)),
        equation("IsCommRing.add_assoc", [headA, tailA, plus(headB, tailB)],
          plus(plus(headA, tailA), plus(headB, tailB)), plus(headA, plus(tailA, plus(headB, tailB)))),
        lift(call2, identity(add), identity(headA), equation("IsCommRing.add_swap", [tailA, headB, tailB],
          plus(tailA, plus(headB, tailB)), plus(headB, tails))),
        reverse(equation("IsCommRing.add_assoc", [headA, headB, tails],
          plus(plus(headA, headB), tails), plus(headA, plus(headB, tails)))),
        lift(call2, identity(add), like.proof, rest.proof),
        like.items.length === 0
          ? equation("IsRing.add_left_identity", [restTerm], plus(zero, restTerm), restTerm)
          : rest.items.length === 0
            ? equation("IsRing.add_right_identity", [likeTerm], plus(likeTerm, zero), likeTerm)
            : identity(plus(likeTerm, restTerm))) };
    }
    if (aKey > bKey) {
      const merged = mergePolynomial(b, a);
      return { items: merged.items, proof: chain(
        equation("IsCommRing.add_comm", [polyTerm(a), polyTerm(b)],
          plus(polyTerm(a), polyTerm(b)), plus(polyTerm(b), polyTerm(a))), merged.proof) };
    }
    const rest = mergePolynomial(a.slice(1), b);
    const items = [a[0]!, ...rest.items];
    return { items, proof: chain(
      lift(call2, identity(add), split(a), identity(polyTerm(b))),
      equation("IsCommRing.add_assoc", [headA, tailA, polyTerm(b)],
        plus(plus(headA, tailA), polyTerm(b)), plus(headA, plus(tailA, polyTerm(b)))),
      lift(call2, identity(add), identity(headA), rest.proof),
      rest.items.length ? identity(polyTerm(items)) : equation("IsRing.add_right_identity", [headA],
        plus(headA, zero), headA)) };
  };
  const sortPolynomial = (items: Poly): { items: Mono[]; proof: Proof } => {
    if (items.length < 2) return { items: [...items], proof: identity(polyTerm(items)) };
    const middle = Math.floor(items.length / 2);
    const left = items.slice(0, middle);
    const right = items.slice(middle);
    const a = sortPolynomial(left);
    const b = sortPolynomial(right);
    const merged = mergePolynomial(a.items, b.items);
    return { items: merged.items, proof: chain(reverse(append(left, right)),
      lift(call2, identity(add), a.proof, b.proof), merged.proof) };
  };
  const productSwap = (factors: readonly Term[], index: number): Proof => {
    if (index > 0) return lift(call2, identity(mul), identity(factors[0]!), productSwap(factors.slice(1), index - 1));
    const [x, y] = factors;
    const exchanged = [y!, x!, ...factors.slice(2)];
    return factors.length === 2 ? equation("IsCommRing.mul_comm", [x!, y!],
      productTerm(factors), productTerm(exchanged)) :
      equation("IsCommRing.mul_swap", [x!, y!, productTerm(factors.slice(2))],
        productTerm(factors), productTerm(exchanged));
  };
  const multiplyFactors = (a: readonly Term[], b: readonly Term[]): { factors: Term[]; proof: Proof } => {
    if (a.length === 0) return { factors: [...b], proof: equation("IsCommRing.one_left", [productTerm(b)],
      times(one, productTerm(b)), productTerm(b)) };
    if (b.length === 0) return { factors: [...a], proof: equation("IsCommRing.one_right", [productTerm(a)],
      times(productTerm(a), one), productTerm(a)) };
    const factors = [...a, ...b];
    const join = (items: readonly Term[]): Proof => {
      if (items.length === 1) return identity(times(items[0]!, productTerm(b)));
      const head = items[0]!;
      const tail = productTerm(items.slice(1));
      const end = productTerm(b);
      return chain(equation("IsCommRing.mul_assoc", [head, tail, end],
        times(times(head, tail), end), times(head, times(tail, end))),
        lift(call2, identity(mul), identity(head), join(items.slice(1))));
    };
    let proof = join(a);
    const keys = factors.map(factorKey);
    for (let target = 0; target < factors.length; target += 1) {
      let selected = target;
      for (let next = target + 1; next < factors.length; next += 1)
        if (keys[next]! < keys[selected]!) selected = next;
      while (selected > target) {
        proof = chain(proof, productSwap(factors, selected - 1));
        [factors[selected - 1], factors[selected]] = [factors[selected]!, factors[selected - 1]!];
        [keys[selected - 1], keys[selected]] = [keys[selected]!, keys[selected - 1]!];
        selected -= 1;
      }
    }
    // Two leading numerals multiply into one coefficient.
    while (factors.length >= 2) {
      const [x, y] = [numeralValue(factors[0]!), numeralValue(factors[1]!)];
      if (x === undefined || y === undefined) break;
      const rest = factors.slice(2);
      const combined = numeralCombine("mul", x, y);
      proof = rest.length === 0 ? chain(proof, combined) : chain(proof,
        reverse(equation("IsCommRing.mul_assoc", [factors[0]!, factors[1]!, productTerm(rest)],
          times(times(factors[0]!, factors[1]!), productTerm(rest)), times(factors[0]!, times(factors[1]!, productTerm(rest))))),
        lift(call2, identity(mul), combined, identity(productTerm(rest))));
      factors.splice(0, 2, numeralTerm(x * y));
    }
    return { factors, proof };
  };
  const multiplyMono = (a: Mono, b: Mono): { item: Mono; proof: Proof } => {
    const x = productTerm(a.factors);
    const y = productTerm(b.factors);
    const signs = a.negative && b.negative ? law("IsCommRing.neg_mul_neg", [x, y]) :
      a.negative ? law("IsRing.neg_mul", [x, y]) :
      b.negative ? law("IsCommRing.mul_neg", [x, y]) : identity(times(x, y));
    const merged = multiplyFactors(a.factors, b.factors);
    const negative = a.negative !== b.negative;
    return { item: { factors: merged.factors, negative }, proof: chain(signs,
      negative ? lift(call1, identity(neg), merged.proof) : merged.proof) };
  };
  const negatePoly = (items: Poly): { items: Mono[]; proof: Proof } => {
    if (items.length === 1) {
      const item = items[0]!;
      const flipped = { factors: item.factors, negative: !item.negative };
      return { items: [flipped], proof: item.negative
        ? equation("IsCommRing.neg_neg", [productTerm(item.factors)], minus(monoTerm(item)), monoTerm(flipped))
        : identity(minus(monoTerm(item))) };
    }
    if (items.length === 0) return { items: [], proof: equation("IsCommRing.neg_zero", [], minus(zero), zero) };
    const head = monoTerm(items[0]!);
    const tail = polyTerm(items.slice(1));
    const first = negatePoly([items[0]!]);
    const rest = negatePoly(items.slice(1));
    return { items: [...first.items, ...rest.items], proof: chain(
      equation("IsCommRing.neg_add", [head, tail], minus(polyTerm(items)), plus(minus(head), minus(tail))),
      lift(call2, identity(add), first.proof, rest.proof),
      append(first.items, rest.items)) };
  };
  const expandRight = (a: Mono, bs: Poly): { items: Mono[]; proof: Proof } => {
    if (bs.length === 1) {
      const merged = multiplyMono(a, bs[0]!);
      return { items: [merged.item], proof: merged.proof };
    }
    const x = monoTerm(a);
    const y = monoTerm(bs[0]!);
    const tail = polyTerm(bs.slice(1));
    const first = multiplyMono(a, bs[0]!);
    const rest = expandRight(a, bs.slice(1));
    return { items: [first.item, ...rest.items], proof: chain(
      equation("IsCommRing.mul_add", [x, y, tail], times(x, polyTerm(bs)),
        plus(times(x, y), times(x, tail))),
      lift(call2, identity(add), first.proof, rest.proof), append([first.item], rest.items)) };
  };
  const multiplyPoly = (as: Poly, bs: Poly): { items: Mono[]; proof: Proof } => {
    if (as.length * bs.length > 256) throw new Error("polynomial expansion exceeds 256 monomials");
    if (as.length === 0) return { items: [], proof: equation("IsRing.zero_mul", [polyTerm(bs)],
      times(zero, polyTerm(bs)), zero) };
    if (bs.length === 0) return { items: [], proof: equation("IsRing.mul_zero", [polyTerm(as)],
      times(polyTerm(as), zero), zero) };
    if (as.length === 1) return expandRight(as[0]!, bs);
    const x = monoTerm(as[0]!);
    const tail = polyTerm(as.slice(1));
    const y = polyTerm(bs);
    const first = expandRight(as[0]!, bs);
    const rest = multiplyPoly(as.slice(1), bs);
    return { items: [...first.items, ...rest.items], proof: chain(
      equation("IsCommRing.add_mul", [x, tail, y], times(polyTerm(as), y),
        plus(times(x, y), times(tail, y))),
      lift(call2, identity(add), first.proof, rest.proof), append(first.items, rest.items)) };
  };
  const unfoldAlias = (term: Term): { term: Term; proof: Proof } | undefined => {
    if (term.tag !== "app" || term.fn === call2 || term.fn === call1) return undefined;
    const bridgeInfo = notationBridge(term.fn);
    if (bridgeInfo && bridgeInfo.arity === term.args.length) {
      let bridge: Proof = at(theorem(bridgeInfo.name), ...term.args);
      let statement = kernel.checkProof(bridge, assumptions);
      while (statement.tag === "imp" && statement.left.tag === "pred" && statement.left.args.length === 1) {
        const evidence = refinements.prove(statement.left.args[0]!, statement.left.pred);
        if (!evidence) break;
        bridge = impElim(bridge, evidence);
        statement = kernel.checkProof(bridge, assumptions);
      }
      if (statement.tag === "eq") {
        const forward = termEquals(statement.left, term);
        const backward = termEquals(statement.right, term);
        const value = forward ? statement.right : backward ? statement.left : undefined;
        if (value?.tag === "app" && (
            value.fn === call2 && value.args.length === 3 && [add, mul].some(op => termEquals(op, value.args[0]!)) ||
            value.fn === call1 && value.args.length === 2 && termEquals(neg, value.args[0]!)))
          return { term: value, proof: forward ? bridge : reverse(bridge) };
      }
    }
    const record = kernel.definitions.get(term.fn);
    if (!record || record.kind !== "function" || record.parameters.length !== term.args.length) return undefined;
    let proof: Proof = at(definition(term.fn), ...term.args);
    while (true) {
      const statement = kernel.checkProof(proof, assumptions);
      if (statement.tag !== "imp" || statement.left.tag !== "pred" || statement.left.args.length !== 1) break;
      const evidence = refinements.prove(statement.left.args[0]!, statement.left.pred);
      if (!evidence) return undefined;
      proof = impElim(proof, evidence);
    }
    const statement = kernel.checkProof(proof, assumptions);
    if (statement.tag !== "eq" || !termEquals(statement.left, term)) return undefined;
    let value = statement.right;
    for (const operation of [add, mul]) {
      if (term.args.length !== 2) continue;
      const candidate = app(call2, operation, term.args[0]!, term.args[1]!);
      const bridge = at(definition(call2), operation, term.args[0]!, term.args[1]!);
      const bridgeFormula = kernel.checkProof(bridge, assumptions);
      if (bridgeFormula.tag === "eq" && termEquals(bridgeFormula.left, candidate) &&
          termEquals(bridgeFormula.right, value)) {
        return { term: candidate, proof: chain(proof, reverse(bridge)) };
      }
    }
    if (termEquals(value, term)) return undefined;
    if (value.tag !== "app" || !(
      value.fn === call2 && [add, mul].some(operation => termEquals(operation, value.args[0]!)) ||
      value.fn === call1 && termEquals(value.args[0]!, neg))) return undefined;
    return { term: value, proof };
  };
  const normalCache = new Map<number, { items: Mono[]; proof: Proof }>();
  const normalize = (term: Term): { items: Mono[]; proof: Proof } => {
    const key = termId(term);
    const cached = normalCache.get(key);
    if (cached) return cached;
    const result = normalizeFresh(term);
    normalCache.set(key, result);
    return result;
  };
  const normalizeFresh = (term: Term): { items: Mono[]; proof: Proof } => {
    if (termEquals(term, zero)) return { items: [], proof: identity(term) };
    if (termEquals(term, one)) return { items: [{ factors: [], negative: false }], proof: identity(term) };
    const aliased = aliasValue(term);
    if (aliased !== undefined && aliasBridge && ringNatName) {
      let bridge: Proof = at(theorem(aliasBridge), nat(aliased));
      while (true) {
        const statement = kernel.checkProof(bridge, assumptions);
        if (statement.tag !== "imp" || statement.left.tag !== "pred" || statement.left.args.length !== 1) break;
        const evidence = refinements.prove(statement.left.args[0]!, statement.left.pred);
        if (!evidence) throw new Error(`ring could not establish ${formatFormula(statement.left)}`);
        bridge = impElim(bridge, evidence);
      }
      const inner = normalize(app(ringNatName, add, zero, one, nat(aliased)));
      return { items: inner.items, proof: chain(bridge, inner.proof) };
    }
    const numeral = numeralValue(term);
    if (numeral !== undefined) {
      if (numeral === 0n) {
        const name = ringTheorem("ringNat.zero");
        if (!name) throw new Error("missing checked ring law ringNat.zero");
        return { items: [], proof: at(theorem(name), add, zero, one) };
      }
      if (numeral === 1n) return { items: [{ factors: [], negative: false }], proof: numeralLaw("IsRing.numeral_one", []) };
      return { items: [{ factors: [term], negative: false }], proof: identity(term) };
    }
    // A power with a literal exponent is its product: A ^ 2 is A * A.
    const power = expandLiteralPower(kernel, term, assumptions, refinements);
    if (power) {
      const inner = normalize(power.term);
      return { items: inner.items, proof: chain(power.proof, inner.proof) };
    }
    const alias = unfoldAlias(term);
    if (alias) {
      const inner = normalize(alias.term);
      return { items: inner.items, proof: chain(alias.proof, inner.proof) };
    }
    const summed = sum(term);
    if (summed) {
      const a = normalize(summed[0]);
      const b = normalize(summed[1]);
      const merged = mergePolynomial(a.items, b.items);
      return { items: merged.items, proof: chain(
        lift(call2, identity(add), a.proof, b.proof), merged.proof) };
    }
    const negated = opposite(term);
    if (negated) {
      const inner = normalize(negated);
      const flipped = negatePoly(inner.items);
      // A normalized polynomial has only one sign for each factor sequence.
      // Flipping every sign preserves factor order and cannot create a pair
      // of opposite monomials, so another sorting certificate is unnecessary.
      return { items: flipped.items, proof: chain(
        lift(call1, identity(neg), inner.proof), flipped.proof) };
    }
    const multiplied = product(term);
    if (multiplied) {
      const a = normalize(multiplied[0]);
      const b = normalize(multiplied[1]);
      const expanded = multiplyPoly(a.items, b.items);
      const sorted = sortPolynomial(expanded.items);
      return { items: sorted.items, proof: chain(
        lift(call2, identity(mul), a.proof, b.proof), expanded.proof, sorted.proof) };
    }
    if (!member(term)) throw new Error(`ring could not establish ${formatTerm(term)} ∈ ${formatTerm(carrier)}`);
    return { items: [{ factors: [term], negative: false }], proof: identity(term) };
  };
  return {
    operations: { call1, call2, add, neg, mul },
    // The ring as a notation scope, so that a coefficient written beside
    // the goal, `2 * h`, reads its numerals and operations in the carrier.
    ring: { name: "ring", carrier, add, zero, neg, mul, one, call1, call2, plainLiterals: true } as RingNotation,
    // Collapse a + (b - b) directly. Expanding b twice only to cancel it
    // creates a large, redundant polynomial certificate.
    cancelDifference: (a: Term, b: Term): Proof => chain(
      lift(call2, identity(add), identity(a), equation("IsRing.add_inverse_right", [b],
        plus(b, minus(b)), zero)),
      equation("IsRing.add_right_identity", [a], plus(a, zero), a)),
    normalize: (inputs: readonly Term[]): readonly { term: Term; proof: Proof }[] | undefined => {
      try {
        return inputs.map(term => {
          const result = normalize(term);
          return { term: polyTerm(result.items), proof: result.proof };
        });
      } catch (error) {
        if (typeof process !== "undefined" && process.env?.G17_RING_DEBUG) console.error("[ring]", error);
        if (operations.length === 0) return undefined;
        throw new SurfaceError(line, `ring could not build a checked CommRing certificate: ${
          error instanceof Error ? error.message : String(error)}`);
      }
    },
  };
}

/** The literal exponents `ring` expands: t ^ k is the k-fold product. */
const LITERAL_POWER_LIMIT = 16n;

/**
 * Expand a power with a literal exponent, `t ^ k` for k ≤ 16, into the
 * product its defining equations give: f(…, x, k) = op(x, f(…, x, k − 1))
 * down to the unit of f(…, x, 0). The certificate chains the recursive
 * function's own equations, with each numeral exponent bridged to its
 * successor form by a computation certificate; a power written through a
 * definition, as `realPow(A, n) := monoidPow(realMul, realOne, A, n)`, is
 * unfolded first. Leading soft-type premises of the equations are
 * discharged by the refinement prover. Returns undefined when the term is
 * not such a power.
 */
function expandLiteralPower(
  kernel: Kernel, term: Term, assumptions: readonly Formula[], refinements: RefinementProver,
): { readonly term: Term; readonly proof: Proof } | undefined {
  if (term.tag !== "app" || term.args.length === 0) return undefined;
  const exponent = naturalValue(term.args.at(-1)!);
  if (exponent === undefined || exponent > LITERAL_POWER_LIMIT) return undefined;
  const relieve = (proof: Proof): Proof | undefined => {
    let result = proof;
    for (;;) {
      const statement = kernel.checkProof(result, assumptions);
      if (statement.tag !== "imp") return result;
      if (statement.left.tag !== "pred" || statement.left.args.length === 0) return undefined;
      const evidence = refinements.prove(statement.left.args.at(-1)!, statement.left.pred, statement.left.args.slice(0, -1));
      if (!evidence) return undefined;
      result = impElim(result, evidence);
    }
  };
  const record = kernel.recursiveFunctions.get(term.fn);
  if (!record) {
    // A power named through a definition, whose body is a recursive power
    // at the definition's last parameter, unfolds to that power.
    const explicit = kernel.functionBodies.get(term.fn);
    const body = explicit?.body;
    if (!explicit || explicit.parameters.length !== term.args.length || body?.tag !== "app" ||
        !kernel.recursiveFunctions.has(body.fn) || body.args.at(-1)?.tag !== "var" ||
        (body.args.at(-1) as Extract<Term, { tag: "var" }>).name !== explicit.parameters.at(-1)) return undefined;
    const unfolded = relieve(at(definition(term.fn), ...term.args));
    if (!unfolded) return undefined;
    const statement = kernel.checkProof(unfolded, assumptions);
    if (statement.tag !== "eq" || !termEquals(statement.left, term) || statement.right.tag !== "app" ||
        !kernel.recursiveFunctions.has(statement.right.fn) ||
        naturalValue(statement.right.args.at(-1) ?? v("")) !== exponent) return undefined;
    const inner = expandLiteralPower(kernel, statement.right, assumptions, refinements);
    return inner ? { term: inner.term, proof: calc(unfolded, inner.proof) } : undefined;
  }
  const last = term.args.length - 1;
  if (record.decreasingParameter !== last || record.equations.length !== 2) return undefined;
  const rootOf = (index: number): string | undefined => {
    const root = record.equations[index]!.patterns[last];
    return root?.tag === "ctor" ? root.name : undefined;
  };
  const zeroIndex = [0, 1].find(index => rootOf(index) === "zero");
  const succIndex = [0, 1].find(index => rootOf(index) === "succ");
  if (zeroIndex === undefined || succIndex === undefined) return undefined;
  if (!record.equations.every(item => item.patterns.slice(0, last).every(pattern => pattern.tag === "bind"))) return undefined;
  const succRoot = record.equations[succIndex]!.patterns[last]!;
  if (succRoot.tag !== "ctor" || succRoot.args.length !== 1 || succRoot.args[0]!.tag !== "bind") return undefined;
  const leading = term.args.slice(0, last);
  const call = (power: Term): Term => app(term.fn, ...leading, power);
  // The numeral exponent in the form the equation's left side has.
  const bridge = (from: Term, to: Term): Proof | undefined => {
    if (termEquals(from, to)) return undefined;
    try { return congr(term.fn, ...leading.map(refl), kernel.proveComputation(from, to)); } catch { return undefined; }
  };
  const expand = (power: bigint): { readonly term: Term; readonly proof: Proof } | undefined => {
    if (power === 0n) {
      const base = relieve(at(definition(term.fn, `equation.${zeroIndex}`), ...leading));
      if (!base) return undefined;
      const statement = kernel.checkProof(base, assumptions);
      if (statement.tag !== "eq" || statement.left.tag !== "app" || statement.left.fn !== term.fn) return undefined;
      const step = bridge(nat(0n), statement.left.args[last]!);
      if (!termEquals(statement.left, call(statement.left.args[last]!))) return undefined;
      return { term: statement.right, proof: step ? calc(step, base) : base };
    }
    const equation = relieve(at(definition(term.fn, `equation.${succIndex}`), ...leading, nat(power - 1n)));
    if (!equation) return undefined;
    const statement = kernel.checkProof(equation, assumptions);
    if (statement.tag !== "eq" || statement.left.tag !== "app" || statement.left.fn !== term.fn ||
        !termEquals(statement.left, call(statement.left.args[last]!))) return undefined;
    const step = bridge(nat(power), statement.left.args[last]!);
    if (statement.right.tag !== "app") return undefined;
    const recursive = call(nat(power - 1n));
    const positions = statement.right.args.flatMap((argument, index) => termEquals(argument, recursive) ? [index] : []);
    if (positions.length !== 1) return undefined;
    const inner = expand(power - 1n);
    if (!inner) return undefined;
    const replaced = app(statement.right.fn, ...statement.right.args.map((argument, index) => index === positions[0] ? inner.term : argument));
    const lifted = congr(statement.right.fn, ...statement.right.args.map((argument, index) => index === positions[0] ? inner.proof : refl(argument)));
    return { term: replaced, proof: step ? calc(step, equation, lifted) : calc(equation, lifted) };
  };
  const result = expand(exponent);
  if (!result) return undefined;
  const bridged = bridge(term.args[last]!, nat(exponent));
  return bridged ? { term: result.term, proof: calc(bridged, result.proof) } : result;
}

interface SemiringMonomial { readonly factors: readonly Term[] }

interface SemiringNormalForm {
  readonly term: Term;
  readonly proof: Proof;
  readonly monomials: readonly SemiringMonomial[];
}

/**
 * Canonical commutative-semiring normalization for Nat expressions.
 *
 * The polynomial computation is untrusted bookkeeping.  Its result is accepted
 * only when `settle` constructs an equality proof from the checked Nat
 * semiring laws, so this adds no kernel rule or reflective axiom.
 */
function normalizeNaturalSemiring(
  kernel: Kernel,
  source: Term,
  line: number,
  scope: SurfaceScope,
  assumptions: readonly Formula[],
  preparedRefinements?: RefinementProver,
): SemiringNormalForm {
  const presentation = naturalLinearArithmeticPresentation(kernel, line, scope);
  const refinements = preparedRefinements ?? prepareRefinementProver(kernel, assumptions, [], scopeVisibility(kernel, scope));
  const typed = (proof: Proof, terms: readonly Term[]): Proof => {
    let result = at(proof, ...terms);
    while (true) {
      const formula = kernel.checkProof(result, assumptions);
      if (formula.tag !== "imp" || formula.left.tag !== "pred" || formula.left.args.length !== 1) return result;
      const evidence = refinements.prove(formula.left.args[0]!, formula.left.pred);
      if (!evidence) throw new SurfaceError(line, `ring could not establish ${formatFormula(formula.left)}`);
      result = impElim(result, evidence);
    }
  };
  const addAssociative = resolveProof(kernel, "Grace.Core.Nat.Algebra.add.associative", line, scope);
  const addCommutative = resolveProof(kernel, "Grace.Core.Nat.Algebra.add.commutative", line, scope);
  const addSwap = resolveProof(kernel, "Grace.Core.Nat.Algebra.add.swap", line, scope);
  const addRightUnit = resolveProof(kernel, "Grace.Core.Nat.Algebra.add.right_unit", line, scope);
  const addRightOne = resolveProof(kernel, "Grace.Core.Nat.Algebra.add.right_one", line, scope);
  const mulAssociative = resolveProof(kernel, "Grace.Core.Nat.Algebra.mul.associative", line, scope);
  const mulCommutative = resolveProof(kernel, "Grace.Core.Nat.Algebra.mul.commutative", line, scope);
  const mulLeftUnit = resolveProof(kernel, "Grace.Core.Nat.Algebra.mul.left_unit", line, scope);
  const mulRightUnit = resolveProof(kernel, "Grace.Core.Nat.Algebra.mul.right_unit", line, scope);
  const mulRightZero = resolveProof(kernel, "Grace.Core.Nat.Algebra.mul.right_zero", line, scope);
  const distributesLeft = resolveProof(kernel, "Grace.Core.Nat.Algebra.mul.distributes_left", line, scope);
  const distributesRight = resolveProof(kernel, "Grace.Core.Nat.Algebra.mul.distributes_right", line, scope);
  const compareFactors = (left: Term, right: Term): number => {
    // Coefficients sort first so that a product carries at most one numeral,
    // in front, and sums compare monomials by their non-numeral factors.
    const leftValue = left.tag === "nat" ? naturalValue(left) : undefined;
    const rightValue = right.tag === "nat" ? naturalValue(right) : undefined;
    if (leftValue !== undefined && rightValue !== undefined) return leftValue < rightValue ? -1 : leftValue > rightValue ? 1 : 0;
    if (leftValue !== undefined) return -1;
    if (rightValue !== undefined) return 1;
    const a = termCanonical(left);
    const b = termCanonical(right);
    return a < b ? -1 : a > b ? 1 : 0;
  };
  const coefficientOf = (item: SemiringMonomial): bigint =>
    item.factors[0]?.tag === "nat" ? (naturalValue(item.factors[0]) ?? 1n) : 1n;
  const bodyOf = (item: SemiringMonomial): readonly Term[] =>
    item.factors[0]?.tag === "nat" ? item.factors.slice(1) : item.factors;
  const numeralSum = (left: bigint, right: bigint): Proof =>
    kernel.proveComputation(app(presentation.add, nat(left), nat(right)), nat(left + right));
  const numeralProduct = (left: bigint, right: bigint): Proof =>
    kernel.proveComputation(app(presentation.mul, nat(left), nat(right)), nat(left * right));
  const productTerm = (factors: readonly Term[]): Term => {
    if (factors.length === 0) return nat(1);
    return factors.slice(0, -1).reduceRight<Term>(
      (tail, head) => app(presentation.mul, head, tail), factors.at(-1)!,
    );
  };
  const additiveTerm = (items: readonly SemiringMonomial[]): Term => {
    const terms = items.map(item => productTerm(item.factors));
    if (terms.length === 0) return nat(0);
    return terms.slice(0, -1).reduceRight<Term>(
      (tail, head) => app(presentation.add, head, tail), terms.at(-1)!,
    );
  };
  const appendAdditive = (left: readonly SemiringMonomial[], right: readonly SemiringMonomial[]): Proof => {
    const rightTerm = additiveTerm(right);
    const visit = (items: readonly SemiringMonomial[]): Proof => {
      if (items.length === 1) return refl(app(presentation.add, productTerm(items[0]!.factors), rightTerm));
      const head = productTerm(items[0]!.factors);
      const tail = additiveTerm(items.slice(1));
      return calc(
        typed(addAssociative, [tail, rightTerm, head]),
        congr(presentation.add, refl(head), visit(items.slice(1))),
      );
    };
    return visit(left);
  };
  const combineAdditive = (left: readonly SemiringMonomial[], right: readonly SemiringMonomial[]): Proof => {
    const leftTerm = additiveTerm(left);
    const rightTerm = additiveTerm(right);
    if (left.length === 0) return calc(
      typed(addCommutative, [rightTerm, nat(0)]),
      typed(addRightUnit, [rightTerm]),
    );
    if (right.length === 0) return typed(addRightUnit, [leftTerm]);
    return appendAdditive(left, right);
  };
  const swapAdditive = (items: readonly SemiringMonomial[], index: number): Proof => {
    if (index > 0) return congr(
      presentation.add, refl(productTerm(items[0]!.factors)), swapAdditive(items.slice(1), index - 1),
    );
    const first = productTerm(items[0]!.factors);
    const second = productTerm(items[1]!.factors);
    if (items.length === 2) return typed(addCommutative, [second, first]);
    return typed(addSwap, [second, additiveTerm(items.slice(2)), first]);
  };
  const monomialKey = (item: SemiringMonomial): string => bodyOf(item).map(termCanonical).join("\u0000");
  // c1 * P + c2 * P = (c1 + c2) * P, where a coefficient of one is implicit.
  const mergeCoefficients = (left: SemiringMonomial, right: SemiringMonomial): { item: SemiringMonomial; proof: Proof } => {
    const body = bodyOf(left);
    const [c1, c2] = [coefficientOf(left), coefficientOf(right)];
    const total = c1 + c2;
    if (body.length === 0) return { item: { factors: [nat(total)] }, proof: numeralSum(c1, c2) };
    const bodyTerm = productTerm(body);
    const lift = (coefficient: bigint): Proof => coefficient === 1n
      ? symm(typed(mulLeftUnit, [bodyTerm]))
      : refl(app(presentation.mul, nat(coefficient), bodyTerm));
    const proof = calc(
      congr(presentation.add, lift(c1), lift(c2)),
      symm(typed(distributesRight, [nat(c2), bodyTerm, nat(c1)])),
      congr(presentation.mul, numeralSum(c1, c2), refl(bodyTerm)),
    );
    return { item: { factors: [nat(total), ...body] }, proof };
  };
  // Merge the monomials at index and index + 1 of a right-nested sum.
  const mergeAt = (items: readonly SemiringMonomial[], index: number): { items: SemiringMonomial[]; proof: Proof } => {
    if (index > 0) {
      const head = productTerm(items[0]!.factors);
      const tail = mergeAt(items.slice(1), index - 1);
      return { items: [items[0]!, ...tail.items], proof: congr(presentation.add, refl(head), tail.proof) };
    }
    const merged = mergeCoefficients(items[0]!, items[1]!);
    if (items.length === 2) return { items: [merged.item], proof: merged.proof };
    const first = productTerm(items[0]!.factors);
    const second = productTerm(items[1]!.factors);
    const rest = additiveTerm(items.slice(2));
    const proof = calc(
      symm(typed(addAssociative, [second, rest, first])),
      congr(presentation.add, merged.proof, refl(rest)),
    );
    return { items: [merged.item, ...items.slice(2)], proof };
  };
  const sortPolynomial = (input: readonly SemiringMonomial[]): { items: SemiringMonomial[]; proof: Proof } => {
    let items = [...input];
    let proof: Proof = refl(additiveTerm(items));
    for (let target = 0; target < items.length; target += 1) {
      let selected = target;
      for (let candidate = target + 1; candidate < items.length; candidate += 1) {
        if (monomialKey(items[candidate]!) < monomialKey(items[selected]!)) selected = candidate;
      }
      while (selected > target) {
        proof = calc(proof, swapAdditive(items, selected - 1));
        [items[selected - 1], items[selected]] = [items[selected]!, items[selected - 1]!];
        selected -= 1;
      }
    }
    for (let index = 0; index + 1 < items.length;) {
      if (monomialKey(items[index]!) === monomialKey(items[index + 1]!)) {
        const merged = mergeAt(items, index);
        proof = calc(proof, merged.proof);
        items = merged.items;
      } else index += 1;
    }
    return { items, proof };
  };
  const appendProduct = (left: readonly Term[], right: readonly Term[]): Proof => {
    if (left.length === 0) return typed(mulLeftUnit, [productTerm(right)]);
    if (right.length === 0) return typed(mulRightUnit, [productTerm(left)]);
    if (left.length === 1) return refl(app(presentation.mul, left[0]!, productTerm(right)));
    const head = left[0]!;
    const tail = productTerm(left.slice(1));
    const rightTerm = productTerm(right);
    return calc(
      typed(mulAssociative, [tail, rightTerm, head]),
      congr(presentation.mul, refl(head), appendProduct(left.slice(1), right)),
    );
  };
  const swapProduct = (factors: readonly Term[], index: number): Proof => {
    if (index > 0) return congr(presentation.mul, refl(factors[0]!), swapProduct(factors.slice(1), index - 1));
    const first = factors[0]!;
    const second = factors[1]!;
    if (factors.length === 2) return typed(mulCommutative, [second, first]);
    const tail = productTerm(factors.slice(2));
    return calc(
      symm(typed(mulAssociative, [second, tail, first])),
      congr(presentation.mul, typed(mulCommutative, [second, first]), refl(tail)),
      typed(mulAssociative, [first, tail, second]),
    );
  };
  const mergeMonomial = (left: SemiringMonomial, right: SemiringMonomial): { item: SemiringMonomial; proof: Proof } => {
    const factors = [...left.factors, ...right.factors];
    let proof = appendProduct(left.factors, right.factors);
    for (let target = 0; target < factors.length; target += 1) {
      let selected = target;
      for (let candidate = target + 1; candidate < factors.length; candidate += 1) {
        if (compareFactors(factors[candidate]!, factors[selected]!) < 0) selected = candidate;
      }
      while (selected > target) {
        proof = calc(proof, swapProduct(factors, selected - 1));
        [factors[selected - 1], factors[selected]] = [factors[selected]!, factors[selected - 1]!];
        selected -= 1;
      }
    }
    // Two leading coefficients a * (b * rest) become (a * b) * rest.
    while (factors.length >= 2 && factors[0]!.tag === "nat" && factors[1]!.tag === "nat") {
      const a = naturalValue(factors[0]!)!;
      const b = naturalValue(factors[1]!)!;
      if (factors.length === 2) {
        proof = calc(proof, numeralProduct(a, b));
      } else {
        const rest = productTerm(factors.slice(2));
        proof = calc(proof,
          symm(typed(mulAssociative, [nat(b), rest, nat(a)])),
          congr(presentation.mul, numeralProduct(a, b), refl(rest)));
      }
      factors.splice(0, 2, nat(a * b));
    }
    return { item: { factors }, proof };
  };
  const expandRight = (left: SemiringMonomial, right: readonly SemiringMonomial[]): { items: SemiringMonomial[]; proof: Proof } => {
    if (right.length === 1) {
      const merged = mergeMonomial(left, right[0]!);
      return { items: [merged.item], proof: merged.proof };
    }
    const leftTerm = productTerm(left.factors);
    const rightHead = productTerm(right[0]!.factors);
    const rightTail = additiveTerm(right.slice(1));
    const head = mergeMonomial(left, right[0]!);
    const tail = expandRight(left, right.slice(1));
    return {
      items: [head.item, ...tail.items],
      proof: calc(
        typed(distributesLeft, [rightHead, rightTail, leftTerm]),
        congr(presentation.add, head.proof, tail.proof),
      ),
    };
  };
  const multiply = (left: readonly SemiringMonomial[], right: readonly SemiringMonomial[]): { items: SemiringMonomial[]; proof: Proof } => {
    if (left.length === 0) {
      const rightTerm = additiveTerm(right);
      return {
        items: [],
        proof: calc(
          typed(mulCommutative, [rightTerm, nat(0)]),
          typed(mulRightZero, [rightTerm]),
        ),
      };
    }
    if (right.length === 0) return {
      items: [], proof: typed(mulRightZero, [additiveTerm(left)]),
    };
    if (left.length === 1) return expandRight(left[0]!, right);
    const leftHead = productTerm(left[0]!.factors);
    const leftTail = additiveTerm(left.slice(1));
    const rightTerm = additiveTerm(right);
    const head = expandRight(left[0]!, right);
    const tail = multiply(left.slice(1), right);
    return {
      items: [...head.items, ...tail.items],
      proof: calc(
        typed(distributesRight, [leftTail, rightTerm, leftHead]),
        congr(presentation.add, head.proof, tail.proof),
        appendAdditive(head.items, tail.items),
      ),
    };
  };
  const normalize = (term: Term): { items: SemiringMonomial[]; term: Term; proof: Proof } => {
    // Zero is the empty sum.
    if (term.tag === "nat" && term.value === "0") {
      return { items: [], term: nat(0), proof: refl(term) };
    }
    // One is the empty product.  This matters as soon
    // as successor is expanded inside a larger polynomial.
    if (term.tag === "nat" && term.value === "1") {
      const items = [{ factors: [] }];
      return { items, term: nat(1), proof: refl(term) };
    }
    // A numeral is a monomial whose only factor is its coefficient. Numerals
    // sort first inside a product and adjacent coefficients collapse by a
    // computation certificate, so 2 * a and a + a share the normal form 2 * a.
    // Nat successor is polynomial addition by one.  Treating succ(k) as an
    // opaque atom made ring miss equalities generated by quotient arithmetic.
    if (term.tag === "app" && term.fn === presentation.successor && term.args.length === 1) {
      const argument = term.args[0]!;
      const inner = normalize(argument);
      const oneItems: SemiringMonomial[] = [{ factors: [] }];
      const combined = [...inner.items, ...oneItems];
      const sorted = sortPolynomial(combined);
      const proof = calc(
        symm(typed(addRightOne, [argument])),
        congr(presentation.add, inner.proof, refl(nat(1))),
        combineAdditive(inner.items, oneItems),
        sorted.proof,
      );
      return { items: sorted.items, term: additiveTerm(sorted.items), proof };
    }
    if (term.tag === "app" && term.args.length === 2 && term.fn === presentation.add) {
      const left = normalize(term.args[0]!);
      const right = normalize(term.args[1]!);
      const combined = [...left.items, ...right.items];
      const sorted = sortPolynomial(combined);
      const proof = calc(
        congr(presentation.add, left.proof, right.proof),
        combineAdditive(left.items, right.items),
        sorted.proof,
      );
      return { items: sorted.items, term: additiveTerm(sorted.items), proof };
    }
    if (term.tag === "app" && term.args.length === 2 && term.fn === presentation.mul) {
      const left = normalize(term.args[0]!);
      const right = normalize(term.args[1]!);
      const expanded = multiply(left.items, right.items);
      const sorted = sortPolynomial(expanded.items);
      const proof = calc(
        congr(presentation.mul, left.proof, right.proof), expanded.proof, sorted.proof,
      );
      return { items: sorted.items, term: additiveTerm(sorted.items), proof };
    }
    // A power with a literal exponent is its product: a ^ 2 is a * a.
    if (term.tag === "app" && term.args.length > 0) {
      const power = expandLiteralPower(kernel, term, assumptions, refinements);
      if (power && (power.term.tag === "nat" || (power.term.tag === "app" && power.term.fn === presentation.mul))) {
        const inner = normalize(power.term);
        return { items: inner.items, term: inner.term, proof: calc(power.proof, inner.proof) };
      }
    }
    // An atom's arguments are normalized too, so f(n + n) and f(2 * n) are
    // the same atom; an argument that is not a natural number is kept as is.
    if (term.tag === "app" && term.args.length > 0) {
      const arguments_: Term[] = [];
      const proofs: Proof[] = [];
      let changed = false;
      for (const argument of term.args) {
        let result: { term: Term; proof: Proof } | undefined;
        try { result = normalize(argument); }
        catch (error) { if (!(error instanceof SurfaceError)) throw error; }
        if (result && !termEquals(result.term, argument)) { changed = true; arguments_.push(result.term); proofs.push(result.proof); }
        else { arguments_.push(argument); proofs.push(refl(argument)); }
      }
      if (changed) {
        const rebuilt = app(term.fn, ...arguments_);
        return { items: [{ factors: [rebuilt] }], term: rebuilt, proof: congr(term.fn, ...proofs) };
      }
    }
    const items = [{ factors: [term] }];
    return { items, term, proof: refl(term) };
  };
  const normalized = normalize(source);
  return { term: normalized.term, proof: normalized.proof, monomials: normalized.items };
}

// Computation certificates replayed in this process, keyed by the closed
// equation. A check of a module repeated in one process, as the Workbench
// and `serve` loops do, reuses the certificate instead of evaluating the
// terms again to build it; the kernel still replays every certificate it
// admits, so a stale entry fails that replay and is rebuilt. Nothing is
// persisted.
const computationCertificates = new Map<string, readonly string[]>();
const COMPUTATION_CERTIFICATE_CACHE = 512;

function cachedComputation(kernel: Kernel, left: Term, right: Term): {
  readonly proof: Proof; readonly key: string; readonly reused: boolean;
} {
  const key = formulaCanonical(eq(left, right));
  const cached = computationCertificates.get(key);
  if (cached) return { proof: compute(left, right, cached), key, reused: true };
  const proof = kernel.proveComputation(left, right);
  if (proof.rule === "compute") {
    if (computationCertificates.size >= COMPUTATION_CERTIFICATE_CACHE) {
      computationCertificates.delete(computationCertificates.keys().next().value!);
    }
    computationCertificates.set(key, proof.definitions);
  }
  return { proof, key, reused: false };
}

/**
 * A closed natural-number order goal for `compute`: `a < b`, `a ≤ b`, or
 * `a ≠ b` with both sides evaluable. The sides are evaluated natively and
 * the gap between them is the witness of the order's definition; a false
 * comparison is reported with the two values.
 */
function closedNaturalOrder(kernel: Kernel, goal: Formula, line: number, scope: SurfaceScope): {
  readonly relation: "less" | "lessEqual" | "notEqual";
  readonly less: string;
  readonly left: Term;
  readonly right: Term;
  readonly leftSmaller: boolean;
  readonly gap: bigint;
} | undefined {
  // The order predicates of the naturals, from the core library.
  const less = resolveOptional("Less", scope, candidate => kernel.predicates.get(candidate) === 2);
  const lessEqual = resolveOptional("LessEqual", scope, candidate => kernel.predicates.get(candidate) === 2);
  if (!less || !lessEqual) return undefined;
  let relation: "less" | "lessEqual" | "notEqual";
  let left: Term;
  let right: Term;
  if (goal.tag === "pred" && goal.args.length === 2 && (goal.pred === less || goal.pred === lessEqual)) {
    relation = goal.pred === less ? "less" : "lessEqual";
    [left, right] = goal.args as [Term, Term];
  } else if (goal.tag === "imp" && goal.right.tag === "bottom" && goal.left.tag === "eq") {
    relation = "notEqual";
    ({ left, right } = goal.left);
  } else return undefined;
  if (freeTermVariables(left).size || freeTermVariables(right).size) return undefined;
  const value = (term: Term): bigint => {
    let result: ReturnType<typeof evaluateNative>["value"];
    try { result = evaluateNative(kernel, term).value; }
    catch (error) {
      throw new SurfaceError(line, `compute could not evaluate ${formatTerm(term)}: ${error instanceof Error ? error.message : String(error)}`);
    }
    if (typeof result !== "bigint") throw new SurfaceError(line, `compute: ${formatTerm(term)} does not evaluate to a natural number`);
    return result;
  };
  const a = value(left);
  const b = value(right);
  const holds = relation === "less" ? a < b : relation === "lessEqual" ? a <= b : a !== b;
  if (!holds) throw new SurfaceError(line, `compute: ${formatFormula(goal)} is false; the sides evaluate to ${a} and ${b}`);
  const leftSmaller = a < b;
  const [small, large] = leftSmaller ? [a, b] : [b, a];
  return { relation, less, left, right, leftSmaller,
    gap: relation === "lessEqual" ? b - a : large - small - 1n };
}

function naturalLinearArithmeticPresentation(
  kernel: Kernel, line: number, scope: SurfaceScope,
): LinearArithmeticPresentation {
  let presentation = linearArithmeticPresentations.get(kernel);
  if (presentation) return presentation;
  const symbol = (name: string, kind: "function" | "predicate"): string => {
    const resolved = resolveOptional(name, scope, candidate =>
      kind === "function" ? kernel.functions.has(candidate) : kernel.predicates.has(candidate));
    if (!resolved) throw new SurfaceError(line, `linear arithmetic requires ${name}`);
    return resolved;
  };
  presentation = Object.freeze({
    carrier: "Nat",
    add: symbol("add", "function"),
    mul: symbol("mul", "function"),
    successor: symbol("succ", "function"),
    less: symbol("Less", "predicate"),
    lessEqual: symbol("LessEqual", "predicate"),
    strictGap: resolveProof(kernel, "Grace.Cumulus.Nat.Order.Less.gap", line, scope),
    lessEqualReflexive: resolveProof(kernel, "Grace.Core.Nat.Order.LessEqual.reflexive", line, scope),
    lessEqualZero: resolveProof(kernel, "Grace.Core.Nat.Order.LessEqual.zero", line, scope),
    lessEqualAddRight: resolveProof(kernel, "Grace.Core.Nat.Order.LessEqual.add_right", line, scope),
    lessEqualAddLeftCancel: resolveProof(kernel, "Grace.Cumulus.Nat.Order.LessEqual.add_left_cancel", line, scope),
    lessEqualAntisymmetric: resolveProof(kernel, "Grace.Cumulus.Nat.Order.LessEqual.antisymmetric", line, scope),
    lessIrreflexive: resolveProof(kernel, "Grace.Cumulus.Nat.Order.Less.irreflexive", line, scope),
    lessTransitiveLessEqual: resolveProof(kernel, "Grace.Cumulus.Nat.Order.Less.transitive_LessEqual", line, scope),
    lessOfNotLessEqual: resolveProof(kernel, "Grace.Cumulus.Nat.Order.Less.of_not_LessEqual", line, scope),
    lessEqualOfNotLess: resolveProof(kernel, "Grace.Cumulus.Nat.Order.LessEqual.of_not_Less", line, scope),
    addLessLess: resolveProof(kernel, "Grace.Cumulus.Nat.Order.Less.add", line, scope),
    addLessLessEqual: resolveProof(kernel, "Grace.Cumulus.Nat.Order.Less.add_LessEqual", line, scope),
    addLessEqualLess: resolveProof(kernel, "Grace.Cumulus.Nat.Order.LessEqual.add_Less", line, scope),
    addLessEqualLessEqual: resolveProof(kernel, "Grace.Cumulus.Nat.Order.LessEqual.add", line, scope),
  });
  linearArithmeticPresentations.set(kernel, presentation);
  return presentation;
}

function resolveRules(kernel: Kernel, names: readonly string[], line: number, scope: SurfaceScope): Proof[] {
  const rules: Proof[] = [];
  for (const rawName of names) {
    const notationTarget = visibleInfixNotations(kernel, scope, line).get(rawName)?.target;
    const name = notationTarget ?? resolveOptional(surfaceSymbol(rawName), scope, candidate =>
      kernel.definitions.has(candidate) || kernel.theorems.has(candidate) || kernel.axioms.has(candidate) ||
      Boolean(definitionProperty(kernel, candidate)), true);
    if (!name) {
      const nearest = nearestName([...kernel.theorems.keys(), ...kernel.definitions.keys()], rawName);
      throw new SurfaceError(line, `unknown settle rule ${rawName}${nearest ? `; did you mean ${nearest}?` : ""}`);
    }
    const property = definitionProperty(kernel, name);
    if (!kernel.definitions.has(name) && !kernel.theorems.has(name) && !kernel.axioms.has(name) && property) {
      rules.push(definition(property.definition, property.property));
      continue;
    }
    const record = kernel.definitions.get(name);
    if (record) {
      const equations = [...record.properties.keys()].filter(key => key.startsWith("equation.")).sort();
      if (equations.length === 0) rules.push(preferredDefinitionProof(name, record));
      else equations.forEach(property => rules.push(definition(name, property)));
    } else if (kernel.theorems.has(name)) {
      rules.push(theorem(name));
    } else if (kernel.axioms.has(name)) {
      rules.push(axiom(name));
    } else {
      throw new SurfaceError(line, `unknown settle rule ${name}`);
    }
  }
  return rules;
}

/** Small, predictable mathematical simp prelude; absent library rules are skipped. */
/**
 * Lemmas for ground reasoning: every visible membership characterization
 * (theorems and definition properties named `membership`) and the Subset
 * definition. They are instantiated only where the problem's atoms match.
 */
interface GroundRuleCache { theoremsScanned: number; definitionsScanned: number; readonly membership: Proof[]; readonly subset: Proof[] }
const groundRuleCaches = new WeakMap<Kernel, Map<string, GroundRuleCache>>();
function defaultGroundRules(kernel: Kernel, line: number, scope: SurfaceScope): Proof[] {
  // The scan is incremental per scope: only declarations admitted since the
  // last call are examined, and visibility is resolved only for the
  // membership rules among them.
  const key = `${scope.moduleName ?? ""}:${scope.imports.join(",")}`;
  let cache = groundRuleCaches.get(kernel);
  if (!cache) { cache = new Map(); groundRuleCaches.set(kernel, cache); }
  let entry = cache.get(key);
  if (!entry) {
    const subset: Proof[] = [];
    try { subset.push(...resolveRules(kernel, ["Subset"], line, scope)); }
    catch (error) { if (!(error instanceof SurfaceError)) throw error; }
    entry = { theoremsScanned: 0, definitionsScanned: 0, membership: [], subset };
    cache.set(key, entry);
  }
  if (entry.theoremsScanned < kernel.theorems.size) {
    let index = 0;
    for (const name of kernel.theorems.keys()) {
      if (index++ < entry.theoremsScanned) continue;
      if (name.endsWith(".membership") && visibleDeclaration(name, scope)) entry.membership.push(theorem(name));
    }
    entry.theoremsScanned = kernel.theorems.size;
  }
  if (entry.definitionsScanned < kernel.definitions.size) {
    let index = 0;
    for (const [name, record] of kernel.definitions) {
      if (index++ < entry.definitionsScanned) continue;
      if (record.properties.has("membership") && visibleDeclaration(name, scope)) entry.membership.push(definition(name, "membership"));
    }
    entry.definitionsScanned = kernel.definitions.size;
  }
  return [...entry.membership, ...entry.subset];
}

/** The Subset definition, so a subset goal unfolds to its pointwise form by itself. */
function defaultSettleRules(kernel: Kernel, line: number, scope: SurfaceScope): Proof[] {
  try { return resolveRules(kernel, ["Subset"], line, scope); }
  catch (error) {
    if (error instanceof SurfaceError && error.message.includes("unknown settle rule")) return [];
    throw error;
  }
}

function defaultSimpRules(kernel: Kernel, line: number, scope: SurfaceScope): Proof[] {
  return [
    "Grace.Cumulus.Set.Finite.FiniteSet.union2.membership",
    "Grace.Cumulus.Set.Finite.FiniteSet.singleton.membership",
    "pair.membership",
  ].flatMap(name => {
    try { return resolveRules(kernel, [name], line, scope); }
    catch (error) {
      if (error instanceof SurfaceError && error.message.includes("unknown settle rule")) return [];
      throw error;
    }
  });
}

function preferredDefinitionProof(name: string, record: DefinitionRecord): Proof {
  if (record.properties.has("equation")) return definition(name);
  if (record.properties.has("membership")) return definition(name, "membership");
  const property = record.properties.keys().next().value as string | undefined;
  if (!property) throw new Error(`definition ${name} has no properties`);
  return definition(name, property);
}

/**
 * The canonical name of a declaration. A function or predicate declared
 * again in the same module at another arity, `Compact(X)` beside
 * `Compact(X, A)`, lives under the namespace `arityN` of its module, which
 * the name index treats as open wherever the module is, so written names
 * resolve by arity as they do across modules and print as the plain name.
 */
function qualifyDeclaration(
  name: string, scope: SurfaceScope, overload?: { readonly kernel: Kernel; readonly kind: "function" | "predicate"; readonly arity: number },
): string {
  let qualified = [...scope.namespaces, name].filter(Boolean).join(".");
  if (overload && !name.includes(".")) {
    const declared = overload.kind === "predicate" ? overload.kernel.predicates.get(qualified) : overload.kernel.functions.get(qualified);
    if (declared !== undefined && declared !== overload.arity && scope.resolution?.owners.get(qualified) === scope.moduleName) {
      qualified = [...scope.namespaces, `arity${overload.arity}`, name].filter(Boolean).join(".");
    }
  }
  const owner = scope.resolution?.owners.get(qualified);
  if (owner && owner !== scope.moduleName)
    throw new SurfaceError(scope.line ?? 1, `duplicate declaration ${qualified}; already provided by module ${owner}`);
  scope.resolution?.register(qualified, scope.moduleName);
  return qualified;
}

function resolutionCandidates(name: string, scope: SurfaceScope): string[] {
  const candidates: string[] = [];
  for (let length = scope.namespaces.length; length > 0; length--)
    candidates.push(`${scope.namespaces.slice(0, length).join(".")}.${name}`);
  candidates.push(...scope.opens.map(opened => `${opened}.${name}`), name);
  return [...new Set(candidates)];
}

function visibleDeclaration(name: string, scope: SurfaceScope): boolean {
  const owner = scope.resolution?.owner(name);
  return !owner || owner === scope.moduleName || Boolean(scope.visibleModules?.has(owner));
}

/** The predicate and function symbols a formula mentions. */
function formulaSymbols(formula: Formula, into = new Set<string>()): Set<string> {
  const visitTerm = (term: Term): void => {
    if (term.tag !== "app") return;
    into.add(term.fn);
    term.args.forEach(visitTerm);
  };
  switch (formula.tag) {
    case "bottom": return into;
    case "eq": visitTerm(formula.left); visitTerm(formula.right); return into;
    case "pred": into.add(formula.pred); formula.args.forEach(visitTerm); return into;
    case "imp": case "and": case "or": case "iff": formulaSymbols(formula.left, into); return formulaSymbols(formula.right, into);
    case "forall": case "exists": return formulaSymbols(formula.body, into);
  }
}

function resolveOptional(
  name: string, scope: SurfaceScope, exists: (candidate: string) => boolean, affinity = false,
): string | undefined {
  // `_root_.Grace.Cumulus.Set.Classes.MemberOf.equation` names a declaration
  // by its full name, however the namespaces and imports stand; the search
  // tactics spell a result this way when no shorter name reaches it.
  if (name.startsWith("_root_.")) {
    const absolute = name.slice("_root_.".length);
    return exists(absolute) ? absolute : undefined;
  }
  const index = scope.resolution ?? new NameResolutionIndex();
  try {
    return index.resolve(name, scope.namespaces, scope.opens, exists,
      candidate => visibleDeclaration(candidate, scope));
  } catch (error) {
    if (error instanceof AmbiguousNameError) {
      // Among declarations sharing a short name, as the six-place Ring over
      // separate pieces and the Ring structure's predicate, the one the goal
      // or a local fact mentions is meant: `unfold Ring` on `Ring(P)`.
      const mentioned = new Set<string>();
      const goal = scope.goal?.();
      if (goal) formulaSymbols(goal, mentioned);
      // The goal decides first, so `unfold Compact` on `Compact(X)` means the
      // one-place predicate although a local fact mentions the two-place one.
      const inGoal = error.candidates.filter(candidate => mentioned.has(candidate));
      if (inGoal.length === 1) return inGoal[0];
      for (const formula of scope.localFormulas?.() ?? []) formulaSymbols(formula, mentioned);
      const present = error.candidates.filter(candidate => mentioned.has(candidate));
      if (present.length === 1) return present[0];
      // Failing that, a definition to unfold or rewrite with is the one
      // declared in a module the goal or a local fact already draws on:
      // `simp [MaximalIdeal, ProperIdeal]` under a six-place MaximalIdeal
      // means the six-place ProperIdeal beside it.
      if (affinity) {
        const owners = new Set([...mentioned].map(symbol => index.owner(symbol)).filter(owner => owner !== undefined));
        const neighbours = error.candidates.filter(candidate => owners.has(index.owner(candidate)));
        if (neighbours.length === 1) return neighbours[0];
      }
      const candidates = error.candidates.map(candidate => {
        const owner = index.owner(candidate);
        return owner ? `${candidate} (module ${owner})` : candidate;
      });
      throw new SurfaceError(scope.line ?? 1, `ambiguous name ${name}; qualify one of: ${candidates.join(", ")}`);
    }
    throw error;
  }
}

function visibleInstanceNames(kernel: Kernel, scope: SurfaceScope): ReadonlySet<string> {
  const environment = surfaceEnvironments.get(kernel);
  if (!environment) return new Set();
  const cache = surfaceVisibilityCache(kernel, environment);
  const key = scopeVisibilityKey(scope);
  const cached = cache.instances.get(key);
  if (cached) return cached;
  const reachable = reachableImports(cache, environment, scope);
  const result = new Set(environment.instances.filter(item =>
    item.module === undefined || item.module === scope.moduleName || reachable.has(item.module)).map(item => item.name));
  cache.instances.set(key, result);
  return result;
}

/**
 * What the refinement prover and the guard registry may consult from a
 * scope: the typing rules of the declarations the scope sees and the guard
 * predicates its visible notations registered, by the rule that governs
 * names and instances. A kernel without a surface environment sees everything.
 */
function scopeVisibility(kernel: Kernel, scope: SurfaceScope): ScopeVisibility | undefined {
  const environment = surfaceEnvironments.get(kernel);
  if (!environment) return undefined;
  const cache = surfaceVisibilityCache(kernel, environment);
  const key = scopeVisibilityKey(scope);
  const cached = cache.visibility.get(key);
  if (cached) return cached;
  const reachable = reachableImports(cache, environment, scope);
  const resolution = resolutionIndex(environment);
  const moduleName = scope.moduleName;
  const visibleModule = (module: string | undefined): boolean =>
    module === undefined || module === moduleName || reachable.has(module);
  const declarations = new Map<string, boolean>();
  const result: ScopeVisibility = {
    module: visibleModule,
    declaration: name => {
      let visible = declarations.get(name);
      if (visible === undefined) { visible = visibleModule(resolution.owner(name)); declarations.set(name, visible); }
      return visible;
    },
  };
  cache.visibility.set(key, result);
  return result;
}

function visibleInfixNotationGroups(
  kernel: Kernel, scope: SurfaceScope, line: number, kind?: "function" | "predicate",
  fixity: "infix" | "prefix" | "postfix" | "numeral" | "alias" | "binder" | "mixfix" | "constant" | "function" | "sequence" | "coercion" | "scoped" = "infix",
): ReadonlyMap<string, readonly SurfaceNotationRecord[]> {
  const environment = surfaceEnvironments.get(kernel);
  if (!environment) return new Map();
  const cache = surfaceVisibilityCache(kernel, environment);
  const cacheKey = `${scopeVisibilityKey(scope)}\u0000${kind ?? "*"}\u0000${fixity}`;
  const cached = cache.notationGroups.get(cacheKey);
  if (cached) return cached;
  const reachable = reachableImports(cache, environment, scope);
  const visible = environment.notations.filter(item =>
    (!kind || item.kind === kind) &&
    (fixity === "infix" ? item.fixity === undefined : item.fixity === fixity) &&
    (item.module === undefined || item.module === scope.moduleName || reachable.has(item.module)));
  const result = new Map<string, readonly SurfaceNotationRecord[]>();
  for (const token of new Set(visible.map(item => item.token))) {
    const candidates = visible.filter(item => item.token === token);
    const local = candidates.filter(item => item.module !== undefined && item.module === scope.moduleName);
    const imported = candidates.filter(item => item.module !== undefined && reachable.has(item.module));
    const fallback = candidates.filter(item => item.module === undefined);
    let selected = local.length ? local : imported.length ? imported : fallback;
    // Typed overloads and hypothesis shapes of one token accumulate across
    // modules: each declaration names a distinct operand type or hypothesis.
    const overloadable = (item: SurfaceNotationRecord): boolean => notationIsTyped(item) || item.hypothesis !== undefined;
    // A form whose left operand is the structure itself, G ⧸ N, never
    // shadows the declarations it falls back to, so the set quotient A ⧸ r
    // keeps its meaning in the module that declares it.
    const shadowing = local.some(item => !item.hypothesis?.structureOperand);
    if (local.length && (!shadowing || (local.every(overloadable) && imported.every(overloadable)))) {
      selected = [...local, ...imported, ...(shadowing ? [] : fallback)];
    }
    const unique = selected.filter((item, index) => selected.findIndex(other =>
      other.precedence === item.precedence && other.associativity === item.associativity && other.kind === item.kind &&
      other.fixity === item.fixity && other.reversed === item.reversed && other.target === item.target &&
      canonical(other.leadingArguments ?? []) === canonical(item.leadingArguments ?? []) &&
      other.operandType === item.operandType && other.leftOperandType === item.leftOperandType &&
      other.rightOperandType === item.rightOperandType &&
      JSON.stringify(other.expansion ?? null) === JSON.stringify(item.expansion ?? null) &&
      JSON.stringify(other.hypothesis ?? null) === JSON.stringify(item.hypothesis ?? null)) === index);
    // A form whose left operand is the structure itself rivals none of the
    // other declarations, which it falls back to.
    const rivals = unique.filter(item => !item.hypothesis?.structureOperand);
    const typedUnique = rivals.filter(notationIsTyped);
    const aligned = unique.every(item => item.precedence === unique[0]!.precedence &&
      item.associativity === unique[0]!.associativity && item.kind === unique[0]!.kind &&
      item.reversed === unique[0]!.reversed);
    const overload = unique.length > 1 && aligned && (rivals.length <= 1 || (rivals.every(overloadable) &&
      new Set(typedUnique.map(notationTypeKey)).size === typedUnique.length));
    if (unique.length > 1 && !overload) {
      throw new SurfaceError(line, `ambiguous notation ${token}; visible declarations target ${unique.map(item => item.target).join(", ")}`);
    }
    if (unique[0]) result.set(token, unique);
  }
  cache.notationGroups.set(cacheKey, result);
  return result;
}

function notationOperandTypes(item: SurfaceNotationRecord): readonly [string | undefined, string | undefined] {
  return [item.leftOperandType ?? item.operandType, item.rightOperandType ?? item.operandType];
}

function notationIsTyped(item: SurfaceNotationRecord): boolean {
  const [left, right] = notationOperandTypes(item);
  return Boolean(left && right);
}

function notationTypeKey(item: SurfaceNotationRecord): string {
  const [left, right] = notationOperandTypes(item);
  return `${left ?? ""}\u0000${right ?? ""}`;
}

function notationTypeLabel(item: SurfaceNotationRecord): string {
  const [left, right] = notationOperandTypes(item);
  if (!left || !right) return "untyped";
  const short = (type: string): string => type.split(".").at(-1)!;
  return left === right ? short(left) : `${short(left)}, ${short(right)}`;
}

function surfaceVisibilityCache(kernel: Kernel, environment: SurfaceEnvironment): SurfaceVisibilityCache {
  const stamp = `${environment.modules.size}:${environment.notations.length}:${environment.instances.length}`;
  const cached = surfaceVisibilityCaches.get(kernel);
  if (cached?.environment === environment && cached.stamp === stamp) return cached;
  const fresh: SurfaceVisibilityCache = {
    environment, stamp, reachable: new Map(), instances: new Map(), notationGroups: new Map(), resultTypes: new Map(),
    visibility: new Map(),
  };
  surfaceVisibilityCaches.set(kernel, fresh);
  return fresh;
}

function scopeVisibilityKey(scope: SurfaceScope): string {
  return `${scope.moduleName ?? ""}\u0000${scope.imports.join("\u0001")}`;
}

function reachableImports(
  cache: SurfaceVisibilityCache, environment: SurfaceEnvironment, scope: SurfaceScope,
): ReadonlySet<string> {
  const key = scope.imports.join("\u0001");
  const cached = cache.reachable.get(key);
  if (cached) return cached;
  const reachable = new Set(scope.imports);
  const pending = [...reachable];
  while (pending.length) {
    const imported = pending.pop()!;
    for (const dependency of environment.modules.get(imported)?.imports ?? []) {
      if (!reachable.has(dependency)) { reachable.add(dependency); pending.push(dependency); }
    }
  }
  cache.reachable.set(key, reachable);
  return reachable;
}

function visibleInfixNotations(
  kernel: Kernel, scope: SurfaceScope, line: number, kind?: "function" | "predicate",
): ReadonlyMap<string, SurfaceNotationRecord> {
  const result = new Map<string, SurfaceNotationRecord>();
  for (const [token, candidates] of visibleInfixNotationGroups(kernel, scope, line, kind)) {
    if (candidates.length === 1) result.set(token, candidates[0]!);
  }
  return result;
}

function resolveExisting(
  name: string,
  scope: SurfaceScope,
  exists: (candidate: string) => boolean,
  line: number,
  kind: string,
): string {
  const resolved = resolveOptional(name, scope, exists);
  if (!resolved) throw new SurfaceError(line, `unknown ${kind} ${name}`);
  return resolved;
}

function resolveNamespace(name: string, scope: SurfaceScope, environment: SurfaceEnvironment, line: number): string {
  if (!QUALIFIED_IDENTIFIER.test(name)) throw new SurfaceError(line, "malformed namespace name");
  const resolved = resolveOptional(surfaceSymbol(name), scope, candidate => {
    if (!environment.namespaces.has(candidate) && !scope.resolution?.namespaceOwners.has(candidate)) return false;
    const owners = scope.resolution?.namespaceOwners.get(candidate);
    return !owners || [...owners].some(owner => !owner || owner === scope.moduleName || scope.visibleModules?.has(owner));
  });
  if (!resolved) throw new SurfaceError(line, `unknown or unimported namespace ${name}`);
  return resolved;
}

function parseBinders(text: string, line: number, implicit = false): Binder[] {
  const result: Binder[] = [];
  for (const group of splitTopLevel(text, ",")) {
    // `(a b ∈ O)` binds set variables guarded by membership in O; the bound
    // is kept as text until the binder's variables are known.
    const bounded = /^\s*([^:]+?)\s+(?:∈|in)\s+(.+?)\s*$/u.exec(group);
    const match = bounded ? null : /^\s*(.+?)\s*:\s*(.+?)\s*$/u.exec(group);
    if (!match && !bounded) throw new SurfaceError(line, "expected binders such as `(x y : Nat)`, `(a ∈ O)`, or `(x : Set, n : Nat)`");
    const names = (bounded ?? match)![1]!.trim().split(/\s+/);
    if (names.some(name => !SIMPLE_IDENTIFIER.test(name))) throw new SurfaceError(line, "malformed binder name");
    const type = bounded ? `∈ ${bounded[2]!.trim()}` : surfaceType(match![2]!.trim());
    result.push(...names.map(name => ({ name, type, implicit })));
  }
  if (result.length === 0 || new Set(result.map(item => item.name)).size !== result.length) {
    throw new SurfaceError(line, "binders must be nonempty and distinct");
  }
  return result;
}

/** Parse a declaration prefix such as `{A : Set} (xs : List(A))`. */
function parseBinderGroups(text: string, line: number): { readonly binders: Binder[]; readonly rest: string } {
  const binders: Binder[] = [];
  let offset = 0;
  while (offset < text.length) {
    while (/\s/.test(text[offset] ?? "")) offset += 1;
    const open = text[offset];
    if (open !== "(" && open !== "{") break;
    const close = open === "(" ? ")" : "}";
    let depth = 0;
    let end = -1;
    for (let index = offset; index < text.length; index += 1) {
      if (text[index] === open) depth += 1;
      else if (text[index] === close) depth -= 1;
      if (depth === 0) { end = index; break; }
    }
    if (end < 0) throw new SurfaceError(line, `unclosed ${open} binder group`);
    binders.push(...parseBinders(text.slice(offset + 1, end), line, open === "{"));
    offset = end + 1;
  }
  if (new Set(binders.map(item => item.name)).size !== binders.length) {
    throw new SurfaceError(line, "binders must be distinct");
  }
  return { binders, rest: text.slice(offset).trim() };
}

function scopedBinders(scope: SurfaceScope, binders: readonly Binder[]): SurfaceScope {
  return { ...scope, binderTypes: new Map(binders.map(item => [item.name, item])) };
}

function resolvedResultType(
  source: string, kernel: Kernel, scope: SurfaceScope, line: number, variables: ReadonlySet<string>,
): { readonly type: string; readonly arguments: readonly Term[] } {
  if (source === "Set" || source === "Nat") return { type: source, arguments: [] };
  const application = /^([^\s(]+)(?:\((.*)\))?$/.exec(source);
  if (!application) throw new SurfaceError(line, `malformed result type ${source}`);
  const arguments_ = application[2]?.trim()
    ? splitTopLevel(application[2]!, ",").map(item => parseTerm(item, kernel, variables, line, scope)) : [];
  for (const argument of arguments_) {
    try { kernel.checkProof(refl(argument)); }
    catch (error) { throw new SurfaceError(line, `invalid result-type carrier in ${source}: ${error instanceof Error ? error.message : String(error)}`); }
  }
  const type = resolveOptional(application[1]!, scope, candidate => kernel.predicates.get(candidate) === arguments_.length + 1);
  if (!type) throw new SurfaceError(line, `unknown definition result type ${source}`);
  return { type, arguments: arguments_ };
}

function resolveResultType(
  source: string, kernel: Kernel, scope: SurfaceScope, line: number, variables: ReadonlySet<string>,
): string {
  return resolvedResultType(source, kernel, scope, line, variables).type;
}

function resolveBinderTypes(
  binders: readonly Binder[], kernel: Kernel, scope: SurfaceScope, line: number,
  extra: readonly string[] = [], outer: ReadonlySet<string> = new Set(), deferred?: Set<string>,
): Binder[] {
  const variables = new Set([...outer, ...binders.map(item => item.name)]);
  // The guards of earlier binders are in scope for later ones, so that
  // `(a b ∈ O) (f : a ⟶ b)` reads the arrow in the category whose objects
  // are O.
  const earlierGuards: Formula[] = [];
  const guardScope: SurfaceScope = { ...scope, localFormulas: () => [...(scope.localFormulas?.() ?? []), ...earlierGuards] };
  return binders.map(binder => {
    if (["Set", "Nat", "Class", ...extra].includes(binder.type)) return binder;
    if (binder.type.startsWith("∈ ")) {
      const guard = pred("in", v(binder.name),
        structureCarrier(kernel, guardScope, parseTerm(binder.type.slice(2), kernel, variables, line, guardScope)));
      earlierGuards.push(guard);
      return { ...binder, type: "Set", guard };
    }
    const guard = mixfixBinderGuard(binder, kernel, variables, line, guardScope) ??
      carrierBinderGuard(binder, kernel, variables, line, guardScope);
    if (guard) { earlierGuards.push(guard); return { ...binder, type: "Set", guard }; }
    const application = /^([^\s(]+)(?:\((.*)\))?$/.exec(binder.type);
    if (!application) throw new SurfaceError(line, `malformed soft type ${binder.type}`);
    const arguments_ = application[2]?.trim()
      ? splitTopLevel(application[2]!, ",").map(item => parseTerm(item, kernel, variables, line, scope)) : [];
    for (const argument of arguments_) {
      try { kernel.checkProof(refl(argument)); }
      catch (error) { throw new SurfaceError(line, `invalid input-type carrier in ${binder.type}: ${error instanceof Error ? error.message : String(error)}`); }
    }
    const type = resolveOptional(application[1]!, scope, candidate => kernel.predicates.get(candidate) === arguments_.length + 1);
    if (!type) {
      // A binder typed by a variable of the same header, (g : G), waits for
      // the requires clauses that may supply G's carrier, Group(G).
      if (deferred && SIMPLE_IDENTIFIER.test(binder.type) && variables.has(binder.type)) {
        deferred.add(binder.name);
        return { ...binder, type: "Set" };
      }
      const structure = SIMPLE_IDENTIFIER.test(binder.type) && variables.has(binder.type)
        ? `; a binder (${binder.name} : ${binder.type}) needs a hypothesis giving ${binder.type} a carrier, such as Group(${binder.type}), ` +
          "in a section hypothesis or a requires clause of this theorem"
        : "";
      throw new SurfaceError(line, `unknown soft type ${binder.type}${structure}`);
    }
    return { ...binder, type, typeArguments: arguments_ };
  });
}

/** A binder that generates a guard requirement: a soft type, or a mixfix guard such as `(f : A → B)`. */
function isGuardBinder(item: Binder): boolean {
  return item.guard !== undefined || (item.type !== "Set" && item.type !== "Class");
}

function binderAssumptions(binders: readonly Binder[]): Formula[] {
  return binders.flatMap(item => item.guard ? [item.guard]
    : item.type !== "Set" && item.type !== "Class" ? [pred(item.type, ...(item.typeArguments ?? []), v(item.name))] : []);
}

/**
 * A binder whose type is written with a mixfix notation that starts with the
 * colon: `(f : A → B)` is the set variable `f` with the guard
 * FunctionBetween(f, A, B), exactly as `(n : Nat)` guards `n` with Nat(n).
 */
function mixfixBinderGuard(
  binder: Binder, kernel: Kernel, variables: ReadonlySet<string>, line: number, scope: SurfaceScope,
): Formula | undefined {
  const groups = visibleInfixNotationGroups(kernel, scope, line, "predicate", "mixfix");
  for (const candidates of groups.values()) {
    const literals = mixfixLiterals(candidates[0]!.token);
    if (literals[0] !== ":") continue;
    const pieces: string[] = [];
    let rest = binder.type;
    let matched = true;
    for (const literal of literals.slice(1)) {
      const found = findMixfixToken(rest, literal);
      if (!found || found.index === 0) { matched = false; break; }
      pieces.push(rest.slice(0, found.index).trim());
      rest = rest.slice(found.index + found.length);
    }
    if (!matched) continue;
    pieces.push(rest.trim());
    if (pieces.some(piece => !piece)) continue;
    let operands: Term[];
    try {
      operands = [v(binder.name), ...pieces.map(piece => parseTerm(piece, kernel, variables, line, scope))];
    } catch (error) {
      if (!(error instanceof SurfaceError)) throw error;
      continue;
    }
    return mixfixApplication(kernel, scope, candidates, operands, line);
  }
  return undefined;
}

/**
 * A binder typed by a structure variable: `(a b : G)` under a hypothesis
 * `Group(G)` is the set variables `a` and `b` guarded by membership in
 * `carrier(G)`, the carrier the hypothesis notation of `Group` names, as
 * `(h : H)` under `Subgroup(H, G)` is membership in `H`. The structure must
 * be a variable in scope, and the carrier a term of that variable alone.
 */
function carrierBinderGuard(
  binder: Binder, kernel: Kernel, variables: ReadonlySet<string>, line: number, scope: SurfaceScope,
): Formula | undefined {
  let structure: Term;
  if (SIMPLE_IDENTIFIER.test(binder.type)) {
    if (!variables.has(binder.type)) return undefined;
    structure = v(binder.type);
  } else {
    // A binder typed by a structure value, `(p : polynomialRing(R, I))`,
    // whose structure an instance supplies under the facts in scope.
    if (!/^[\p{L}_][\p{L}\p{M}\p{N}_.]*\(.*\)$/u.test(binder.type)) return undefined;
    let term: Term;
    try { term = parseTerm(binder.type, kernel, variables, line, scope); }
    catch (error) {
      if (!(error instanceof SurfaceError)) throw error;
      return undefined;
    }
    if (!structureValueOf(kernel, scope, term)) return undefined;
    structure = term;
  }
  const carriers = hypothesisCarriersOfTerm(kernel, scope, structure, line);
  if (carriers.length === 0) return undefined;
  if (carriers.length > 1) {
    throw new SurfaceError(line, `ambiguous binder (${binder.name} : ${binder.type}); hypotheses in scope give ${binder.type} the carriers ${carriers.map(item => formatTerm(item)).join(" and ")}; write (${binder.name} ∈ ${formatTerm(carriers[0]!)})`);
  }
  return pred("in", v(binder.name), carriers[0]!);
}

/** The carriers the hypotheses in scope give a structure variable, through the templates of the carrier notations. */
function hypothesisCarriersOf(kernel: Kernel, scope: SurfaceScope, name: string, line: number): Term[] {
  return hypothesisCarriersOfTerm(kernel, scope, v(name), line);
}

/**
 * The carriers the hypotheses in scope give a structure, a variable or a
 * term built by a structure's constructor whose structure an instance
 * supplies, through the templates of the carrier notations.
 */
/**
 * `(1 : G)` and `(0 : G)` for a structure variable G whose carrier a
 * hypothesis in scope supplies: the projections G.one and G.zero of that
 * structure, when it declares the field. Undefined otherwise.
 */
function structureConstant(
  kernel: Kernel, scope: SurfaceScope, term: Term, label: string, variables: ReadonlySet<string>, line: number,
): Term | undefined {
  const value = naturalValue(term);
  if (value === undefined || value > 1n || !SIMPLE_IDENTIFIER.test(label) || !variables.has(label)) return undefined;
  const carriers = hypothesisCarriersOfTerm(kernel, scope, v(label), line);
  if (carriers.length !== 1) return undefined;
  const carrier = carriers[0]!;
  if (carrier.tag !== "app" || carrier.args.length !== 1 || !termEquals(carrier.args[0]!, v(label))) return undefined;
  const member = structureMember(carrier.fn);
  if (member?.role !== "projection") return undefined;
  const field = structureFieldSymbol(member.structure, value === 1n ? "one" : "zero");
  return field ? app(field, v(label)) : undefined;
}

function hypothesisCarriersOfTerm(kernel: Kernel, scope: SurfaceScope, structure: Term, line: number): Term[] {
  const notations = visibleHypothesisCarrierNotations(kernel, scope, line);
  if (!notations.length) return [];
  const local = expandedLocalFormulas(kernel, scope);
  const facts = structure.tag === "var" ? local : [...local, ...instanceStructureFacts(kernel, scope, structure, local)];
  const carriers: Term[] = [];
  for (const notation of notations) {
    const pattern = notation.hypothesis!;
    for (const fact of facts) {
      if (fact.tag !== "pred" || fact.pred !== pattern.predicate || fact.args.length !== pattern.arity) continue;
      for (const template of pattern.carriers) {
        const free = [...freeTermVariables(template)];
        if (free.length !== 1) continue;
        const argument = fact.args[pattern.names.indexOf(free[0]!)];
        if (!argument || !termEquals(argument, structure)) continue;
        const carrier = instantiatePattern(template, pattern, fact);
        if (!carriers.some(item => termEquals(item, carrier))) carriers.push(carrier);
      }
    }
  }
  return carriers;
}

/** The structure whose constructor builds this term, directly or through a definition whose body is the constructor applied. */
function structureValueOf(kernel: Kernel, scope: SurfaceScope, term: Term): SurfaceDatatypeRecord | undefined {
  if (term.tag !== "app" || term.args.length === 0) return undefined;
  const head = definitionHeadSymbol(kernel, term.fn) ?? term.fn;
  return visibleStructures(kernel, scope).find(item => item.structure!.constructor === head);
}

const instanceStructureCache = new WeakMap<Kernel, Map<string, boolean>>();

/**
 * The structure facts the instances derive for a term built by a
 * structure's constructor, or by a definition whose body is one:
 * `CommRing(polynomialRing(R, I))` by `polynomialRing.comm_ring` under
 * `CommRing(R)`. The predicates tried are those of the hypothesis notations
 * in scope that take the structure first, the search is the bounded
 * instance search of `with *` under the facts given, and its outcomes are
 * remembered per kernel.
 */
function instanceStructureFacts(kernel: Kernel, scope: SurfaceScope, term: Term, assumptions: readonly Formula[]): Formula[] {
  const record = structureValueOf(kernel, scope, term);
  if (!record) return [];
  const structure = record.structure!;
  const line = scope.line ?? 0;
  const predicates = new Set<string>();
  for (const notation of [...visibleHypothesisCarrierNotations(kernel, scope, line),
      ...[...visibleInfixNotationGroups(kernel, scope, line, "function", "function").values()].flat()]) {
    const predicate = notation.hypothesis!.predicate;
    if (notation.hypothesis!.arity !== 1 || predicates.has(predicate)) continue;
    if (predicate === structure.predicate || predicate === record.predicate ||
        receiverParameters(kernel, predicate).get(0) === structure.predicate) predicates.add(predicate);
  }
  if (!predicates.size) return [];
  const context = assumptions.map(formulaCanonical).sort().join("\u0000");
  let cache = instanceStructureCache.get(kernel);
  if (!cache) { cache = new Map(); instanceStructureCache.set(kernel, cache); }
  const result: Formula[] = [];
  let prover: InstanceProver | undefined;
  for (const predicate of predicates) {
    const key = `${predicate}\u0000${termCanonical(term)}\u0000${scopeVisibilityKey(scope)}\u0000${context}`;
    let known = cache.get(key);
    if (known === undefined) {
      prover ??= prepareInstanceProver(kernel, visibleInstanceNames(kernel, scope), assumptions, [], {}, scopeVisibility(kernel, scope));
      try { known = prover.prove(term, predicate) !== undefined; }
      catch (error) {
        if (!(error instanceof InstanceResolutionError || error instanceof InstanceResolutionLimitError)) throw error;
        known = false;
      }
      if (cache.size > 4096) cache.clear();
      cache.set(key, known);
    }
    if (known) result.push(pred(predicate, term));
  }
  return result;
}

/**
 * The structure facts the instances supply for the compound terms the facts
 * and operands place elements in: from `p ∈ Ring.carrier(polynomialRing(R, I))`
 * comes `CommRing(polynomialRing(R, I))` under `CommRing(R)`, so that the
 * elements of a constructed structure carry its notation without a
 * hypothesis naming the instance.
 */
function derivedStructureFacts(
  kernel: Kernel, scope: SurfaceScope, facts: readonly Formula[], operands: readonly Term[] = [],
  extra: readonly Formula[] = [],
): Formula[] {
  const candidates: Term[] = [];
  const consider = (term: Term): void => {
    if (term.tag !== "app" || term.args.length === 0 || candidates.some(item => termEquals(item, term))) return;
    if (structureValueOf(kernel, scope, term)) candidates.push(term);
  };
  // A projection applied to a structure value, Ring.carrier(polynomialRing(R, I)),
  // wherever it stands in the facts given.
  const visitTerm = (term: Term): void => {
    if (term.tag !== "app") return;
    if (term.args.length === 1 && projectionOf(kernel, term.fn)) consider(term.args[0]!);
    term.args.forEach(visitTerm);
  };
  const visitFormula = (formula: Formula): void => {
    switch (formula.tag) {
      case "bottom": return;
      case "eq": visitTerm(formula.left); visitTerm(formula.right); return;
      case "pred": formula.args.forEach(visitTerm); return;
      case "imp": case "and": case "or": case "iff": visitFormula(formula.left); visitFormula(formula.right); return;
      case "forall": case "exists": visitFormula(formula.body); return;
    }
  };
  facts.forEach(visitFormula);
  extra.forEach(visitFormula);
  operands.forEach(consider);
  return candidates.flatMap(term => instanceStructureFacts(kernel, scope, term, facts));
}

const completedCarrierCache = new WeakMap<Kernel, Map<string, Term | undefined>>();

/**
 * The carrier the certified typing rules place a term in when the local
 * facts do not: `Ring.carrier(polynomialRing(R, I))` for `X(R, I, j)` by
 * the instance `X.mem`. The completion is the bounded instance search of
 * `with *` with the carrier as its hole, remembered per kernel.
 */
function completedCarrier(kernel: Kernel, scope: SurfaceScope, facts: readonly Formula[], term: Term): Term | undefined {
  if (term.tag !== "app" || term.args.length === 0) return undefined;
  const context = facts.map(formulaCanonical).sort().join("\u0000");
  const key = `${termCanonical(term)}\u0000${scopeVisibilityKey(scope)}\u0000${context}`;
  let cache = completedCarrierCache.get(kernel);
  if (!cache) { cache = new Map(); completedCarrierCache.set(kernel, cache); }
  if (cache.has(key)) return cache.get(key);
  let carrier: Term | undefined;
  try {
    carrier = prepareInstanceProver(kernel, visibleInstanceNames(kernel, scope), facts, [], {}, scopeVisibility(kernel, scope))
      .complete("in", [term, undefined])?.arguments[1];
  } catch (error) {
    if (!(error instanceof InstanceResolutionError || error instanceof InstanceResolutionLimitError)) throw error;
  }
  if (cache.size > 4096) cache.clear();
  cache.set(key, carrier);
  return carrier;
}

/** The conclusion of a closed theorem statement: the formula under its quantifier prefix and antecedents. */
function statementConclusion(statement: Formula): Formula {
  let formula = statement;
  while (formula.tag === "forall") formula = formula.body;
  while (formula.tag === "imp" && formula.right.tag !== "bottom") formula = formula.right;
  return formula;
}

/**
 * A structure variable read as its carrier where a set of elements is
 * meant: `x ∈ G`, `S ⊆ G`, `∀ x ∈ G`, `cardinality(G)`, and `Finite(G)`
 * under a hypothesis `Group(G)` are read at `G.carrier`, the carrier the
 * hypothesis notation names, and print back as written. A variable given
 * no carrier, or two, is left as it is.
 */
function structureCarrier(kernel: Kernel, scope: SurfaceScope, term: Term): Term {
  if (term.tag !== "var" && !structureValueOf(kernel, scope, term)) return term;
  const carriers = hypothesisCarriersOfTerm(kernel, scope, term, scope.line ?? 0);
  return carriers.length === 1 ? carriers[0]! : term;
}

/** The functions and predicates whose argument is a set of elements, so that a structure variable there is its carrier. */
const CARRIER_ARGUMENT_SYMBOLS = new Set([...CARRIER_ARGUMENT_FUNCTIONS, "Finite"]);

/**
 * The predicate a mixfix form denotes: for the plain declaration, the target
 * applied to the written placeholders; for declarations supplied by a
 * hypothesis, the target of the selected shape applied to the arguments read
 * off that hypothesis at their declared positions and to the placeholders.
 */
function mixfixApplication(
  kernel: Kernel, scope: SurfaceScope, candidates: readonly SurfaceNotationRecord[], operands: readonly Term[], line: number,
): Formula {
  const supplied = candidates.filter(item => item.hypothesis?.fixed);
  const plain = candidates.find(item => !item.hypothesis);
  const shape = supplied.length ? selectHypothesisShape(kernel, scope, supplied, operands, line, plain !== undefined) : undefined;
  if (!shape) return pred(plain!.target, ...operands);
  return shapeApplication(shape, operands);
}

/** The target of a hypothesis shape at its fixed arguments and the written operands, in order. */
function shapeApplication(shape: HypothesisShape, operands: readonly Term[]): Formula {
  const result: Term[] = [];
  let next = 0;
  for (let index = 0; index < shape.fixed.size + operands.length; index += 1) {
    result.push(shape.fixed.get(index) ?? operands[next++]!);
  }
  return pred(shape.notation.target, ...result);
}

interface HypothesisShape {
  readonly notation: SurfaceNotationRecord;
  readonly fact: Extract<Formula, { readonly tag: "pred" }>;
  /** The fixed target arguments, keyed by target position. */
  readonly fixed: ReadonlyMap<number, Term>;
  /** The carriers named by `for`: the objects, then the morphisms. */
  readonly carriers: readonly Term[];
}

/** Whether a hom-set `hom(C, a, b)` lies in the morphisms `mor(C)` among these carriers. */
function homSetInCarriers(set: Term, carriers: readonly Term[]): boolean {
  return set.tag === "app" && shortName(set.fn) === "hom" && set.args.length === 3 &&
    carriers.some(carrier => carrier.tag === "app" && shortName(carrier.fn) === "mor" && carrier.args.length === 1 &&
      termEquals(carrier.args[0]!, set.args[0]!));
}

/** The distinct shapes the hypotheses in scope supply for the declarations of one mixfix token. */
function hypothesisShapes(facts: readonly Formula[], notations: readonly SurfaceNotationRecord[]): HypothesisShape[] {
  const shapes: HypothesisShape[] = [];
  for (const notation of notations) {
    const pattern = notation.hypothesis;
    if (!pattern?.fixed) continue;
    for (const fact of facts) {
      if (fact.tag !== "pred" || fact.pred !== pattern.predicate || fact.args.length !== pattern.arity) continue;
      const fixed = new Map(pattern.fixed.map(item => [item.target, instantiatePattern(item.template, pattern, fact)]));
      const carriers = pattern.carriers.map(template => instantiatePattern(template, pattern, fact));
      if (!shapes.some(item => item.notation.target === notation.target && item.fixed.size === fixed.size &&
          item.carriers.length === carriers.length &&
          item.carriers.every((term, index) => termEquals(term, carriers[index]!)) &&
          [...fixed].every(([target, term]) => item.fixed.has(target) && termEquals(item.fixed.get(target)!, term)))) {
        shapes.push({ notation, fact, fixed, carriers });
      }
    }
  }
  return shapes;
}

/**
 * Choose the hypothesis a mixfix predicate notation reads its fixed
 * arguments from. One shape is taken as it stands; among several, an
 * operand selects the shape one of whose fixed arguments or carrier it lies
 * in, by a membership fact, a hom-set membership, an earlier guard in the
 * same shape, being an operation value in that carrier, or being the value
 * of a function into it; the operands must agree on one.
 */
function selectHypothesisShape(
  kernel: Kernel, scope: SurfaceScope, notations: readonly SurfaceNotationRecord[], operands: readonly Term[], line: number,
  optional = false,
): HypothesisShape | undefined {
  const facts = expandedLocalFormulas(kernel, scope);
  const shapes = hypothesisShapes(facts, notations);
  const token = notations[0]!.token;
  if (shapes.length === 0) {
    if (optional) return undefined;
    const names = [...new Set(notations.map(item => shortName(item.hypothesis!.predicate)))].join(", ");
    throw new SurfaceError(line, `no hypothesis in scope supplies the notation ${token}; it needs one of ${names}`);
  }
  if (shapes.length === 1) return shapes[0]!;
  const functionNotations = [...visibleInfixNotationGroups(kernel, scope, line, "function").values()].flat()
    .filter(item => item.hypothesis && !item.hypothesis.fixed);
  const operations = hypothesisOperations(facts, functionNotations);
  const inShape = (term: Term, shape: HypothesisShape): boolean =>
    operandInShape(kernel, facts, operations, shape, operands.length, term);
  const placed = (term: Term): boolean => shapes.some(shape => inShape(term, shape));
  const matching = shapes.filter(shape => operands.some(term => inShape(term, shape)) &&
    operands.every(term => !placed(term) || inShape(term, shape)));
  if (matching.length === 1) return matching[0]!;
  const objects = shapes.find(shape => shape.carriers.length)?.carriers[0];
  throw new SurfaceError(line, `ambiguous notation ${token}; hypotheses in scope supply morphisms of ${shapes.map(shape =>
    formatTerm(shape.carriers[1] ?? shape.carriers[0] ?? shape.fixed.values().next().value as Term)).join(" and ")}, and the operands ${operands.map(term => formatTerm(term)).join(", ")} do not select one; add ${objects ? `a binder such as (a ∈ ${formatTerm(objects)})` : "a binder (a ∈ O) for the objects"} or a membership fact`);
}

/**
 * Whether an operand lies in a hypothesis shape: by a membership fact in one
 * of its fixed arguments or carriers, by a fact of the shape's own predicate
 * at the same fixed arguments that mentions the operand, by being a
 * composite read under a hypothesis operation on one of its carriers, or by
 * being the value of a function into one.
 */
function operandInShape(
  kernel: Kernel, facts: readonly Formula[], operations: readonly HypothesisOperation[], shape: HypothesisShape,
  operandCount: number, term: Term,
): boolean {
  const carriers = [...shape.fixed.values(), ...shape.carriers];
  const inside = (set: Term): boolean => carriers.some(carrier => termEquals(carrier, set)) || homSetInCarriers(set, carriers);
  for (const fact of facts) {
    if (fact.tag !== "pred") continue;
    if (fact.pred === "in" && fact.args.length === 2 && termEquals(fact.args[0]!, term) && inside(fact.args[1]!)) return true;
    if (fact.pred === shape.notation.target && fact.args.length === shape.fixed.size + operandCount &&
        [...shape.fixed].every(([index, value]) => termEquals(fact.args[index]!, value)) &&
        fact.args.some((argument, index) => !shape.fixed.has(index) && termEquals(argument, term))) return true;
  }
  if (operations.some(item => item.notation.fixity === "constant" && termEquals(item.operation, term) && inside(item.carrier))) return true;
  if (term.tag !== "app") return false;
  if ((term.args.length === 3 || term.args.length === 2) && operations.some(item => item.notation.target === term.fn &&
      item.notation.fixity !== "constant" && (term.args.length === 3) === !item.notation.fixity &&
      termEquals(item.operation, term.args[0]!) && inside(item.carrier))) return true;
  if (shortName(term.fn) === "apply" && term.args.length === 2) {
    return hypothesisCodomains(kernel, facts, term.args[0]!).some(inside);
  }
  return false;
}

/**
 * The shape an infix predicate notation supplied by a hypothesis denotes for
 * these operands, `a ≤ b` under an order, or undefined when the token keeps
 * its typed declarations: the hypothesis form is read when an operand lies
 * in the carrier of a supplying hypothesis, by local evidence or by the
 * certified typing rules, and no operand outside it carries the sort of a
 * typed declaration; with no typed declaration of the token in scope the
 * hypothesis form is read as it stands, and the operands choose between
 * several shapes as they do for a mixfix form.
 */
function selectInfixPredicateShape(
  kernel: Kernel, scope: SurfaceScope, notations: readonly SurfaceNotationRecord[], typed: readonly SurfaceNotationRecord[],
  operands: readonly Term[], line: number,
): HypothesisShape | undefined {
  let facts = expandedLocalFormulas(kernel, scope);
  let shapes = hypothesisShapes(facts, notations);
  if (shapes.length === 0) {
    const closed = closedInstanceFacts(kernel, scope);
    shapes = hypothesisShapes(closed, notations);
    if (shapes.length) facts = [...facts, ...closed];
  }
  const token = notations[0]!.token;
  if (shapes.length === 0) {
    if (typed.length) return undefined;
    const names = [...new Set(notations.map(item => shortName(item.hypothesis!.predicate)))].join(", ");
    throw new SurfaceError(line, `no hypothesis in scope supplies the notation ${token}; it needs one of ${names}`);
  }
  const operations = hypothesisOperations(facts, visibleHypothesisFunctionNotations(kernel, scope, line));
  const inShape = (term: Term, shape: HypothesisShape): boolean =>
    operandInShape(kernel, facts, operations, shape, operands.length, term);
  const placed = (term: Term): boolean => shapes.some(shape => inShape(term, shape));
  if (typed.length) {
    const sorts = new Set(typed.flatMap(item => notationOperandTypes(item).filter((type): type is string => type !== undefined)));
    const sorted = (term: Term): boolean => naturalValue(term) !== undefined ||
      [...termTypeNames(kernel, term, scope)].some(type => sorts.has(type));
    const assumptions = scope.localFormulas?.() ?? [];
    const lies = operands.map(term => placed(term) || (!sorted(term) && shapes.some(shape =>
      shape.carriers.some(carrier => Boolean(proveRefinement(kernel, carrier, "in", [term], assumptions, [], scopeVisibility(kernel, scope)))))));
    if (!lies.some(Boolean) || operands.some((term, index) => !lies[index] && sorted(term))) return undefined;
  }
  if (shapes.length === 1) return shapes[0]!;
  const matching = shapes.filter(shape => operands.some(term => inShape(term, shape)) &&
    operands.every(term => !placed(term) || inShape(term, shape)));
  if (matching.length === 1) return matching[0]!;
  throw new SurfaceError(line, `ambiguous notation ${token}; hypotheses in scope supply orders on ${shapes.map(shape =>
    formatTerm(shape.carriers[0] ?? shape.fixed.values().next().value as Term)).join(" and ")}, and the operands ${operands.map(term => formatTerm(term)).join(", ")} do not select one; add a membership binder or fact`);
}

/**
 * The carriers the hypotheses give structure variables, for printing a
 * membership binder in one as the carrier binder it was written as: `G`
 * for `G.carrier` under `Group(G)`, `H` for `H` under `Subgroup(H, G)`,
 * read off the same templates a binder `(a : G)` is. A carrier that two
 * hypotheses give different variables is left as a membership.
 */
function displayCarriers(
  kernel: Kernel, scope: SurfaceScope, facts: readonly Formula[], conclusions: readonly Formula[] = [],
): CarrierNotation[] {
  const notations = visibleHypothesisCarrierNotations(kernel, scope, scope.line ?? 0);
  if (!notations.length) return [];
  const opened = facts.flatMap(formula => [formula,
    ...openGuardFact(kernel, { formula, proof: assume(formula) }, scopeVisibility(kernel, scope)).map(item => item.formula)]);
  // A structure value an instance supplies, polynomialRing(R, I) under
  // CommRing(R), prints its carrier binders as (p : polynomialRing(R, I)).
  const all = [...opened, ...derivedStructureFacts(kernel, scope, opened, [], conclusions)];
  const found: CarrierNotation[] = [];
  for (const notation of notations) {
    const pattern = notation.hypothesis!;
    for (const fact of all) {
      if (fact.tag !== "pred" || fact.pred !== pattern.predicate || fact.args.length !== pattern.arity) continue;
      for (const template of pattern.carriers) {
        const free = [...freeTermVariables(template)];
        if (free.length !== 1) continue;
        const structure = fact.args[pattern.names.indexOf(free[0]!)];
        if (!structure || (structure.tag !== "var" && !structureValueOf(kernel, scope, structure))) continue;
        const carrier = instantiatePattern(template, pattern, fact);
        const name = structure.tag === "var" ? structure.name : formatTerm(structure);
        if (!found.some(item => item.structure === name && termEquals(item.carrier, carrier))) {
          found.push({ structure: name, carrier, ...(structure.tag === "var" ? {} : { term: structure }) });
        }
      }
    }
  }
  return found.filter(item => !found.some(other => other.structure !== item.structure && termEquals(other.carrier, item.carrier)));
}

/** The local formulas in scope, with transparent guard facts opened to their conjuncts. */
function expandedLocalFormulas(kernel: Kernel, scope: SurfaceScope): Formula[] {
  const facts = scope.localFormulas?.() ?? [];
  const opened = facts.flatMap(formula => [formula,
    ...openGuardFact(kernel, { formula, proof: assume(formula) }, scopeVisibility(kernel, scope)).map(item => item.formula)]);
  return [...opened, ...derivedStructureFacts(kernel, scope, opened)];
}

/**
 * The mixfix predicate forms that hypotheses in scope supply, for printing a
 * statement or goal with the declared pattern: `Morphism(M, dom, cod, f, a,
 * b)` prints as `f : a ⟶ b` while a `Category(O, M, dom, cod, comp, id)` is
 * among the hypotheses.
 */
function displayPredicates(kernel: Kernel, scope: SurfaceScope, facts: readonly Formula[]): PredicateNotation[] {
  const line = scope.line ?? 0;
  // The infix predicate forms, `a ≤ b` for `Le(P, a, b)`, print beside the
  // mixfix ones.
  const notations = [
    ...[...visibleInfixNotationGroups(kernel, scope, line, "predicate", "mixfix").values()].flat(),
    ...[...visibleInfixNotationGroups(kernel, scope, line, "predicate").values()].flat(),
  ].filter(item => item.hypothesis?.fixed);
  if (!notations.length) return [];
  const result: PredicateNotation[] = [];
  for (const shape of hypothesisShapes(facts, notations)) {
    const infix = shape.notation.fixity !== "mixfix";
    const literals = infix ? [shape.notation.token] : mixfixLiterals(shape.notation.token);
    const arity = shape.fixed.size + literals.length + 1;
    const fixed = Array.from({ length: arity }, (_, index) => shape.fixed.get(index));
    if (!result.some(item => item.predicate === shape.notation.target && item.fixed.length === fixed.length &&
        item.fixed.every((term, index) =>
          (term === undefined) === (fixed[index] === undefined) && (term === undefined || termEquals(term, fixed[index]!))))) {
      result.push({ predicate: shape.notation.target, fixed, literals, ...(infix ? { infix: true } : {}) });
    }
  }
  return result;
}

/** Number of leading domain conjuncts generated for a soft-typed predicate. */
function predicateSoftGuardCount(reference: string, kernel: Kernel, scope: SurfaceScope): number {
  const environment = surfaceEnvironments.get(kernel);
  if (!environment) return 0;
  const notationTarget = visibleInfixNotations(kernel, scope, 0).get(reference)?.target;
  const resolved = notationTarget ?? resolveOptional(surfaceSymbol(reference), scope,
    candidate => environment.signatures.get(candidate)?.kind === "predicate");
  const signature = resolved ? environment.signatures.get(resolved) : undefined;
  return signature?.parameters.filter(isGuardBinder).length ?? 0;
}

function explicitClassExpression(
  text: string,
  kernel: Kernel,
  scope: SurfaceScope,
  classParameters: ReadonlySet<string>,
): boolean {
  const application = /^([^\s(]+)(?:\((.*)\))?$/u.exec(text.trim());
  if (!application) return false;
  const head = surfaceSymbol(application[1]!);
  if (classParameters.has(head)) return application[2] === undefined;
  const environment = surfaceEnvironments.get(kernel);
  return !!environment && !!resolveOptional(head, scope, candidate => environment.classes.has(candidate));
}

function parseClassExpression(
  text: string,
  kernel: Kernel,
  variables: ReadonlySet<string>,
  line: number,
  scope: SurfaceScope,
  classParameters: ReadonlySet<string>,
): SurfaceClassExpression {
  const source = text.trim();
  const application = /^([^\s(]+)(?:\((.*)\))?$/u.exec(source);
  const rawHead = application ? surfaceSymbol(application[1]!) : undefined;
  if (rawHead && classParameters.has(rawHead)) {
    if (application![2] !== undefined) throw new SurfaceError(line, `class parameter ${rawHead} does not take arguments`);
    return { tag: "parameter", name: rawHead };
  }
  const environment = surfaceEnvironments.get(kernel);
  const className = rawHead && environment
    ? resolveOptional(rawHead, scope, candidate => environment.classes.has(candidate))
    : undefined;
  if (!className) return { tag: "set", term: parseTerm(source, kernel, variables, line, scope) };
  const record = environment!.classes.get(className)!;
  const argumentSources = application![2]?.trim() ? splitTopLevel(application![2]!, ",") : [];
  if (argumentSources.length !== record.parameters.length) {
    throw new SurfaceError(line, `class ${application![1]} expects ${record.parameters.length} parameters`);
  }
  const arguments_ = argumentSources.map((argument, index) => record.parameterTypes[index] === "Class"
    ? parseClassExpression(argument, kernel, variables, line, scope, classParameters)
    : parseTerm(argument, kernel, variables, line, scope));
  return { tag: "named", name: className, arguments: arguments_ };
}

function classExpressionFreeVariables(expression: SurfaceClassExpression, into = new Set<string>()): Set<string> {
  if (expression.tag === "set") freeTermVariables(expression.term, into);
  else if (expression.tag === "named") {
    for (const argument of expression.arguments) {
      if ("tag" in argument && (argument.tag === "var" || argument.tag === "app" || argument.tag === "nat")) freeTermVariables(argument as Term, into);
      else classExpressionFreeVariables(argument as SurfaceClassExpression, into);
    }
  }
  return into;
}

function freshSurfaceVariable(base: string, forbidden: ReadonlySet<string>): string {
  if (!forbidden.has(base)) return base;
  for (let index = 1; ; index += 1) {
    const candidate = `${base}_${index}`;
    if (!forbidden.has(candidate)) return candidate;
  }
}

function replaceClassParameters(
  formula: Formula,
  replacements: ReadonlyMap<string, SurfaceClassExpression>,
  kernel: Kernel,
  environment: SurfaceEnvironment,
): Formula {
  const replacementVariables = new Set<string>();
  for (const expression of replacements.values()) classExpressionFreeVariables(expression, replacementVariables);
  const visit = (current: Formula): Formula => {
    switch (current.tag) {
      case "bottom": return current;
      case "eq": return current;
      case "pred": {
        if (!current.pred.startsWith(CLASS_PARAMETER_PREFIX)) return current;
        const parameter = current.pred.slice(CLASS_PARAMETER_PREFIX.length);
        const replacement = replacements.get(parameter);
        if (!replacement || current.args.length !== 1) throw new Error(`unresolved class parameter ${parameter}`);
        return classMembershipFormula(replacement, current.args[0]!, kernel, environment);
      }
      case "imp": return imp(visit(current.left), visit(current.right));
      case "and": return and(visit(current.left), visit(current.right));
      case "or": return or(visit(current.left), visit(current.right));
      case "iff": return iff(visit(current.left), visit(current.right));
      case "forall":
      case "exists": {
        let variable = current.variable;
        let body = current.body;
        if (replacementVariables.has(variable)) {
          const forbidden = freeFormulaVariables(body);
          replacementVariables.forEach(item => forbidden.add(item));
          variable = freshSurfaceVariable(variable, forbidden);
          body = substituteFormula(body, current.variable, v(variable));
        }
        return current.tag === "forall" ? forall(variable, visit(body)) : exists(variable, visit(body));
      }
    }
  };
  return visit(formula);
}

function classMembershipFormula(
  expression: SurfaceClassExpression,
  element: Term,
  kernel: Kernel,
  environment: SurfaceEnvironment,
): Formula {
  if (expression.tag === "set") return pred("in", element, expression.term);
  if (expression.tag === "parameter") return pred(`${CLASS_PARAMETER_PREFIX}${expression.name}`, element);
  const record = environment.classes.get(expression.name)!;
  const definition = environment.classDefinitions.get(expression.name)!;
  if (definition.predicateBacked) {
    return pred(expression.name, element, ...(expression.arguments as readonly Term[]));
  }
  let result = substituteFormula(definition.body, record.element, element);
  const classReplacements = new Map<string, SurfaceClassExpression>();
  for (let index = 0; index < record.parameters.length; index += 1) {
    const parameter = record.parameters[index]!;
    const argument = expression.arguments[index]!;
    if (record.parameterTypes[index] === "Class") classReplacements.set(parameter, argument as SurfaceClassExpression);
    else result = substituteFormula(result, parameter, argument as Term);
  }
  return replaceClassParameters(result, classReplacements, kernel, environment);
}

/** Recover the unary soft type represented by a concrete carrier set.
 *
 * For example, `class Rational (q : Set) := q ∈ ℚ` makes a variable
 * bounded by `ℚ` available to notation resolution as a `Rational`.  This is
 * elaboration metadata only: the kernel receives the bounded
 * quantifier expansion using membership.
 */
function boundedCarrierType(
  kernel: Kernel, bound: Term,
): string | undefined {
  // Nat is a primitive soft type rather than a predicate-backed surface
  // class, so its concrete carrier needs the same direct bridge that ℕ gets
  // in binder syntax, so `∀ n ∈ ℕ, ...` resolves arithmetic notation
  // for n exactly as `(n : Nat)` does.
  if (bound.tag === "app" && bound.args.length === 0 &&
      (bound.fn === "omega" || bound.fn.endsWith(".omega"))) return "Nat";
  const environment = surfaceEnvironments.get(kernel);
  if (!environment) return undefined;
  const matches: string[] = [];
  for (const [name, record] of environment.classes) {
    if (record.parameters.length !== 0) continue;
    const definition = environment.classDefinitions.get(name);
    if (!definition?.predicateBacked || definition.body.tag !== "pred" ||
        definition.body.pred !== "in" || definition.body.args.length !== 2) continue;
    if (!termEquals(definition.body.args[0]!, v(record.element))) continue;
    if (termEquals(definition.body.args[1]!, bound)) matches.push(name);
  }
  return matches.length === 1 ? matches[0] : undefined;
}


/** ASCII spellings accepted for Unicode literal tokens inside a mixfix pattern. */
const MIXFIX_ASCII: Readonly<Record<string, string>> = Object.freeze({ "→": "->", "↔": "<->" });

/** The first top-level occurrence of a literal token that is not part of a longer punctuation run. */
function findMixfixToken(source: string, token: string): { readonly index: number; readonly length: number } | undefined {
  for (const spelling of [token, MIXFIX_ASCII[token]].filter((item): item is string => item !== undefined)) {
    let from = 0;
    while (from <= source.length) {
      const index = findTopLevel(source.slice(from), spelling);
      if (index < 0) break;
      const at = from + index;
      const before = source[at - 1] ?? " ";
      const after = source[at + spelling.length] ?? " ";
      const punctuation = /[^\p{L}\p{M}\p{N}\s_(),."]/u;
      if (!punctuation.test(before) && !punctuation.test(after)) return { index: at, length: spelling.length };
      from = at + spelling.length;
    }
  }
  return undefined;
}

/** A formula written with a visible mixfix predicate notation, or undefined when the text has no such shape. */
function parseMixfixFormula(
  source: string, kernel: Kernel, variables: ReadonlySet<string>, line: number, scope: SurfaceScope,
): Formula | undefined {
  const groups = visibleInfixNotationGroups(kernel, scope, line, "predicate", "mixfix");
  for (const candidates of groups.values()) {
    const pieces: string[] = [];
    let rest = source;
    let matched = true;
    for (const literal of mixfixLiterals(candidates[0]!.token)) {
      const found = findMixfixToken(rest, literal);
      if (!found || found.index === 0) { matched = false; break; }
      pieces.push(rest.slice(0, found.index).trim());
      rest = rest.slice(found.index + found.length);
    }
    if (!matched) continue;
    pieces.push(rest.trim());
    if (pieces.some(piece => !piece)) continue;
    let operands: Term[];
    try {
      operands = pieces.map(piece => parseTerm(piece, kernel, variables, line, scope));
    } catch (error) {
      if (!(error instanceof SurfaceError)) throw error;
      continue;
    }
    return mixfixApplication(kernel, scope, candidates, operands, line);
  }
  return undefined;
}

function parseFormula(
  text: string,
  kernel: Kernel,
  variables: ReadonlySet<string>,
  line: number,
  scope: SurfaceScope,
  classParameters: ReadonlySet<string> = new Set(),
): Formula {
  const source = stripOuterParentheses(text.trim());
  // `∀ (a b ∈ obj(C)) (f : a ⟶ b), φ`: binder groups as in a theorem header,
  // each guard in scope for the later binders and for the body.
  const grouped = /^(forall|exists|∀|∃)\s*(\(.+)$/u.exec(source);
  if (grouped) {
    const universal = grouped[1] === "forall" || grouped[1] === "∀";
    const groups = parseBinderGroups(grouped[2]!, line);
    if (!groups.rest.startsWith(",")) throw new SurfaceError(line, "a quantifier over binder groups needs a comma after its binders");
    const binders = resolveBinderTypes(groups.binders, kernel, scope, line, [], variables);
    const nestedVariables = new Set(variables);
    const nestedTypes = new Map(scope.binderTypes ?? []);
    for (const binder of binders) { nestedVariables.add(binder.name); nestedTypes.set(binder.name, binder); }
    const guards = binderAssumptions(binders);
    const body = parseFormula(groups.rest.slice(1), kernel, nestedVariables, line,
      { ...scope, binderTypes: nestedTypes, localFormulas: () => [...(scope.localFormulas?.() ?? []), ...guards] },
      classParameters);
    return binders.reduceRight<Formula>((result, binder) => {
      const guard = binderAssumptions([binder])[0];
      const inner = guard ? (universal ? imp(guard, result) : and(guard, result)) : result;
      return universal ? forall(binder.name, inner) : exists(binder.name, inner);
    }, body);
  }
  // `∃ m n : ℕ, φ` and `∀ f : A → B, φ`: the typed binders of a theorem
  // header without their parentheses, read as the group `(m n : ℕ)`.
  const typedPrefix = /^(forall|exists|∀|∃)\s*((?:[\p{L}_][\p{L}\p{M}\p{N}_']*\s+)*[\p{L}_][\p{L}\p{M}\p{N}_']*)\s*:\s*(.+)$/u.exec(source);
  if (typedPrefix) {
    const comma = findTopLevel(typedPrefix[3]!, ",");
    if (comma < 0) throw new SurfaceError(line, "a typed quantifier needs a comma after its type");
    const type = typedPrefix[3]!.slice(0, comma).trim();
    const body = typedPrefix[3]!.slice(comma + 1).trim();
    if (!type || !body) throw new SurfaceError(line, "malformed typed quantifier");
    return parseFormula(`${typedPrefix[1]} (${typedPrefix[2]!.trim()} : ${type}), ${body}`,
      kernel, variables, line, scope, classParameters);
  }
  // `∀ k ≤ n, φ` and `∀ k < n, φ` bind natural numbers below a bound:
  // `∀ k, Nat(k) → k ≤ n → φ`, with Nat(k) in scope for φ.
  const orderedPrefix = /^(forall|exists|∀|∃)\s*((?:[\p{L}_][\p{L}\p{M}\p{N}_]*\s+)*[\p{L}_][\p{L}\p{M}\p{N}_]*)\s*(≤|<)\s*(.+)$/u.exec(source);
  if (orderedPrefix) {
    const names = orderedPrefix[2]!.trim().split(/\s+/);
    const comma = findTopLevel(orderedPrefix[4]!, ",");
    if (comma < 0) throw new SurfaceError(line, "a bounded quantifier needs a comma after its bound");
    const boundSource = orderedPrefix[4]!.slice(0, comma).trim();
    const bodySource = orderedPrefix[4]!.slice(comma + 1).trim();
    if (!boundSource || !bodySource) throw new SurfaceError(line, "malformed bounded quantifier");
    const nestedVariables = new Set(variables);
    const nestedTypes = new Map(scope.binderTypes ?? []);
    for (const name of names) {
      if (variables.has(name)) throw new SurfaceError(line, `${name} is already bound; a bounded quantifier binds a fresh variable`);
      nestedVariables.add(name);
      nestedTypes.set(name, { name, type: "Nat" });
    }
    const sorts = names.map(name => pred("Nat", v(name)));
    const nestedScope: SurfaceScope = { ...scope, binderTypes: nestedTypes, localFormulas: () => [...(scope.localFormulas?.() ?? []), ...sorts] };
    const bounds = names.map(name => parseFormula(`${name} ${orderedPrefix[3]} ${boundSource}`, kernel, nestedVariables, line, nestedScope, classParameters));
    const body = parseFormula(bodySource, kernel, nestedVariables, line,
      { ...nestedScope, localFormulas: () => [...(scope.localFormulas?.() ?? []), ...sorts, ...bounds] }, classParameters);
    const universal = orderedPrefix[1] === "forall" || orderedPrefix[1] === "∀";
    return names.reduceRight<Formula>((result, name, index) => universal
      ? forall(name, imp(sorts[index]!, imp(bounds[index]!, result)))
      : exists(name, and(sorts[index]!, and(bounds[index]!, result))), body);
  }
  // `∀ a b ∈ A, φ` binds each variable by membership in A, in scope for φ.
  const boundedPrefix = /^(forall|exists|∀|∃)\s*([^,]+?)\s+(?:in\s+|∈\s*)(.+)$/u.exec(source);
  if (boundedPrefix) {
    const names = boundedPrefix[2]!.trim().split(/\s+/);
    if (names.some(name => !SIMPLE_IDENTIFIER.test(name))) throw new SurfaceError(line, "malformed bounded quantified variable");
    const comma = findTopLevel(boundedPrefix[3]!, ",");
    if (comma < 0) throw new SurfaceError(line, "a bounded quantifier needs a comma after its carrier");
    const boundSource = boundedPrefix[3]!.slice(0, comma).trim();
    const bodySource = boundedPrefix[3]!.slice(comma + 1).trim();
    if (!boundSource || !bodySource) throw new SurfaceError(line, "malformed bounded quantifier");
    const bound = structureCarrier(kernel, scope, parseTerm(boundSource, kernel, variables, line, scope));
    const nestedVariables = new Set(variables);
    const nestedTypes = new Map(scope.binderTypes ?? []);
    for (const name of names) {
      nestedVariables.add(name);
      nestedTypes.set(name, { name, type: boundedCarrierType(kernel, bound) ?? "Set" });
    }
    const memberships = names.map(name => pred("in", v(name), bound));
    const body = parseFormula(bodySource, kernel, nestedVariables, line,
      { ...scope, binderTypes: nestedTypes, localFormulas: () => [...(scope.localFormulas?.() ?? []), ...memberships] },
      classParameters);
    const universal = boundedPrefix[1] === "forall" || boundedPrefix[1] === "∀";
    return names.reduceRight<Formula>((result, name, index) => universal
      ? forall(name, imp(memberships[index]!, result))
      : exists(name, and(memberships[index]!, result)), body);
  }
  const quantifier = /^(forall|exists|∀|∃)\s*([^\s,]+)\s*,\s*(.+)$/u.exec(source);
  if (quantifier) {
    if (!SIMPLE_IDENTIFIER.test(quantifier[2]!)) throw new SurfaceError(line, "malformed quantified variable");
    const nestedVariables = new Set(variables);
    nestedVariables.add(quantifier[2]!);
    const body = parseFormula(quantifier[3]!, kernel, nestedVariables, line, scope, classParameters);
    return quantifier[1] === "forall" || quantifier[1] === "∀" ? forall(quantifier[2]!, body) : exists(quantifier[2]!, body);
  }
  // A visible mixfix predicate notation, such as `f : A → B` for
  // FunctionBetween(f, A, B): its literal tokens at the top level with a
  // term in every placeholder.
  const mixfixFormula = parseMixfixFormula(source, kernel, variables, line, scope);
  if (mixfixFormula) return mixfixFormula;
  const binary: readonly [string, (left: Formula, right: Formula) => Formula][] = [
    ["<->", iff], ["↔", iff], ["->", imp], ["→", imp],
    [" or ", or], ["∨", or], [" and ", and], ["∧", and],
  ];
  for (const [operator, build] of binary) {
    const index = findTopLevel(source, operator);
    if (index >= 0) {
      const left = parseFormula(source.slice(0, index), kernel, variables, line, scope, classParameters);
      // A conjunction's left side may carry soft-type evidence used by its
      // right side, as in `p ∈ ℝ × ℝ ∧ p = (A ↦ 0)`, and an implication's
      // antecedent may supply the notation of its consequent, as
      // `Category(C) → ∀ (f : a ⟶ b), …` does. This affects only elaboration
      // of notation; the kernel still receives an and or an imp.
      const rightScope = operator === " and " || operator === "∧" || operator === "->" || operator === "→"
        ? { ...scope, localFormulas: () => [...(scope.localFormulas?.() ?? []), left] }
        : scope;
      const right = parseFormula(source.slice(index + operator.length), kernel,
        variables, line, rightScope, classParameters);
      return build(left, right);
    }
  }
  if (source.startsWith("not ")) return not(parseFormula(source.slice(4), kernel, variables, line, scope, classParameters));
  if (source.startsWith("¬")) return not(parseFormula(source.slice(1), kernel, variables, line, scope, classParameters));
  if (source === "false" || source === "⊥") return bottom;
  const classEquality = findTopLevel(source, "=");
  if (classEquality >= 0) {
    const leftSource = source.slice(0, classEquality).trim();
    const rightSource = source.slice(classEquality + 1).trim();
    if (explicitClassExpression(leftSource, kernel, scope, classParameters) ||
        explicitClassExpression(rightSource, kernel, scope, classParameters)) {
      const environment = surfaceEnvironments.get(kernel)!;
      const left = parseClassExpression(leftSource, kernel, variables, line, scope, classParameters);
      const right = parseClassExpression(rightSource, kernel, variables, line, scope, classParameters);
      const forbidden = new Set(variables);
      classExpressionFreeVariables(left, forbidden);
      classExpressionFreeVariables(right, forbidden);
      const element = freshSurfaceVariable("x", forbidden);
      return forall(element, iff(
        classMembershipFormula(left, v(element), kernel, environment),
        classMembershipFormula(right, v(element), kernel, environment),
      ));
    }
  }
  // `x ∉ A` abbreviates `¬(x ∈ A)`, as `≠` abbreviates a negated equality.
  const nonMembership = findTopLevel(source, "∉");
  if (nonMembership >= 0) {
    return not(parseFormula(
      `${source.slice(0, nonMembership)} ∈ ${source.slice(nonMembership + 1)}`,
      kernel, variables, line, scope, classParameters,
    ));
  }
  for (const operator of [" in ", "∈"] as const) {
    const index = findTopLevel(source, operator);
    if (index >= 0) {
      const element = parseTerm(source.slice(0, index), kernel, variables, line, scope);
      const container = source.slice(index + operator.length).trim();
      const environment = surfaceEnvironments.get(kernel);
      if (environment && explicitClassExpression(container, kernel, scope, classParameters)) {
        return classMembershipFormula(
          parseClassExpression(container, kernel, variables, line, scope, classParameters), element, kernel, environment);
      }
      return pred("in", element, structureCarrier(kernel, scope, parseTerm(container, kernel, variables, line, scope)));
    }
  }
  const relationNotationGroups = [...visibleInfixNotationGroups(kernel, scope, line, "predicate").entries()]
    .sort(([left], [right]) => right.length - left.length || left.localeCompare(right));
  for (const [token, visible] of relationNotationGroups) {
    const index = findTopLevel(source, token);
    if (index >= 0) {
      // The operands of `⊆` and `⊂` are sets of elements, so a structure
      // variable there is its carrier.
      const setRelation = visible.some(item => ["Subset", "ProperSubset"].includes(shortName(item.target)));
      const operand = (text: string): Term => {
        const term = parseTerm(text, kernel, variables, line, scope);
        return setRelation ? structureCarrier(kernel, scope, term) : term;
      };
      const left = operand(source.slice(0, index));
      const right = operand(source.slice(index + token.length));
      // A predicate supplied by a hypothesis in scope, `a ≤ b` under an
      // order, when an operand lies in its carrier; otherwise the typed
      // declarations of the token decide as they do with no hypothesis.
      const supplied = visible.filter(item => item.hypothesis?.fixed);
      const candidates = visible.filter(item => !item.hypothesis);
      if (supplied.length) {
        const shape = selectInfixPredicateShape(kernel, scope, supplied, candidates, [left, right], line);
        if (shape) return shapeApplication(shape, [left, right]);
      }
      const leftTypes = termTypeNames(kernel, left, scope);
      const rightTypes = termTypeNames(kernel, right, scope);
      // `Set` is the ambient kernel sort.  A term declared as Set may still
      // acquire its mathematical carrier
      // from the other operand (or from a typed numeral).
      const informativeLeft = new Set([...leftTypes].filter(type => type !== "Set"));
      const informativeRight = new Set([...rightTypes].filter(type => type !== "Set"));
      const exactTyped = candidates.filter(item => {
        const [leftType, rightType] = notationOperandTypes(item);
        return leftType && rightType && leftTypes.has(leftType) && rightTypes.has(rightType);
      });
      const compatibleTyped = candidates.filter(item => {
        const [leftType, rightType] = notationOperandTypes(item);
        return leftType && rightType &&
          (informativeLeft.size === 0 || informativeLeft.has(leftType) || typedNumeral(kernel, scope, line, left, leftType) !== undefined) &&
          (informativeRight.size === 0 || informativeRight.has(rightType) || typedNumeral(kernel, scope, line, right, rightType) !== undefined) &&
          (leftTypes.has(leftType) || rightTypes.has(rightType) ||
            typedNumeral(kernel, scope, line, left, leftType) !== undefined || typedNumeral(kernel, scope, line, right, rightType) !== undefined);
      });
      // When one operand says nothing about its carrier, the other operand's
      // own type decides between otherwise compatible candidates: `0 < t`
      // with `t` untyped is the natural order, not a reinterpretation of
      // the numeral in another carrier.
      const sidedTyped = (informativeLeft.size === 0) !== (informativeRight.size === 0)
        ? compatibleTyped.filter(item => {
          const [leftType, rightType] = notationOperandTypes(item);
          return (leftType !== undefined && leftTypes.has(leftType)) || (rightType !== undefined && rightTypes.has(rightType));
        })
        : [];
      const fallback = candidates.filter(item => !notationIsTyped(item));
      // With no carrier information on either side, the natural-number
      // reading is the library's default, as it is for bare numerals.
      const evidenced = candidates.filter(item => {
        const [leftType, rightType] = notationOperandTypes(item);
        return (leftType !== undefined && informativeLeft.has(leftType)) ||
          (rightType !== undefined && informativeRight.has(rightType));
      });
      const natDefault = evidenced.length === 0
        ? candidates.filter(item => {
          const [leftType, rightType] = notationOperandTypes(item);
          return leftType === "Nat" && rightType === "Nat";
        })
        : [];
      // An operand typed by a refinement (Prime(p) for a natural p) selects
      // the carrier its refinement proves, through the same search that
      // discharges soft-type guards.
      const refinedTyped = exactTyped.length === 0 && compatibleTyped.length !== 1 && sidedTyped.length !== 1
        ? candidates.filter(item => {
          const [leftType, rightType] = notationOperandTypes(item);
          if (!leftType || !rightType) return false;
          const leftFits = informativeLeft.size === 0 || leftTypes.has(leftType) ||
            typedNumeral(kernel, scope, line, left, leftType) !== undefined || termHasType(kernel, left, leftType, scope);
          const rightFits = leftFits && (informativeRight.size === 0 || rightTypes.has(rightType) ||
            typedNumeral(kernel, scope, line, right, rightType) !== undefined || termHasType(kernel, right, rightType, scope));
          const evidence = rightFits && (
            (informativeLeft.size > 0 && (leftTypes.has(leftType) || termHasType(kernel, left, leftType, scope))) ||
            (informativeRight.size > 0 && (rightTypes.has(rightType) || termHasType(kernel, right, rightType, scope))));
          return leftFits && rightFits && evidence;
        })
        : [];
      // One operand of a declared sort and the other of a sort coerced to
      // it, n < X for realNat(n) < X.
      const coercions = [...visibleInfixNotationGroups(kernel, scope, line, "function", "coercion").values()].flat();
      const coerced = (term: Term, types: ReadonlySet<string>, type: string): Term | undefined => {
        if (naturalValue(term) !== undefined || types.has(type)) return undefined;
        const coercion = coercions.find(item => item.resultType === type && item.operandType !== undefined && types.has(item.operandType));
        return coercion ? app(coercion.target, term) : undefined;
      };
      const coercible = exactTyped.length === 0 && coercions.length ? candidates.filter(item => {
        const [leftType, rightType] = notationOperandTypes(item);
        if (!leftType || !rightType) return false;
        const leftFits = leftTypes.has(leftType);
        const rightFits = rightTypes.has(rightType);
        return leftFits !== rightFits && (leftFits ? coerced(right, rightTypes, rightType) : coerced(left, leftTypes, leftType)) !== undefined;
      }) : [];
      const notation = candidates.length === 1 ? candidates[0]
        : exactTyped.length === 1 ? exactTyped[0]
        : exactTyped.length === 0 && coercible.length === 1 ? coercible[0]
        : exactTyped.length === 0 && compatibleTyped.length === 1 ? compatibleTyped[0]
        : exactTyped.length === 0 && sidedTyped.length === 1 ? sidedTyped[0]
        : refinedTyped.length === 1 ? refinedTyped[0]
        : compatibleTyped.length === 0 && fallback.length === 1 ? fallback[0]
        : compatibleTyped.length === 0 && fallback.length === 0 && natDefault.length === 1 ? natDefault[0]
        : undefined;
      if (!notation) {
        const display = (types: ReadonlySet<string>): string =>
          [...types].map(item => item.split(".").at(-1)!).join("|") || "?";
        throw new SurfaceError(line,
          `cannot resolve notation ${token} for operand types ${display(leftTypes)}, ${display(rightTypes)}; candidates are ${candidates.map(notationTypeLabel).join("; ")}`);
      }
      const [leftType, rightType] = notationOperandTypes(notation);
      const typedLeft = leftType ? typedNumeral(kernel, scope, line, left, leftType) ?? coerced(left, leftTypes, leftType) ?? left : left;
      const typedRight = rightType ? typedNumeral(kernel, scope, line, right, rightType) ?? coerced(right, rightTypes, rightType) ?? right : right;
      return pred(notation.target, ...(notation.leadingArguments ?? []),
        ...(notation.reversed ? [typedRight, typedLeft] : [typedLeft, typedRight]));
    }
  }
  const equality = findTopLevel(source, "=");
  if (equality >= 0) {
    let operands = harmonizeTypedNumerals(
      kernel, scope, line,
      parseTerm(source.slice(0, equality), kernel, variables, line, scope),
      parseTerm(source.slice(equality + 1), kernel, variables, line, scope),
    );
    operands = [
      harmonizeProductPairNumerals(kernel, scope, line, operands[0], operands[1]),
      harmonizeProductPairNumerals(kernel, scope, line, operands[1], operands[0]),
    ];
    operands = harmonizeCoercedEquation(kernel, scope, line, operands[0], operands[1]);
    return eq(operands[0], operands[1]);
  }
  const inequality = findTopLevel(source, "≠");
  if (inequality >= 0) {
    const operands = harmonizeTypedNumerals(
      kernel, scope, line,
      parseTerm(source.slice(0, inequality), kernel, variables, line, scope),
      parseTerm(source.slice(inequality + 1), kernel, variables, line, scope),
    );
    return not(eq(operands[0], operands[1]));
  }
  // Mathematical prose often leaves a space before an application, as in
  // `Finite (ω)`. Whitespace must not degrade that into "malformed formula".
  const predicate = /^([^\s({]+)\s*(?:\{(.*)\})?\s*\((.*)\)$/u.exec(source);
  const predicateName = predicate ? resolveOptional(surfaceSymbol(predicate[1]!), scope, candidate => {
    if (!kernel.predicates.has(candidate)) return false;
    const signature = surfaceEnvironments.get(kernel)?.signatures.get(candidate);
    const supplied = predicate[3]!.trim() ? splitTopLevel(predicate[3]!, ",").length : 0;
    const dropped = scope.sectionDefinitions?.get(candidate)?.length ?? 0;
    return !signature || supplied === signature.parameters.length ||
      supplied === signature.parameters.filter(item => !item.implicit).length ||
      (dropped > 0 && supplied + dropped === signature.parameters.length);
  }) : undefined;
  // Ordinary declarations take precedence. Shorthand is available only for
  // the exact established predicate, never a matching basename; an argument
  // that names an active ring scope, as `CommRing(R)` under
  // `notation ring R := …`, is the shorthand even where a bundled predicate
  // of the same name and arity is in scope.
  const namesRingScope = (text: string): boolean => Boolean(scope.rings?.length) && (text.trim() ? splitTopLevel(text, ",") : [])
    .some(item => (scope.ringAliases ?? scope.rings)!.some(ring => ring.name === item.trim()));
  if (predicate && (!predicateName || namesRingScope(predicate[3]!)) && !predicate[2] && scope.rings?.length) {
    const supplied = predicate[3]!.trim() ? splitTopLevel(predicate[3]!, ",") : [];
    const record = scopedNotationFor(kernel, scope, line, "predicate", predicate[1]!, supplied.length);
    if (record) {
      const target = resolveOptional(predicate[1]!, scope, name => kernel.predicates.get(name) === record.expansion!.length);
      if (!target || target === record.target) {
        return pred(record.target, ...expandScopedArguments(record, supplied,
          index => parseTerm(supplied[index]!, kernel, variables, line, scope), scope, line, predicate[1]!));
      }
      if (namesRingScope(predicate[3]!)) {
        throw new SurfaceError(line, `unknown predicate ${predicate[1]}; the scoped form expands to ${record.target}, which is shadowed or unavailable`);
      }
    }
  }
  if (predicate && QUALIFIED_IDENTIFIER.test(predicate[1]!) && predicateName) {
    // A bundled predicate of the same name as a scoped shorthand, applied to
    // the carrier variable of an active scope, is the shorthand misspelled:
    // `Ideal(A, M)` under `notation ring R := (A, …)` wants `Ideal(R, M)`.
    if (scope.rings?.length) {
      const supplied = predicate[3]!.trim() ? splitTopLevel(predicate[3]!, ",") : [];
      const record = scopedNotationFor(kernel, scope, line, "predicate", predicate[1]!, supplied.length);
      record?.parameters!.forEach((parameter, i) => {
        if (!record.expansion!.some(argument => argument.parameter === parameter && argument.piece && argument.piece !== "carrier")) return;
        const name = supplied[i]!.trim();
        const carrierOf = (scope.ringAliases ?? scope.rings)!.find(ring => ring.carrier.tag === "var" && ring.carrier.name === name);
        if (carrierOf) throw new SurfaceError(line, `${predicate[1]} argument ${i + 1} requires a scoped ring name; ${name} is not an active ring notation`);
      });
    }
    const args = predicate[3]!.trim() === "" ? [] : splitTopLevel(predicate[3]!, ",")
      .map(item => parseTerm(item, kernel, variables, line, scope));
    const overrides: ImplicitOverride[] = predicate[2]?.trim()
      ? splitTopLevel(predicate[2]!, ",").map(item => {
          const assignment = findTopLevel(item, ":=");
          if (assignment < 0) return { value: parseTerm(item, kernel, variables, line, scope) };
          const name = item.slice(0, assignment).trim();
          if (!SIMPLE_IDENTIFIER.test(name)) throw new SurfaceError(line, `malformed implicit argument name ${name}`);
          return { name, value: parseTerm(item.slice(assignment + 2), kernel, variables, line, scope) };
        }) : [];
    return pred(predicateName, ...elaborateApplicationArguments(kernel, predicateName, args, overrides, variables, scope, line));
  }
  if (predicate && QUALIFIED_IDENTIFIER.test(predicate[1]!)) {
    throw new SurfaceError(line,
      `unknown predicate ${predicate[1]}; it may be unavailable in the current imports`);
  }
  throw new SurfaceError(line, "malformed formula");
}

function stripOuterParentheses(text: string): string {
  let result = text;
  while (result.startsWith("(") && result.endsWith(")")) {
    let depth = 0;
    let enclosesAll = true;
    for (let index = 0; index < result.length; index += 1) {
      if (result[index] === "(") depth += 1;
      else if (result[index] === ")") depth -= 1;
      if (depth === 0 && index < result.length - 1) { enclosesAll = false; break; }
    }
    if (!enclosesAll) break;
    result = result.slice(1, -1).trim();
  }
  return result;
}

/** Whether the text is one parenthesized group: its first "(" closes at its last character. */
function outerParenthesized(text: string): boolean {
  if (!text.startsWith("(") || !text.endsWith(")")) return false;
  let depth = 0;
  for (let index = 0; index < text.length; index++) {
    const character = text[index]!;
    if ("([{⟨".includes(character)) depth += 1;
    else if (")]}⟩".includes(character)) {
      depth -= 1;
      if (depth === 0) return index === text.length - 1;
      if (depth < 0) return false;
    }
  }
  return false;
}

/** Whether every bracket in the text is closed at depth zero or above. */
function balanced(text: string): boolean {
  let depth = 0;
  for (const character of text) {
    if ("([{⟨".includes(character)) depth += 1;
    else if (")]}⟩".includes(character)) { depth -= 1; if (depth < 0) return false; }
  }
  return depth === 0;
}

/** Position of a standalone word outside brackets, or -1. */
function findTopLevelWord(text: string, word: string): number {
  let depth = 0;
  for (let index = 0; index < text.length; index++) {
    const character = text[index]!;
    if ("([{⟨".includes(character)) depth += 1;
    else if (")]}⟩".includes(character)) depth -= 1;
    else if (depth === 0 && text.startsWith(word, index) &&
      (index === 0 || /\s/.test(text[index - 1]!)) && /^\s*$/.test(text[index + word.length] ?? "")) return index;
  }
  return -1;
}

function findTopLevel(text: string, operator: string): number {
  let depth = 0;
  for (let index = 0; index <= text.length - operator.length; index += 1) {
    // The `<` in a big-operator header, as in `∑ k < n, uₖ`, bounds the
    // index and is not a comparison of the formula.
    const binderHeader = /^[∑∏⋃⋂]\s*[\p{L}_][\p{L}\p{M}\p{N}_]*\s*(?:<|≤)/u.exec(text.slice(index));
    if (binderHeader) { index += binderHeader[0].length - 1; continue; }
    if (text[index] === "(" || text[index] === "{" || text[index] === "[" || text[index] === "⟨") depth += 1;
    else if (text[index] === ")" || text[index] === "}" || text[index] === "]" || text[index] === "⟩") depth -= 1;
    if (depth === 0 && text.startsWith(operator, index) && !(operator === "=" && text[index - 1] === ":")) return index;
  }
  return -1;
}

function parsePattern(text: string, kernel: Kernel, scope: SurfaceScope, line: number): Pattern {
  const trimmed = text.trim();
  const consIndex = findTopLevel(trimmed, "::");
  if (consIndex >= 0) {
    const cons = resolveExisting("Grace.Core.Data.List.cons", scope,
      candidate => kernel.functions.get(candidate) === 2, line, "List.cons constructor");
    return ctor(cons, parsePattern(trimmed.slice(0, consIndex), kernel, scope, line),
      parsePattern(trimmed.slice(consIndex + 2), kernel, scope, line));
  }
  if (trimmed.startsWith("[") && trimmed.endsWith("]")) {
    const nil = resolveExisting("Grace.Core.Data.List.nil", scope,
      candidate => kernel.functions.get(candidate) === 0, line, "List.nil constructor");
    const cons = resolveExisting("Grace.Core.Data.List.cons", scope,
      candidate => kernel.functions.get(candidate) === 2, line, "List.cons constructor");
    const body = trimmed.slice(1, -1).trim();
    return (body ? splitTopLevel(body, ",") : []).reduceRight<Pattern>(
      (tail, head) => ctor(cons, parsePattern(head, kernel, scope, line), tail), ctor(nil));
  }
  if (trimmed === "zero" || trimmed === "0") return ctor("zero");
  // `n + 2` is the pattern succ(succ(n)) written as arithmetic.
  const offsetPattern = /^(.+?)\s*\+\s*(\d+)$/u.exec(trimmed);
  if (offsetPattern && !/[()]/u.test(offsetPattern[1]!)) {
    let pattern = parsePattern(offsetPattern[1]!, kernel, scope, line);
    for (let step = 0; step < Number(offsetPattern[2]); step += 1) pattern = ctor("succ", pattern);
    return pattern;
  }
  const application = /^([^\s(]+)\((.*)\)$/u.exec(trimmed);
  if (application) {
    const name = resolveOptional(surfaceSymbol(application[1]!), scope, candidate =>
      [...kernel.datatypes.values()].some(data => data.constructors.some(item => item.name === candidate)));
    if (!name) throw new SurfaceError(line, `unknown constructor ${application[1]}`);
    const arguments_ = application[2]!.trim() ? splitTopLevel(application[2]!, ",") : [];
    const arity = [...kernel.datatypes.values()].flatMap(data => data.constructors).find(item => item.name === name)!.arity;
    if (arguments_.length !== arity) throw new SurfaceError(line, `constructor ${application[1]} expects ${arity} fields`);
    return ctor(name, ...arguments_.map(item => parsePattern(item, kernel, scope, line)));
  }
  const nullary = resolveOptional(surfaceSymbol(trimmed), scope, candidate =>
    [...kernel.datatypes.values()].some(data => data.constructors.some(item => item.name === candidate && item.arity === 0)));
  if (nullary) return ctor(nullary);
  if (!SIMPLE_IDENTIFIER.test(trimmed)) throw new SurfaceError(line, `malformed pattern ${trimmed}`);
  return bind(trimmed);
}

function collectPatternBindings(pattern: Pattern, result: Set<string>): void {
  if (pattern.tag === "bind") result.add(pattern.name);
  else pattern.args.forEach(item => collectPatternBindings(item, result));
}

interface Token {
  readonly text: string;
  readonly offset: number;
  /** Original identifier before a possible Unicode-subscript expansion. */
  readonly subscriptOriginal?: string;
}

interface ImplicitOverride { readonly name?: string; readonly value: Term }

function substituteTerms(term: Term, substitution: ReadonlyMap<string, Term>): Term {
  let result = term;
  for (const [name, value] of substitution) result = substituteTerm(result, name, value);
  return result;
}

function termTypeDescriptor(kernel: Kernel, term: Term, scope: SurfaceScope): Binder | undefined {
  if (naturalValue(term) !== undefined) return { name: "_", type: "Nat" };
  if (term.tag === "var") return scope.binderTypes?.get(term.name);
  const signature = surfaceEnvironments.get(kernel)?.signatures.get(term.fn);
  if (!signature?.resultType) return undefined;
  const listCarrier = listLiteralCarriers.get(term);
  if (listCarrier) return { name: "_", type: signature.resultType, typeArguments: [listCarrier] };
  const substitution = new Map(signature.parameters.map((parameter, index) => [parameter.name, term.args[index]!]));
  return {
    name: "_", type: signature.resultType,
    typeArguments: signature.resultTypeArguments?.map(argument => substituteTerms(argument, substitution)),
  };
}

/** Recover notation hints structurally after substitution/checkpoint replay.
 * AST identity is not stable across interning eviction. These are elaboration
 * hints only; all refinement certificates remain kernel checked. */
function notationTypesForTerm(kernel: Kernel, term: Term, scope: SurfaceScope): readonly string[] {
  if (term.tag !== "app") return [];
  const environment = surfaceEnvironments.get(kernel);
  if (!environment) return [];
  const cache = surfaceVisibilityCache(kernel, environment);
  const key = scopeVisibilityKey(scope);
  let index = cache.resultTypes.get(key);
  if (!index) {
    const reachable = reachableImports(cache, environment, scope);
    const fresh = new Map<string, SurfaceNotationRecord[]>();
    for (const item of environment.notations) {
      if (item.kind !== "function" || item.fixity === "sequence" ||
          !(item.fixity === "coercion" ? item.resultType : item.operandType) ||
          (item.module !== undefined && item.module !== scope.moduleName && !reachable.has(item.module))) continue;
      const entries = fresh.get(item.target) ?? [];
      entries.push(item);
      fresh.set(item.target, entries);
    }
    index = fresh;
    cache.resultTypes.set(key, index);
  }
  // A coercion's result has the sort it produces, realNat(n) : Real; a
  // postfix form has one operand, two when its token carries an index.
  return (index.get(term.fn) ?? []).filter(item => {
    const leading = item.leadingArguments ?? [];
    const arity = item.fixity === "numeral" ? 0 : item.fixity === "prefix" || item.fixity === "coercion" ? 1
      : item.fixity === "postfix" ? (item.token.includes("_") ? 2 : 1) : 2;
    return term.args.length === leading.length + arity &&
      leading.every((argument, i) => termEquals(argument, term.args[i]!));
  }).map(item => item.fixity === "coercion" ? item.resultType! : item.operandType!);
}

function termTypeNames(kernel: Kernel, term: Term, scope: SurfaceScope): ReadonlySet<string> {
  const result = new Set<string>();
  const descriptor = termTypeDescriptor(kernel, term, scope);
  if (descriptor) result.add(descriptor.type);
  const notationType = notationResultTypes.get(term);
  if (notationType) result.add(notationType);
  const annotated = kernelAnnotations.get(kernel)?.get(termCanonical(term));
  if (annotated) result.add(annotated);
  for (const type of notationTypesForTerm(kernel, term, scope)) result.add(type);
  // The value f(x) of a function `f : A → B` in scope has the sort of B, so
  // that `(f : ℝ → ℝ)` makes f(B) a real for the notation around it.
  const application = term.tag === "app" && term.args.length === 2 && shortName(term.fn) === "apply" ? term.args[0]! : undefined;
  for (const formula of scope.localFormulas?.() ?? []) {
    if (formula.tag === "pred" && formula.args.length === 1 && termEquals(formula.args[0]!, term)) {
      result.add(formula.pred);
    }
    if (application && formula.tag === "pred" && formula.args.length === 3 && shortName(formula.pred) === "FunctionBetween" &&
        termEquals(formula.args[0]!, application)) {
      const codomain = carrierSortName(kernel, scope, formula.args[2]!);
      if (codomain) result.add(codomain);
    }
  }
  return result;
}

/** The unary sort of a carrier set, `Real` for ℝ and `Nat` for ℕ, as the predicate the notation declarations name. */
function carrierSortName(kernel: Kernel, scope: SurfaceScope, carrier: Term): string | undefined {
  const bounded = boundedCarrierType(kernel, carrier);
  if (bounded) return bounded;
  if (carrier.tag !== "app" || carrier.args.length !== 0) return undefined;
  const sort = ({ reals: "Real", rationals: "Rational", integers: "Integer" } as Readonly<Record<string, string>>)[shortName(carrier.fn)];
  return sort ? resolveOptional(sort, scope, candidate => kernel.predicates.get(candidate) === 1) : undefined;
}

/** Decide an overloaded-notation operand type using both syntax and checked refinements. */
function termHasType(kernel: Kernel, term: Term, type: string, scope: SurfaceScope): boolean {
  if (termTypeNames(kernel, term, scope).has(type)) return true;
  // During recursive-body parsing the signature exists, but the function is
  // not admitted yet. Use its syntax-level type hint; refinement proof search
  // cannot query the kernel about any term containing that pending function.
  if (scope.pendingFunction && containsFunction(term, scope.pendingFunction)) return false;
  return Boolean(proveRefinement(kernel, term, type, [], scope.localFormulas?.() ?? [], [], scopeVisibility(kernel, scope)));
}

function typedNumeral(
  kernel: Kernel, scope: SurfaceScope, line: number, term: Term, type: string,
): Term | undefined {
  const value = naturalValue(term)?.toString();
  if (value === undefined) return undefined;
  const groups = visibleInfixNotationGroups(kernel, scope, line, "function", "numeral");
  const selected = (groups.get(value) ?? []).find(item => item.operandType === type);
  if (selected) return app(selected.target, ...(selected.leadingArguments ?? []));
  // A numeral template for the type covers every literal.
  const template = (groups.get("_") ?? []).find(item => item.operandType === type);
  return template ? app(template.target, ...(template.leadingArguments ?? []), nat(value)) : undefined;
}

/**
 * An equation between a term of a sort a coercion reads from and a term of
 * the sort it reads into, k! = X with X real, takes the coercion on the
 * first: realNat(k!) = X. A numeral keeps its typed declaration.
 */
function harmonizeCoercedEquation(
  kernel: Kernel, scope: SurfaceScope, line: number, left: Term, right: Term,
): readonly [Term, Term] {
  const coercions = [...visibleInfixNotationGroups(kernel, scope, line, "function", "coercion").values()].flat();
  if (!coercions.length) return [left, right];
  const leftTypes = termTypeNames(kernel, left, scope);
  const rightTypes = termTypeNames(kernel, right, scope);
  const coerce = (term: Term, types: ReadonlySet<string>, other: ReadonlySet<string>): Term | undefined => {
    if (naturalValue(term) !== undefined) return undefined;
    const coercion = coercions.find(item => item.operandType !== undefined && item.resultType !== undefined &&
      types.has(item.operandType) && !types.has(item.resultType) && other.has(item.resultType) && !other.has(item.operandType));
    return coercion ? app(coercion.target, term) : undefined;
  };
  return [coerce(left, leftTypes, rightTypes) ?? left, coerce(right, rightTypes, leftTypes) ?? right];
}

function harmonizeTypedNumerals(
  kernel: Kernel, scope: SurfaceScope, line: number, left: Term, right: Term,
): readonly [Term, Term] {
  // Explicit numeral annotations survive relation elaboration as well as term
  // parsing. In particular, (0 : Nat) must not become an ambient ring's zero.
  const untypedNumeral = (term: Term): boolean =>
    naturalValue(term) !== undefined && !notationResultTypes.has(term);
  if (scope.rings?.length && (untypedNumeral(left) || untypedNumeral(right))) {
    const ring = selectRing(scope, [left, right], line);
    return [untypedNumeral(left) ? ringNumeral(kernel, scope, left, ring, line) : left,
      untypedNumeral(right) ? ringNumeral(kernel, scope, right, ring, line) : right];
  }
  const convertFor = (numeral: Term, other: Term): Term => {
    if (notationResultTypes.has(numeral)) return numeral;
    const known = [...termTypeNames(kernel, other, scope)].filter(type => type !== "Set");
    const conversions = known
      .map(type => typedNumeral(kernel, scope, line, numeral, type))
      .filter((term): term is Term => term !== undefined);
    if (conversions.length === 1) return conversions[0]!;
    if (known.length || conversions.length) return numeral;
    // With no sort on the other side, the certified typing rules decide,
    // so that f′(X) = 0 reads the zero of the carrier f′(X) is proved to
    // lie in; a term the rules place nowhere keeps the natural numeral.
    const groups = visibleInfixNotationGroups(kernel, scope, line, "function", "numeral");
    const types = new Set([...groups.values()].flat().map(item => item.operandType).filter((type): type is string => type !== undefined));
    const proved = [...types].filter(type => type !== "Nat" && termHasType(kernel, other, type, scope))
      .map(type => typedNumeral(kernel, scope, line, numeral, type))
      .filter((term): term is Term => term !== undefined);
    return proved.length === 1 ? proved[0]! : numeral;
  };
  if (naturalValue(left) !== undefined && naturalValue(right) === undefined) {
    left = convertFor(left, right);
  } else if (naturalValue(right) !== undefined && naturalValue(left) === undefined) {
    right = convertFor(right, left);
  }
  return [left, right];
}

/** Use a graph element's product bound to type numerals in an ordered pair.
 *
 * This is the contextual information needed for natural graph notation such
 * as `p ∈ ℝ × ℝ ∧ p = (A ↦ 0)`: maplets may connect different carriers, so
 * guessing the result carrier from `A` would be unsound, while the product
 * bound determines both coordinates exactly.
 */
function harmonizeProductPairNumerals(
  kernel: Kernel, scope: SurfaceScope, line: number, pair: Term, bounded: Term,
): Term {
  if (pair.tag !== "app" || shortName(pair.fn) !== "orderedPair" || pair.args.length !== 2) return pair;
  for (const formula of scope.localFormulas?.() ?? []) {
    if (formula.tag !== "pred" || formula.pred !== "in" || formula.args.length !== 2 ||
        !termEquals(formula.args[0]!, bounded)) continue;
    const product = formula.args[1]!;
    if (product.tag !== "app" || shortName(product.fn) !== "product" || product.args.length !== 2) continue;
    const leftType = boundedCarrierType(kernel, product.args[0]!);
    const rightType = boundedCarrierType(kernel, product.args[1]!);
    const left = leftType ? typedNumeral(kernel, scope, line, pair.args[0]!, leftType) ?? pair.args[0]! : pair.args[0]!;
    const right = rightType ? typedNumeral(kernel, scope, line, pair.args[1]!, rightType) ?? pair.args[1]! : pair.args[1]!;
    return app(pair.fn, left, right);
  }
  return pair;
}

function matchImplicitTerm(
  pattern: Term, actual: Term, implicitNames: ReadonlySet<string>, substitution: Map<string, Term>,
): boolean {
  if (pattern.tag === "var" && implicitNames.has(pattern.name)) {
    const previous = substitution.get(pattern.name);
    if (previous) return termEquals(previous, actual);
    substitution.set(pattern.name, actual);
    return true;
  }
  if (pattern.tag !== actual.tag) return false;
  if (pattern.tag === "var" && actual.tag === "var") return pattern.name === actual.name;
  if (pattern.tag === "nat" && actual.tag === "nat") return pattern.value === actual.value;
  return pattern.tag === "app" && actual.tag === "app" && pattern.fn === actual.fn &&
    pattern.args.length === actual.args.length &&
    pattern.args.every((argument, index) => matchImplicitTerm(argument, actual.args[index]!, implicitNames, substitution));
}

function elaborateApplicationArguments(
  kernel: Kernel, symbol: string, explicitArguments: readonly Term[], overrides: readonly ImplicitOverride[],
  variables: ReadonlySet<string>, scope: SurfaceScope, line: number,
): readonly Term[] {
  const signature = surfaceEnvironments.get(kernel)?.signatures.get(symbol);
  // A definition of the open section is applied without its section
  // variables inside the section; they are put back here.
  const dropped = scope.sectionDefinitions?.get(symbol);
  if (dropped?.length && signature && explicitArguments.length + dropped.length === signature.parameters.length) {
    return [...dropped.map(name => v(name)), ...explicitArguments];
  }
  if (CARRIER_ARGUMENT_SYMBOLS.has(shortName(symbol))) {
    return explicitArguments.map(argument => structureCarrier(kernel, scope, argument));
  }
  if (!signature || !signature.parameters.some(item => item.implicit)) return explicitArguments;
  // Full applications remain accepted as a migration and kernel-facing escape hatch.
  if (overrides.length === 0 && explicitArguments.length === signature.parameters.length) return explicitArguments;
  const implicit = signature.parameters.filter(item => item.implicit);
  const ordinary = signature.parameters.filter(item => !item.implicit);
  if (explicitArguments.length !== ordinary.length) {
    throw new SurfaceError(line, `${shortName(symbol)} expects ${ordinary.length} explicit argument${ordinary.length === 1 ? "" : "s"} and ${implicit.length} implicit argument${implicit.length === 1 ? "" : "s"}`);
  }
  const inferred = new Map<string, Term>();
  let positional = 0;
  for (const override of overrides) {
    const parameter = override.name
      ? implicit.find(item => item.name === override.name)
      : implicit[positional++];
    if (!parameter) throw new SurfaceError(line, override.name
      ? `unknown implicit argument ${override.name} for ${shortName(symbol)}`
      : `too many positional implicit arguments for ${shortName(symbol)}`);
    if (inferred.has(parameter.name)) throw new SurfaceError(line, `implicit argument ${parameter.name} is specified more than once`);
    inferred.set(parameter.name, override.value);
  }
  const implicitNames = new Set(implicit.map(item => item.name));
  const literalDefaults: { pattern: Term; carrier: Term }[] = [];
  ordinary.forEach((parameter, index) => {
    const listCarrier = listLiteralCarriers.get(explicitArguments[index]!);
    if (listCarrier && parameter.typeArguments?.length === 1) {
      literalDefaults.push({ pattern: parameter.typeArguments[0]!, carrier: listCarrier });
      return;
    }
    const actualType = termTypeDescriptor(kernel, explicitArguments[index]!, scope);
    if (!actualType || parameter.type !== actualType.type) return;
    const expected = parameter.typeArguments ?? [];
    const actual = actualType.typeArguments ?? [];
    if (expected.length !== actual.length) return;
    expected.forEach((argument, argumentIndex) => {
      if (!matchImplicitTerm(argument, actual[argumentIndex]!, implicitNames, inferred)) {
        throw new SurfaceError(line, `incompatible soft type for argument ${parameter.name} of ${shortName(symbol)}`);
      }
    });
  });
  // A literal's finite carrier is a fallback, not a constraint: [] inhabits
  // every List(A), and [x] may use a larger carrier selected by another input.
  // Membership obligations are still discharged by checked constructor rules.
  for (const { pattern, carrier } of literalDefaults) {
    if (pattern.tag === "var" && implicitNames.has(pattern.name) && !inferred.has(pattern.name))
      inferred.set(pattern.name, carrier);
  }
  for (const parameter of implicit) {
    if (!inferred.has(parameter.name) && variables.has(parameter.name)) inferred.set(parameter.name, v(parameter.name));
    if (!inferred.has(parameter.name)) {
      throw new SurfaceError(line,
        `cannot infer implicit argument ${parameter.name} for ${shortName(symbol)}; use ${shortName(symbol)}{${parameter.name} := ...}(...)`);
    }
  }
  let explicitIndex = 0;
  return signature.parameters.map(parameter => parameter.implicit
    ? inferred.get(parameter.name)!
    : explicitArguments[explicitIndex++]!);
}

/** The embedding of the naturals into a ring, ringNat(add, zero, one, n), when its module is loaded. */
function ringNatSymbol(kernel: Kernel, scope: SurfaceScope): string | undefined {
  return resolveOptional("ringNat", scope, candidate => kernel.functions.get(candidate) === 4) ??
    [...kernel.functions.keys()].find(name => name.endsWith(".ringNat") && kernel.functions.get(name) === 4);
}

/** A numeral inside a scoped ring: 0 and 1 are the ring's constants, and k ≥ 2 is ringNat(add, zero, one, k). */
function ringNumeral(kernel: Kernel, scope: SurfaceScope, term: Term, ring: RingNotation, line: number): Term {
  const n = naturalValue(term);
  if (n === undefined) return term;
  if (n === 0n) return ring.zero;
  if (n === 1n) return ring.one;
  // A concrete carrier with declared numerals, such as ℝ, keeps them: 2 in a
  // real ring scope is the real two, as (2:R) is.
  const carrierType = boundedCarrierType(kernel, ring.carrier);
  if (carrierType && carrierType !== "Nat") {
    const declared = typedNumeral(kernel, scope, line, term, carrierType);
    if (declared) return declared;
  }
  const symbol = ringNatSymbol(kernel, scope);
  if (!symbol) throw new SurfaceError(line,
    `the scoped ring numeral ${n} needs ringNat from Grace.Cumulus.Algebra.Ring.Numeral; import Grace.Cumulus.Algebra.Ring`);
  return app(symbol, ring.add, ring.zero, ring.one, nat(n));
}

interface HypothesisOperation {
  readonly operation: Term;
  readonly carrier: Term;
  readonly notation: SurfaceNotationRecord;
}

/** The operations that hypotheses in scope supply for the given `via hypothesis` notations. */
function hypothesisOperations(facts: readonly Formula[], notations: readonly SurfaceNotationRecord[]): HypothesisOperation[] {
  const found: HypothesisOperation[] = [];
  for (const notation of notations) {
    const pattern = notation.hypothesis;
    if (!pattern?.output || !pattern.carriers.length) continue;
    for (const fact of facts) {
      if (fact.tag !== "pred" || fact.pred !== pattern.predicate || fact.args.length !== pattern.arity) continue;
      const operation = instantiatePattern(pattern.output, pattern, fact);
      const carrier = instantiatePattern(pattern.carriers[0]!, pattern, fact);
      if (!found.some(item => item.notation.token === notation.token &&
          termEquals(item.operation, operation) && termEquals(item.carrier, carrier))) {
        found.push({ operation, carrier, notation });
      }
    }
  }
  return found;
}

/**
 * The function facts a hypothesis asserts outright: the `FunctionBetween`
 * conjuncts of its predicate's definition, instantiated at its arguments,
 * opening defined conjuncts to a small depth. `Functor(F0, F1, O, M, …)`
 * yields `F1 : M → M2`; the notation uses this to read `F1(f)` as a
 * morphism of the target, with no proof search.
 */
function definitionFunctionFacts(kernel: Kernel, facts: readonly Formula[], depth = 2): Formula[] {
  return definitionConjuncts(kernel, facts, depth).filter(conjunct =>
    conjunct.tag === "pred" && shortName(conjunct.pred) === "FunctionBetween" && conjunct.args.length === 3);
}

/**
 * The atomic conjuncts of the definitions of the predicate facts given,
 * instantiated at their arguments, opening defined conjuncts to a small
 * depth: from `InversePair(C, f, g)` come `f ∈ mor(C)`, `g ∈ mor(C)`, and
 * the endpoint equations.
 */
function definitionConjuncts(kernel: Kernel, facts: readonly Formula[], depth = 2): Formula[] {
  const result: Formula[] = [];
  for (const fact of facts) {
    if (fact.tag !== "pred") continue;
    const equation = kernel.definitions.get(fact.pred)?.properties.get("equation");
    if (!equation) continue;
    let formula = equation;
    const parameters: string[] = [];
    while (formula.tag === "forall") { parameters.push(formula.variable); formula = formula.body; }
    if (formula.tag !== "iff" || parameters.length !== fact.args.length) continue;
    // Simultaneous substitution through placeholders, since an argument may
    // be a variable spelled like a later parameter.
    let body = formula.right;
    parameters.forEach((parameter, index) => { body = substituteFormula(body, parameter, v(`$${index}`)); });
    parameters.forEach((_, index) => { body = substituteFormula(body, `$${index}`, fact.args[index]!); });
    // An existential conjunct still asserts the conjuncts about its free
    // terms; its bound variables are renamed so that they match nothing.
    let bound = 0;
    const peel = (current: Formula): Formula => {
      while (current.tag === "exists") { current = substituteFormula(current.body, current.variable, v(`$bound${bound++}`)); }
      return current;
    };
    const conjuncts: Formula[] = [];
    const stack = [peel(body)];
    while (stack.length) {
      const current = peel(stack.pop()!);
      if (current.tag === "and") stack.push(current.left, current.right);
      else conjuncts.push(current);
    }
    for (const conjunct of conjuncts) {
      result.push(conjunct);
      if (conjunct.tag === "pred" && depth > 1 && kernel.definitions.has(conjunct.pred)) {
        result.push(...definitionConjuncts(kernel, [conjunct], depth - 1));
      }
    }
  }
  return result;
}

/**
 * `F(x)` for a functor `F` in scope is `obj(F)(x)` when `x` is an object of
 * the source category and `map(F)(x)` when it is a morphism, as the local
 * facts decide, so that both are written as `F` applied, in the manner of
 * a structure's `F.obj` and `F.map`. Undefined when no `Functor(F, C, D)` fact is
 * in scope; an error when the facts do not place the argument.
 */
function functorApplication(kernel: Kernel, scope: SurfaceScope, base: Term, argument: Term, line: number): Term | undefined {
  const facts = expandedLocalFormulas(kernel, scope);
  const functor = facts.find(fact => fact.tag === "pred" && shortName(fact.pred) === "Functor" &&
    fact.args.length === 3 && termEquals(fact.args[0]!, base));
  if (!functor || functor.tag !== "pred") return undefined;
  const source = functor.args[1]!;
  const kind = functorArgumentKind(kernel, scope, facts, argument, source);
  if (!kind) {
    throw new SurfaceError(line, `${formatTerm(base)} is a functor, and ${formatTerm(argument)} is not known to be an object or a morphism of ${formatTerm(source)}; add a binder such as (x ∈ obj(${formatTerm(source)})) or (f : a ⟶ b), or write obj(${formatTerm(base)})(x) for an object and map(${formatTerm(base)})(f) for a morphism`);
  }
  const field = kind === "object" ? "obj" : "map";
  const structure = structureOfPredicate(kernel, functor.pred)?.structure;
  const projection = structure && structure.fields.includes(field)
    ? structure.projections[structure.fields.indexOf(field)]!
    : resolveExisting(field, scope, candidate => kernel.functions.get(candidate) === 1, line, "functor projection");
  const applySymbol = resolveExisting("apply", scope, candidate => kernel.functions.get(candidate) === 2, line, "function application");
  return app(applySymbol, app(projection, base), argument);
}

/** Whether the facts place a term among the objects or the morphisms of a category. */
function functorArgumentKind(
  kernel: Kernel, scope: SurfaceScope, facts: readonly Formula[], term: Term, source: Term,
): "object" | "morphism" | undefined {
  // The objects and morphisms of the source are its projections, read off
  // the category structure that the facts place the source in.
  const category = facts.flatMap(fact => fact.tag === "pred" && fact.args.length === 1 && termEquals(fact.args[0]!, source)
    ? [structureOfPredicate(kernel, fact.pred)?.structure] : []).find(Boolean) ??
    [...(surfaceEnvironments.get(kernel)?.datatypes.values() ?? [])]
      .find(item => item.structure && ["obj", "mor"].every(field => item.structure!.fields.includes(field)))?.structure;
  const projection = (field: string): string | undefined => category && category.fields.includes(field)
    ? category.projections[category.fields.indexOf(field)]
    : resolveOptional(field, scope, candidate => kernel.functions.get(candidate) === 1 && !projectionOf(kernel, candidate));
  const obj = projection("obj");
  const mor = projection("mor");
  if (!obj || !mor) return undefined;
  const objects = app(obj, source);
  const morphisms = app(mor, source);
  const classify = (set: Term): "object" | "morphism" | undefined => termEquals(set, objects) ? "object"
    : termEquals(set, morphisms) || homSetInCarriers(set, [morphisms]) ? "morphism" : undefined;
  for (const fact of [...facts, ...definitionConjuncts(kernel, facts)]) {
    if (fact.tag !== "pred") continue;
    if (fact.pred === "in" && fact.args.length === 2 && termEquals(fact.args[0]!, term)) {
      const kind = classify(fact.args[1]!);
      if (kind) return kind;
    }
    // The endpoints of a hom-set membership or of a guard are objects.
    if (fact.pred === "in" && fact.args.length === 2 && homSetInCarriers(fact.args[1]!, [morphisms]) &&
        fact.args[1]!.tag === "app" && fact.args[1]!.args.slice(1).some(endpoint => termEquals(endpoint, term))) return "object";
    if (shortName(fact.pred) === "Morphism" && fact.args.length === 4 && termEquals(fact.args[0]!, source)) {
      if (termEquals(fact.args[1]!, term)) return "morphism";
      if (fact.args.slice(2).some(endpoint => termEquals(endpoint, term))) return "object";
    }
  }
  if (term.tag !== "app") return undefined;
  if (shortName(term.fn) === "apply" && term.args.length === 2) {
    const graph = term.args[0]!;
    if (graph.tag === "app" && graph.args.length === 1 && shortName(graph.fn) === "obj") return "object";
    if (graph.tag === "app" && graph.args.length === 1 && shortName(graph.fn) === "map") return "morphism";
    for (const codomain of hypothesisCodomains(kernel, facts, graph)) {
      const kind = classify(codomain);
      if (kind) return kind;
    }
    return undefined;
  }
  if (term.args.length === 3 && shortName(term.fn) === "call2" && term.args[0]!.tag === "app" &&
      shortName(term.args[0]!.fn) === "comp" && term.args[0]!.args.length === 1 &&
      termEquals(term.args[0]!.args[0]!, source)) return "morphism";
  return undefined;
}

/** The functors that facts in scope declare, printed as `F(x)` for `obj(F)(x)` and `map(F)(x)`. */
function displayFunctors(facts: readonly Formula[]): Term[] {
  const result: Term[] = [];
  for (const fact of facts) {
    if (fact.tag !== "pred" || fact.args.length !== 3) continue;
    const candidates = shortName(fact.pred) === "Functor" ? [fact.args[0]!]
      : shortName(fact.pred) === "NaturalTransformation" ? [fact.args[1]!, fact.args[2]!] : [];
    for (const candidate of candidates) {
      if (!result.some(item => termEquals(item, candidate))) result.push(candidate);
    }
  }
  return result;
}

/**
 * The codomains the context gives a function graph: direct `F : A → B`
 * facts and those its hypotheses assert; the components of a transformation
 * `η : F ⟹ G` lie in the morphisms of the target of `F`, read off the
 * functor hypothesis about `F`.
 */
function hypothesisCodomains(kernel: Kernel, facts: readonly Formula[], graph: Term): Term[] {
  const functionFacts = [...facts, ...definitionFunctionFacts(kernel, facts)];
  const codomains = functionFacts.flatMap(fact =>
    fact.tag === "pred" && shortName(fact.pred) === "FunctionBetween" && fact.args.length === 3 &&
      termEquals(fact.args[0]!, graph) ? [fact.args[2]!] : []);
  for (const fact of facts) {
    if (fact.tag !== "pred" || shortName(fact.pred) !== "NaturalTransformation" || fact.args.length !== 3 ||
        !termEquals(fact.args[0]!, graph)) continue;
    const functor = fact.args[1]!;
    for (const item of functionFacts) {
      if (item.tag === "pred" && shortName(item.pred) === "FunctionBetween" && item.args.length === 3 &&
          item.args[0]!.tag === "app" && shortName(item.args[0]!.fn) === "map" && item.args[0]!.args.length === 1 &&
          termEquals(item.args[0]!.args[0]!, functor)) codomains.push(item.args[2]!);
    }
  }
  return codomains;
}

/**
 * Whether an operand lies in a carrier: by a membership fact, a hom-set
 * membership, being a constant or a composite already read under a
 * hypothesis token on that carrier, or being the value of a function into it.
 */
function operandInCarrier(
  kernel: Kernel, facts: readonly Formula[], composites: readonly HypothesisOperation[], term: Term, carrier: Term,
): boolean {
  if (facts.some(fact => fact.tag === "pred" && fact.pred === "in" && fact.args.length === 2 &&
      termEquals(fact.args[0]!, term) &&
      (termEquals(fact.args[1]!, carrier) || homSetInCarriers(fact.args[1]!, [carrier])))) return true;
  if (composites.some(item => item.notation.fixity === "constant" && termEquals(item.operation, term) &&
      termEquals(item.carrier, carrier))) return true;
  if (term.tag !== "app") return false;
  if ((term.args.length === 3 || term.args.length === 2) && composites.some(item => item.notation.target === term.fn &&
      item.notation.fixity !== "constant" && (term.args.length === 3) === !item.notation.fixity &&
      termEquals(item.operation, term.args[0]!) && termEquals(item.carrier, carrier))) return true;
  if (shortName(term.fn) === "apply" && term.args.length === 2) {
    return hypothesisCodomains(kernel, facts, term.args[0]!).some(codomain => termEquals(codomain, carrier));
  }
  return false;
}

/**
 * Whether the typed declarations of a token win over the operations the
 * hypotheses in scope supply for these operands: no operand is placed in a
 * supplying hypothesis' carrier, and an operand carries the sort of a typed
 * declaration, by its syntax, a local fact, or the certified typing rules.
 * So `n * m` and `2 ^ n` are natural arithmetic inside a group section,
 * `a ^ 2` is the group power, and `index(G, H) * cardinality(H)` is the
 * natural product once the index is known to be a natural number.
 */
function typedOperandsOutsideHypothesis(
  kernel: Kernel, scope: SurfaceScope, supplied: readonly SurfaceNotationRecord[], typed: readonly SurfaceNotationRecord[],
  operands: readonly Term[], line: number,
): boolean {
  const facts = expandedLocalFormulas(kernel, scope);
  let found = hypothesisOperations(facts, supplied);
  if (!found.length) found = hypothesisOperations(closedInstanceFacts(kernel, scope), supplied);
  if (!found.length) return false;
  const composites = hypothesisOperations(facts, visibleHypothesisFunctionNotations(kernel, scope, line));
  if (operands.some(term => found.some(item => operandInCarrier(kernel, facts, composites, term, item.carrier)))) return false;
  const sorts = [...new Set(typed.flatMap(item => notationOperandTypes(item).filter((type): type is string => type !== undefined)))];
  const sorted = (term: Term): boolean => naturalValue(term) !== undefined ||
    [...termTypeNames(kernel, term, scope)].some(type => sorts.includes(type));
  // An operand without a sort that the certified typing rules place in a
  // carrier keeps the hypothesis: G.one ^ 1 is the group power, since
  // Group.one_mem places the unit in G.carrier.
  const assumptions = scope.localFormulas?.() ?? [];
  const placed = (term: Term): boolean => found.some(item =>
    Boolean(proveRefinement(kernel, item.carrier, "in", [term], assumptions, [], scopeVisibility(kernel, scope))));
  const unsorted = operands.filter(term => !sorted(term));
  if (unsorted.length < operands.length) return !unsorted.some(placed);
  if (unsorted.some(placed)) return false;
  return operands.some(term => sorts.some(type => termHasType(kernel, term, type, scope)));
}

/**
 * The form whose left operand is the structure itself that these operands
 * select: `G ⧸ N` is `quotientGroup(G, N)` when the left operand is the
 * structure of a hypothesis in scope, a section hypothesis, an earlier
 * `requires`, a structure-typed binder, a fact in the proof state, or a
 * closed instance such as `CommRing(integerRing)`. With no such hypothesis
 * the token falls back to its other declarations; two forms with different
 * targets for one structure are an error that asks for the function by name.
 */
function selectStructureOperation(
  kernel: Kernel, scope: SurfaceScope, notations: readonly SurfaceNotationRecord[], left: Term, line: number,
): HypothesisOperation | undefined {
  const constructed = left.tag === "app" && left.args.length > 0 && structureValueOf(kernel, scope, left) !== undefined;
  if (left.tag !== "var" && !(left.tag === "app" && left.args.length === 0) && !constructed) return undefined;
  const local = expandedLocalFormulas(kernel, scope);
  const facts = [...local, ...closedInstanceFacts(kernel, scope),
    ...(constructed ? instanceStructureFacts(kernel, scope, left, local) : [])];
  const found = hypothesisOperations(facts, notations).filter(item => termEquals(item.operation, left));
  const targets = [...new Set(found.map(item => item.notation.target))];
  if (targets.length > 1) {
    throw new SurfaceError(line, `ambiguous notation ${notations[0]!.token}; hypotheses in scope make ${formatTerm(left)} a structure of ${targets.map(target => shortName(target)).join(" and ")}; write the function by name`);
  }
  return found[0];
}

/**
 * Choose the operation a `via hypothesis` token denotes for these operands.
 * One supplied operation is taken as it stands; among several, an operand
 * selects the supplier whose carrier it lies in, by a membership fact, a
 * hom-set membership, being a composite already read in that carrier, or
 * being the value of a function into it, and the operands must agree on one.
 */
function selectHypothesisOperation(
  kernel: Kernel, scope: SurfaceScope, notations: readonly SurfaceNotationRecord[], operands: readonly Term[], line: number,
  optional = false,
): HypothesisOperation | undefined {
  let facts = expandedLocalFormulas(kernel, scope);
  let found = hypothesisOperations(facts, notations);
  const token = notations[0]!.token;
  if (found.length === 0) {
    // A closed instance such as CommRing(integerRing) supplies the token where
    // no local hypothesis does.
    const closed = closedInstanceFacts(kernel, scope);
    found = hypothesisOperations(closed, notations);
    if (found.length) facts = [...facts, ...closed];
  }
  if (found.length === 0) {
    // With no supplying hypothesis the token falls back to its other
    // declarations, such as the typed `*` of the naturals, when it has any.
    if (optional) return undefined;
    const shapes = [...new Set(notations.map(item => shortName(item.hypothesis!.predicate)))].join(", ");
    throw new SurfaceError(line, `no hypothesis in scope supplies an operation for ${token}; it needs one of ${shapes}`);
  }
  const distinct = (items: readonly HypothesisOperation[]): HypothesisOperation[] =>
    items.filter((item, index) => items.findIndex(other => termEquals(other.operation, item.operation)) === index);
  let operations = distinct(found);
  // A composite already read under any hypothesis-supplied token, a⁻¹ among
  // them, lies in that token's carrier.
  let composites = hypothesisOperations(facts, visibleHypothesisFunctionNotations(kernel, scope, line));
  const inCarrier = (term: Term, carrier: Term): boolean => operandInCarrier(kernel, facts, composites, term, carrier);
  // An operand the local facts place nowhere may be placed by the certified
  // typing rules in the carrier of a structure value an instance supplies,
  // X(R, I, j) in Ring.carrier(polynomialRing(R, I)) by X.mem: that
  // structure's operations join the candidates.
  const unplaced = operands.filter(term => term.tag === "app" && term.args.length > 0 &&
    !found.some(item => inCarrier(term, item.carrier)));
  const derived = unplaced.flatMap(term => {
    const carrier = completedCarrier(kernel, scope, facts, term);
    return carrier?.tag === "app" && carrier.args.length === 1 && projectionOf(kernel, carrier.fn) &&
      !found.some(item => termEquals(item.carrier, carrier)) && structureValueOf(kernel, scope, carrier.args[0]!)
      ? instanceStructureFacts(kernel, scope, carrier.args[0]!, facts).map(fact => ({ fact, term, carrier })) : [];
  });
  if (derived.length) {
    facts = [...facts, ...derived.map(item => item.fact), ...derived.map(item => pred("in", item.term, item.carrier))];
    found = hypothesisOperations(facts, notations);
    operations = distinct(found);
    composites = hypothesisOperations(facts, visibleHypothesisFunctionNotations(kernel, scope, line));
  }
  if (operations.length === 1) return operations[0];
  // An operand selects a supplier when it lies in its carrier; an operand
  // with no evidence either way does not stand in the way.
  const select = (lies: (term: Term, carrier: Term) => boolean): HypothesisOperation[] => {
    const placed = (term: Term): boolean => found.some(item => lies(term, item.carrier));
    return distinct(found.filter(item =>
      operands.some(term => lies(term, item.carrier)) &&
      operands.every(term => !placed(term) || lies(term, item.carrier))));
  };
  const matching = select(inCarrier);
  if (matching.length === 1) return matching[0];
  // With no syntactic evidence, the certified typing rules decide: unit(G)
  // lies in carrier(G) by the closure instance of the group.
  const typed = select((term, carrier) => inCarrier(term, carrier) ||
    Boolean(proveRefinement(kernel, carrier, "in", [term], scope.localFormulas?.() ?? [], [], scopeVisibility(kernel, scope))));
  if (typed.length === 1) return typed[0];
  if (!operands.length) {
    throw new SurfaceError(line, `ambiguous notation ${token}; hypotheses in scope supply ${operations.map(item => formatTerm(item.operation)).join(" and ")}; write the constant by name`);
  }
  throw new SurfaceError(line, `ambiguous notation ${token}; hypotheses in scope supply ${operations.map(item => formatTerm(item.operation)).join(" and ")}, and the operands ${operands.map(term => formatTerm(term)).join(", ")} do not select one; write the operation by name`);
}

/**
 * The operations a theorem's hypotheses supply, for printing its statement
 * and goals with the declared tokens. Two different operations on the same
 * carrier are left unprinted, since the token alone would not tell them apart.
 */
function displayOperations(
  kernel: Kernel, scope: SurfaceScope, facts: readonly Formula[], conclusions: readonly Formula[] = [],
): OperationNotation[] {
  const notations = visibleHypothesisFunctionNotations(kernel, scope, scope.line ?? 0);
  if (!notations.length) return [];
  // A transparent guard among the hypotheses, such as f : G →* H, supplies
  // the operations of the structures it opens to.
  const expanded = facts.flatMap(formula => [formula,
    ...openGuardFact(kernel, { formula, proof: assume(formula) }, scopeVisibility(kernel, scope)).map(item => item.formula)]);
  const opened = [...expanded, ...derivedStructureFacts(kernel, scope, expanded, [], conclusions)];
  const local = hypothesisOperations(opened, notations);
  const found = [...local, ...hypothesisOperations(closedInstanceFacts(kernel, scope), notations)
    .filter(item => !local.some(other => other.notation.token === item.notation.token))];
  return found.flatMap(item => {
    // The infix and prefix `-` of a ring share the token and the carrier
    // and are told apart by their arity, so only one fixity counts as a rival.
    const rivals = found.filter(other => other.notation.token === item.notation.token &&
      other.notation.fixity === item.notation.fixity &&
      termEquals(other.carrier, item.carrier) && !termEquals(other.operation, item.operation));
    if (rivals.length) return [];
    return [{
      operation: item.operation, token: item.notation.token, precedence: item.notation.precedence,
      associativity: item.notation.associativity, call: item.notation.target,
      ...(item.notation.fixity === "postfix" || item.notation.fixity === "prefix" || item.notation.fixity === "constant"
        ? { fixity: item.notation.fixity } : {}),
      ...(item.notation.hypothesis?.structureOperand ? { structure: true as const } : {}),
    }];
  });
}

/**
 * The term a function form supplied by a hypothesis denotes, `ker(f)` for
 * `ringKernel(f, R.carrier, S.zero)` under `f : R →+* S`, or undefined when
 * no hypothesis in scope supplies the name at this arity, so that a declared
 * function of the name is read instead. A parameter named as a pattern
 * variable must be that argument of the hypothesis; among several
 * hypotheses the free arguments choose by lying in the carrier named by
 * `for`, and otherwise the error asks for the function by name.
 */
function functionNotationApplication(
  kernel: Kernel, scope: SurfaceScope, name: string, args: readonly Term[], line: number,
): Term | undefined {
  const candidates = visibleInfixNotationGroups(kernel, scope, line, "function", "function").get(name)
    ?.filter(item => item.hypothesis?.parameters?.length === args.length);
  if (!candidates?.length) return undefined;
  const local = [...expandedLocalFormulas(kernel, scope), ...binderAssumptions([...(scope.binderTypes?.values() ?? [])])];
  const facts = [...local, ...closedInstanceFacts(kernel, scope)];
  const found: { readonly term: Term; readonly carrier?: Term }[] = [];
  for (const notation of candidates) {
    const pattern = notation.hypothesis!;
    for (const fact of facts) {
      if (fact.tag !== "pred" || fact.pred !== pattern.predicate || fact.args.length !== pattern.arity) continue;
      const instantiated = functionNotationTemplate(pattern, fact, args);
      if (!instantiated) continue;
      const carrier = pattern.carriers[0] ? instantiatePattern(pattern.carriers[0], pattern, fact) : undefined;
      if (!found.some(item => termEquals(item.term, instantiated))) found.push({ term: instantiated, ...(carrier ? { carrier } : {}) });
    }
  }
  if (found.length === 0) return undefined;
  if (found.length === 1) return found[0]!.term;
  const composites = hypothesisOperations(facts, visibleHypothesisFunctionNotations(kernel, scope, line));
  const placed = found.filter(item => item.carrier &&
    args.some(argument => operandInCarrier(kernel, facts, composites, argument, item.carrier!)));
  if (placed.length === 1) return placed[0]!.term;
  throw new SurfaceError(line, `ambiguous notation ${name}(${args.map(argument => formatTerm(argument)).join(", ")}); hypotheses in scope supply ${found.map(item => formatTerm(item.term)).join(" and ")}; write the function by name`);
}

/**
 * The template of a function form at a hypothesis and the written
 * arguments, or undefined when an argument tied to a pattern variable is
 * not that argument of the hypothesis. With no arguments given, the free
 * parameters stay as the holes `$argument0`, `$argument1`, … for printing.
 */
function functionNotationTemplate(
  pattern: HypothesisPattern, fact: Extract<Formula, { readonly tag: "pred" }>, args?: readonly Term[],
): Term | undefined {
  let term = pattern.output!;
  for (const [index, parameter] of pattern.parameters!.entries()) {
    const position = pattern.names.indexOf(parameter);
    if (position >= 0) {
      if (args && !termEquals(fact.args[position]!, args[index]!)) return undefined;
    } else term = substituteTerm(term, parameter, v(`$argument${index}`));
  }
  term = instantiatePattern(term, pattern, fact);
  if (args) pattern.parameters!.forEach((_, index) => { term = substituteTerm(term, `$argument${index}`, args[index]!); });
  return term;
}

/**
 * The function forms the hypotheses in scope supply, for printing a
 * statement or goal: the template at each hypothesis with the free
 * parameters as holes, so that `ringKernel(f, R.carrier, S.zero)` prints as
 * `ker(f)` under `f : R →+* S`. Two hypotheses that would print different
 * terms the same way, with no carrier to tell their arguments apart, leave
 * the token unprinted.
 */
function displayFunctions(kernel: Kernel, scope: SurfaceScope, facts: readonly Formula[]): FunctionNotation[] {
  const notations = [...visibleInfixNotationGroups(kernel, scope, scope.line ?? 0, "function", "function").values()].flat();
  if (!notations.length) return [];
  const opened = facts.flatMap(formula => [formula,
    ...openGuardFact(kernel, { formula, proof: assume(formula) }, scopeVisibility(kernel, scope)).map(item => item.formula)]);
  const all = [...opened, ...closedInstanceFacts(kernel, scope)];
  const found: (FunctionNotation & { readonly carrier?: Term })[] = [];
  for (const notation of notations) {
    const pattern = notation.hypothesis!;
    for (const fact of all) {
      if (fact.tag !== "pred" || fact.pred !== pattern.predicate || fact.args.length !== pattern.arity) continue;
      const template = functionNotationTemplate(pattern, fact)!;
      const holes = pattern.parameters!.map(parameter => {
        const position = pattern.names.indexOf(parameter);
        return position >= 0 ? fact.args[position]! : undefined;
      });
      const carrier = pattern.carriers[0] ? instantiatePattern(pattern.carriers[0], pattern, fact) : undefined;
      if (!found.some(item => item.token === notation.token && termEquals(item.template, template))) {
        found.push({ token: notation.token, template, arguments: holes, ...(carrier ? { carrier } : {}) });
      }
    }
  }
  const sameArguments = (left: FunctionNotation, right: FunctionNotation): boolean =>
    left.arguments.length === right.arguments.length && left.arguments.every((term, index) => {
      const other = right.arguments[index];
      return (term === undefined) === (other === undefined) && (term === undefined || termEquals(term, other!));
    });
  return found.filter(item => item.carrier || !found.some(other => other !== item && other.token === item.token &&
    !other.carrier && sameArguments(item, other))).map(({ token, template, arguments: holes }) => ({ token, template, arguments: holes }));
}

/**
 * The closed facts the visible instances assert outright, `CommRing(integerRing)`
 * for a declared `integerRing : Set := Ring.mk(…)`: a hypothesis notation whose
 * token no local hypothesis supplies falls back to these, so `x + y` on
 * members of `integerRing.carrier` is the addition of that ring.
 */
function closedInstanceFacts(kernel: Kernel, scope: SurfaceScope): Formula[] {
  const result: Formula[] = [];
  for (const name of visibleInstanceNames(kernel, scope)) {
    const statement = kernel.theorems.get(name);
    if (statement?.tag === "pred" && freeFormulaVariables(statement).size === 0) result.push(statement);
  }
  return result;
}

/** The infix, postfix, and prefix function notations in scope that a hypothesis supplies. */
function visibleHypothesisFunctionNotations(kernel: Kernel, scope: SurfaceScope, line: number): SurfaceNotationRecord[] {
  return (["infix", "postfix", "prefix", "constant"] as const).flatMap(fixity =>
    [...visibleInfixNotationGroups(kernel, scope, line, "function", fixity).values()].flat()
      .filter(item => item.hypothesis?.output));
}

/**
 * The notations in scope whose hypothesis names one carrier: the operations
 * and the infix predicates, `a ≤ b` under an order, so that a binder
 * `(a : P)` reads its carrier off either.
 */
function visibleHypothesisCarrierNotations(kernel: Kernel, scope: SurfaceScope, line: number): SurfaceNotationRecord[] {
  return [
    // A form whose left operand is the structure itself names no carrier.
    ...visibleHypothesisFunctionNotations(kernel, scope, line).filter(item => !item.hypothesis?.structureOperand),
    ...[...visibleInfixNotationGroups(kernel, scope, line, "predicate").values()].flat()
      .filter(item => item.hypothesis?.fixed),
  ];
}

/** The hypotheses of a closed theorem statement: the antecedents under its quantifier prefix. */
function statementHypotheses(statement: Formula): Formula[] {
  let formula = statement;
  while (formula.tag === "forall") formula = formula.body;
  const result: Formula[] = [];
  while (formula.tag === "imp") {
    result.push(formula.left);
    formula = formula.right;
  }
  return result;
}

function selectRing(scope: SurfaceScope, operands: readonly Term[], line: number): RingNotation {
  const rings = scope.rings ?? [];
  if (rings.length === 1) return rings[0]!;
  const facts = scope.localFormulas?.() ?? [];
  const inRing = (term: Term, ring: RingNotation): boolean => {
    if (termEquals(term, ring.zero) || termEquals(term, ring.one) || ringNumeralValue(term, ring) !== undefined) return true;
    if (term.tag === "app" && ((term.fn === ring.call1 && termEquals(term.args[0]!, ring.neg)) ||
        (term.fn === ring.call2 && (termEquals(term.args[0]!, ring.add) || termEquals(term.args[0]!, ring.mul))))) return true;
    if (term.tag === "app" && term.fn.split(".").at(-1) === "apply" && term.args.length === 2 &&
        facts.some(fact => fact.tag === "pred" &&
          ((fact.pred.endsWith(".IsRingHom") && fact.args.length === 13 && termEquals(fact.args[7]!, ring.carrier)) ||
           (fact.pred.endsWith(".FunctionBetween") && fact.args.length === 3 && termEquals(fact.args[2]!, ring.carrier))) &&
          termEquals(fact.args[0]!, term.args[0]!))) return true;
    return facts.some(fact => fact.tag === "pred" && fact.pred === "in" &&
      termEquals(fact.args[0]!, term) && termEquals(fact.args[1]!, ring.carrier));
  };
  const candidates = rings.filter(ring => operands.every(term => naturalValue(term) !== undefined || inRing(term, ring)));
  if (candidates.length === 1) return candidates[0]!;
  throw new SurfaceError(line, `ambiguous ring notation; use ${rings.map(r => `${r.name}[...]`).join(" or ")} to select operations`);
}


/** A declared function whose short name is within two edits of a misspelt one. */
function nearestFunctionName(kernel: Kernel, written: string): string | undefined {
  return nearestName(kernel.functions.keys(), written);
}

/** The declared name within edit distance two of a misspelt one, by its last segment. */
function nearestName(names: Iterable<string>, written_: string): string | undefined {
  const target = written_.split(".").at(-1)!;
  const distance = (a: string, b: string): number => {
    if (Math.abs(a.length - b.length) > 2) return 3;
    let previous = Array.from({ length: b.length + 1 }, (_, i) => i);
    for (let i = 1; i <= a.length; i++) {
      const current = [i];
      for (let j = 1; j <= b.length; j++) {
        current[j] = Math.min(previous[j]! + 1, current[j - 1]! + 1, previous[j - 1]! + (a[i - 1] === b[j - 1] ? 0 : 1));
      }
      previous = current;
    }
    return previous[b.length]!;
  };
  // A misspelling is within edit distance two of the last segment; a wrong
  // choice of words, `mul.right_one` for `mul_one`, is a declared name all
  // of whose words occur in what was written.
  const words = (name: string): string[] => name.split(/[._]/u).filter(Boolean);
  const writtenWords = words(written_);
  const written = new Set(writtenWords);
  let best: { name: string; score: number } | undefined;
  for (const name of names) {
    const short = name.split(".").at(-1)!;
    const edits = distance(short, target);
    const own = words(short);
    // Among names made of the written words, one that keeps their order
    // (`mul_one` for `mul.right_one`, not `one_mul`) is the likelier.
    const ordered = own.map(word => writtenWords.indexOf(word)).every((position, index, all) => position >= 0 && (index === 0 || position > all[index - 1]!));
    const covered = own.length >= 2 && own.every(word => written.has(word)) ? (ordered ? 2.5 : 3) - own.length / 10 : 9;
    const score = Math.min(edits > 0 && edits <= 2 ? edits : 9, covered);
    if (score < 9 && (!best || score < best.score)) best = { name: short, score };
  }
  return best?.name;
}

/** The sorts an expression annotation names: (2:R), (0:N), (-1:Z), (1:Q), and their full and glyph spellings. */
const ANNOTATION_TYPE_NAMES: Readonly<Record<string, string>> = Object.freeze({
  R: "Real", Real: "Real", "ℝ": "Real",
  N: "Nat", Nat: "Nat", "ℕ": "Nat",
  Z: "Integer", Integer: "Integer", "ℤ": "Integer",
  Q: "Rational", Rational: "Rational", "ℚ": "Rational",
});

/** The one-letter annotation label of a sort, Z for Integer, or its short name when it has none. */
function annotationLabel(type: string): string {
  const short = type.split(".").at(-1)!;
  return Object.entries(ANNOTATION_TYPE_NAMES).find(([label, name]) => name === short && label.length === 1)?.[0] ?? short;
}

function parseTerm(text: string, kernel: Kernel, variables: ReadonlySet<string>, line: number, scope: SurfaceScope): Term {
  // The index of a big operator is a natural number in its body: its sort
  // and the fact Nat(k) are in scope while the body is read.
  const boundTypes = new Map(scope.binderTypes ?? []);
  const boundFacts: Formula[] = [];
  const outerFormulas = scope.localFormulas;
  scope = { ...scope, binderTypes: boundTypes, localFormulas: () => [...(outerFormulas?.() ?? []), ...boundFacts] };
  const baseGroups = visibleInfixNotationGroups(kernel, scope, line, "function");
  const basePrefixes = visibleInfixNotationGroups(kernel, scope, line, "function", "prefix");
  const postfixGroups = visibleInfixNotationGroups(kernel, scope, line, "function", "postfix");
  const constantGroups = visibleInfixNotationGroups(kernel, scope, line, "function", "constant");
  const aliasGroups = visibleInfixNotationGroups(kernel, scope, line, "function", "alias");
  const notationGroups = scope.rings?.length ? new Map(baseGroups) : baseGroups;
  const prefixGroups = scope.rings?.length ? new Map(basePrefixes) : basePrefixes;
  if (scope.rings?.length) {
    for (const [token, precedence] of [["+", 65], ["-", 65], ["*", 70]] as const)
      (notationGroups as Map<string, readonly SurfaceNotationRecord[]>).set(token, [{ token, precedence, associativity: "left", kind: "function", reversed: false, target: "$ring" }]);
    (prefixGroups as Map<string, readonly SurfaceNotationRecord[]>).set("-", [{ token: "-", precedence: 80, fixity: "prefix", associativity: "none", kind: "function", reversed: false, target: "$ring" }]);
  }
  const powerTarget = "Grace.Cumulus.Algebra.Group.Power.monoidPow";
  if (scope.rings?.length && kernel.functions.get(powerTarget) === 4)
    (notationGroups as Map<string, readonly SurfaceNotationRecord[]>).set("^", [{ token: "^", precedence: 80, associativity: "right", kind: "function", reversed: false, target: "$ringPower" }]);
  // Exponents retain natural arithmetic, even inside a selected ring.
  let exponentDepth = 0;
  const binderGroups = visibleInfixNotationGroups(kernel, scope, line, "function", "binder");
  // Variables bound by a big operator inside this term.
  const boundVariables = new Set<string>();
  // Word operators are ordinary identifier tokens; only punctuation, and a
  // modifier letter such as ᶜ, is declared to the tokenizer.
  const tokens = tokenize(text, line, [...new Set([...notationGroups.keys(), ...prefixGroups.keys(), ...postfixGroups.keys(),
    ...constantGroups.keys(), ...binderGroups.keys(), ...(binderGroups.size ? ["<", "≤"] : [])])]
    .filter(token => !/^[\p{L}_]/u.test(token) || /^\p{Lm}+$/u.test(token)));
  // An indexed postfix form, f⁽ᵏ⁾, is keyed by its opening half.
  const indexedPostfix = new Map([...postfixGroups].filter(([token]) => token.includes("_"))
    .map(([token, records]) => [token.split("_")[0]!, records] as const));
  const coercions = [...visibleInfixNotationGroups(kernel, scope, line, "function", "coercion").values()].flat();
  // A term of a sort a coercion reads into `type`, wrapped; a numeral or a
  // term already of that sort is left alone.
  const coerced = (term: Term, types: ReadonlySet<string>, type: string): Term | undefined => {
    if (naturalValue(term) !== undefined || types.has(type)) return undefined;
    const coercion = coercions.find(item => item.resultType === type && item.operandType !== undefined && types.has(item.operandType));
    return coercion ? app(coercion.target, term) : undefined;
  };
  // Exact declared names win over suffix sugar. Thus the established constant
  // `ε₀` remains a constant, while an undeclared `uₙ` means `u[n]`.
  for (let index = tokens.length - 4; index >= 0; index -= 1) {
    const original = tokens[index]?.subscriptOriginal;
    if (!original || tokens[index + 1]?.text !== "[" || tokens[index + 3]?.text !== "]") continue;
    const raw = surfaceSymbol(original);
    const declared = variables.has(original) || Boolean(resolveOptional(raw, scope,
      candidate => kernel.functions.get(candidate) === 0));
    if (declared) tokens.splice(index, 4, { text: original, offset: tokens[index]!.offset });
  }
  let cursor = 0;
  const peek = () => tokens[cursor]?.text;
  const take = (expected?: string): Token => {
    const token = tokens[cursor];
    if (!token || (expected !== undefined && token.text !== expected)) {
      throw new SurfaceError(line, expected ? `expected ${expected}` : "unexpected end of term");
    }
    cursor += 1;
    return token;
  };
  // The sort an annotation names after the group opening at the cursor,
  // (-1:Z) or (x - 1 : R), read ahead of the group so that it reaches the
  // notation inside; a label naming no sort, (1 : G), is left to the group.
  const annotationAhead = (): string | undefined => {
    let depth = 0;
    for (let index = cursor; index < tokens.length; index += 1) {
      const item = tokens[index]!.text;
      if (item === "(" || item === "[" || item === "{" || item === "⟦") depth += 1;
      else if (item === ")" || item === "]" || item === "}" || item === "⟧") {
        if (depth === 0) return undefined;
        depth -= 1;
      } else if (item === "," && depth === 0) return undefined;
      else if (item === ":" && depth === 0) {
        const typeName = ANNOTATION_TYPE_NAMES[tokens[index + 1]?.text ?? ""];
        return typeName ? resolveOptional(typeName, scope, candidate => kernel.predicates.get(candidate) === 1) : undefined;
      }
    }
    return undefined;
  };
  const numeralFor = (term: Term, type: string): Term | undefined => {
    return typedNumeral(kernel, scope, line, term, type);
  };
  // The sort the position of a term fixes for it, when one does: the
  // parameter an argument fills, the other operand of an infix, or an
  // annotation around it. It decides a numeral under an overloaded prefix
  // that the operand alone leaves open, integerPow(-1, k), among the
  // typed declarations the operand fits.
  const expectedAmong = (expected: string | undefined, items: readonly SurfaceNotationRecord[]): SurfaceNotationRecord | undefined => {
    if (!expected) return undefined;
    const matching = items.filter(item => notationOperandTypes(item).every(type => type === expected));
    return matching.length === 1 ? matching[0] : undefined;
  };
  // The sorts of a term for an ambiguity message, short, deduplicated, and in declaration order.
  const sortList = (items: readonly SurfaceNotationRecord[]): string[] =>
    [...new Set(items.map(item => item.operandType ? item.operandType.split(".").at(-1)! : "untyped"))];
  const primary = (expected?: string): Term => {
    const finiteSet = (elements: readonly Term[]): Term => {
      const functionName = (name: string, arity: number): string =>
        resolveOptional(name, scope, candidate => kernel.functions.get(candidate) === arity) ?? name;
      const empty = functionName("empty", 0);
      const singleton = functionName("singleton", 1);
      const pair = functionName("pair", 2);
      const union2 = functionName("union2", 2);
      if (elements.length === 0) return app(empty);
      if (elements.length === 1) return app(singleton, elements[0]!);
      let result = app(pair, elements.at(-2)!, elements.at(-1)!);
      for (let index = elements.length - 3; index >= 0; index -= 1) {
        result = app(union2, app(singleton, elements[index]!), result);
      }
      return result;
    };
    const binderCandidates = binderGroups.get(peek() ?? "");
    if (binderCandidates?.length) {
      const notation = binderCandidates[0]!;
      take(notation.token);
      const index = take();
      if (!SIMPLE_IDENTIFIER.test(index.text) || variables.has(index.text) || boundVariables.has(index.text)) {
        throw new SurfaceError(line, `${notation.token} binds a fresh variable, as in ${notation.token} k < n, uₖ`);
      }
      const comparison = take();
      if (comparison.text !== "<" && comparison.text !== "≤") throw new SurfaceError(line, `expected < or ≤ after ${notation.token} ${index.text}`);
      let bound = expression(0);
      // An inclusive bound, ∑ k ≤ n, is the sum below n + 1.
      if (comparison.text === "≤") {
        const natural = baseGroups.get("+")?.find(item => item.operandType !== undefined && shortName(item.operandType) === "Nat" &&
          !item.leftOperandType && !item.rightOperandType)?.target ??
          resolveOptional("add", scope, candidate => kernel.functions.get(candidate) === 2);
        if (!natural) throw new SurfaceError(line, `${notation.token} ${index.text} ≤ … needs natural addition in scope`);
        bound = app(natural, bound, nat("1"));
        notationResultTypes.set(bound, "Nat");
      }
      take(",");
      boundVariables.add(index.text);
      boundTypes.set(index.text, { name: index.text, type: "Nat" });
      boundFacts.push(pred("Nat", v(index.text)));
      let body: Term;
      // The body extends over a product, so ∑ k ≤ n, uₖ * vₖ + w is the sum
      // plus w; a sum used as a factor is parenthesized.
      try { body = expression(61); } finally {
        boundVariables.delete(index.text);
        boundTypes.delete(index.text);
        boundFacts.pop();
      }
      let sequence = body.tag === "app" && body.args.length === 2 && body.fn.split(".").at(-1) === "apply" &&
        body.args[1]!.tag === "var" && body.args[1]!.name === index.text &&
        !freeTermVariables(body.args[0]!).has(index.text) ? body.args[0]! : undefined;
      // A body written out, f⁽ᵏ⁾(A) * (B - A) ^ k / k!, is the value of a
      // graph declared as a sequence, matched with its parameters as
      // pattern variables and its own index at the bound variable.
      if (!sequence) {
        for (const candidates of visibleInfixNotationGroups(kernel, scope, line, "function", "sequence").values()) {
          for (const item of candidates) {
            const bindings = new Map<string, Term>([[item.index!, v(index.text)]]);
            if (!matchImplicitTerm(item.template!, body, new Set([...item.parameters!, item.index!]), bindings)) continue;
            const arguments_ = item.parameters!.map(name => bindings.get(name));
            if (arguments_.some(argument => argument === undefined || freeTermVariables(argument).has(index.text))) continue;
            sequence = app(item.target, ...arguments_.map(argument => argument!));
            break;
          }
          if (sequence) break;
        }
      }
      if (!sequence) throw new SurfaceError(line,
        `the body of ${notation.token} ${index.text} ${comparison.text} …, … must apply a sequence to ${index.text}, as in u(${index.text}), or be the value of a graph declared as a sequence`);
      return app(notation.target, sequence, bound);
    }
    // A constant a hypothesis supplies, such as ⊥ under BoundedLattice(P).
    const constantCandidates = constantGroups.get(peek() ?? "");
    if (constantCandidates?.length) {
      take(constantCandidates[0]!.token);
      return selectHypothesisOperation(kernel, scope, constantCandidates, [], line)!.operation;
    }
    const prefixCandidates = (exponentDepth ? basePrefixes : prefixGroups).get(peek() ?? "");
    if (prefixCandidates?.length) {
      const shape = prefixCandidates[0]!;
      take(shape.token);
      // A prefix keeps the sort of its operand, so the operand sits in the
      // same position as the whole: integerPow(-1, k) reads -1 as an integer.
      const operand = expression(shape.precedence, expected);
      if (shape.target === "$ring") {
        const ring = selectRing(scope, [operand], line);
        return app(ring.call1, ring.neg, ringNumeral(kernel, scope, operand, ring, line));
      }
      const operandTypes = termTypeNames(kernel, operand, scope);
      const exactTyped = prefixCandidates.filter(item => item.operandType && operandTypes.has(item.operandType));
      // A unary operation a hypothesis supplies, such as -x under Ring(R),
      // unless the operand's sort names a typed declaration.
      const hypothesisPrefix = prefixCandidates.filter(item => item.hypothesis);
      if (hypothesisPrefix.length && exactTyped.length !== 1) {
        const operation = selectHypothesisOperation(kernel, scope, hypothesisPrefix, [operand], line,
          hypothesisPrefix.length < prefixCandidates.length);
        if (operation) return app(operation.notation.target, operation.operation, operand);
      }
      const plainPrefix = prefixCandidates.filter(item => !item.hypothesis);
      const typed = plainPrefix.length > 1 && exactTyped.length === 0 ? plainPrefix.filter(item => item.operandType &&
        (termHasType(kernel, operand, item.operandType, scope) || numeralFor(operand, item.operandType) !== undefined)) : [];
      const fallback = plainPrefix.filter(item => !item.operandType);
      // A numeral fits every typed declaration; the sort of its position
      // decides among them, and with none it is left to an annotation.
      const selected = plainPrefix.length === 1 ? plainPrefix[0]
        : exactTyped.length === 1 ? exactTyped[0]
        : exactTyped.length === 0 && typed.length === 1 ? typed[0]
        : exactTyped.length === 0 && typed.length > 1 ? expectedAmong(expected, typed)
        : exactTyped.length === 0 && typed.length === 0 && fallback.length === 1 ? fallback[0]
        : undefined;
      if (!selected) {
        const actual = [...operandTypes].map(item => item.split(".").at(-1)!).join("|") || "unknown";
        const value = naturalValue(operand);
        const orList = (items: readonly string[]): string =>
          items.length < 3 ? items.join(" or ") : `${items.slice(0, -1).join(", ")}, or ${items.at(-1)}`;
        if (value !== undefined && typed.length > 1) throw new SurfaceError(line,
          `cannot resolve notation ${shape.token} on the numeral ${value}: it could be the ${orList(sortList(typed))} one; ` +
          `annotate it, as in ${orList(sortList(typed).map(sort => `(${shape.token}${value}:${annotationLabel(sort)})`))}, ` +
          `or place it where its sort is fixed, as an argument of a function with a parameter of that sort`);
        throw new SurfaceError(line,
          `cannot resolve notation ${shape.token} for operand type ${actual}; candidates are ${sortList(prefixCandidates).join(", ")}`);
      }
      const result = app(selected.target, ...(selected.leadingArguments ?? []),
        selected.operandType ? numeralFor(operand, selected.operandType) ?? operand : operand);
      if (selected.operandType) notationResultTypes.set(result, selected.operandType);
      return result;
    }
    if (peek() === "⋃") {
      take("⋃");
      const symbol = resolveExisting("union", scope, candidate => kernel.functions.get(candidate) === 1, line, "union function");
      return app(symbol, atom());
    }
    if (peek() === "∫") {
      take("∫");
      take("[");
      const lower = expression(0);
      take(",");
      const upper = expression(0);
      take("]");
      const integrand = expression(90);
      const symbol = resolveExisting("riemannIntegral", scope,
        candidate => kernel.functions.get(candidate) === 3, line, "Riemann integral function");
      const result = app(symbol, integrand, lower, upper);
      // The checked choice definition selects its value from the real carrier.
      const real = resolveExisting("Real", scope,
        candidate => kernel.predicates.get(candidate) === 1, line, "real carrier");
      notationResultTypes.set(result, real);
      return result;
    }
    if (peek() === "⟦") {
      take("⟦");
      const representative = expression(0);
      take("⟧");
      take("[");
      const carrier = expression(0);
      take(",");
      const relation = expression(0);
      take("]");
      const symbol = resolveExisting("equivalenceClass", scope,
        candidate => kernel.functions.get(candidate) === 3, line, "equivalence-class function");
      return app(symbol, carrier, relation, representative);
    }
    if (peek() === "[") {
      take("[");
      const elements: Term[] = [];
      if (peek() !== "]") {
        for (;;) {
          elements.push(expression(0));
          if (peek() !== ",") break;
          take(",");
        }
      }
      take("]");
      const carrier = finiteSet(elements);
      const nil = resolveExisting("Grace.Core.Data.List.nil", scope,
        candidate => kernel.functions.get(candidate) === 0, line, "List.nil constructor");
      const cons = resolveExisting("Grace.Core.Data.List.cons", scope,
        candidate => kernel.functions.get(candidate) === 2, line, "List.cons constructor");
      const result = elements.reduceRight<Term>((tail, element) => app(cons, element, tail), app(nil));
      listLiteralCarriers.set(result, carrier);
      return result;
    }
    if (peek() === "{") {
      take("{");
      const elements: Term[] = [];
      if (peek() !== "}") {
        for (;;) {
          elements.push(expression(0));
          if (peek() !== ",") break;
          take(",");
        }
      }
      take("}");
      return finiteSet(elements);
    }
    if (peek() === "(") {
      take("(");
      // An explicit numeral type takes precedence over the lexical ring scope.
      // Delay its interpretation until the annotation below is resolved.
      // An annotation on the group, (-1:Z), fixes the sort of what it
      // encloses before that is read, so the prefix inside resolves to it.
      const annotated = annotationAhead();
      const first = /^\d+$/.test(peek() ?? "") && tokens[cursor + 1]?.text === ":"
        ? nat(take().text) : expression(0, annotated ?? expected);
      if (peek() === ",") {
        take(",");
        const second = expression(0);
        take(")");
        const symbol = resolveOptional("orderedPair", scope,
          candidate => kernel.functions.get(candidate) === 2) ?? "orderedPair";
        return app(symbol, first, second);
      }
      if (peek() === ":") {
        take(":");
        const label = take().text;
        const typeName = ANNOTATION_TYPE_NAMES[label];
        if (!typeName) {
          // (1 : G) and (0 : G) under a hypothesis giving the structure
          // variable G a carrier are the structure's unit and zero.
          const constant = structureConstant(kernel, scope, first, label, variables, line);
          if (constant) {
            take(")");
            return constant;
          }
          throw new SurfaceError(line, `unknown expression type annotation ${label}`);
        }
        const type = resolveExisting(typeName, scope,
          candidate => kernel.predicates.get(candidate) === 1, line, "unary soft type for annotation");
        take(")");
        const known = [...termTypeNames(kernel, first, scope)].filter(item => item !== "Set" &&
          !(naturalValue(first) !== undefined && item === "Nat"));
        if (known.length && !known.includes(type)) throw new SurfaceError(line,
          `expression annotated ${label} already has type ${known.map(item => item.split(".").at(-1)).join(" or ")}`);
        const numeral = numeralFor(first, type);
        if (naturalValue(first) !== undefined && typeName !== "Nat" && !numeral) throw new SurfaceError(line,
          `no ${typeName} numeral notation for ${naturalValue(first)}`);
        const result = numeral ?? first;
        // AST nodes are interned process-wide. The annotation belongs to this
        // occurrence in this scope, not to every later occurrence of the same
        // numeral or variable in any module or kernel. Numerals get a private
        // copy; everything else is recorded against the current scope only.
        if (naturalValue(result) !== undefined) {
          const annotated = Object.freeze({ ...result });
          notationResultTypes.set(annotated, type);
          return annotated;
        }
        annotationsFor(kernel).set(termCanonical(result), type);
        return result;
      }
      take(")");
      return first;
    }
    const token = take();
    if (token.text === "∅") {
      const symbol = resolveOptional("empty", scope, candidate => kernel.functions.get(candidate) === 0) ?? "empty";
      return app(symbol);
    }
    if (/^\d+$/.test(token.text)) {
      return !exponentDepth && scope.rings?.length === 1 && !scope.rings[0]!.plainLiterals
        ? ringNumeral(kernel, scope, nat(token.text), scope.rings[0]!, line) : nat(token.text);
    }
    const qualifier = (scope.ringAliases ?? scope.rings)?.find(ring => ring.name === token.text) ??
      (peek() === "[" && SIMPLE_IDENTIFIER.test(token.text) ? bundledRingScope(kernel, scope, token.text, variables) : undefined);
    if (qualifier && peek() === "[") {
      const start = take("[").offset + 1;
      let depth = 1;
      while (cursor < tokens.length && depth) {
        const item = tokens[cursor]!;
        if (item.text === "[") depth++;
        if (item.text === "]") depth--;
        if (!depth) return parseTerm(text.slice(start, take("]").offset), kernel, variables, line, { ...scope, ringAliases: scope.ringAliases ?? scope.rings, rings: [qualifier] });
        cursor++;
      }
      throw new SurfaceError(line, `unclosed ring expression ${qualifier.name}[...]`);
    }
    // A scoped ring name also names its carrier set, so hypotheses can say
    // `p ∈ P`. This expands immediately and introduces no kernel symbol.
    if (qualifier) return qualifier.carrier;
    if (!QUALIFIED_IDENTIFIER.test(token.text)) throw new SurfaceError(line, `unexpected token ${token.text}`);
    // `C.obj` on a variable in scope is the projection of a structure;
    // `F.src.obj` chains projections, and `C.dom(f)` applies the value.
    const access = token.text.includes(".") ? token.text.split(".") : undefined;
    // A constant may be the receiver too: `integerRing.carrier` for a declared
    // `integerRing : Set := Ring.mk(…)`, when the dotted name is not itself a
    // declared symbol and every later segment is a field of a visible structure.
    const constantReceiver = access && !variables.has(access[0]!) && !boundVariables.has(access[0]!) &&
      !resolveOptional(surfaceSymbol(token.text), scope, candidate => kernel.functions.has(candidate) || kernel.predicates.has(candidate)) &&
      access.slice(1).every(field => visibleStructures(kernel, scope).some(item => structureHasMember(item, field)))
      ? resolveOptional(access[0]!, scope, candidate => kernel.functions.get(candidate) === 0) : undefined;
    if (access && (variables.has(access[0]!) || boundVariables.has(access[0]!) || constantReceiver)) {
      let receiver: Term = constantReceiver ? app(constantReceiver) : v(access[0]!);
      for (const field of access.slice(1)) {
        const projection = structureProjection(kernel, scope, field, receiver, line);
        if (!projection) throw new SurfaceError(line, `${field} is not a field of any structure in scope, so ${token.text} has no meaning`);
        receiver = projection;
      }
      return receiver;
    }
    const rawSymbol = surfaceSymbol(token.text);
    const environment = surfaceEnvironments.get(kernel);
    const className = environment
      ? resolveOptional(rawSymbol, scope, candidate => environment.classes.has(candidate))
      : undefined;
    if (className) {
      throw new SurfaceError(line, `class ${token.text} is not a Set; use class membership or bounded realization`);
    }
    const overrides: ImplicitOverride[] = [];
    if (peek() === "{") {
      take("{");
      if (peek() !== "}") {
        for (;;) {
          if (tokens[cursor + 1]?.text === ":=") {
            const name = take().text;
            if (!SIMPLE_IDENTIFIER.test(name)) throw new SurfaceError(line, `malformed implicit argument name ${name}`);
            take(":=");
            overrides.push({ name, value: expression(0) });
          } else overrides.push({ value: expression(0) });
          if (peek() !== ",") break;
          take(",");
        }
      }
      take("}");
    }
    if (peek() === "(") {
      take("(");
      const args: Term[] = [];
      const argumentSources: string[] = [];
      // The sort of the parameter each argument fills, from the signature
      // of the declared function the name reaches, by position among all
      // the parameters or among the explicit ones; the two must agree.
      // A hint only: an ambiguous name is resolved by the application itself.
      const declared = ((): string | undefined => {
        if (variables.has(token.text) || boundVariables.has(token.text)) return undefined;
        try {
          return resolveOptional(rawSymbol, scope, candidate => kernel.functions.has(candidate) || candidate === scope.pendingFunction);
        } catch (error) {
          // Ambiguity is reported where the name is applied, with its arity.
          if (error instanceof AmbiguousNameError ||
              (error instanceof SurfaceError && error.message.includes("ambiguous name"))) return undefined;
          throw error;
        }
      })();
      const parameters = declared ? surfaceEnvironments.get(kernel)?.signatures.get(declared)?.parameters : undefined;
      const parameterSort = (index: number): string | undefined => {
        if (!parameters) return undefined;
        const sorts = new Set([parameters[index], parameters.filter(item => !item.implicit)[index]]
          .map(item => item?.type).filter(type => type !== undefined && type !== "Set" && type !== "Class"));
        return sorts.size === 1 ? [...sorts][0] : undefined;
      };
      if (peek() !== ")") {
        for (;;) {
          const start = tokens[cursor]!.offset;
          args.push(expression(0, parameterSort(args.length)));
          argumentSources.push(text.slice(start, tokens[cursor]?.offset ?? text.length).trim());
          if (peek() !== ",") break;
          take(",");
        }
      }
      take(")");
      if (variables.has(token.text) || boundVariables.has(token.text)) {
        // A variable applied to two arguments is a binary operation graph,
        // op(a, b) = call2(op, a, b); applied to one argument it is function
        // application f(x), which is also how a unary operation applies.
        if (overrides.length || args.length === 0 || args.length > 2) throw new SurfaceError(line,
          `set-theoretic function ${token.text} expects one argument; use ${token.text}(x)`);
        if (args.length === 2) {
          const call2 = resolveOptional("call2", scope, candidate => kernel.functions.get(candidate) === 3);
          if (!call2) throw new SurfaceError(line,
            `set-theoretic function ${token.text} expects one argument; use ${token.text}(x)`);
          return app(call2, v(token.text), args[0]!, args[1]!);
        }
        const applySymbol = resolveExisting("apply", scope,
          candidate => kernel.functions.get(candidate) === 2, line, "function application");
        return functorApplication(kernel, scope, v(token.text), args[0]!, line) ?? app(applySymbol, v(token.text), args[0]!);
      }
      const environment = surfaceEnvironments.get(kernel);
      // A function form a hypothesis in scope supplies, ker(f) under
      // f : R →+* S; with no supplying hypothesis a declared function of
      // the name is read instead.
      if (!overrides.length) {
        const supplied = functionNotationApplication(kernel, scope, rawSymbol, args, line);
        if (supplied) return supplied;
      }
      // An alias stands for its function unless the name is a declared function itself.
      const aliased = aliasGroups.get(rawSymbol)?.[0]?.target;
      if (aliased !== undefined && !kernel.functions.has(rawSymbol) && kernel.functions.get(aliased) === args.length) {
        return app(aliased, ...args);
      }
      // A field name applied to one argument, `obj(C)`, is the projection of
      // the structure the receiver belongs to unless a declared function of
      // that name answers first; `Category.obj(C)` names the projection.
      if (args.length === 1 && !overrides.length && !rawSymbol.includes(".") &&
          visibleStructures(kernel, scope).some(item => item.structure!.fields.includes(rawSymbol))) {
        const plain = resolveOptional(rawSymbol, scope, candidate => kernel.functions.get(candidate) === 1 &&
          !projectionOf(kernel, candidate));
        if (!plain) {
          const projection = structureProjection(kernel, scope, rawSymbol, args[0]!, line);
          if (projection) return projection;
        }
      }
      const symbol = resolveOptional(rawSymbol, scope, candidate => {
        if (!(kernel.functions.has(candidate) || candidate === scope.pendingFunction)) return false;
        const signature = environment?.signatures.get(candidate);
        const dropped = scope.sectionDefinitions?.get(candidate)?.length ?? 0;
        return !signature || args.length === signature.parameters.length ||
          args.length === signature.parameters.filter(item => !item.implicit).length ||
          (dropped > 0 && args.length + dropped === signature.parameters.length);
      }) ?? rawSymbol;
      if (!kernel.functions.has(symbol) && !overrides.length && scope.rings?.length) {
        const record = scopedNotationFor(kernel, scope, line, "function", rawSymbol, args.length);
        if (record) {
          const target = resolveOptional(rawSymbol, scope, name => kernel.functions.get(name) === record.expansion!.length);
          if (!target || target === record.target) {
            return app(record.target, ...expandScopedArguments(record, argumentSources, index => args[index]!, scope, line, token.text));
          }
        }
      }
      if ((args.length === 1 || args.length === 2) && !overrides.length && !kernel.functions.has(symbol)) {
        const constant = resolveOptional(rawSymbol, scope,
          candidate => kernel.functions.get(candidate) === 0);
        if (constant && args.length === 2) {
          // A constant operation graph applied to two arguments: op(a, b) = call2(op, a, b).
          const call2 = resolveOptional("call2", scope, candidate => kernel.functions.get(candidate) === 3);
          if (call2) return app(call2, app(constant), args[0]!, args[1]!);
        } else if (constant) {
          const applySymbol = resolveExisting("apply", scope,
            candidate => kernel.functions.get(candidate) === 2, line, "function application");
          return app(applySymbol, app(constant), args[0]!);
        }
      }
      if (!kernel.functions.has(symbol) && !kernel.predicates.has(symbol) && symbol !== scope.pendingFunction &&
        !resolveOptional(rawSymbol, scope, candidate => kernel.predicates.has(candidate))) {
        const forms = visibleInfixNotationGroups(kernel, scope, line, "function", "function").get(rawSymbol);
        if (forms?.length) {
          const shapes = [...new Set(forms.map(item => shortName(item.hypothesis!.predicate)))].join(", ");
          throw new SurfaceError(line, `no hypothesis in scope supplies ${token.text}(${forms[0]!.hypothesis!.parameters!.join(", ")}); it needs one of ${shapes}`);
        }
        const suggestion = nearestFunctionName(kernel, rawSymbol);
        throw new SurfaceError(line, `unknown function ${token.text}${suggestion ? `; did you mean ${suggestion}?` : ""}`);
      }
      const elaborated = elaborateApplicationArguments(kernel, symbol, args, overrides, variables, scope, line);
      const signature = environment?.signatures.get(symbol);
      const typedArguments = signature && signature.parameters.length === elaborated.length
        ? elaborated.map((argument, index) => {
          const parameterType = signature.parameters[index]!.type;
          return parameterType === "Set" || parameterType === "Class"
            ? argument
            : numeralFor(argument, parameterType) ?? argument;
        })
        : elaborated;
      return app(symbol, ...typedArguments);
    }
    if (overrides.length) throw new SurfaceError(line, `implicit arguments for ${token.text} must be followed by an explicit argument list`);
    if (variables.has(token.text) || boundVariables.has(token.text)) return v(token.text);
    const symbol = resolveOptional(rawSymbol, scope, candidate => kernel.functions.get(candidate) === 0 ||
      (scope.sectionDefinitions?.get(candidate)?.length ?? -1) === kernel.functions.get(candidate));
    if (symbol) return app(symbol, ...(scope.sectionDefinitions?.get(symbol) ?? []).map(name => v(name)));
    throw new SurfaceError(line, `unknown variable or constant ${token.text}`);
  };
  const atom = (expected?: string): Term => {
    let result = primary(expected);
    // The numerals and scoped expressions of a constructed ring an instance
    // supplies: polynomialRing(R, I)[2].
    if (peek() === "[" && result.tag === "app" && result.args.length > 0) {
      const ring = bundledRingScopeOfTerm(kernel, scope, result);
      if (ring) {
        take("[");
        const start = tokens[cursor]!.offset;
        let depth = 1;
        while (cursor < tokens.length) {
          const item = tokens[cursor]!;
          if (item.text === "[") depth++;
          if (item.text === "]") depth--;
          if (!depth) {
            result = parseTerm(text.slice(start, take("]").offset), kernel, variables, line,
              { ...scope, ringAliases: scope.ringAliases ?? scope.rings, rings: [ring] });
            break;
          }
          cursor++;
        }
        if (depth) throw new SurfaceError(line, `unclosed ring expression ${ring.name}[...]`);
      }
    }
    return applied(result);
  };
  // The application suffixes of a term, f(x), op(a, b), u[n], and M[i, j],
  // after an atom or after a postfix form such as f′ or f⁽ᵏ⁾.
  const applied = (base: Term): Term => {
    let result = base;
    while (peek() === "[" || peek() === "(") {
      if (peek() === "(") {
        take("(");
        const argument = expression(0);
        if (peek() === ",") {
          // A binary operation graph applied to two arguments: (expr)(a, b) = call2(expr, a, b).
          take(",");
          const second = expression(0);
          take(")");
          const call2 = resolveExisting("call2", scope,
            candidate => kernel.functions.get(candidate) === 3, line, "binary operation application");
          result = app(call2, result, argument, second);
          continue;
        }
        take(")");
        const symbol = resolveExisting("apply", scope,
          candidate => kernel.functions.get(candidate) === 2, line, "function application");
        result = functorApplication(kernel, scope, result, argument, line) ?? app(symbol, result, argument);
        continue;
      }
      take("[");
      const index = expression(0);
      let argument = index;
      if (peek() === ",") {
        take(",");
        const column = expression(0);
        const pairSymbol = resolveExisting("orderedPair", scope,
          candidate => kernel.functions.get(candidate) === 2, line, "ordered pair");
        argument = app(pairSymbol, index, column);
      }
      take("]");
      const symbol = resolveExisting("apply", scope,
        candidate => kernel.functions.get(candidate) === 2, line, "function application");
      result = app(symbol, result, argument);
    }
    return result;
  };
  const expression = (minimumPrecedence: number, expected?: string): Term => {
    let left = atom(expected);
    for (;;) {
      // An indexed postfix form, f⁽ᵏ⁾ for iteratedDerivative(f, k): the
      // index between the halves of the token is a term, typed by the
      // target's signature, and the form may be applied, f⁽ᵏ⁾(A).
      const indexedCandidates = indexedPostfix.get(peek() ?? "");
      if (indexedCandidates?.length && indexedCandidates[0]!.precedence >= minimumPrecedence) {
        const shape = indexedCandidates[0]!;
        const [open, close] = shape.token.split("_");
        take(open!);
        const index = expression(0);
        take(close!);
        const indexType = surfaceEnvironments.get(kernel)?.signatures.get(shape.target)?.parameters[1]?.type;
        left = app(shape.target, left, indexType && indexType !== "Set" && indexType !== "Class" ? numeralFor(index, indexType) ?? index : index);
        left = applied(left);
        continue;
      }
      const postfixCandidates = postfixGroups.get(peek() ?? "");
      if (postfixCandidates?.length && postfixCandidates[0]!.precedence >= minimumPrecedence) {
        const shape = postfixCandidates[0]!;
        take(shape.token);
        const operandTypes = termTypeNames(kernel, left, scope);
        const exactTyped = postfixCandidates.filter(item => item.operandType && operandTypes.has(item.operandType));
        // A unary operation a hypothesis supplies, such as a⁻¹ under
        // Group(G), unless the operand's sort names a typed declaration.
        const hypothesisPostfix = postfixCandidates.filter(item => item.hypothesis);
        if (hypothesisPostfix.length && exactTyped.length !== 1) {
          const operation = selectHypothesisOperation(kernel, scope, hypothesisPostfix, [left], line,
            hypothesisPostfix.length < postfixCandidates.length);
          if (operation) {
            left = applied(app(operation.notation.target, operation.operation, left));
            continue;
          }
        }
        const plainPostfix = postfixCandidates.filter(item => !item.hypothesis);
        const typed = plainPostfix.length > 1 && exactTyped.length === 0 ? plainPostfix.filter(item => item.operandType &&
          (termHasType(kernel, left, item.operandType, scope) || numeralFor(left, item.operandType) !== undefined)) : [];
        const fallback = plainPostfix.filter(item => !item.operandType);
        const selected = plainPostfix.length === 1 ? plainPostfix[0]
          : exactTyped.length === 1 ? exactTyped[0]
          : exactTyped.length === 0 && typed.length === 1 ? typed[0]
          : exactTyped.length === 0 && typed.length === 0 && fallback.length === 1 ? fallback[0]
          : undefined;
        if (!selected) {
          const actual = [...operandTypes].map(item => item.split(".").at(-1)!).join("|") || "unknown";
          throw new SurfaceError(line,
            `cannot resolve notation ${shape.token} for operand type ${actual}; candidates are ${postfixCandidates.map(item => item.operandType ?? "untyped").join(", ")}`);
        }
        left = app(selected.target, ...(selected.leadingArguments ?? []),
          selected.operandType ? numeralFor(left, selected.operandType) ?? left : left);
        if (selected.operandType) notationResultTypes.set(left, selected.operandType);
        left = applied(left);
        continue;
      }
      const candidates = (exponentDepth ? baseGroups : notationGroups).get(peek() ?? "");
      const shape = candidates?.[0];
      if (!candidates || !shape || shape.precedence < minimumPrecedence) break;
      take(shape.token);
      if (shape.target === "$ringPower") {
        const ring = selectRing(scope, [left], line);
        exponentDepth++;
        const exponent = expression(shape.precedence);
        exponentDepth--;
        left = app(powerTarget, ring.mul, ring.one, ringNumeral(kernel, scope, left, ring, line), exponent);
        continue;
      }
      const leftTypes = termTypeNames(kernel, left, scope);
      // The sort of the left operand, when the token has a declaration for
      // it, is the sort of the right operand's position: X * -1 with X real
      // reads -1 as a real.
      const leftSorts = [...leftTypes].filter(type => candidates.some(item => notationOperandTypes(item)[1] === type));
      let right = expression(shape.associativity === "left" ? shape.precedence + 1 : shape.precedence,
        leftSorts.length === 1 ? leftSorts[0] : expected);
      if (shape.target === "$ring") {
        // Operands of natural-number type keep natural arithmetic inside a
        // selected ring, as exponents do: n + 1 is the next natural number.
        const natural = baseGroups.get(shape.token)?.find(item => item.operandType?.split(".").at(-1) === "Nat" &&
          !item.leftOperandType && !item.rightOperandType && leftTypes.has(item.operandType!) &&
          (termTypeNames(kernel, right, scope).has(item.operandType!) || naturalValue(right) !== undefined));
        if (natural && naturalValue(left) === undefined) {
          left = app(natural.target, left, right);
          notationResultTypes.set(left, natural.operandType!);
          continue;
        }
        const ring = selectRing(scope, [left, right], line);
        left = ringNumeral(kernel, scope, left, ring, line);
        right = ringNumeral(kernel, scope, right, ring, line);
        if (shape.token === "-") right = app(ring.call1, ring.neg, right);
        left = app(ring.call2, shape.token === "*" ? ring.mul : ring.add, left, right);
        continue;
      }
      const rightTypes = termTypeNames(kernel, right, scope);
      const exactTyped = candidates.filter(item => {
        const [leftType, rightType] = notationOperandTypes(item);
        return leftType && rightType && leftTypes.has(leftType) && rightTypes.has(rightType);
      });
      // Operands whose sorts name one typed declaration keep it, so that
      // n * m stays natural multiplication inside a group section, as does
      // a product with one operand of a typed sort and none in the carrier
      // of a supplying hypothesis; otherwise a hypothesis in scope supplies
      // the operation, and with none in scope the token falls back to its
      // typed declarations.
      // A form whose left operand is the structure itself, G ⧸ N for
      // quotientGroup(G, N), is read when the left operand is a structure of
      // a supplying hypothesis, and is otherwise out of the running.
      const structureCandidates = candidates.filter(item => item.hypothesis?.structureOperand);
      if (structureCandidates.length) {
        const structural = selectStructureOperation(kernel, scope, structureCandidates, left, line);
        if (structural) {
          left = app(structural.notation.target, left, right);
          continue;
        }
      }
      const hypothesisCandidates = candidates.filter(item => item.hypothesis && !item.hypothesis.structureOperand);
      const plainCandidates = candidates.filter(item => !item.hypothesis);
      const typedAlternative = hypothesisCandidates.length > 0 && plainCandidates.length > 0 && exactTyped.length !== 1 &&
        typedOperandsOutsideHypothesis(kernel, scope, hypothesisCandidates, plainCandidates, [left, right], line);
      if (hypothesisCandidates.length && exactTyped.length !== 1 && !typedAlternative) {
        const operation = selectHypothesisOperation(kernel, scope, hypothesisCandidates, [left, right], line,
          hypothesisCandidates.length < candidates.length - structureCandidates.length);
        if (operation) {
          left = app(operation.notation.target, operation.operation, left, right);
          continue;
        }
      }
      // With no supplying hypothesis the hypothesis declarations are out of
      // the running, and the token is resolved among its other declarations.
      const plain = candidates.filter(item => !item.hypothesis);
      // One operand of a declared sort and the other of a sort coerced to
      // the declaration's: n! * X is realNat(n!) * X.
      const coercible = plain.length > 1 && exactTyped.length === 0 ? plain.filter(item => {
        const [leftType, rightType] = notationOperandTypes(item);
        if (!leftType || !rightType) return false;
        const leftFits = leftTypes.has(leftType);
        const rightFits = rightTypes.has(rightType);
        return leftFits !== rightFits && (leftFits ? coerced(right, rightTypes, rightType) : coerced(left, leftTypes, leftType)) !== undefined;
      }) : [];
      const typed = plain.length > 1 && exactTyped.length === 0 && coercible.length !== 1 ? plain.filter(item => {
        const [leftType, rightType] = notationOperandTypes(item);
        return leftType && rightType &&
          (termHasType(kernel, left, leftType, scope) || numeralFor(left, leftType) !== undefined) &&
          (termHasType(kernel, right, rightType, scope) || numeralFor(right, rightType) !== undefined);
      }) : [];
      const fallback = plain.filter(item => !notationIsTyped(item));
      const selected = plain.length === 1 ? plain[0]
        : exactTyped.length === 1 ? exactTyped[0]
        : exactTyped.length === 0 && coercible.length === 1 ? coercible[0]
        : exactTyped.length === 0 && typed.length === 1 ? typed[0]
        : exactTyped.length === 0 && typed.length > 1 ? expectedAmong(expected, typed)
        : exactTyped.length === 0 && typed.length === 0 && fallback.length === 1 ? fallback[0]
        : undefined;
      if (!selected) {
        const display = (types: ReadonlySet<string>): string =>
          [...types].map(item => item.split(".").at(-1)!).join("|") || "?";
        const actual = leftTypes.size || rightTypes.size ? `${display(leftTypes)}, ${display(rightTypes)}` : "unknown";
        throw new SurfaceError(line,
          `cannot resolve notation ${shape.token} for operand types ${actual}; candidates are ${[...new Set(candidates.map(notationTypeLabel))].join("; ")}`);
      }
      const [leftType, rightType] = notationOperandTypes(selected);
      if (leftType) left = numeralFor(left, leftType) ?? coerced(left, leftTypes, leftType) ?? left;
      if (rightType) right = numeralFor(right, rightType) ?? coerced(right, rightTypes, rightType) ?? right;
      left = app(selected.target, ...(selected.leadingArguments ?? []), left, right);
      if (selected.operandType) notationResultTypes.set(left, selected.operandType);
    }
    return left;
  };
  const result = expression(0);
  if (cursor !== tokens.length) throw new SurfaceError(line, `unexpected token ${tokens[cursor]!.text}`);
  return result;
}

/** A doubled or tripled prime is that many primes: f″ is f′′, the second derivative. */
const PRIME_MULTIPLES: Readonly<Record<string, number>> = Object.freeze({ "″": 2, "‴": 3, "⁗": 4 });

function tokenize(text: string, line: number, operators: readonly string[] = []): Token[] {
  const result: Token[] = [];
  const longestOperators = [...operators].filter(item => !item.includes("_"))
    .sort((left, right) => right.length - left.length || left.localeCompare(right));
  // An indexed postfix token, ⁽_⁾, encloses an index written in superscript
  // digits, letters, and signs; the index is read as the term it spells.
  const indexed = operators.filter(item => item.includes("_")).map(item => item.split("_") as [string, string]);
  for (let offset = 0; offset < text.length;) {
    if (/\s/.test(text[offset]!)) { offset += 1; continue; }
    const source = text.slice(offset);
    const bracket = indexed.find(([open]) => source.startsWith(open));
    if (bracket) {
      const [open, close] = bracket;
      const end = source.indexOf(close, open.length);
      if (end < 0) throw new SurfaceError(line, `unclosed index after ${open}`);
      result.push({ text: open, offset });
      const inner = fromSuperscript(source.slice(open.length, end));
      for (const token of tokenize(inner, line, operators)) result.push({ ...token, offset: offset + open.length + token.offset });
      result.push({ text: close, offset: offset + end });
      offset += end + close.length;
      continue;
    }
    const primes = PRIME_MULTIPLES[source[0]!];
    if (primes && operators.includes("′")) {
      for (let count = 0; count < primes; count += 1) result.push({ text: "′", offset });
      offset += 1;
      continue;
    }
    const match = /^[\p{L}_][\p{L}\p{M}\p{N}_.]*|^\d+|^:=|^[∅⋃∫⟦⟧]|^[(),:{}\[\]]/u.exec(source);
    const operator = longestOperators.find(item => source.startsWith(item));
    if (operator && (!match || operator.length >= match[0].length || /^\p{Lm}/u.test(operator))) {
      result.push({ text: operator, offset });
      offset += operator.length;
      continue;
    }
    if (!match) throw new SurfaceError(line, `unexpected character ${JSON.stringify(text[offset])}`);
    // A modifier-letter operator such as ᶜ ends the identifier it follows.
    let identifier = match[0];
    for (const item of longestOperators) {
      if (!/^\p{Lm}/u.test(item)) continue;
      const at = identifier.indexOf(item);
      if (at > 0) identifier = identifier.slice(0, at);
    }
    const subscript = splitUnicodeSubscript(identifier);
    if (subscript) {
      result.push({ text: subscript.base, offset, subscriptOriginal: identifier });
      result.push({ text: "[", offset: offset + subscript.base.length });
      result.push({ text: subscript.index, offset: offset + subscript.base.length });
      result.push({ text: "]", offset: offset + identifier.length });
    } else result.push({ text: identifier, offset });
    offset += identifier.length;
  }
  return result;
}

const UNICODE_SUBSCRIPT_CHARACTERS = "₀₁₂₃₄₅₆₇₈₉ₐₑₕᵢⱼₖₗₘₙₚᵣₛₜₓ";
const UNICODE_SUBSCRIPT_VALUES = new Map([..."0123456789aehijklmnoprstx"].map((value, index) =>
  [UNICODE_SUBSCRIPT_CHARACTERS[index]!, value] as const));

/** Split the conventional suffix in `uₙ` or `a₁₂` into postfix indexing tokens. */
function splitUnicodeSubscript(identifier: string): { readonly base: string; readonly index: string } | undefined {
  let start = identifier.length;
  while (start > 0) {
    const character = identifier[start - 1]!;
    if (!UNICODE_SUBSCRIPT_VALUES.has(character)) break;
    start -= character.length;
  }
  if (start === identifier.length || start === 0) return undefined;
  const base = identifier.slice(0, start);
  const index = [...identifier.slice(start)].map(character => UNICODE_SUBSCRIPT_VALUES.get(character)!).join("");
  if (!/^\d+$|^[\p{L}_][\p{L}\p{M}\p{N}_]*$/u.test(index)) return undefined;
  return { base, index };
}

function splitTopLevel(text: string, separator: string): string[] {
  const result: string[] = [];
  let depth = 0;
  let start = 0;
  // The comma after a big-operator header, as in `∑ k < n, uₖ`, separates
  // the bound from the body, not two arguments.
  let binderCommas = 0;
  for (let index = 0; index < text.length; index += 1) {
    if (separator === ",") {
      const binderHeader = /^[∑∏⋃⋂]\s*[\p{L}_][\p{L}\p{M}\p{N}_]*\s*(?:<|≤)/u.exec(text.slice(index));
      if (binderHeader) { binderCommas += 1; index += binderHeader[0].length - 1; continue; }
    }
    if (text[index] === "(" || text[index] === "{" || text[index] === "[" || text[index] === "⟨") depth += 1;
    else if (text[index] === ")" || text[index] === "}" || text[index] === "]" || text[index] === "⟩") depth -= 1;
    else if (text[index] === separator && depth === 0) {
      if (binderCommas > 0) { binderCommas -= 1; continue; }
      result.push(text.slice(start, index).trim());
      start = index + 1;
    }
    if (depth < 0) return [text];
  }
  result.push(text.slice(start).trim());
  return result;
}
