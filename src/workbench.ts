// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { auditTheoremAxioms } from "./axiom-audit.ts";
import { performance } from "node:perf_hooks";
import { projectRoot } from "./project-root.ts";
import { relative, resolve } from "node:path";
import { readFileSync } from "node:fs";
import { callNative } from "./runtime.ts";
import { exportTheorem, theoremDependencies } from "./export.ts";
import { formatFormula, formatTerm, type PrettyOptions } from "./pretty.ts";
import { createSetTheoryFoundationKernel, createSetTheoryKernel, SET_THEORY_BOOTSTRAP_FILES } from "./zfg.ts";
import {
  beginDependencyReads, dependencyStampsCurrent, endDependencyReads, loadModuleSourceGraph, moduleNameFromRoots, noteDependencyRead,
  type DependencyStamp, type LoadedModule, type ModuleSourceFile,
} from "./module-loader.ts";
import { scanModule, type ModuleNameDeriver } from "./module-source-loader.ts";
import { openParentheses } from "./library-search.ts";
import { resolveImportName } from "./module-names.ts";
import { classReport, elaborateModule, exportSurfaceEnvironmentIndex, forkSurfaceEnvironment, installSurfaceEnvironmentIndex, moduleReport, notationReport, setSurfaceTraceCapture, SurfaceError, tacticReport } from "./surface.ts";
import { compileSeparateKernelModule, replaySeparateKernelModuleExact, type CompiledModuleDependency } from "./compiled-module.ts";
import { installStandardCheckpoint, standardDependencyCheckpoints, type StandardDependencyCheckpoint } from "./standard-checkpoints.ts";
export { installStandardCheckpoint };
import { KernelError } from "./kernel.ts";
import { sha256Hex } from "./hash.ts";
import type { Formula, Term } from "./ast.ts";
import type { TacticScopeEntry, TacticStateSnapshot, TacticStepInfo } from "./tactic-trace.ts";

export type WorkbenchFoundation = "ZF" | "ZFC" | "ZFG";
export interface WorkbenchFile { readonly name: string; readonly source: string }

/**
 * Ignore only an EOF suffix that the surface language itself ignores and that
 * cannot move an existing declaration.  Narrative comments remain semantic:
 * they are rendered in proof maps and therefore must select a distinct leaf.
 */
function checkedLeafSource(source: string): string {
  const lines = source.split(/\r?\n/);
  while (lines.length > 0) {
    const line = lines.at(-1)!;
    if (/^\s*$/.test(line) || /^\s*--(?![!|])/.test(line)) lines.pop();
    else break;
  }
  return lines.join("\n");
}

export interface WorkbenchGoal {
  readonly goal: string;
  readonly assumptions: readonly string[];
  readonly locals: readonly { readonly name: string; readonly formula: string }[];
}

export interface WorkbenchState { readonly goals: readonly WorkbenchGoal[] }

export interface WorkbenchSorry {
  readonly file: string;
  readonly theorem: string;
  readonly axiom: string;
  readonly line: number;
  readonly goal: string;
}

/** A query-tactic result with every formula and term printed as the goal pane prints them. */
export interface WorkbenchSuggestion {
  readonly command: string;
  readonly tactic: "exact" | "apply" | "rw";
  readonly name: string;
  readonly reference: string;
  readonly source: "local" | "theorem" | "axiom" | "definition";
  readonly arguments: readonly string[];
  readonly premises: readonly { readonly formula: string; readonly evidence?: string; readonly routine?: boolean }[];
  readonly closes: boolean;
  readonly reverse?: boolean;
  readonly goal?: string;
}

export interface WorkbenchStepInfo {
  readonly title: string;
  readonly items: readonly string[];
  readonly suggestions?: readonly WorkbenchSuggestion[];
}

export interface WorkbenchStep {
  readonly line: number;
  readonly columnStart?: number;
  readonly columnEnd?: number;
  readonly command: string;
  readonly info?: WorkbenchStepInfo;
  readonly before: WorkbenchState;
  readonly after: WorkbenchState;
}

export interface WorkbenchTheorem {
  readonly name: string;
  readonly file: string;
  readonly lineStart: number;
  readonly lineEnd: number;
  readonly statement: string;
  readonly sorries: readonly WorkbenchSorry[];
  readonly proofNodes: number;
  readonly judgments: number;
  readonly dependencies: { readonly axioms: readonly string[]; readonly theorems: readonly string[]; readonly definitions: readonly string[] };
  /** The declarations the proof cites and the statement mentions directly, without their own dependencies. */
  readonly uses?: WorkbenchDirectUses;
  readonly proofMap: readonly { readonly line: number; readonly indent: number; readonly kind: "heading" | "note"; readonly text: string }[];
  readonly initial?: WorkbenchState;
  /** The names bound outside the proof that its lines can refer to, with their binding lines. */
  readonly scope?: readonly TacticScopeEntry[];
  readonly steps: readonly WorkbenchStep[];
  readonly kernel: readonly {
    readonly id: number;
    readonly proofNode: number;
    readonly rule: string;
    readonly ruleCode: string;
    readonly ruleName: string;
    readonly premiseLabels: readonly string[];
    readonly sideConditions: readonly string[];
    readonly arguments: readonly { readonly name: string; readonly value: string }[];
    readonly assumptions: readonly string[];
    readonly conclusion: string;
    readonly children: readonly number[];
  }[];
}

function kernelRulePresentation(payload: Record<string, unknown>): {
  readonly code: string;
  readonly name: string;
  readonly premiseLabels: readonly string[];
  readonly sideConditions: readonly string[];
  readonly arguments: readonly { readonly name: string; readonly value: string }[];
} {
  const rule = String(payload.rule ?? "unknown");
  const labels: Record<string, readonly [string, string]> = {
    assumption: ["hyp", "Hypothesis"], axiom: ["ax", "Foundation axiom"], theorem: ["thm", "Checked theorem"],
    definition: ["def", "Definition equation"], refl: ["=I", "Equality reflexivity"], compute: ["δ", "Checked computation"],
    rationalClassCompute: ["ℚ", "Checked quotient rational computation"],
    symm: ["=sym", "Equality symmetry"], trans: ["=trans", "Equality transitivity"], congr: ["congr", "Function congruence"],
    eqElim: ["=E", "Equality elimination"], impIntro: ["→I", "Implication introduction"], impElim: ["→E", "Modus ponens"],
    forallIntro: ["∀I", "Universal introduction"], forallElim: ["∀E", "Universal specialization"],
    andIntro: ["∧I", "Conjunction introduction"], andElimLeft: ["∧E₁", "Left conjunction elimination"],
    andElimRight: ["∧E₂", "Right conjunction elimination"], orIntroLeft: ["∨I₁", "Left disjunction introduction"],
    orIntroRight: ["∨I₂", "Right disjunction introduction"], orElim: ["∨E", "Disjunction elimination"],
    iffIntro: ["↔I", "Equivalence introduction"], iffElimLeft: ["↔E₁", "Forward equivalence elimination"],
    iffElimRight: ["↔E₂", "Backward equivalence elimination"], existsIntro: ["∃I", "Existential introduction"],
    existsElim: ["∃E", "Existential elimination"], falseElim: ["⊥E", "Explosion"], dne: ["¬¬E", "Classical double-negation elimination"],
    induction: ["ind", "Structural induction"], wellFoundedInduction: ["wf-ind", "Well-founded induction"],
  };
  const pair = labels[rule] ?? [rule, rule] as const;
  const fixedPremises: Record<string, readonly string[]> = {
    symm: ["equality"], trans: ["left equality", "right equality"],
    eqElim: ["equality", "property before substitution"],
    impIntro: ["conclusion under assumption"], impElim: ["implication", "antecedent"],
    forallIntro: ["body for fresh variable"], forallElim: ["universal statement"],
    andIntro: ["left conjunct", "right conjunct"], andElimLeft: ["conjunction"], andElimRight: ["conjunction"],
    orIntroLeft: ["left disjunct"], orIntroRight: ["right disjunct"],
    orElim: ["disjunction", "left case", "right case"],
    iffIntro: ["forward implication", "backward implication"],
    iffElimLeft: ["equivalence"], iffElimRight: ["equivalence"],
    existsIntro: ["witness satisfies predicate"], existsElim: ["existential", "body for fresh witness"],
    falseElim: ["contradiction"], dne: ["double negation"],
    wellFoundedInduction: ["well-founded relation", "induction step"],
  };
  let premiseLabels = fixedPremises[rule] ?? [];
  if (rule === "congr") {
    const proofs = Array.isArray(payload.proofs) ? payload.proofs.length : 0;
    premiseLabels = Array.from({ length: proofs }, (_, index) => `argument equality ${index + 1}`);
  }
  if (rule === "induction") {
    const cases = Array.isArray(payload.cases) ? payload.cases as Record<string, unknown>[] : [];
    premiseLabels = cases.map(item => typeof item.constructor === "string" ? `case ${item.constructor}` : "constructor case");
  }
  const ruleArguments: { name: string; value: string }[] = [];
  const term = (name: string) => {
    const value = payload[name];
    if (value && typeof value === "object" && !Array.isArray(value)) ruleArguments.push({ name, value: formatTerm(value as Term) });
  };
  const formula = (name: string, label = name) => {
    const value = payload[name];
    if (value && typeof value === "object" && !Array.isArray(value)) ruleArguments.push({ name: label, value: formatFormula(value as Formula) });
  };
  const text = (name: string, label = name) => {
    const value = payload[name];
    if (typeof value === "string") ruleArguments.push({ name: label, value });
  };
  const terms = (name: string, label = name) => {
    const value = payload[name];
    if (Array.isArray(value) && value.length) ruleArguments.push({ name: label, value: value.map(item => formatTerm(item as Term)).join(", ") });
  };
  const texts = (name: string, label = name) => {
    const value = payload[name];
    if (Array.isArray(value) && value.length) ruleArguments.push({ name: label, value: value.map(String).join(", ") });
  };
  if (["axiom", "theorem", "definition"].includes(rule)) {
    text("name", "declaration");
    text("property", "equation");
  }
  if (rule === "refl") term("term");
  if (rule === "compute") { term("left"); term("right"); texts("definitions", "allowed equations"); }
  if (rule === "rationalClassCompute") { term("left"); term("right"); }
  if (rule === "congr") text("fn", "function");
  if (rule === "eqElim") { text("variable", "motive variable"); formula("motive"); if (payload.reverse === true) ruleArguments.push({ name: "direction", value: "right to left" }); }
  if (rule === "impIntro") formula("assumption", "discharged assumption");
  if (["forallIntro", "forallElim"].includes(rule)) { text("variable", "bound variable"); term("term"); }
  if (rule === "orIntroLeft") formula("right", "other disjunct");
  if (rule === "orIntroRight") formula("left", "other disjunct");
  if (rule === "existsIntro") { text("variable", "bound variable"); term("witness"); formula("body", "predicate"); }
  if (rule === "existsElim") text("witness", "fresh witness");
  if (rule === "falseElim") formula("conclusion", "target");
  if (rule === "dne") formula("proposition");
  if (rule === "induction") { text("datatype"); terms("parameters"); text("variable", "induction variable"); formula("motive"); }
  if (rule === "wellFoundedInduction") { term("relation"); term("domain"); text("variable"); text("predecessor"); formula("motive"); }
  const sideConditions: string[] = [];
  if (rule === "forallIntro" && typeof payload.variable === "string") {
    sideConditions.push(`${payload.variable} ∉ FV(Γ)`);
  }
  if (rule === "existsElim" && typeof payload.witness === "string") {
    sideConditions.push(`${payload.witness} ∉ FV(Γ, existential premise, conclusion)`);
  }
  if (rule === "induction" && typeof payload.variable === "string") {
    sideConditions.push(`${payload.variable} ∉ FV(Γ, datatype parameters)`);
    sideConditions.push("constructor fields are fresh");
  }
  if (rule === "wellFoundedInduction" && typeof payload.variable === "string" && typeof payload.predecessor === "string") {
    sideConditions.push(`${payload.variable}, ${payload.predecessor} ∉ FV(Γ, relation, domain)`);
    sideConditions.push(`${payload.predecessor} ∉ FV(motive)`);
  }
  return { code: pair[0], name: pair[1], premiseLabels, sideConditions, arguments: ruleArguments };
}

const libraryModuleRoot = resolve(projectRoot, "lib");
const moduleRoots = [libraryModuleRoot] as const;

/** The module roots a workspace resolves imports against: any extra roots first, then the library. */
interface WorkspaceRoots {
  readonly roots: readonly string[];
  readonly derive: ModuleNameDeriver;
  readonly key: string;
}
const rootsCache = new Map<string, WorkspaceRoots>();
function workspaceRoots(extra?: readonly string[]): WorkspaceRoots {
  const roots = [...new Set([...(extra ?? []).map(root => resolve(root)), libraryModuleRoot])];
  const key = roots.join("\u0000");
  const known = rootsCache.get(key);
  if (known) return known;
  const derive: ModuleNameDeriver = roots.length === 1 ? workspaceModuleName
    : file => moduleNameFromRoots(file, roots) ?? workspaceModuleName(file);
  const created = { roots, derive, key };
  rootsCache.set(key, created);
  return created;
}

/**
 * The module a workspace file denotes: by its path under the library root,
 * or, for a file named relative to the Cumulus distribution such as
 * "Rat/Defs.g17", by the library file at that place.
 */
function workspaceModuleName(file: string): string | undefined {
  const direct = moduleNameFromRoots(file, moduleRoots);
  if (direct) return direct;
  const normal = file.replace(/\\/g, "/");
  if (normal.startsWith("/") || !normal.endsWith(".g17")) return undefined;
  const inCumulus = resolve(libraryModuleRoot, "Grace", "Cumulus", normal);
  if (safeRead(inCumulus) !== undefined) return moduleNameFromRoots(inCumulus, moduleRoots);
  return undefined;
}
const foundationInterfaceFile = resolve(libraryModuleRoot, "Grace", "Kernel", "Foundation.g17");

function displayState(state: TacticStateSnapshot, display: (formula: Formula) => string = formatFormula): WorkbenchState {
  return {
    goals: state.goals.map(goal => ({
      goal: display(goal.goal),
      assumptions: goal.assumptions.map(display),
      locals: goal.locals.map(local => ({ name: local.name, formula: display(local.formula) })),
    })),
  };
}

interface DependencyCheckpoint {
  readonly key: string;
  readonly profile: WorkbenchFoundation;
  readonly kernel: ReturnType<typeof createSetTheoryKernel>;
  readonly loaded: readonly LoadedModule[];
  readonly sourceDigests: ReadonlyMap<string, string>;
  /**
   * What the elaborated part grew from, so it compiles as one module: the
   * bare foundation, the kernel holding the replayed prefix (the foundation
   * itself when nothing was replayed), the boundary there, the replayed
   * modules as receipt-bearing dependencies, and the checkpoint that
   * provided them.
   */
  readonly base: {
    readonly foundation: ReturnType<typeof createSetTheoryKernel>;
    readonly kernel: ReturnType<typeof createSetTheoryKernel>;
    readonly mark: ReturnType<ReturnType<typeof createSetTheoryKernel>["admissionCheckpoint"]>;
    readonly dependencies: readonly CompiledModuleDependency[];
    readonly prefix?: string;
  };
  /** How many modules this checkpoint elaborated from source rather than replayed, and how long that took. */
  readonly elaborated: number;
  readonly elaboratedMilliseconds: number;
}

const incrementalBases = new Map<string, DependencyCheckpoint>();
// Each prepared base holds a whole kernel; in a browser worker a few large
// ones are all the memory there is.
const maximumIncrementalBases = 3;
interface CheckedLeafCheckpoint {
  readonly kernel: ReturnType<typeof createSetTheoryKernel>;
  readonly activeLoaded: readonly LoadedModule[];
}
const checkedLeaves = new Map<string, CheckedLeafCheckpoint>();
const maximumCheckedLeaves = 32;

function loadWorkspace(files: readonly WorkbenchFile[], profile: WorkbenchFoundation, entryFiles?: readonly string[], roots: WorkspaceRoots = workspaceRoots()) {
  if (files.length === 0) throw new SurfaceError(1, "workspace has no files");
  if (new Set(files.map(file => file.name)).size !== files.length) throw new SurfaceError(1, "workspace file names must be distinct");
  if (entryFiles?.length === 1) {
    const active = files.find(file => file.name === entryFiles[0]);
    if (active) {
      const bootstrap = loadBootstrapWorkspace(files, active, profile, roots);
      if (bootstrap) return bootstrap;
      const incremental = loadIncrementalWorkspace(files, active, profile, roots);
      if (incremental) return incremental;
    }
  }
  const kernel = createSetTheoryKernel({ profile });
  const loaded = loadDisplayedModuleGraph(kernel, files.map(file => ({ file: file.name, source: file.source })), roots.roots, entryFiles, [], roots.derive);
  return { kernel, loaded, context: "workspace" as const };
}

function normalizedPath(name: string): string {
  return name.replaceAll("\\", "/").replace(/^\.\//, "");
}

function bootstrapRelativeName(canonical: string): string {
  return canonical.slice(canonical.indexOf("Bootstrap/"));
}

function bootstrapStage(name: string): number {
  const normalized = normalizedPath(name);
  return SET_THEORY_BOOTSTRAP_FILES.findIndex(canonical => {
    const relative = bootstrapRelativeName(canonical);
    return normalized === canonical || normalized === relative || normalized.endsWith(`/${canonical}`) || normalized.endsWith(`/${relative}`);
  });
}

/**
 * Bootstrap sources are editable proof programs, but they cannot be replayed
 * over a kernel that already contains their declarations. Reconstruct the
 * exact stage instead: axiomatic foundation, preceding bootstrap files, then
 * the active file with tactic tracing enabled.
 */
function loadBootstrapWorkspace(
  files: readonly WorkbenchFile[],
  active: WorkbenchFile,
  profile: WorkbenchFoundation,
  roots: WorkspaceRoots,
): { readonly kernel: ReturnType<typeof createSetTheoryKernel>; readonly loaded: readonly LoadedModule[]; readonly context: "bootstrap" } | undefined {
  const target = bootstrapStage(active.name);
  if (target < 0) return undefined;
  const kernel = createSetTheoryFoundationKernel({ profile });
  const loaded: LoadedModule[] = [];
  for (let index = 0; index <= target; index += 1) {
    const canonical = SET_THEORY_BOOTSTRAP_FILES[index]!;
    const relative = bootstrapRelativeName(canonical);
    const workspace = files.find(file => {
      const name = normalizedPath(file.name);
      return name === canonical || name === relative || name.endsWith(`/${canonical}`) || name.endsWith(`/${relative}`);
    });
    const file = workspace?.name ?? resolve(libraryModuleRoot, canonical);
    const source = workspace?.source ?? safeRead(file);
    if (source === undefined) {
      const error = new SurfaceError(1, `cannot locate bootstrap source ${relative}`);
      error.file = file;
      throw error;
    }
    setSurfaceTraceCapture(kernel, index === target);
    try {
      const declared = scanModule(source, file, roots.derive).name;
      loaded.push({ file, ...elaborateModule(kernel, source, declared ? { moduleName: declared } : {}) });
    } catch (error) {
      if (error instanceof SurfaceError) error.file ??= file;
      rememberFailureDisplay(error, kernel);
      throw error;
    }
  }
  return { kernel, loaded, context: "bootstrap" };
}

// Keep presentation metadata with a failed check, without retaining its kernel.
// The same formatter must be used before and after a proof is completed.
const failureDisplays = new WeakMap<SurfaceError, WorkbenchDisplay>();
// The kernel a failed elaboration left behind: it holds the theorems that
// completed before the failure, with their tactic traces, so a failed check
// can still report them.
const failureKernels = new WeakMap<SurfaceError, ReturnType<typeof createSetTheoryKernel>>();

/** The printers of one checked environment: a formula and a term print with the same names and notations. */
export interface WorkbenchDisplay {
  (formula: Formula): string;
  readonly term: (term: Term) => string;
}

const plainDisplay: WorkbenchDisplay = Object.assign((formula: Formula) => formatFormula(formula), { term: (term: Term) => formatTerm(term) });

function formulaDisplay(
  kernel: ReturnType<typeof createSetTheoryKernel>,
  shortNames = shortestUniqueNames([...new Set([...kernel.functions.keys(), ...kernel.predicates.keys()])], symbolSignature(kernel)),
  notations = notationReport(kernel),
  rings?: readonly import("./pretty.ts").RingNotation[],
  operations?: readonly import("./pretty.ts").OperationNotation[],
  predicates?: readonly import("./pretty.ts").PredicateNotation[],
  functors?: readonly import("./ast.ts").Term[],
  carriers?: readonly import("./pretty.ts").CarrierNotation[],
  functions?: readonly import("./pretty.ts").FunctionNotation[],
): WorkbenchDisplay {
  const classNames = new Set(classReport(kernel).map(item => item.name));
  const options: PrettyOptions = {
    symbol: name => shortNames.get(name) ?? name,
    classPredicate: name => classNames.has(name), notations, rings, operations, predicates, functors, carriers, functions,
  };
  const cache = new WeakMap<Formula, string>();
  return Object.assign((formula: Formula): string => {
    const known = cache.get(formula);
    if (known !== undefined) return known;
    const rendered = formatFormula(formula, options);
    cache.set(formula, rendered);
    return rendered;
  }, { term: (term: Term) => formatTerm(term, options) });
}

/** A step's query-tactic results with their formulas and terms printed. */
function displayInfo(info: TacticStepInfo | undefined, display: WorkbenchDisplay): { info?: WorkbenchStepInfo } {
  if (!info) return {};
  return { info: {
    title: info.title, items: info.items,
    ...(info.suggestions ? { suggestions: info.suggestions.map(item => ({
      command: item.command, tactic: item.tactic, name: item.name, reference: item.reference, source: item.source,
      arguments: item.arguments.map(display.term),
      premises: item.premises.map(premise => ({
        formula: display(premise.formula),
        ...(premise.evidence !== undefined ? { evidence: premise.evidence } : {}),
        ...(premise.routine !== undefined ? { routine: premise.routine } : {}),
      })),
      closes: item.closes,
      ...(item.reverse !== undefined ? { reverse: item.reverse } : {}),
      ...(item.goal ? { goal: display(item.goal) } : {}),
    })) } : {}),
  } };
}

export function rememberFailureDisplay(error: unknown, kernel: ReturnType<typeof createSetTheoryKernel>): void {
  if (!(error instanceof SurfaceError)) return;
  failureKernels.set(error, kernel);
  if (error.partialTrace) failureDisplays.set(error, formulaDisplay(kernel, undefined, undefined, error.partialTrace.rings, error.partialTrace.operations, error.partialTrace.predicates, error.partialTrace.functors, error.partialTrace.carriers, error.partialTrace.functions));
}

function loadDisplayedModuleGraph(...args: Parameters<typeof loadModuleSourceGraph>): ReturnType<typeof loadModuleSourceGraph> {
  try { return loadModuleSourceGraph(...args); }
  catch (error) { rememberFailureDisplay(error, args[0]); throw error; }
}

/** Recheck only the edited leaf over an exact, content-addressed dependency checkpoint. */
function loadIncrementalWorkspace(
  files: readonly WorkbenchFile[],
  active: WorkbenchFile,
  profile: WorkbenchFoundation,
  roots: WorkspaceRoots,
): { readonly kernel: ReturnType<typeof createSetTheoryKernel>; readonly loaded: readonly LoadedModule[]; readonly context: "workspace" } | undefined {
  const checkpoint = dependencyCheckpoint(files, active, profile, roots);
  if (!checkpoint) return undefined;
  const leafKey = sha256Hex(JSON.stringify({
    dependency: checkpoint.key,
    file: active.name,
    source: sha256Hex(checkedLeafSource(active.source)),
  }));
  const known = checkedLeaves.get(leafKey);
  if (known) {
    checkedLeaves.delete(leafKey);
    checkedLeaves.set(leafKey, known);
    const kernel = known.kernel.fork();
    forkSurfaceEnvironment(known.kernel, kernel);
    return { kernel, loaded: [...checkpoint.loaded, ...known.activeLoaded], context: "workspace" as const };
  }
  const kernel = checkpoint.kernel.fork();
  forkSurfaceEnvironment(checkpoint.kernel, kernel);
  setSurfaceTraceCapture(kernel, true);
  const activeLoaded = loadDisplayedModuleGraph(kernel, [{ file: active.name, source: active.source }], roots.roots, undefined, [], roots.derive);
  checkedLeaves.set(leafKey, { kernel, activeLoaded });
  while (checkedLeaves.size > maximumCheckedLeaves) checkedLeaves.delete(checkedLeaves.keys().next().value!);
  return { kernel, loaded: [...checkpoint.loaded, ...activeLoaded], context: "workspace" as const };
}

// Cache processing of exact contents, never filesystem freshness. Current
// sources are still read on every lookup, so user-library edits invalidate immediately.
interface DependencySourceInfo {
  readonly source: string;
  readonly metadata: ReturnType<typeof scanModule>;
  readonly pathDigest: string;
  contentDigest?: string;
  locations?: ReadonlyMap<string, SymbolLocation>;
}
const dependencySourceInfo = new Map<string, DependencySourceInfo>();
function inspectDependencySource(file: string, source: string, roots: WorkspaceRoots = workspaceRoots()): DependencySourceInfo {
  const cacheKey = roots.roots.length === 1 ? file : `${roots.key}\u0000${file}`;
  const known = dependencySourceInfo.get(cacheKey);
  if (known?.source === source) return known;
  const info = { source, metadata: scanModule(source, file, roots.derive), pathDigest: sha256Hex(JSON.stringify([file, source])) };
  dependencySourceInfo.delete(cacheKey);
  dependencySourceInfo.set(cacheKey, info);
  while (dependencySourceInfo.size > 512) dependencySourceInfo.delete(dependencySourceInfo.keys().next().value!);
  return info;
}

/** Build or reuse a checked dependency environment without admitting the edited leaf. */
interface DependencyGraph {
  readonly activeMetadata: ReturnType<typeof scanModule>;
  readonly imports: readonly string[];
  readonly dependencies: ReadonlyMap<string, ModuleSourceFile>;
  readonly orderedSources: readonly (readonly [string, ModuleSourceFile])[];
  readonly sourceDigests: ReadonlyMap<string, string>;
  readonly key: string;
}

/** The active file's import closure with content digests, or undefined when it cannot be resolved. */
function dependencyGraph(
  files: readonly WorkbenchFile[],
  active: WorkbenchFile,
  profile: WorkbenchFoundation,
  roots: WorkspaceRoots,
): DependencyGraph | undefined {
  const activeMetadata = scanModule(active.source, active.name, roots.derive);
  if (!activeMetadata.name) return undefined;
  const workspaceModules = new Map<string, ModuleSourceFile>();
  for (const file of files) {
    if (file.name === active.name) continue;
    const name = scanModule(file.source, file.name, roots.derive).name;
    if (name) workspaceModules.set(name, { file: file.name, source: file.source });
  }
  const libraryFile = (name: string): string | undefined => {
    const relative = `${name.split(".").join("/")}.g17`;
    return roots.roots.map(root => resolve(root, relative)).find(candidate => readDependency(candidate) !== undefined);
  };
  const exists = (name: string): boolean => workspaceModules.has(name) || libraryFile(name) !== undefined;
  const resolved = (current: string | undefined, raw: string): string => resolveImportName(current, raw, exists) ?? raw;
  if (activeMetadata.imports.some(raw => resolved(activeMetadata.name, raw) === activeMetadata.name)) return undefined;
  const dependencies = new Map<string, ModuleSourceFile>();
  const visiting = new Set<string>();
  const collect = (name: string): boolean => {
    if (dependencies.has(name)) return true;
    if (name === activeMetadata.name || visiting.has(name)) return false;
    let source = workspaceModules.get(name);
    if (!source) {
      const candidate = libraryFile(name);
      if (!candidate) return false;
      source = { file: candidate, source: readDependency(candidate)! };
    }
    visiting.add(name);
    const metadata = inspectDependencySource(source.file, source.source, roots).metadata;
    if (metadata.name !== name || !metadata.imports.every(raw => collect(resolved(name, raw)))) return false;
    visiting.delete(name);
    dependencies.set(name, source);
    return true;
  };
  if (!activeMetadata.imports.every(raw => collect(resolved(activeMetadata.name, raw)))) return undefined;
  const orderedSources = [...dependencies].sort(([left], [right]) => left.localeCompare(right));
  const sourceDigests = new Map(orderedSources.map(([name, source]) =>
    [name, inspectDependencySource(source.file, source.source, roots).pathDigest]));
  const key = sha256Hex(JSON.stringify({ profile, roots: roots.roots, imports: activeMetadata.imports, sources: [...sourceDigests] }));
  const imports = activeMetadata.imports.map(raw => resolved(activeMetadata.name, raw));
  return { activeMetadata, imports, dependencies, orderedSources, sourceDigests, key };
}

/** A checkpoint can be replayed once its payload, and its prefix's, are installed. */
function replayable(entry: StandardDependencyCheckpoint | undefined): boolean {
  if (!entry || !entry.compiled || !entry.surface || !entry.loaded) return false;
  return entry.prefix === undefined || replayable(standardDependencyCheckpoints.get(entry.prefix));
}

/** Replay a checkpoint, after its prefix, onto a fresh foundation; the result holds its surface metadata. */
function replayStandardCheckpoint(foundation: ReturnType<typeof createSetTheoryKernel>, entry: StandardDependencyCheckpoint) {
  const dependencies: CompiledModuleDependency[] = [];
  let kernel = foundation;
  for (const stage of entry.prefix ? [standardDependencyCheckpoints.get(entry.prefix)!, entry] : [entry]) {
    kernel = replaySeparateKernelModuleExact(kernel, stage.compiled!);
    installSurfaceEnvironmentIndex(kernel, stage.surface!);
    dependencies.push({ module: stage.compiled!.module, digest: stage.compiled!.digest });
  }
  return { kernel, dependencies };
}

/** Bundled or kept checkpoints whose exact sources all lie in the graph, largest first. */
function matchingStandardCheckpoints(graph: DependencyGraph, profile: WorkbenchFoundation, roots: WorkspaceRoots): StandardDependencyCheckpoint[] {
  return [...standardDependencyCheckpoints.values()]
    .filter(candidate => (candidate.profile ?? "ZFG") === profile)
    .filter(candidate => candidate.sources.every(([name, digest]) => {
      const source = graph.dependencies.get(name);
      if (!source) return false;
      const info = inspectDependencySource(source.file, source.source, roots);
      return (info.contentDigest ??= sha256Hex(source.source)) === digest;
    }))
    .sort((left, right) => right.sources.length - left.sources.length);
}

function rememberCheckpoint(checkpoint: DependencyCheckpoint): DependencyCheckpoint {
  incrementalBases.set(checkpoint.key, checkpoint);
  while (incrementalBases.size > maximumIncrementalBases) incrementalBases.delete(incrementalBases.keys().next().value!);
  return checkpoint;
}

function dependencyCheckpoint(
  files: readonly WorkbenchFile[],
  active: WorkbenchFile,
  profile: WorkbenchFoundation,
  roots: WorkspaceRoots,
): DependencyCheckpoint | undefined {
  const graph = dependencyGraph(files, active, profile, roots);
  if (!graph) return undefined;
  const { key, imports, dependencies, orderedSources, sourceDigests } = graph;
  const exact = incrementalBases.get(key);
  if (exact) {
    incrementalBases.delete(key);
    incrementalBases.set(key, exact);
    return exact;
  }

  // Any authenticated checkpoint whose exact sources form a subset of this
  // dependency graph is a sound prefix, bundled with the build or kept by
  // this browser from an earlier elaboration. Only an installed payload can
  // be replayed; the worker fetches the best candidate before asking.
  const standard = matchingStandardCheckpoints(graph, profile, roots).find(replayable);
  // A smaller exact-source checkpoint is a sound prefix: it was constructed by
  // this kernel in this process, and every source contributing to it still has
  // the same content digest. Extend the largest compatible prefix.
  const compatible = [...incrementalBases.values()]
    .filter(candidate => candidate.profile === profile &&
      [...candidate.sourceDigests].every(([name, digest]) => sourceDigests.get(name) === digest))
    .sort((left, right) => right.sourceDigests.size - left.sourceDigests.size)[0];
  if (standard && (!compatible || standard.sources.length > compatible.sourceDigests.size)) {
    const foundation = createSetTheoryKernel({ profile });
    const replayed = replayStandardCheckpoint(foundation, standard);
    const mark = replayed.kernel.admissionCheckpoint();
    const kernel = replayed.kernel.fork();
    forkSurfaceEnvironment(replayed.kernel, kernel);
    const standardLoaded: LoadedModule[] = standard.loaded!.map(item => ({
      file: dependencies.get(item.module)!.file,
      module: item.module,
      definitions: item.definitions,
      theorems: item.theorems,
      theoremLocations: [],
      evaluations: [],
      sorries: [],
    }));
    setSurfaceTraceCapture(kernel, false);
    const started = performance.now();
    const newlyLoaded = loadDisplayedModuleGraph(kernel,
      orderedSources.map(([, source]) => source), roots.roots, [], imports, roots.derive);
    return rememberCheckpoint({ key, profile, kernel, loaded: [...standardLoaded, ...newlyLoaded], sourceDigests,
      base: { foundation, kernel: replayed.kernel, mark, dependencies: replayed.dependencies, prefix: standard.rootModule },
      elaborated: newlyLoaded.length, elaboratedMilliseconds: performance.now() - started });
  }

  let base: DependencyCheckpoint["base"];
  let kernel: ReturnType<typeof createSetTheoryKernel>;
  if (compatible) {
    base = compatible.base;
    kernel = compatible.kernel.fork();
    forkSurfaceEnvironment(compatible.kernel, kernel);
  } else {
    const foundation = createSetTheoryKernel({ profile });
    base = { foundation, kernel: foundation, mark: foundation.admissionCheckpoint(), dependencies: [] };
    kernel = foundation.fork();
    forkSurfaceEnvironment(foundation, kernel);
  }
  setSurfaceTraceCapture(kernel, false);
  const started = performance.now();
  const newlyLoaded = loadDisplayedModuleGraph(kernel, orderedSources.map(([, source]) => source), roots.roots, [], imports, roots.derive);
  const loaded = compatible ? [...compatible.loaded, ...newlyLoaded] : newlyLoaded;
  return rememberCheckpoint({ key, profile, kernel, loaded, sourceDigests, base,
    elaborated: (compatible?.elaborated ?? 0) + newlyLoaded.length,
    elaboratedMilliseconds: (compatible?.elaboratedMilliseconds ?? 0) + performance.now() - started });
}

/** What the active file's dependency prefix needs before a prepare or check, so a worker can fetch or recall it. */
export interface DependencyCheckpointPlan {
  readonly key: string;
  readonly modules: number;
  readonly sources: readonly (readonly [module: string, digest: string])[];
  /** This exact dependency set is already prepared in this process. */
  readonly exact: boolean;
  /** Modules the prepared checkpoint elaborated from source, and the time that took; absent until it exists. */
  readonly elaborated?: number;
  readonly elaboratedMilliseconds?: number;
  /** The largest matching checkpoint whose payload is not installed yet. */
  readonly standard?: { readonly rootModule: string; readonly file?: string };
  /** Sources covered by the largest installed matching checkpoint. */
  readonly installedPrefix: number;
}

export function dependencyCheckpointPlan(
  files: readonly WorkbenchFile[],
  profile: WorkbenchFoundation = "ZFG",
  activeFile?: string,
  options: WorkbenchWorkspaceOptions = {},
): DependencyCheckpointPlan | undefined {
  const active = files.find(file => file.name === (activeFile ?? files[0]?.name));
  if (!active || bootstrapStage(active.name) >= 0) return undefined;
  const roots = workspaceRoots(options.moduleRoots);
  const graph = dependencyGraph(files, active, profile, roots);
  if (!graph) return undefined;
  const matching = matchingStandardCheckpoints(graph, profile, roots);
  const best = matching[0];
  const installed = matching.find(replayable);
  const exact = incrementalBases.get(graph.key);
  return {
    key: graph.key,
    modules: graph.dependencies.size,
    sources: graph.orderedSources.map(([name, source]) =>
      [name, inspectDependencySource(source.file, source.source, roots).contentDigest ??= sha256Hex(source.source)] as const),
    exact: exact !== undefined,
    ...(exact ? { elaborated: exact.elaborated, elaboratedMilliseconds: Math.round(exact.elaboratedMilliseconds) } : {}),
    ...(best && best !== installed ? { standard: { rootModule: best.rootModule, ...(best.file ? { file: best.file } : {}) } } : {}),
    installedPrefix: installed?.sources.length ?? 0,
  };
}

/**
 * Compile the prepared dependency prefix of the active file into a
 * self-contained checkpoint, in the form of a bundled one, so a browser can
 * keep it and replay it on a later visit instead of elaborating again.
 */
export function exportDependencyCheckpoint(
  files: readonly WorkbenchFile[],
  profile: WorkbenchFoundation = "ZFG",
  activeFile?: string,
  options: WorkbenchWorkspaceOptions = {},
): StandardDependencyCheckpoint | undefined {
  const active = files.find(file => file.name === (activeFile ?? files[0]?.name));
  if (!active || bootstrapStage(active.name) >= 0) return undefined;
  const roots = workspaceRoots(options.moduleRoots);
  const graph = dependencyGraph(files, active, profile, roots);
  const checkpoint = graph && incrementalBases.get(graph.key);
  if (!graph || !checkpoint) return undefined;
  // A kept checkpoint stands on at most one bundled one, so that replaying
  // it later needs only that bundled payload beside it.
  const { base } = checkpoint;
  if (base.prefix !== undefined && (base.dependencies.length !== 1 || standardDependencyCheckpoints.get(base.prefix)?.prefix !== undefined)) return undefined;
  const module = `Grace.Checkpoint.Kept.${graph.key.slice(0, 16)}`;
  const compiled = compileSeparateKernelModule(base.foundation, base.kernel, checkpoint.kernel, base.mark,
    { module, sourceDigest: graph.key, dependencies: base.dependencies });
  const surface = exportSurfaceEnvironmentIndex(checkpoint.kernel, module, compiled.digest);
  return {
    rootModule: `kept:${graph.key}`,
    profile,
    ...(base.prefix !== undefined ? { prefix: base.prefix } : {}),
    sources: graph.orderedSources.map(([name, source]) =>
      [name, inspectDependencySource(source.file, source.source, roots).contentDigest ??= sha256Hex(source.source)] as const),
    compiled,
    surface,
    loaded: checkpoint.loaded.map(item => ({ module: item.module, definitions: item.definitions, theorems: item.theorems })),
  };
}

/** Precheck an active file's imports so its first interactive check only elaborates the leaf. */
export function prepareWorkbenchFiles(
  files: readonly WorkbenchFile[],
  profile: WorkbenchFoundation = "ZFG",
  activeFile?: string,
  options: WorkbenchWorkspaceOptions = {},
) {
  const started = performance.now();
  const active = files.find(file => file.name === (activeFile ?? files[0]?.name));
  if (!active) throw new SurfaceError(1, "unknown workspace entry");
  if (bootstrapStage(active.name) >= 0) {
    return { ok: true as const, milliseconds: Number((performance.now() - started).toFixed(2)), modules: 0 };
  }
  const checkpoint = dependencyCheckpoint(files, active, profile, workspaceRoots(options.moduleRoots));
  return {
    ok: true as const,
    milliseconds: Number((performance.now() - started).toFixed(2)),
    modules: checkpoint?.loaded.length ?? 0,
    symbols: checkpoint ? [...new Set([
      ...checkpoint.kernel.functions.keys(), ...checkpoint.kernel.predicates.keys(),
      ...checkpoint.kernel.axioms.keys(), ...checkpoint.kernel.theorems.keys(),
    ])] : [],
  };
}

export function checkWorkbenchSource(source: string, profile: WorkbenchFoundation = "ZFG") {
  return checkWorkbenchFiles([{ name: "Playground.g17", source }], profile);
}

export interface WorkbenchWorkspaceOptions {
  /** Module roots searched before the library root when an import names a file on disk. */
  readonly moduleRoots?: readonly string[];
}

export interface WorkbenchCheckOptions extends WorkbenchWorkspaceOptions {
  readonly includeKernelDetails?: boolean;
  readonly includeEnvironmentDigest?: boolean;
  /** Compute each theorem's dependencies even without kernel details. */
  readonly includeDependencies?: boolean;
  /** Also report the kernel's foundation and module reports and a summary of every loaded module. */
  readonly includeReports?: boolean;
  /** Add each theorem's `uses`: the declarations its proof and statement name directly. */
  readonly includeDirectDependencies?: boolean;
}

export interface WorkbenchDirectUses {
  readonly axioms: readonly string[];
  readonly theorems: readonly string[];
  readonly definitions: readonly string[];
  /** The function and predicate symbols of the statement. */
  readonly symbols: readonly string[];
}

/**
 * The declarations a theorem names directly: the axioms, theorems, and
 * definition properties its own certificate cites (not those of the
 * theorems it cites), and the symbols of its statement.
 */
export function directTheoremUses(kernel: ReturnType<typeof createSetTheoryKernel>, name: string): WorkbenchDirectUses {
  const axioms = new Set<string>();
  const theorems = new Set<string>();
  const definitions = new Set<string>();
  const visited = new Set<object>();
  const visit = (value: unknown): void => {
    if (value === null || typeof value !== "object" || visited.has(value)) return;
    visited.add(value);
    if (Array.isArray(value)) { value.forEach(visit); return; }
    const record = value as Record<string, unknown>;
    if (typeof record.rule === "string") {
      if (record.rule === "axiom") axioms.add(String(record.name));
      else if (record.rule === "theorem") { if (record.name !== name) theorems.add(String(record.name)); return; }
      else if (record.rule === "definition") definitions.add(String(record.name));
      else if (record.rule === "compute" && Array.isArray(record.definitions)) record.definitions.forEach(item => definitions.add(String(item)));
    }
    Object.entries(record).forEach(([key, child]) => { if (key !== "rule") visit(child); });
  };
  visit(kernel.theoremProofs.get(name));
  const symbols = new Set<string>();
  const walkTerm = (term: Term): void => {
    if (term.tag !== "app") return;
    symbols.add(term.fn);
    term.args.forEach(walkTerm);
  };
  const walk = (formula: Formula): void => {
    switch (formula.tag) {
      case "bottom": return;
      case "eq": walkTerm(formula.left); walkTerm(formula.right); return;
      case "pred": symbols.add(formula.pred); formula.args.forEach(walkTerm); return;
      case "imp": case "and": case "or": case "iff": walk(formula.left); walk(formula.right); return;
      case "forall": case "exists": walk(formula.body); return;
    }
  };
  const statement = kernel.theorems.get(name);
  if (statement) walk(statement);
  const sorted = (items: Set<string>): string[] => [...items].sort();
  return { axioms: sorted(axioms), theorems: sorted(theorems), definitions: sorted(definitions), symbols: sorted(symbols) };
}

export interface WorkbenchShadowedProperty {
  readonly theorem: string;
  readonly definition: string;
  readonly property: string;
  readonly module?: string;
  readonly file: string;
  readonly line: number;
}

/**
 * The theorems of the loaded modules whose name is also a generated
 * property of a definition (`rationalCut.membership` as a theorem beside
 * the definition `rationalCut` with its `membership` property): a name that
 * then resolves to the theorem and hides the property.
 */
export function shadowedProperties(kernel: ReturnType<typeof createSetTheoryKernel>, loaded: readonly LoadedModule[]): WorkbenchShadowedProperty[] {
  const result: WorkbenchShadowedProperty[] = [];
  for (const item of loaded) {
    const lines = new Map(item.theoremLocations?.map(location => [location.name, location.lineStart]));
    for (const theorem of item.theorems) {
      for (let cut = theorem.lastIndexOf("."); cut > 0; cut = theorem.lastIndexOf(".", cut - 1)) {
        const definition = theorem.slice(0, cut);
        const property = theorem.slice(cut + 1);
        if (!kernel.definitions.get(definition)?.properties.has(property)) continue;
        result.push({ theorem, definition, property, ...(item.module ? { module: item.module } : {}), file: item.file, line: lines.get(theorem) ?? 1 });
        break;
      }
    }
  }
  return result;
}

export function checkWorkbenchFiles(
  files: readonly WorkbenchFile[],
  profile: WorkbenchFoundation = "ZFG",
  entryFiles?: readonly string[],
  options: WorkbenchCheckOptions = {},
) {
  const started = performance.now();
  const profileWorkbench = (globalThis as typeof globalThis & {
    process?: { env?: Record<string, string | undefined> };
  }).process?.env?.GRACE_PROFILE_WORKBENCH === "1";
  let profileMark = started;
  const markProfile = (label: string): void => {
    if (!profileWorkbench) return;
    const now = performance.now();
    console.error(`${(now - profileMark).toFixed(2)} ms\tworkbench ${label}`);
    profileMark = now;
  };
  const roots = workspaceRoots(options.moduleRoots);
  const { kernel, loaded, context } = loadWorkspace(files, profile, entryFiles, roots);
  markProfile("load workspace");
  return renderWorkbenchCheck(kernel, loaded, context, files, profile, entryFiles, options, roots, started, markProfile);
}

/**
 * Present modules checked over any loader exactly as the Workbench presents
 * a workspace: the same theorem records, proof states, and printed forms.
 * The command line calls this over its own module loader and artifact store.
 */
export function renderCheckedWorkspace(
  kernel: ReturnType<typeof createSetTheoryKernel>,
  loaded: readonly LoadedModule[],
  files: readonly WorkbenchFile[],
  profile: WorkbenchFoundation = "ZFG",
  entryFiles?: readonly string[],
  options: WorkbenchCheckOptions = {},
) {
  return renderWorkbenchCheck(kernel, loaded, "workspace", files, profile, entryFiles, options, workspaceRoots(options.moduleRoots), performance.now(), () => {});
}

export type WorkbenchCheckResult = ReturnType<typeof renderWorkbenchCheck>;

function renderWorkbenchCheck(
  kernel: ReturnType<typeof createSetTheoryKernel>,
  loaded: readonly LoadedModule[],
  context: "workspace" | "bootstrap",
  files: readonly WorkbenchFile[],
  profile: WorkbenchFoundation,
  entryFiles: readonly string[] | undefined,
  options: WorkbenchCheckOptions,
  roots: WorkspaceRoots,
  started: number,
  markProfile: (label: string) => void,
) {
  const symbolNames = [...new Set([...kernel.functions.keys(), ...kernel.predicates.keys()])];
  const shortNames = shortestUniqueNames(symbolNames, symbolSignature(kernel));
  const notations = notationReport(kernel);
  const reportedNotations = notations.map(({ definitionTarget, ...notation }) => ({
    ...notation,
    target: definitionTarget ?? notation.target,
  }));
  const display = formulaDisplay(kernel, shortNames, notations);
  const workspaceNames = new Set(files.map(file => file.name));
  const reportedNames = entryFiles ? new Set(entryFiles) : workspaceNames;
  const workspaceModules = loaded.filter(item => reportedNames.has(item.file));
  const sourceByName = new Map(files.map(file => [file.name, file.source]));
  const locations = new Map<string, { file: string; lineStart: number; lineEnd: number }>();
  for (const item of workspaceModules) {
    const ranges = theoremRanges(sourceByName.get(item.file) ?? "");
    const exact = new Map(item.theoremLocations?.map(location => [location.name, location]));
    item.theorems.forEach((name, index) => locations.set(name, {
      file: item.file,
      lineStart: exact.get(name)?.lineStart ?? ranges[index]?.lineStart ?? 1,
      lineEnd: exact.get(name)?.lineEnd ?? ranges[index]?.lineEnd ?? (sourceByName.get(item.file)?.split(/\r?\n/).length ?? 1),
    }));
  }
  const theoremNames = workspaceModules.flatMap(item => item.theorems);
  const evaluations = workspaceModules.flatMap(item => item.evaluations.map(evaluation => ({ file: item.file, ...evaluation })));
  const sorries: WorkbenchSorry[] = loaded.flatMap(item => item.sorries.map(sorry => ({
    file: item.file, theorem: sorry.theorem, axiom: sorry.axiom, line: sorry.line, goal: display(sorry.goal),
  })));
  const theorems: WorkbenchTheorem[] = theoremNames.map(name =>
    renderTheorem(kernel, name, locations.get(name)!, shortNames, notations, sorries, options));
  markProfile("render theorem states");
  const symbols = symbolReport(kernel, loaded, sourceByName, shortNames, display, roots);
  markProfile("build symbol report");
  const documents = [...loaded.map(item => ({
    file: item.file,
    name: displayDocumentName(item.file, roots),
    ...(item.module ? { module: item.module } : {}),
    source: sourceByName.get(item.file) ?? safeRead(item.file),
  })), ...SET_THEORY_BOOTSTRAP_FILES.map(name => {
    const file = resolve(libraryModuleRoot, name);
    return { file, name: displayDocumentName(file, roots), source: safeRead(file) };
  }), {
    file: foundationInterfaceFile,
    name: displayDocumentName(foundationInterfaceFile, roots),
    module: "Grace.Kernel.Foundation",
    source: safeRead(foundationInterfaceFile),
  }].filter((item, index, all) => typeof item.source === "string" &&
    all.findIndex(candidate => candidate.file === item.file) === index);
  markProfile("collect documents");
  const digest = options.includeEnvironmentDigest === false ? undefined : kernel.digest();
  markProfile("digest environment");
  const moduleRecords = moduleReport(kernel);
  const reports = options.includeReports ? {
    foundationReport: kernel.foundationReport(),
    moduleReport: moduleRecords,
    loaded: loaded.map(item => ({
      file: item.file,
      ...(item.module ? { module: item.module } : {}),
      definitions: item.definitions,
      theorems: item.theorems,
      theoremLocations: item.theoremLocations ?? [],
      evaluations: item.evaluations,
      sorries: item.sorries.map(sorry => ({ theorem: sorry.theorem, axiom: sorry.axiom, line: sorry.line, goal: display(sorry.goal) })),
    })),
  } : {};
  return {
    ok: true as const,
    context,
    foundation: profile,
    milliseconds: Number((performance.now() - started).toFixed(2)),
    ...(digest === undefined ? {} : { digest }),
    definitions: workspaceModules.flatMap(item => item.definitions),
    evaluations,
    sorries,
    checkedFiles: workspaceModules.map(item => item.file),
    modules: moduleRecords.length,
    notations: reportedNotations,
    tactics: tacticReport(kernel).map(tactic => ({
      ...tactic,
      short: tactic.name.split(".").at(-1)!,
      file: loaded.find(item => item.module === tactic.module)?.file,
    })),
    symbols,
    documents,
    files: files.map(file => ({ name: file.name, definitions: workspaceModules.find(item => item.file === file.name)?.definitions.length ?? 0,
      theorems: workspaceModules.find(item => item.file === file.name)?.theorems.length ?? 0,
      evaluations: workspaceModules.find(item => item.file === file.name)?.evaluations.length ?? 0,
      sorries: workspaceModules.find(item => item.file === file.name)?.sorries.length ?? 0,
      admittedSorries: new Set(theorems.filter(theorem => theorem.file === file.name)
        .flatMap(theorem => theorem.sorries.map(sorry => sorry.axiom))).size })),
    theorems,
    shadowed: shadowedProperties(kernel, workspaceModules),
    ...reports,
  };
}

/** One checked theorem as the Workbench presents it: its statement, states, and on request its kernel derivation. */
function renderTheorem(
  kernel: ReturnType<typeof createSetTheoryKernel>,
  name: string,
  location: { readonly file: string; readonly lineStart: number; readonly lineEnd: number },
  shortNames: ReadonlyMap<string, string>,
  notations: ReturnType<typeof notationReport>,
  sorries: readonly WorkbenchSorry[],
  options: WorkbenchCheckOptions,
): WorkbenchTheorem {
  const statement = kernel.theorems.get(name)!;
  const tactics = kernel.theoremTacticTraces.get(name);
  const display = formulaDisplay(kernel, shortNames, notations, tactics?.rings, tactics?.operations, tactics?.predicates, tactics?.functors, tactics?.carriers, tactics?.functions);
  const dependencies = options.includeKernelDetails === false && !options.includeDependencies && sorries.length === 0
    ? { axioms: [], theorems: [], definitions: [] } as const
    : theoremDependencies(kernel, name);
  const theoremSorries = sorries.filter(sorry => dependencies.axioms.includes(sorry.axiom));
  const uses = options.includeDirectDependencies ? { uses: directTheoremUses(kernel, name) } : {};
  const steps: WorkbenchStep[] = tactics?.steps.map(step => ({
    line: step.line,
    columnStart: step.columnStart,
    columnEnd: step.columnEnd,
    command: step.command,
    ...displayInfo(step.info, display),
    before: displayState(step.before, display),
    after: displayState(step.after, display),
  })) ?? [];
  if (options.includeKernelDetails === false) return {
    name,
    ...location,
    statement: display(statement),
    sorries: theoremSorries,
    proofNodes: 0,
    judgments: 0,
    dependencies,
    ...uses,
    proofMap: tactics?.narrative ?? [],
    ...(tactics ? { initial: displayState(tactics.initial, display) } : {}),
    ...(tactics?.scope ? { scope: tactics.scope } : {}),
    steps,
    kernel: [],
  };
  const exported = exportTheorem(kernel, name);
  return {
    name,
    ...location,
    statement: display(exported.statement),
    sorries: theoremSorries,
    proofNodes: exported.proof.nodes.length,
    judgments: exported.trace.nodes.length,
    dependencies: exported.dependencies,
    ...uses,
    proofMap: tactics?.narrative ?? [],
    ...(tactics ? { initial: displayState(tactics.initial, display) } : {}),
    ...(tactics?.scope ? { scope: tactics.scope } : {}),
    steps,
    kernel: exported.trace.nodes.map((node, id) => {
      const payload = exported.proof.nodes[node.proofNode]!.payload as Record<string, unknown>;
      const presentation = kernelRulePresentation(payload);
      return {
        id,
        proofNode: node.proofNode,
        rule: String(payload.rule ?? "unknown"),
        ruleCode: presentation.code,
        ruleName: presentation.name,
        premiseLabels: presentation.premiseLabels,
        sideConditions: presentation.sideConditions,
        arguments: presentation.arguments,
        assumptions: node.assumptions.map(display),
        conclusion: display(node.conclusion),
        children: node.children,
      };
    }),
  };
}

/**
 * The theorems of the workspace files that completed before a failed
 * elaboration, rendered as a successful check renders them. They come from
 * the kernel the failure left behind: the dependency environment carries no
 * tactic traces, so a traced theorem located in a workspace file is one the
 * failed check proved before it stopped.
 */
function completedTheorems(
  error: unknown, files: readonly WorkbenchFile[], roots: WorkspaceRoots,
): readonly WorkbenchTheorem[] {
  const kernel = error instanceof SurfaceError ? failureKernels.get(error) : undefined;
  if (!kernel) return [];
  const traced = [...kernel.theoremTacticTraces.keys()].filter(name => kernel.theorems.has(name));
  if (traced.length === 0) return [];
  const symbolNames = [...new Set([...kernel.functions.keys(), ...kernel.predicates.keys()])];
  const shortNames = shortestUniqueNames(symbolNames, symbolSignature(kernel));
  const notations = notationReport(kernel);
  const display = formulaDisplay(kernel, shortNames, notations);
  const located: { name: string; file: string; lineStart: number; lineEnd: number }[] = [];
  for (const file of files) {
    const locations = sourceSymbolLocations(file.name, file.source, roots);
    const ranges = proofRanges(file.source);
    for (const name of traced) {
      // A traced theorem is a declared one, or the proof block of a
      // definition, such as a defgraph's codomain proof `ident.closed`.
      const direct = locations.get(name);
      const owner = direct ? undefined : proofOwner(name);
      const location = direct && ["theorem", "lemma", "instance"].includes(direct.kind ?? "") ? direct
        : owner && owner.kinds.includes(locations.get(owner.name)?.kind ?? "") ? locations.get(owner.name) : undefined;
      if (!location) continue;
      const range = ranges.find(item => item.lineStart === location.line);
      if (range) located.push({ name, file: file.name, ...range });
    }
  }
  // A sorry is an axiom named after its theorem and line; the surface list
  // of admissions is lost with the failure, so read them back from the kernel.
  const sorries: WorkbenchSorry[] = [];
  for (const [axiom, goal] of kernel.axioms) {
    const admitted = /^sorry\.(.+)\.(\d+)\.\d+$/.exec(axiom);
    const owner = admitted && located.find(item => item.name === admitted[1]);
    if (admitted && owner) sorries.push({ file: owner.file, theorem: owner.name, axiom, line: Number(admitted[2]), goal: display(goal) });
  }
  return located
    .sort((left, right) => files.findIndex(file => file.name === left.file) - files.findIndex(file => file.name === right.file) || left.lineStart - right.lineStart)
    .map(({ name, ...location }) => renderTheorem(kernel, name, location, shortNames, notations, sorries, { includeKernelDetails: false, includeDependencies: true }));
}

/**
 * The environment a failed check loaded before it stopped: the symbols of
 * every dependency and of the failing file's declarations before the
 * failure, reported as a checked environment reports them, with the
 * notations in scope and a lookup of generated properties. A failure with no
 * kernel behind it, such as an unresolved import, has no environment.
 */
export function workbenchFailureEnvironment(error: unknown, files: readonly WorkbenchFile[], options: WorkbenchWorkspaceOptions = {}) {
  const kernel = error instanceof SurfaceError ? failureKernels.get(error) : undefined;
  if (!kernel) return undefined;
  const roots = workspaceRoots(options.moduleRoots);
  const sourceByName = new Map(files.map(file => [file.name, file.source]));
  const workspaceModules = new Map<string, string>();
  for (const file of files) {
    const name = scanModule(file.source, file.name, roots.derive).name;
    if (name) workspaceModules.set(name, file.name);
  }
  const fileOf = (module: string): string | undefined => {
    const known = workspaceModules.get(module);
    if (known) return known;
    const relativePath = `${module.split(".").join("/")}.g17`;
    return roots.roots.map(root => resolve(root, relativePath)).find(candidate => safeRead(candidate) !== undefined);
  };
  const empty = { definitions: [], theorems: [], theoremLocations: [], evaluations: [], sorries: [] } as const;
  const loaded: LoadedModule[] = moduleReport(kernel).map(record => ({ file: fileOf(record.name) ?? record.name, module: record.name, ...empty }));
  // The failing file's own declarations before the failure are in the
  // kernel whether or not its module is registered yet.
  for (const file of files) {
    if (loaded.some(item => item.file === file.name)) continue;
    const module = [...workspaceModules].find(([, name]) => name === file.name)?.[0];
    loaded.push({ file: file.name, ...(module ? { module } : {}), ...empty });
  }
  const symbolNames = [...new Set([...kernel.functions.keys(), ...kernel.predicates.keys()])];
  const shortNames = shortestUniqueNames(symbolNames, symbolSignature(kernel));
  const notations = notationReport(kernel);
  const display = formulaDisplay(kernel, shortNames, notations);
  return {
    symbols: symbolReport(kernel, loaded, sourceByName, shortNames, display, roots),
    loaded,
    notations: notations.map(({ definitionTarget, ...notation }) => ({ ...notation, target: definitionTarget ?? notation.target })),
    property: (name: string) => kernelProperty(kernel, name),
  };
}

function displayDocumentName(file: string, roots: WorkspaceRoots = workspaceRoots()): string {
  for (const root of roots.roots) if (file.startsWith(`${root}/`)) return relative(root, file);
  return file;
}

/**
 * The shortest suffix that names each symbol alone among those of the same
 * kind and arity, as the parser resolves a written name: two symbols of
 * different arity may share a short name and still print by it.
 */
function shortestUniqueNames(names: readonly string[], signature: (name: string) => string = () => ""): ReadonlyMap<string, string> {
  const result = new Map<string, string>();
  const suffixCounts = new Map<string, number>();
  const key = (name: string, suffix: string): string => `${signature(name)}\u0000${suffix}`;
  for (const name of names) {
    const parts = name.split(".");
    for (let length = 1; length <= parts.length; length += 1) {
      const suffix = key(name, parts.slice(-length).join("."));
      suffixCounts.set(suffix, (suffixCounts.get(suffix) ?? 0) + 1);
    }
  }
  for (const name of names) {
    const parts = name.split(".");
    let candidate = name;
    for (let length = 1; length <= parts.length; length += 1) {
      const suffix = parts.slice(-length).join(".");
      if (suffixCounts.get(key(name, suffix)) === 1) {
        candidate = suffix;
        break;
      }
    }
    result.set(name, candidate);
  }
  return result;
}

/** The kind and arity of a declared symbol, the key under which written names resolve. */
function symbolSignature(kernel: ReturnType<typeof createSetTheoryKernel>): (name: string) => string {
  return name => kernel.functions.has(name) ? `function/${kernel.functions.get(name)}` : `predicate/${kernel.predicates.get(name)}`;
}

interface SymbolLocation { file: string; line: number; signature: string; info?: string; kind?: string }

function sourceSymbolLocations(file: string, text: string, roots: WorkspaceRoots = workspaceRoots()): ReadonlyMap<string, SymbolLocation> {
  const info = inspectDependencySource(file, text, roots);
  if (info.locations) return info.locations;
  const locations = new Map<string, SymbolLocation>();
  const namespaces: string[] = [];
  const namespaceDepths: number[] = [];
  // Every module puts its declarations in its own namespace, as the
  // elaborator does; a bare `module Name` under the library root takes its
  // qualification from the file's place there.
  const metadata = info.metadata;
  const implicit = metadata.name || undefined;
  if (implicit) namespaces.push(...implicit.split("."));
  let datatype: string | undefined;
  const sourceLines = text.split(/\r?\n/);
  sourceLines.forEach((raw, index) => {
    let line = raw.replace(/--.*$/, "").trim();
    if (/^section\s+/.test(line)) { datatype = undefined; namespaceDepths.push(namespaces.length); return; }
    // A header whose binder list wraps onto the indented lines beneath it is
    // one signature line, as the elaborator reads it.
    for (let next = index + 1; /^(?:theorem|lemma|instance)\s/.test(line) && openParentheses(line) > 0 && next < sourceLines.length; next += 1) {
      const continuation = sourceLines[next]!.replace(/--.*$/, "");
      if (!/^\s+\S/.test(continuation)) break;
      line = `${line} ${continuation.trim()}`;
    }
    const namespace = /^namespace\s+(\S+)/.exec(line);
    if (namespace) {
      datatype = undefined;
      namespaceDepths.push(namespaces.length);
      // Reopening the module's own implicit namespace changes nothing.
      if (!(implicit && namespace[1] === implicit && namespaces.join(".") === implicit)) namespaces.push(...namespace[1]!.split("."));
      return;
    }
    if (/^end(?:\s|$)/.test(line)) { datatype = undefined; namespaces.length = namespaceDepths.pop() ?? 0; return; }
    const datatypeDeclaration = /^datatype\s+([^\s(]+)/.exec(line);
    if (datatypeDeclaration) {
      datatype = [...namespaces, datatypeDeclaration[1]!].filter(Boolean).join(".");
      locations.set(datatype, { file, line: index + 1, signature: line });
      return;
    }
    const constructor = datatype && /^\|\s*([^\s(]+)/.exec(line);
    if (constructor) {
      locations.set(`${datatype}.${constructor[1]!}`, { file, line: index + 1, signature: line });
      return;
    }
    if (line) datatype = undefined;
    const declaration = /^(?:(?:noncomputable|transfinite|foundation|well-founded)\s+)*(defgraph|defchoose|defunique|def|define|predicate|class|theorem|lemma|instance)\s+([^\s(]+)/.exec(line);
    if (!declaration) return;
    // Mathematical carrier declarations use their surface glyph in source
    // but are stored under stable kernel identifiers.  Location metadata
    // must follow that same desugaring or ℤ, ℚ, and ℝ lose their defining
    // line and cannot navigate from notation hover.
    const sourceName = ({ "ℕ": "omega", "ℤ": "integers", "ℚ": "rationals", "ℝ": "reals" } as
      Readonly<Record<string, string>>)[declaration[2]!] ?? declaration[2]!;
    const canonical = [...namespaces, sourceName].filter(Boolean).join(".");
    locations.set(canonical, { file, line: index + 1, signature: line, kind: declaration[1]! });
  });
  info.locations = locations;
  return locations;
}

/**
 * The proof-producing declaration whose source range holds a line, named as
 * the checker names it, so a failure can be reported against its theorem.
 */
export function declarationAtLine(
  file: string, source: string, line: number, options: WorkbenchWorkspaceOptions = {},
): { readonly name: string; readonly kind: string; readonly lineStart: number; readonly lineEnd: number } | undefined {
  const range = proofRanges(source).find(item => line >= item.lineStart && line <= item.lineEnd);
  if (!range) return undefined;
  for (const [name, location] of sourceSymbolLocations(file, source, workspaceRoots(options.moduleRoots))) {
    if (location.line !== range.lineStart || !PROOF_KINDS.has(location.kind ?? "")) continue;
    const proved = provedTheoremNames(name, location.kind!);
    // A defunique has two proof blocks; the uniqueness proof follows its marker.
    const lines = source.split(/\r?\n/);
    const uniqueness = location.kind === "defunique"
      && lines.slice(range.lineStart - 1, line).some(text => /^\s*uniqueness\s*(?:--.*)?$/.test(text));
    return { name: uniqueness ? proved[1]! : proved[0]!, kind: location.kind!, ...range };
  }
  return undefined;
}

/** The declaration kinds whose source carries a checked proof block. */
const PROOF_KINDS = new Set(["theorem", "lemma", "instance", "defgraph", "defunique", "defchoose", "def", "define"]);

/**
 * The theorems a declaration's proof blocks become, as the checker names
 * them: a theorem is itself; a defgraph's codomain proof is `name.closed`; a
 * defunique's existence and uniqueness proofs are `name.exists` and
 * `name.unique`; a definition's result-type proof is `name.type`.
 */
export function provedTheoremNames(name: string, kind: string): readonly string[] {
  switch (kind) {
    case "theorem": case "lemma": case "instance": return [name];
    case "defgraph": return [`${name}.closed`];
    case "defunique": return [`${name}.exists`, `${name}.unique`];
    case "defchoose": return [`${name}.exists`];
    case "def": case "define": return [`${name}.type`];
    default: return [];
  }
}

/** The declaration a generated proof theorem belongs to: `ident.closed` is the defgraph `ident`. */
function proofOwner(theorem: string): { readonly name: string; readonly kinds: readonly string[] } | undefined {
  const suffix = /\.(closed|exists|unique|type)$/.exec(theorem);
  if (!suffix) return undefined;
  const kinds = suffix[1] === "closed" ? ["defgraph"] : suffix[1] === "type" ? ["def", "define"]
    : suffix[1] === "unique" ? ["defunique"] : ["defunique", "defchoose"];
  return { name: theorem.slice(0, -(suffix[1]!.length + 1)), kinds };
}

function symbolReport(
  kernel: ReturnType<typeof createSetTheoryKernel>,
  loaded: readonly LoadedModule[],
  sourceByName: ReadonlyMap<string, string>,
  shortNames: ReadonlyMap<string, string>,
  display: (formula: Formula) => string,
  roots: WorkspaceRoots = workspaceRoots(),
) {
  const locations = new Map<string, SymbolLocation>();
  const sourceItems = [...loaded, ...SET_THEORY_BOOTSTRAP_FILES.map(name => ({ file: resolve(libraryModuleRoot, name), module: undefined }))]
    .filter((item, index, items) => items.findIndex(candidate => candidate.file === item.file) === index);
  for (const item of sourceItems) {
    const source = sourceByName.get(item.file) ?? safeRead(item.file);
    const text = source ?? "";
    for (const [name, location] of sourceSymbolLocations(item.file, text, roots)) locations.set(name, location);
  }
  const foundationSource = safeRead(foundationInterfaceFile) ?? "";
  const foundationLines = foundationSource.split(/\r?\n/);
  foundationLines.forEach((raw, index) => {
    const marker = /^\s*--\s*@symbol\s+(\S+)\s*$/.exec(raw);
    if (!marker) return;
    const documentation: string[] = [];
    for (let cursor = index + 1; cursor < foundationLines.length; cursor += 1) {
      const comment = /^\s*--\s?(.*)$/.exec(foundationLines[cursor]!);
      if (!comment || comment[1] === "" || comment[1]!.startsWith("@symbol ")) break;
      documentation.push(comment[1]!);
    }
    const signature = documentation[0] ?? marker[1]!;
    locations.set(marker[1]!, {
      file: foundationInterfaceFile,
      line: index + 2,
      signature,
      info: documentation.join("\n"),
    });
  });
  // Nat is a trusted set-encoded datatype installed by the foundation rather
  // than redeclared in surface syntax. Navigate it to the public Core module
  // where its recursion interface and laws begin.
  const naturalModule = loaded.find(item => item.module === "Grace.Core.Nat");
  if (naturalModule) {
    const source = sourceByName.get(naturalModule.file) ?? safeRead(naturalModule.file) ?? "";
    const line = source.split(/\r?\n/).findIndex(item => /^\s*module\s+Grace\.Core\.Nat\s*$/.test(item)) + 1;
    locations.set("Nat", {
      file: naturalModule.file,
      line: Math.max(1, line),
      signature: "predicate Nat (n : Set) · trusted set-encoded natural datatype",
    });
  }
  const classes = new Map(classReport(kernel).map(item => [item.name, item]));
  const names = [...new Set([
    ...kernel.functions.keys(), ...kernel.predicates.keys(), ...kernel.axioms.keys(), ...kernel.theorems.keys(), ...classes.keys(),
  ])];
  return names.map(name => {
    let location = locations.get(name);
    if (!location) {
      const parts = name.split(".");
      while (!location && parts.length > 1) {
        parts.pop();
        location = locations.get(parts.join("."));
      }
    }
    const proposition = kernel.theorems.get(name) ?? kernel.axioms.get(name);
    const forward = proposition && directionalStatement(proposition, false);
    const backward = proposition && directionalStatement(proposition, true);
    const kind = classes.has(name) ? "class" : kernel.axioms.has(name) ? "axiom" : kernel.theorems.has(name) ? "theorem"
      : kernel.predicates.has(name) ? "predicate" : kernel.definitions.has(name) ? "definition" : "function";
    const arity = kernel.functions.get(name) ?? kernel.predicates.get(name);
    const { kind: _declarationKind, ...locationFields } = location ?? {};
    return {
      name, short: shortNames.get(name) ?? name.slice(name.lastIndexOf(".") + 1), kind,
      info: proposition ? `${location?.info ? `${location.info}\n` : ""}${display(proposition)}`
        : location?.info ?? location?.signature ?? `${kind}${arity === undefined ? "" : ` · ${arity} argument${arity === 1 ? "" : "s"}`}`,
      ...locationFields,
      ...(proposition ? { statement: display(proposition) } : {}),
      ...(location?.info ? { documentation: location.info } : {}),
      ...(forward && backward ? { directions: { forward: display(forward), backward: display(backward) } } : {}),
    };
  });
}

/** Presentation only: mirror proof application through binders and premises. */
function directionalStatement(formula: Formula, backward: boolean): Formula | undefined {
  if (formula.tag === "iff") return { tag: "imp",
    left: backward ? formula.right : formula.left, right: backward ? formula.left : formula.right };
  if (formula.tag === "forall") {
    const body = directionalStatement(formula.body, backward);
    return body ? { ...formula, body } : undefined;
  }
  if (formula.tag === "imp") {
    const right = directionalStatement(formula.right, backward);
    return right ? { ...formula, right } : undefined;
  }
  return undefined;
}

function safeRead(file: string): string | undefined {
  try { return readFileSync(file, "utf8"); } catch { return undefined; }
}

export function runWorkbenchFunction(
  source: string,
  requestedName: string,
  args: readonly bigint[],
  profile: WorkbenchFoundation = "ZFG",
) {
  return runWorkbenchFiles([{ name: "Playground.g17", source }], requestedName, args, profile);
}

export function runWorkbenchFiles(
  files: readonly WorkbenchFile[],
  requestedName: string,
  args: readonly bigint[],
  profile: WorkbenchFoundation = "ZFG",
  entryFiles?: readonly string[],
  options: WorkbenchWorkspaceOptions = {},
) {
  const started = performance.now();
  const { kernel } = loadWorkspace(files, profile, entryFiles, workspaceRoots(options.moduleRoots));
  const names = [...kernel.functions.keys()].filter(name => name === requestedName || name.endsWith(`.${requestedName}`));
  if (names.length === 0) throw new KernelError(`Unknown native function ${requestedName}`);
  if (names.length > 1 && !names.includes(requestedName)) throw new KernelError(`Ambiguous function ${requestedName}; use its qualified name`);
  const name = names.includes(requestedName) ? requestedName : names[0]!;
  const result = callNative(kernel, name, args);
  if (typeof result.value !== "bigint") throw new KernelError("The workbench currently displays natural-number results");
  return {
    ok: true as const,
    function: name,
    args: args.map(String),
    value: String(result.value),
    stats: result.stats,
    milliseconds: Number((performance.now() - started).toFixed(2)),
  };
}

export interface WorkbenchFailureOptions extends WorkbenchWorkspaceOptions {
  /** The workspace files; given, the theorems that completed before the failure are reported as `completed`. */
  readonly files?: readonly WorkbenchFile[];
}

export function workbenchFailure(error: unknown, options: WorkbenchFailureOptions = {}) {
  const message = error instanceof Error ? error.message : String(error);
  const display = error instanceof SurfaceError ? failureDisplays.get(error) ?? plainDisplay : plainDisplay;
  const completed = options.files ? completedTheorems(error, options.files, workspaceRoots(options.moduleRoots)) : [];
  return {
    ok: false as const,
    kind: error instanceof SurfaceError ? "surface" : error instanceof KernelError ? "kernel" : "server",
    // SurfaceError keeps the line in its CLI-facing message. The workbench
    // transports the line separately, so avoid repeating it in the editor and
    // proof-state views.
    message: error instanceof SurfaceError ? message.replace(/^line \d+:\s*/, "") : message,
    ...(error instanceof SurfaceError ? { line: error.line } : {}),
    ...(error instanceof SurfaceError && error.file ? { file: error.file } : {}),
    ...(completed.length ? { completed } : {}),
    ...(error instanceof SurfaceError && error.partialTrace ? {
      trace: {
        initial: displayState(error.partialTrace.initial, display),
        ...(error.partialTrace.scope ? { scope: error.partialTrace.scope } : {}),
        proofMap: error.partialTrace.narrative ?? [],
        steps: error.partialTrace.steps.map((step): WorkbenchStep => ({
          line: step.line,
          columnStart: step.columnStart,
          columnEnd: step.columnEnd,
          command: step.command,
          ...displayInfo(step.info, display),
          before: displayState(step.before, display),
          after: displayState(step.after, display),
        })),
      },
    } : {}),
  };
}

export function theoremRanges(source: string): readonly { lineStart: number; lineEnd: number }[] {
  return declarationRanges(source, false);
}

/**
 * The source ranges of every declaration with a proof block: the theorems,
 * lemmas, and instances of `theoremRanges`, and the definitions whose block
 * holds a `proof` line (a defgraph's codomain proof, a defunique's
 * existence and uniqueness proofs, a definition's result-type proof).
 */
export function proofRanges(source: string): readonly { lineStart: number; lineEnd: number }[] {
  return declarationRanges(source, true);
}

function declarationRanges(source: string, definitions: boolean): readonly { lineStart: number; lineEnd: number }[] {
  const lines = source.split(/\r?\n/);
  // Instances are checked theorems and occupy entries in
  // ElaboratedModule.theorems. They must therefore participate in the same
  // source-order range table or every later proof is paired with its
  // predecessor's trace and appears permanently complete in the Workbench.
  const proof = /^\s*(?:theorem|lemma|instance)\s+\S+/;
  const defined = /^\s*(?:defgraph|defchoose|defunique|def|define)\s+\S+/;
  const boundary = /^\s*(?:noncomputable\s+(?:transfinite|foundation|well-founded)\s+def|datatype|class|defgraph|defchoose|defunique|def|define|predicate|theorem|lemma|instance|eval|notation|tactic|module|import|namespace|section|variable|hypothesis|export\s+open|open|end)\b/;
  const ranges: { lineStart: number; lineEnd: number }[] = [];
  let nextBoundary = lines.length + 1;
  let proofLine = false;
  for (let index = lines.length - 1; index >= 0; index -= 1) {
    const line = lines[index]!;
    if (/^\s*proof\s*(?:--.*)?$/.test(line)) proofLine = true;
    if (proof.test(line) || (definitions && proofLine && defined.test(line))) ranges.push({ lineStart: index + 1, lineEnd: nextBoundary - 1 });
    if (boundary.test(line)) { nextBoundary = index + 1; proofLine = false; }
  }
  return ranges.reverse();
}

// The checked kernel of a workspace, by the digest of its files, so that
// audits and statement queries that follow a check reuse the environment
// instead of loading it again. The incremental loader already keeps the
// dependency checkpoint; this keeps the checked leaf as well.
// Kept with the dependency files their load read, so a kernel whose
// dependency was rewritten on disk since is loaded again rather than reused.
const workspaceKernels = new Map<string, { readonly kernel: ReturnType<typeof createSetTheoryKernel>; readonly stamps: readonly DependencyStamp[] }>();
const maximumWorkspaceKernels = 4;

function workspaceKernel(
  files: readonly WorkbenchFile[], profile: WorkbenchFoundation, entryFiles: readonly string[] | undefined, roots: WorkspaceRoots,
): ReturnType<typeof createSetTheoryKernel> {
  const key = sha256Hex(JSON.stringify([files, entryFiles ?? null, profile, roots.key]));
  const known = workspaceKernels.get(key);
  if (known) {
    workspaceKernels.delete(key);
    if (pinnedDependencies || dependencyStampsCurrent(known.stamps)) {
      workspaceKernels.set(key, known);
      return known.kernel;
    }
  }
  beginDependencyReads();
  let kernel: ReturnType<typeof createSetTheoryKernel>;
  let stamps: readonly DependencyStamp[];
  try { kernel = loadWorkspace(files, profile, entryFiles, roots).kernel; }
  finally { stamps = endDependencyReads(); }
  workspaceKernels.set(key, { kernel, stamps });
  while (workspaceKernels.size > maximumWorkspaceKernels) workspaceKernels.delete(workspaceKernels.keys().next().value!);
  return kernel;
}

/** Audit only the requested theorem, without proof-DAG rendering. */
export function auditWorkbenchTheorem(files: readonly WorkbenchFile[], name: string,
  profile: WorkbenchFoundation = "ZFG", entryFiles?: readonly string[], options: WorkbenchWorkspaceOptions = {}) {
  const kernel = workspaceKernel(files, profile, entryFiles, workspaceRoots(options.moduleRoots));
  return { ok: true as const, ...auditTheoremAxioms(kernel, name) };
}

/** Audit several theorems over one loaded environment. */
export function auditWorkbenchTheorems(files: readonly WorkbenchFile[], names: readonly string[],
  profile: WorkbenchFoundation = "ZFG", entryFiles?: readonly string[], options: WorkbenchWorkspaceOptions = {}) {
  const kernel = workspaceKernel(files, profile, entryFiles, workspaceRoots(options.moduleRoots));
  return { ok: true as const, audits: names.map(name => auditTheoremAxioms(kernel, name)) };
}

/** What a symbol of an elaborated statement is in the checked environment. */
export interface WorkbenchSymbolKind {
  readonly kind: "function" | "predicate" | "definition" | "class" | "datatype";
  readonly arity?: number;
}

/**
 * A theorem's elaborated statement with the printers of its environment:
 * `print` prints as the goal pane prints, `canonical` prints every symbol by
 * its full name and no notation. The name may be a suffix of the full name.
 */
export function describeWorkbenchStatement(files: readonly WorkbenchFile[], theorem: string,
  profile: WorkbenchFoundation = "ZFG", entryFiles?: readonly string[], options: WorkbenchWorkspaceOptions = {}) {
  const kernel = workspaceKernel(files, profile, entryFiles, workspaceRoots(options.moduleRoots));
  const name = kernel.theorems.has(theorem) ? theorem : [...kernel.theorems.keys()].find(item => item.endsWith(`.${theorem}`));
  if (!name) return undefined;
  const symbolNames = [...new Set([...kernel.functions.keys(), ...kernel.predicates.keys()])];
  const shortNames = shortestUniqueNames(symbolNames, symbolSignature(kernel));
  const notations = notationReport(kernel);
  const tactics = kernel.theoremTacticTraces.get(name);
  const print = formulaDisplay(kernel, shortNames, notations, tactics?.rings, tactics?.operations, tactics?.predicates, tactics?.functors, tactics?.carriers, tactics?.functions);
  const classes = new Set(classReport(kernel).map(item => item.name));
  const symbolKind = (symbol: string): WorkbenchSymbolKind | undefined => {
    if (classes.has(symbol)) return { kind: "class", arity: kernel.predicates.get(symbol) };
    if (kernel.datatypes.has(symbol)) return { kind: "datatype" };
    if (kernel.definitions.has(symbol)) return { kind: "definition", arity: kernel.functions.get(symbol) ?? kernel.predicates.get(symbol) };
    if (kernel.functions.has(symbol)) return { kind: "function", arity: kernel.functions.get(symbol) };
    if (kernel.predicates.has(symbol)) return { kind: "predicate", arity: kernel.predicates.get(symbol) };
    return undefined;
  };
  // The initial goal of the tactic trace is the `shows` clause alone, with
  // every binder and premise already in context.
  const goal = tactics?.initial.goals[0]?.goal;
  return { name, statement: kernel.theorems.get(name)!, ...(goal ? { goal } : {}), print, canonical: plainDisplay, symbolKind };
}

/**
 * A generated fact of a definition, named `<definition>.<property>` as a
 * proof cites it: a datatype's `constructor.c`, `injective.c`,
 * `disjoint.c.d`, or `cases`, or a definition's own equations. The name may
 * be a suffix of the definition's full name. Several matches are returned
 * as candidates and none as an empty list.
 */
export function describeWorkbenchProperty(files: readonly WorkbenchFile[], name: string,
  profile: WorkbenchFoundation = "ZFG", entryFiles?: readonly string[], options: WorkbenchWorkspaceOptions = {}) {
  return kernelProperty(workspaceKernel(files, profile, entryFiles, workspaceRoots(options.moduleRoots)), name);
}

/** The generated property a name denotes in a kernel; see `describeWorkbenchProperty`. */
function kernelProperty(kernel: ReturnType<typeof createSetTheoryKernel>, name: string) {
  const parts = name.split(".");
  const candidates: { readonly definition: string; readonly kind: string; readonly property: string; readonly formula: Formula }[] = [];
  for (let split = parts.length - 1; split >= 1 && candidates.length === 0; split -= 1) {
    const head = parts.slice(0, split).join(".");
    const property = parts.slice(split).join(".");
    for (const [definition, record] of kernel.definitions) {
      const formula = definition === head || definition.endsWith(`.${head}`) ? record.properties.get(property) : undefined;
      if (formula) candidates.push({ definition, kind: record.kind, property, formula });
    }
  }
  if (candidates.length !== 1) return { candidates: candidates.map(item => `${item.definition}.${item.property}`) };
  const found = candidates[0]!;
  const symbolNames = [...new Set([...kernel.functions.keys(), ...kernel.predicates.keys()])];
  const print = formulaDisplay(kernel, shortestUniqueNames(symbolNames, symbolSignature(kernel)), notationReport(kernel));
  return {
    name: `${found.definition}.${found.property}`, definition: found.definition, definitionKind: found.kind, property: found.property,
    statement: print(found.formula), canonical: plainDisplay(found.formula),
  };
}

// Pinned dependency sources: once a session pins, every library or root file
// the incremental loader reads keeps the content first seen, so a request
// does not change its answer while another process edits a dependency.
let pinnedDependencies: Map<string, string> | undefined;

/** Pin or release the dependency sources the incremental loader reads; returns the files pinned so far. */
export function pinWorkbenchDependencies(enabled: boolean): readonly string[] {
  pinnedDependencies = enabled ? pinnedDependencies ?? new Map() : undefined;
  return [...(pinnedDependencies?.keys() ?? [])];
}

/** The pinned dependency files, or undefined when nothing is pinned. */
export function pinnedWorkbenchDependencies(): readonly string[] | undefined {
  return pinnedDependencies ? [...pinnedDependencies.keys()] : undefined;
}

function readDependency(file: string): string | undefined {
  const pinned = pinnedDependencies?.get(file);
  if (pinned !== undefined) return pinned;
  const source = safeRead(file);
  noteDependencyRead(file);
  if (pinnedDependencies && source !== undefined) pinnedDependencies.set(file, source);
  return source;
}
