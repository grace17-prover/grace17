// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// The machine interface: what the Workbench shows, as structured data over a
// stable protocol. Every method calls the functions the Workbench calls, so
// goal states, suggestions, search results, and declarations print exactly
// as the Workbench prints them. `g17 serve` speaks the protocol over stdio as
// newline-delimited JSON; the command line offers each method as a
// subcommand. See docs/machine-interface.md.

import { readdirSync, readFileSync, statSync } from "node:fs";
import { join, relative, resolve } from "node:path";
import { createInterface } from "node:readline";
import type { Formula, Term } from "./ast.ts";
import { KernelError } from "./kernel.ts";
import {
  LibrarySearchWorkspace, moduleDocument, moduleNameOf, parseDeclarationHeader, parseHeaderBinders, scanSearchDeclarations,
  type SearchDeclaration,
} from "./library-search.ts";
import { projectRoot } from "./project-root.ts";
import { sha256Hex } from "./hash.ts";
import { SurfaceError } from "./surface.ts";
import {
  auditWorkbenchTheorem, checkWorkbenchFiles, declarationAtLine, describeWorkbenchProperty, describeWorkbenchStatement,
  pinWorkbenchDependencies, pinnedWorkbenchDependencies, theoremRanges, workbenchFailure,
  type WorkbenchCheckResult, type WorkbenchFile, type WorkbenchFoundation, type WorkbenchState, type WorkbenchStep,
  type WorkbenchStepInfo, type WorkbenchSuggestion, type WorkbenchTheorem,
} from "./workbench.ts";
import { diagnosticSpan, resolveSymbolCandidate, tacticStepAtCursor } from "./workbench-navigation.ts";

/** The protocol version; it changes only when a documented shape changes incompatibly. */
export const MACHINE_PROTOCOL_VERSION = "1";

export const grace17Version: string = (() => {
  try { return String(JSON.parse(readFileSync(join(projectRoot, "package.json"), "utf8")).version); }
  catch { return "unknown"; }
})();

/** A protocol error: a code a program can branch on and a message a person can read. */
export class MachineError extends Error {
  readonly code: string;
  readonly details?: Record<string, unknown>;
  constructor(code: string, message: string, details?: Record<string, unknown>) {
    super(message);
    this.name = "MachineError";
    this.code = code;
    this.details = details;
  }
}

export type MachineId = string | number | null;

export interface MachineRequest {
  readonly id?: MachineId;
  readonly method: string;
  readonly params?: Record<string, unknown>;
}

export interface MachineErrorBody {
  readonly code: string;
  readonly message: string;
  readonly [detail: string]: unknown;
}

export type MachineResponse =
  | { readonly id: MachineId; readonly version: string; readonly ok: true; readonly method: string; readonly result: unknown }
  | { readonly id: MachineId; readonly version: string; readonly ok: false; readonly method?: string; readonly error: MachineErrorBody };

export const MACHINE_METHODS: readonly { readonly name: string; readonly description: string }[] = [
  { name: "capabilities", description: "The protocol version, the Grace17 version, and the methods available." },
  { name: "check", description: "Check a workspace: per-theorem status, the goal state after every step, diagnostics, and on request the axiom audit." },
  { name: "goal", description: "The proof state at a file position, as the Workbench goal pane shows it." },
  { name: "suggest", description: "Run exact?, apply?, or rw? at a position without editing the file, returning each suggestion as structured data." },
  { name: "search", description: "Search library and workspace declarations with the Workbench query language." },
  { name: "declaration", description: "The statement, documentation, module, file, and line of a named declaration, as the hover shows." },
  { name: "signature", description: "A declaration's parameters, premises, and conclusion from its header, in the order at and with lists supply them." },
  { name: "elaborate", description: "Elaborate a written term or formula in a module context and print its kernel form with resolved names." },
  { name: "audit", description: "The axioms a theorem depends on, direct and inherited." },
  { name: "library", description: "The library's modules and their declarations, optionally by area or module." },
  { name: "notations", description: "The notation table and tactic macros in scope for a workspace or module." },
  { name: "pin", description: "Pin the dependency sources this process has read, so later requests keep answering over them." },
];

const FOUNDATIONS: readonly WorkbenchFoundation[] = ["ZF", "ZFC", "ZFG"];

type Params = Record<string, unknown>;

function parameters(value: unknown): Params {
  if (value === undefined || value === null) return {};
  if (typeof value !== "object" || Array.isArray(value)) throw new MachineError("invalid_params", "params must be an object");
  return value as Params;
}

function stringParam(params: Params, name: string): string | undefined {
  const value = params[name];
  if (value === undefined || value === null) return undefined;
  if (typeof value !== "string") throw new MachineError("invalid_params", `${name} must be a string`);
  return value;
}

function requiredString(params: Params, name: string): string {
  const value = stringParam(params, name);
  if (value === undefined || value === "") throw new MachineError("invalid_params", `${name} is required`);
  return value;
}

function stringsParam(params: Params, name: string): readonly string[] | undefined {
  const value = params[name];
  if (value === undefined || value === null) return undefined;
  if (!Array.isArray(value) || !value.every(item => typeof item === "string" && item)) throw new MachineError("invalid_params", `${name} must be an array of names`);
  return value as string[];
}

function integerParam(params: Params, name: string, fallback?: number): number | undefined {
  const value = params[name];
  if (value === undefined || value === null) return fallback;
  if (typeof value !== "number" || !Number.isSafeInteger(value) || value < 1) throw new MachineError("invalid_params", `${name} must be a positive integer`);
  return value;
}

function booleanParam(params: Params, name: string, fallback: boolean): boolean {
  const value = params[name];
  if (value === undefined || value === null) return fallback;
  if (typeof value !== "boolean") throw new MachineError("invalid_params", `${name} must be true or false`);
  return value;
}

function foundationParam(params: Params): WorkbenchFoundation {
  const value = stringParam(params, "foundation") ?? "ZFG";
  if (!FOUNDATIONS.includes(value as WorkbenchFoundation)) throw new MachineError("invalid_params", "foundation must be ZF, ZFC, or ZFG");
  return value as WorkbenchFoundation;
}

function rootsParam(params: Params): readonly string[] | undefined {
  const value = params.moduleRoots;
  if (value === undefined || value === null) return undefined;
  if (!Array.isArray(value) || !value.every(item => typeof item === "string")) throw new MachineError("invalid_params", "moduleRoots must be an array of directories");
  return value as string[];
}

/** Workspace files as given, or read from disk when a file carries no source. */
function filesParam(params: Params, required = true): WorkbenchFile[] {
  const value = params.files;
  if (value === undefined || value === null) {
    if (required) throw new MachineError("invalid_params", "files is required: an array of { name, source? }");
    return [];
  }
  if (!Array.isArray(value) || value.length === 0) throw new MachineError("invalid_params", "files must be a non-empty array of { name, source? }");
  const files = value.map((item, index): WorkbenchFile => {
    const entry = typeof item === "string" ? { name: item } : item;
    if (entry === null || typeof entry !== "object") throw new MachineError("invalid_params", `files[${index}] must be { name, source? }`);
    const name = (entry as Params).name;
    if (typeof name !== "string" || !name || name.includes("\0")) throw new MachineError("invalid_params", `files[${index}] needs a name`);
    const source = (entry as Params).source;
    if (source !== undefined && typeof source !== "string") throw new MachineError("invalid_params", `files[${index}].source must be a string`);
    if (source !== undefined) return { name, source };
    try { return { name, source: readFileSync(resolve(name), "utf8") }; }
    catch { throw new MachineError("unknown_file", `cannot read ${name}`, { file: name }); }
  });
  if (new Set(files.map(file => file.name)).size !== files.length) throw new MachineError("invalid_params", "file names must be distinct");
  return files;
}

interface Workspace {
  readonly files: readonly WorkbenchFile[];
  readonly activeFile: string | undefined;
  readonly entry: readonly string[] | undefined;
  readonly profile: WorkbenchFoundation;
  readonly moduleRoots: readonly string[] | undefined;
}

function workspaceParam(params: Params): Workspace {
  const files = filesParam(params);
  const activeFile = stringParam(params, "activeFile");
  if (activeFile !== undefined && !files.some(file => file.name === activeFile)) {
    throw new MachineError("unknown_file", `activeFile ${activeFile} is not among the files`, { file: activeFile });
  }
  const entry = activeFile ? [activeFile] : files.length === 1 ? [files[0]!.name] : undefined;
  return { files, activeFile, entry, profile: foundationParam(params), moduleRoots: rootsParam(params) };
}

/** A workspace that is one probe file importing a module, or the core prelude alone. */
function moduleWorkspace(params: Params, module: string | undefined): Workspace {
  const files = [{ name: "Probe.g17", source: module ? `module Probe\nimport ${module}\n` : "module Probe\n" }];
  return { files, activeFile: "Probe.g17", entry: ["Probe.g17"], profile: foundationParam(params), moduleRoots: rootsParam(params) };
}

function hasWorkspace(params: Params): boolean {
  return params.files !== undefined && params.files !== null;
}

// Identical workspaces checked again return the same rendering; the kernel
// behind it is cached by checkWorkbenchFiles, this memo only skips the
// presentation work when goal, suggest, and declaration follow a check.
type RawCheck = { readonly ok: true; readonly result: WorkbenchCheckResult } | { readonly ok: false; readonly failure: ReturnType<typeof workbenchFailure> };
const checkMemo = new Map<string, RawCheck>();
const checkMemoLimit = 6;

interface CheckOptions {
  readonly kernel: boolean;
  readonly digest: boolean;
  readonly dependencies: boolean;
}

const plainCheck: CheckOptions = { kernel: false, digest: false, dependencies: false };

const workspaceMemo = new Map<string, RawCheck>();

function workspaceKey(workspace: Workspace): string {
  return sha256Hex(JSON.stringify([workspace.files, workspace.entry ?? null, workspace.profile, workspace.moduleRoots ?? null]));
}

/**
 * The check of a workspace under any options: the symbols, notations, and
 * loaded modules of a checked environment do not depend on them, so a
 * `declaration`, `signature`, or `notations` call after a `check` or `goal`
 * on the same workspace answers from that check.
 */
function rawCheckAny(workspace: Workspace): RawCheck {
  return workspaceMemo.get(workspaceKey(workspace)) ?? rawCheck(workspace, plainCheck);
}

function rawCheck(workspace: Workspace, options: CheckOptions): RawCheck {
  const workspaceDigest = workspaceKey(workspace);
  const key = sha256Hex(JSON.stringify([workspaceDigest, options]));
  const known = checkMemo.get(key);
  if (known) { checkMemo.delete(key); checkMemo.set(key, known); return known; }
  let raw: RawCheck;
  try {
    raw = { ok: true, result: checkWorkbenchFiles(workspace.files, workspace.profile, workspace.entry, {
      includeKernelDetails: options.kernel, includeEnvironmentDigest: options.digest, includeDependencies: options.dependencies,
      includeReports: true, moduleRoots: workspace.moduleRoots,
    }) };
  } catch (error) {
    if (!(error instanceof SurfaceError) && !(error instanceof KernelError)) throw error;
    raw = { ok: false, failure: workbenchFailure(error, { files: workspace.files, moduleRoots: workspace.moduleRoots }) };
  }
  checkMemo.set(key, raw);
  while (checkMemo.size > checkMemoLimit) checkMemo.delete(checkMemo.keys().next().value!);
  workspaceMemo.delete(workspaceDigest);
  workspaceMemo.set(workspaceDigest, raw);
  while (workspaceMemo.size > checkMemoLimit) workspaceMemo.delete(workspaceMemo.keys().next().value!);
  return raw;
}

function checkFailed(raw: RawCheck & { readonly ok: false }, fallbackFile: string | undefined): MachineError {
  const failure = raw.failure;
  return new MachineError("check_failed", failure.message, { file: failure.file ?? fallbackFile, line: failure.line });
}

export interface MachineDiagnostic {
  readonly severity: "error" | "warning";
  readonly kind: string;
  readonly file: string;
  readonly line: number;
  readonly column: number;
  readonly endColumn: number;
  readonly message: string;
  readonly theorem?: string;
}

export type MachineTheoremStatus = "proved" | "admitted" | "failed";

/** The failing declaration's partial trace, presented like a checked theorem. */
function failedTheorem(failure: ReturnType<typeof workbenchFailure>, file: string, source: string, moduleRoots?: readonly string[]) {
  if (!failure.trace || failure.line === undefined) return undefined;
  const declaration = declarationAtLine(file, source, failure.line, { moduleRoots });
  return {
    ...(declaration ? { name: declaration.name, kind: declaration.kind } : {}),
    file,
    lineStart: declaration?.lineStart ?? failure.line,
    lineEnd: declaration?.lineEnd ?? failure.line,
    status: "failed" as const,
    sorries: [],
    proofMap: failure.trace.proofMap,
    initial: failure.trace.initial,
    steps: failure.trace.steps,
  };
}

function failureDiagnostic(failure: ReturnType<typeof workbenchFailure>, file: string, source: string | undefined, theorem?: string): MachineDiagnostic {
  const line = failure.line ?? 1;
  const lineText = source?.split(/\r?\n/)[line - 1];
  const span = diagnosticSpan(lineText, failure.message);
  return {
    severity: "error", kind: failure.kind, file, line, column: span.startColumn, endColumn: span.endColumn,
    message: failure.message, ...(theorem ? { theorem } : {}),
  };
}

function sorryDiagnostic(sorry: WorkbenchCheckResult["sorries"][number]): MachineDiagnostic {
  return {
    severity: "warning", kind: "sorry", file: sorry.file, line: sorry.line, column: 1, endColumn: 1,
    message: `sorry admits ${sorry.goal}`, theorem: sorry.theorem,
  };
}

function stripKernel(theorem: WorkbenchTheorem, keepKernel: boolean) {
  const { kernel, proofNodes, judgments, ...rest } = theorem;
  return keepKernel ? { ...rest, proofNodes, judgments, kernel } : rest;
}

/** The theorems that completed before a failure, presented as a checked file presents them. */
function completedTheorems(failure: ReturnType<typeof workbenchFailure>) {
  return (failure.completed ?? []).map(theorem => ({
    ...stripKernel(theorem, false),
    status: (theorem.sorries.length ? "admitted" : "proved") as MachineTheoremStatus,
  }));
}

/**
 * The `check` result for a workspace already checked, or its failure. A
 * failed check still reports the theorems of the workspace files that
 * completed before the failure, so a position in one of them has a state.
 */
function presentCheck(workspace: Workspace, raw: RawCheck, options: CheckOptions & { readonly audit: boolean; readonly symbols: boolean }) {
  if (!raw.ok) {
    const failure = raw.failure;
    const file = failure.file ?? workspace.activeFile ?? workspace.files[0]!.name;
    const source = workspace.files.find(item => item.name === file)?.source;
    const failed = source !== undefined ? failedTheorem(failure, file, source, workspace.moduleRoots) : undefined;
    const completed = completedTheorems(failure);
    const order = (name: string): number => workspace.files.findIndex(item => item.name === name);
    const theorems = [...completed, ...(failed ? [failed] : [])]
      .sort((left, right) => order(left.file) - order(right.file) || left.lineStart - right.lineStart);
    return {
      status: "failed" as const,
      foundation: { profile: workspace.profile },
      milliseconds: 0,
      files: workspace.files.map(item => ({ name: item.name, status: item.name === file ? "failed" as const : "unchecked" as const })),
      checked: [],
      modules: [],
      notations: [],
      theorems,
      diagnostics: [failureDiagnostic(failure, file, source, failed?.name), ...completed.flatMap(theorem => theorem.sorries.map(sorryDiagnostic))],
      sorries: completed.flatMap(theorem => theorem.sorries),
      evaluations: [],
    };
  }
  return presentCheckedWorkspace(raw.result, {
    kernel: options.kernel, symbols: options.symbols,
    ...(options.audit ? { audit: (name: string) => audit(workspace, name) } : {}),
  });
}

/**
 * The protocol's `check` result for a workspace the Workbench renderer has
 * presented, whichever loader checked it. `audit`, when given, supplies each
 * theorem's axiom audit.
 */
export function presentCheckedWorkspace(result: WorkbenchCheckResult, options: {
  readonly kernel?: boolean; readonly symbols?: boolean; readonly audit?: (theorem: string) => unknown;
} = {}) {
  const theorems = result.theorems.map(theorem => ({
    ...stripKernel(theorem, options.kernel ?? false),
    status: (theorem.sorries.length ? "admitted" : "proved") as MachineTheoremStatus,
    ...(options.audit ? { audit: options.audit(theorem.name) } : {}),
  }));
  const diagnostics: MachineDiagnostic[] = result.sorries.map(sorryDiagnostic);
  const reported = new Set(result.checkedFiles);
  return {
    status: "checked" as const,
    foundation: result.foundationReport ?? { profile: result.foundation },
    context: result.context,
    milliseconds: result.milliseconds,
    ...(result.digest ? { digest: result.digest } : {}),
    files: result.files.map(file => ({
      ...file,
      ...(result.loaded?.find(item => item.file === file.name)?.module ? { module: result.loaded.find(item => item.file === file.name)!.module } : {}),
      status: reported.has(file.name) ? "checked" as const : "context" as const,
    })),
    checked: result.loaded ?? [],
    modules: result.moduleReport ?? [],
    notations: result.notations,
    theorems,
    diagnostics,
    sorries: result.sorries,
    evaluations: result.evaluations,
    ...(options.symbols ? { symbols: result.symbols } : {}),
  };
}

export type MachineCheckResult = ReturnType<typeof presentCheck>;
export type MachineCheckedResult = ReturnType<typeof presentCheckedWorkspace>;

function checkOptions(params: Params): CheckOptions & { readonly audit: boolean; readonly symbols: boolean } {
  return {
    kernel: booleanParam(params, "kernel", false),
    digest: booleanParam(params, "digest", false),
    dependencies: booleanParam(params, "dependencies", true),
    audit: booleanParam(params, "audit", false),
    symbols: booleanParam(params, "symbols", false),
  };
}

function check(params: Params): MachineCheckResult {
  const workspace = workspaceParam(params);
  const options = checkOptions(params);
  return presentCheck(workspace, rawCheck(workspace, options), options);
}

/**
 * The checker's own JSON for a failure (`ok: false`, `kind`, `message`,
 * `line`, `file`, `trace`), extended with the protocol's `status`,
 * `diagnostics`, and `theorems` fields, so one reader serves both. The
 * theorems are those that completed before the failure, then the failed one.
 */
export function machineCheckFailure(error: unknown, files: readonly WorkbenchFile[], moduleRoots?: readonly string[]) {
  const failure = workbenchFailure(error, { files, moduleRoots });
  const file = failure.file ?? files[0]?.name ?? "";
  const source = files.find(item => item.name === file)?.source;
  const failed = source !== undefined ? failedTheorem(failure, file, source, moduleRoots) : undefined;
  const { completed: _completed, ...rest } = failure;
  const completed = completedTheorems(failure);
  return {
    ...rest,
    version: MACHINE_PROTOCOL_VERSION,
    status: "failed" as const,
    theorems: [...completed, ...(failed ? [failed] : [])],
    diagnostics: [failureDiagnostic(failure, file, source, failed?.name), ...completed.flatMap(theorem => theorem.sorries.map(sorryDiagnostic))],
  };
}

/** The theorem whose source range holds a line, in file order, as the Workbench selects it. */
function theoremAt<T extends { readonly file: string; readonly lineStart: number; readonly lineEnd: number; readonly steps?: readonly { readonly line: number }[] }>(
  theorems: readonly T[], file: string, line: number,
): T | undefined {
  const holding = theorems.filter(theorem => theorem.file === file && line >= theorem.lineStart && line <= theorem.lineEnd);
  if (holding.length <= 1) return holding[0];
  // A definition's proof blocks share one source range with the theorems
  // generated from it: the proof whose steps reach the line is the one shown.
  const reach = (theorem: T): number => theorem.steps?.filter(step => step.line <= line).at(-1)?.line ?? -1;
  return holding.reduce((best, theorem) => reach(theorem) > reach(best) ? theorem : best);
}

type MachineTheorem = MachineCheckResult["theorems"][number];

interface Position { readonly file: string; readonly line: number; readonly column: number }

function positionParam(params: Params, workspace: Workspace): Position {
  const file = stringParam(params, "file") ?? workspace.activeFile ?? (workspace.files.length === 1 ? workspace.files[0]!.name : undefined);
  if (!file) throw new MachineError("invalid_params", "file is required when the workspace has several files");
  if (!workspace.files.some(item => item.name === file)) throw new MachineError("unknown_file", `${file} is not among the files`, { file });
  const line = integerParam(params, "line");
  if (line === undefined) throw new MachineError("invalid_params", "line is required");
  return { file, line, column: integerParam(params, "column", 1)! };
}

interface LocatedTheorem {
  readonly name?: string;
  readonly status: MachineTheoremStatus;
  readonly lineStart: number;
  readonly lineEnd: number;
  readonly initial?: WorkbenchState;
  readonly steps: readonly WorkbenchStep[];
  readonly sorries: readonly WorkbenchCheckResult["sorries"][number][];
  readonly diagnostic?: MachineDiagnostic;
}

function errorDiagnostic(checked: MachineCheckResult): MachineDiagnostic | undefined {
  return checked.status === "failed" ? checked.diagnostics.find(item => item.severity === "error") : undefined;
}

function locateTheorem(checked: MachineCheckResult, position: Position): LocatedTheorem | undefined {
  const theorem = theoremAt(checked.theorems as readonly MachineTheorem[], position.file, position.line);
  if (!theorem) return undefined;
  const failed = theorem.status === "failed";
  return {
    ...("name" in theorem && typeof theorem.name === "string" ? { name: theorem.name } : {}),
    status: theorem.status,
    lineStart: theorem.lineStart,
    lineEnd: theorem.lineEnd,
    initial: theorem.initial,
    steps: theorem.steps,
    sorries: theorem.sorries,
    ...(failed ? { diagnostic: errorDiagnostic(checked) } : {}),
  };
}

/**
 * The step that failed in a failed theorem: the last traced step, on the
 * diagnostic's line. A proof that ran out of steps with goals remaining has
 * no failed step; every step of it checked, and a tactic can follow the last.
 */
function failedStepOf(theorem: LocatedTheorem): WorkbenchStep | undefined {
  if (!theorem.diagnostic || /^\d+ goals? remains?\b/.test(theorem.diagnostic.message)) return undefined;
  const last = theorem.steps.at(-1);
  return last && last.line === theorem.diagnostic.line ? last : undefined;
}

/** The error a position cannot be answered from: beyond the failure, or in a workspace whose dependency failed. */
function positionBlocked(checked: MachineCheckResult, position: Position): MachineError | undefined {
  const failure = errorDiagnostic(checked);
  if (!failure) return undefined;
  const where = { file: position.file, line: position.line, failureFile: failure.file, failureLine: failure.line, ...(failure.theorem ? { theorem: failure.theorem } : {}) };
  if (failure.file !== position.file) {
    return new MachineError("dependency_failed", `${failure.file} fails at line ${failure.line}: ${failure.message}`, where);
  }
  if (position.line > failure.line) {
    return new MachineError("after_failure", `line ${position.line} of ${position.file} is after the failure at line ${failure.line}: ${failure.message}; fix that first`, where);
  }
  return undefined;
}

function goal(params: Params) {
  const workspace = workspaceParam(params);
  const position = positionParam(params, workspace);
  const checked = presentCheck(workspace, rawCheck(workspace, checkOptions(params)), { ...checkOptions(params), audit: false, symbols: false });
  const evaluation = checked.evaluations.find(item => item.file === position.file && item.line === position.line);
  if (evaluation) return { ...position, status: checked.status, kind: "evaluation" as const, evaluation };
  const theorem = locateTheorem(checked, position);
  const failure = errorDiagnostic(checked);
  if (!theorem) {
    const blocked = positionBlocked(checked, position);
    return {
      ...position, status: checked.status, kind: "none" as const,
      ...(blocked ? { code: blocked.code } : {}),
      message: blocked?.message ?? "Move the cursor into a theorem proof.",
      ...(failure ? { diagnostic: failure } : {}),
    };
  }
  const step = tacticStepAtCursor(theorem.steps, position.line, position.column);
  const failedStep = failedStepOf(theorem);
  const base = {
    ...position,
    status: checked.status,
    kind: "theorem" as const,
    ...(theorem.name ? { theorem: theorem.name } : {}),
    theoremStatus: theorem.status,
    lineStart: theorem.lineStart,
    lineEnd: theorem.lineEnd,
    ...(theorem.scope ? { scope: theorem.scope } : {}),
  };
  if (failedStep && theorem.diagnostic && position.line > failedStep.line) {
    // Beyond the step that failed nothing was checked; the state where the
    // proof stopped is the one to repair.
    return {
      ...base,
      code: "after_failure" as const,
      step: theorem.steps.length,
      stepLine: failedStep.line,
      command: failedStep.command,
      caption: `After the failure at line ${failedStep.line}`,
      state: failedStep.before,
      complete: false,
      message: `line ${position.line} is after the failure at line ${failedStep.line}: ${theorem.diagnostic.message}; fix that first`,
      sorries: theorem.sorries,
      diagnostic: theorem.diagnostic,
    };
  }
  const stage = step === 0 ? undefined : theorem.steps[step - 1]!;
  const state = stage ? stage.after : theorem.initial;
  const failedStage = theorem.diagnostic !== undefined && step === theorem.steps.length && stage?.line === theorem.diagnostic.line;
  const caption = step === 0 ? "Current goal, at theorem start"
    : failedStage ? `Current position, after line ${stage!.line}` : `Current goal, after line ${stage!.line}`;
  return {
    ...base,
    step,
    ...(stage ? { stepLine: stage.line, command: stage.command } : {}),
    caption,
    state: state ?? null,
    complete: state ? state.goals.length === 0 : false,
    ...(stage?.info ? { info: stage.info } : {}),
    sorries: theorem.sorries,
    ...(theorem.diagnostic ? { diagnostic: theorem.diagnostic } : {}),
  };
}

const QUERY_TACTICS = ["exact?", "apply?", "rw?"] as const;
type QueryTactic = typeof QUERY_TACTICS[number];

function tacticParam(params: Params): QueryTactic {
  const raw = requiredString(params, "tactic").trim();
  const tactic = (raw.endsWith("?") ? raw : `${raw}?`) as QueryTactic;
  if (!QUERY_TACTICS.includes(tactic)) throw new MachineError("invalid_params", "tactic must be exact?, apply?, or rw?");
  return tactic;
}

function indentation(line: string | undefined): string {
  return /^\s*/.exec(line ?? "")?.[0] ?? "";
}

/**
 * Where a query tactic goes so that it runs at the state the `goal` method
 * reports for the position: before the step that follows the cursor's
 * state, after the last step when the cursor is past it, or as the first
 * line of an empty proof block.
 */
function insertionPoint(source: string, theorem: LocatedTheorem, position: Position): { readonly line: number; readonly indent: string } {
  const lines = source.split(/\r?\n/);
  const step = tacticStepAtCursor(theorem.steps, position.line, position.column);
  if (step < theorem.steps.length) {
    const next = theorem.steps[step]!;
    return { line: next.line, indent: indentation(lines[next.line - 1]) };
  }
  if (theorem.steps.length > 0) {
    const last = theorem.steps.at(-1)!;
    let end = last.line;
    for (let index = last.line; index <= Math.min(theorem.lineEnd, lines.length); index += 1) {
      if (lines[index - 1]!.trim()) end = index;
    }
    return { line: end + 1, indent: indentation(lines[last.line - 1]) };
  }
  for (let index = theorem.lineStart; index <= Math.min(theorem.lineEnd, lines.length); index += 1) {
    if (/^\s*proof\b/.test(lines[index - 1]!)) return { line: index + 1, indent: `${indentation(lines[index - 1])}  ` };
  }
  throw new MachineError("no_proof_block", "the theorem at this position has no proof block to search in");
}

function suggest(params: Params) {
  const workspace = workspaceParam(params);
  const position = positionParam(params, workspace);
  const tactic = tacticParam(params);
  const options = { ...checkOptions(params), audit: false, symbols: false };
  const checked = presentCheck(workspace, rawCheck(workspace, options), options);
  const theorem = locateTheorem(checked, position);
  if (!theorem) {
    throw positionBlocked(checked, position)
      ?? new MachineError("no_theorem_at_position", `no theorem holds line ${position.line} of ${position.file}`, { file: position.file, line: position.line });
  }
  const failedStep = failedStepOf(theorem);
  if (failedStep && theorem.diagnostic && tacticStepAtCursor(theorem.steps, position.line, position.column) === theorem.steps.length) {
    throw new MachineError("after_failure", `line ${position.line} of ${position.file} is at or after the failed step at line ${failedStep.line}: ${theorem.diagnostic.message}; fix that first`, {
      file: position.file, line: position.line, failureFile: position.file, failureLine: failedStep.line, ...(theorem.name ? { theorem: theorem.name } : {}),
    });
  }
  const source = workspace.files.find(item => item.name === position.file)!.source;
  const point = insertionPoint(source, theorem, position);
  const lines = source.split(/\r?\n/);
  const text = `${point.indent}${tactic}`;
  const probe = [...lines.slice(0, point.line - 1), text, ...lines.slice(point.line - 1)].join("\n");
  const probeWorkspace: Workspace = { ...workspace, files: workspace.files.map(item => item.name === position.file ? { name: item.name, source: probe } : item) };
  const raw = rawCheck(probeWorkspace, options);
  const isQueryStep = (step: WorkbenchStep): boolean => step.line === point.line && step.command === tactic;
  let step: WorkbenchStep | undefined;
  let message: string | undefined;
  if (raw.ok) {
    step = raw.result.theorems.flatMap(item => item.steps).find(isQueryStep);
  } else {
    // The query ran in the failing theorem's trace, or in a theorem that
    // completed before a failure further down the file.
    step = raw.failure.trace?.steps.find(isQueryStep) ?? raw.failure.completed?.flatMap(item => item.steps).find(isQueryStep);
    // The query tactic itself failed: search found nothing. A failure
    // elsewhere means the proof was broken before the position.
    if (raw.failure.line === point.line && raw.failure.file === position.file) message = raw.failure.message;
    else if (!step) throw checkFailed(raw, position.file);
  }
  const base = {
    ...position, tactic, ...(theorem.name ? { theorem: theorem.name } : {}),
    inserted: { line: point.line, text },
  };
  if (!step || message !== undefined) return { ...base, goal: step?.before ?? null, suggestions: [], items: [], message: message ?? `${tactic} produced no step` };
  const info: WorkbenchStepInfo | undefined = step.info;
  return {
    ...base,
    goal: step.before,
    suggestions: (info?.suggestions ?? []) as readonly WorkbenchSuggestion[],
    items: info?.items ?? [],
    after: step.after,
  };
}

// The standard library as the Workbench bundles it: every .g17 file under
// lib/, keyed by its path from the repository root, read again on each use so
// an edit is visible at once.
const standardLibrary = new Map<string, string>();
let standardLibraryStamp = "";

function walk(directory: string): string[] {
  return readdirSync(directory, { withFileTypes: true }).flatMap(entry =>
    entry.isDirectory() ? walk(join(directory, entry.name)) : entry.name.endsWith(".g17") ? [join(directory, entry.name)] : []);
}

/** The bundled library files by repository-relative path, refreshed from disk. */
export function standardLibraryFiles(): ReadonlyMap<string, string> {
  const root = join(projectRoot, "lib");
  const files = walk(root).sort();
  const stamp = files.map(file => `${file}:${statSync(file).mtimeMs}:${statSync(file).size}`).join("\n");
  if (stamp === standardLibraryStamp) return standardLibrary;
  const keys = new Set<string>();
  for (const file of files) {
    const key = relative(projectRoot, file).replaceAll("\\", "/");
    keys.add(key);
    const source = readFileSync(file, "utf8");
    if (standardLibrary.get(key) !== source) standardLibrary.set(key, source);
  }
  for (const key of [...standardLibrary.keys()]) if (!keys.has(key)) standardLibrary.delete(key);
  standardLibraryStamp = stamp;
  return standardLibrary;
}

let searchWorkspace: LibrarySearchWorkspace | undefined;

function searchIndex(files: readonly WorkbenchFile[]): LibrarySearchWorkspace {
  const library = standardLibraryFiles();
  searchWorkspace ??= new LibrarySearchWorkspace(library);
  for (const file of [...searchWorkspace.index.files.keys()]) {
    if (!library.has(file) && !searchWorkspace.overlays.has(file)) searchWorkspace.index.removeFile(file);
  }
  searchWorkspace.sync(files);
  return searchWorkspace;
}

function search(params: Params) {
  const query = requiredString(params, "query");
  const files = filesParam(params, false);
  const limit = integerParam(params, "limit", 60)!;
  try {
    const result = searchIndex(files).index.search(query, limit);
    return { query, limit, ...result };
  } catch (error) {
    throw new MachineError("bad_query", error instanceof Error ? error.message : String(error));
  }
}

/** The name the checker gives a scanned declaration: its module, then its namespaces, without a repeated module prefix. */
function qualifiedName(record: SearchDeclaration): string {
  const name = record.name.replace(/^_root_\./, "");
  if (record.module === record.file || !record.module) return name;
  if (name === record.module || name.startsWith(`${record.module}.`)) return name;
  if (record.name.startsWith("_root_.")) return name;
  return `${record.module}.${name}`;
}

function sourceRecord(file: string, source: string | undefined, line: number | undefined): SearchDeclaration | undefined {
  if (source === undefined || line === undefined) return undefined;
  return scanSearchDeclarations(file, source).find(record => record.line === line);
}

function libraryOrWorkspaceSource(files: readonly WorkbenchFile[], file: string): string | undefined {
  const open = files.find(item => item.name === file);
  if (open) return open.source;
  const library = standardLibraryFiles();
  const key = relative(projectRoot, resolve(file)).replaceAll("\\", "/");
  if (library.has(key)) return library.get(key);
  try { return readFileSync(resolve(file), "utf8"); } catch { return undefined; }
}

/** The indexed source declarations: the library, with the workspace files overlaid. */
function indexedRecords(files: readonly WorkbenchFile[]): readonly SearchDeclaration[] {
  return [...searchIndex(files).index.records.values()].map(({ text: _text, trigrams: _trigrams, conclusionTokens: _tokens, ...record }) => record);
}

/** The records a written name denotes: by its full name, else by suffix or short name. */
function matchingRecords(records: readonly SearchDeclaration[], name: string): SearchDeclaration[] {
  const exact = records.filter(record => qualifiedName(record) === name);
  if (exact.length) return exact;
  return records.filter(record => record.short === name || record.name === name || qualifiedName(record).endsWith(`.${name}`));
}

/** The source form of a declaration: what the library index knows without elaboration. */
function sourceDeclaration(record: SearchDeclaration) {
  return {
    elaborated: false as const,
    name: qualifiedName(record), short: record.short, kind: record.kind, module: record.module, file: record.file, line: record.line,
    signature: record.signature, conclusion: record.conclusion, documentation: record.documentation, context: record.context,
  };
}

function ambiguous(name: string, matches: readonly SearchDeclaration[]): MachineError {
  return new MachineError("ambiguous_name", `${name} names several declarations`, {
    candidates: matches.map(qualifiedName), modules: [...new Set(matches.map(record => record.module))],
    declarations: matches.map(record => ({ name: qualifiedName(record), module: record.module, file: record.file, line: record.line })),
  });
}

/**
 * The module that declares the longest named prefix of a generated name,
 * such as `Bool` for `Bool.inductive.disjoint.false.true`, when one module
 * declares it alone.
 */
function moduleOfPrefix(records: readonly SearchDeclaration[], name: string): string | undefined {
  return ownerOfGenerated(records, name)?.module;
}

/** The source declaration whose name is the longest named prefix of a generated name, when it is unique. */
function ownerOfGenerated(records: readonly SearchDeclaration[], name: string): SearchDeclaration | undefined {
  const parts = name.split(".");
  for (let length = parts.length - 1; length >= 1; length -= 1) {
    const matches = matchingRecords(records, parts.slice(0, length).join("."));
    const modules = new Set(matches.map(record => record.module));
    if (modules.size === 1) return matches[0];
    if (modules.size > 1) return undefined;
  }
  return undefined;
}

type CheckedEnvironment = WorkbenchCheckResult;
type EnvironmentSymbol = CheckedEnvironment["symbols"][number];

/** The module that declares a full name in a checked environment: the longest loaded module that prefixes it. */
function moduleOfSymbol(environment: CheckedEnvironment, records: readonly SearchDeclaration[], name: string): string | undefined {
  const modules = (environment.loaded ?? []).flatMap(item => item.module ? [item.module] : []);
  const prefix = modules.filter(module => name === module || name.startsWith(`${module}.`)).sort((left, right) => right.length - left.length)[0];
  return prefix ?? records.find(record => qualifiedName(record) === name)?.module;
}

function ambiguousSymbols(environment: CheckedEnvironment, records: readonly SearchDeclaration[], name: string, candidates: readonly EnvironmentSymbol[], what = "declarations"): MachineError {
  const declarations = candidates.map(symbol => {
    const module = moduleOfSymbol(environment, records, symbol.name);
    return { name: symbol.name, ...(module ? { module } : {}), ...(symbol.file ? { file: symbol.file } : {}), ...(symbol.line ? { line: symbol.line } : {}) };
  });
  return new MachineError("ambiguous_name", `${name} names several ${what}`, {
    candidates: declarations.map(item => item.name),
    modules: [...new Set(declarations.flatMap(item => item.module ? [item.module] : []))],
    declarations,
  });
}

/** The hover's answer for a symbol of a checked environment. */
function describeSymbol(symbol: EnvironmentSymbol, files: readonly WorkbenchFile[]) {
  const record = symbol.file ? sourceRecord(symbol.file, libraryOrWorkspaceSource(files, symbol.file), symbol.line) : undefined;
  return {
    elaborated: true as const,
    name: symbol.name, short: symbol.short, kind: record?.kind === "instance" ? "instance" : symbol.kind, info: symbol.info,
    ...(record ? { module: record.module } : {}),
    ...(symbol.file ? { file: symbol.file } : {}),
    ...(symbol.line ? { line: symbol.line } : {}),
    ...("signature" in symbol && symbol.signature ? { signature: symbol.signature } : {}),
    ...(record ? { signature: record.signature, conclusion: record.conclusion, context: record.context } : {}),
    ...("statement" in symbol && symbol.statement ? { statement: symbol.statement } : {}),
    ...("documentation" in symbol && symbol.documentation ? { documentation: symbol.documentation } : record?.documentation ? { documentation: record.documentation } : {}),
    ...("directions" in symbol && symbol.directions ? { directions: symbol.directions } : {}),
  };
}

/**
 * A name resolved in a checked environment as the hover resolves it: a
 * declared symbol, or a generated fact of a definition's kernel record.
 * Undefined when the environment has no such name; an error when several.
 */
function resolveInEnvironment(workspace: Workspace, environment: CheckedEnvironment, name: string, files: readonly WorkbenchFile[], records: readonly SearchDeclaration[], contextModule: string | undefined) {
  const symbols = environment.symbols;
  const symbol = resolveSymbolCandidate(symbols, name, { module: contextModule, file: workspace.activeFile });
  if (symbol) return describeSymbol(symbol, files);
  const candidates = symbols.filter(item => item.short === name || item.name.endsWith(`.${name}`));
  if (candidates.length) throw ambiguousSymbols(environment, records, name, candidates);
  // A generated fact of a definition, such as a datatype's
  // disjoint.false.true, lives on the definition's record in the kernel.
  const property = describeWorkbenchProperty(workspace.files, name, workspace.profile, workspace.entry, { moduleRoots: workspace.moduleRoots });
  if ("candidates" in property && property.candidates.length > 1) throw new MachineError("ambiguous_name", `${name} names several generated facts`, { candidates: property.candidates });
  if (!("name" in property)) return undefined;
  const owner = resolveSymbolCandidate(symbols, property.definition) ?? resolveSymbolCandidate(symbols, property.definition.replace(/\.inductive$/, ""));
  const ownerRecord = owner?.file ? sourceRecord(owner.file, libraryOrWorkspaceSource(files, owner.file), owner.line) : undefined;
  return {
    elaborated: true as const, generated: true as const,
    name: property.name, short: property.property, kind: "property", info: property.statement, statement: property.statement,
    canonical: property.canonical, definition: property.definition, definitionKind: property.definitionKind, property: property.property,
    ...(ownerRecord ? { module: ownerRecord.module } : {}),
    ...(owner?.file ? { file: owner.file } : {}),
    ...(owner?.line ? { line: owner.line } : {}),
  };
}

function declaration(params: Params) {
  const name = requiredString(params, "name");
  const module = stringParam(params, "module");
  const files = hasWorkspace(params) ? filesParam(params) : [];
  const records = indexedRecords(files);
  if (!hasWorkspace(params) && !module) {
    const matches = matchingRecords(records, name);
    if (matches.length === 1) return sourceDeclaration(matches[0]!);
    if (matches.length > 1) throw ambiguous(name, matches);
    // No source declaration: a generated name, resolved in the environment
    // of the module that declares its longest named prefix.
    const prefix = moduleOfPrefix(records, name);
    if (!prefix) throw new MachineError("unknown_declaration", `no library declaration named ${name}`);
    const workspace = moduleWorkspace(params, prefix);
    const raw = rawCheckAny(workspace);
    if (!raw.ok) throw checkFailed(raw, workspace.activeFile);
    const resolved = resolveInEnvironment(workspace, raw.result, name, files, records, prefix);
    if (!resolved) throw new MachineError("unknown_declaration", `no declaration named ${name}; its prefix is declared in ${prefix}`, { import: prefix });
    return resolved;
  }
  const workspace: Workspace = hasWorkspace(params) ? {
    files, activeFile: stringParam(params, "activeFile"),
    entry: stringParam(params, "activeFile") ? [stringParam(params, "activeFile")!] : files.length === 1 ? [files[0]!.name] : undefined,
    profile: foundationParam(params), moduleRoots: rootsParam(params),
  } : moduleWorkspace(params, module);
  const raw = rawCheckAny(workspace);
  if (!raw.ok) throw checkFailed(raw, workspace.activeFile);
  // A short name resolves as the module's own code resolves it: the
  // module's declarations before those its imports reach.
  const active = workspace.files.find(item => item.name === workspace.activeFile);
  const contextModule = module ?? (active ? moduleNameOf(active.source, active.name) : undefined);
  const resolved = resolveInEnvironment(workspace, raw.result, name, files, records, contextModule);
  if (resolved) return resolved;
  // Not in this environment: say which module declares it, so the caller
  // can import it, and give the source form meanwhile.
  const outside = matchingRecords(records, name);
  if (outside.length === 1) {
    const record = outside[0]!;
    return { ...sourceDeclaration(record), inScope: false, import: record.module, message: `${name} is not in this environment; import ${record.module}` };
  }
  if (outside.length > 1) throw ambiguous(name, outside);
  // A generated name of a definition outside the environment: resolve it
  // where its prefix is declared, and say so.
  const hint = moduleOfPrefix(records, name);
  if (!hint) throw new MachineError("unknown_declaration", `no declaration named ${name} in this environment`);
  const elsewhere = moduleWorkspace(params, hint);
  const there = rawCheckAny(elsewhere);
  const found = there.ok ? resolveInEnvironment(elsewhere, there.result, name, [], records, hint) : undefined;
  if (found) return { ...found, inScope: false, import: hint, message: `${name} is not in this environment; import ${hint}` };
  throw new MachineError("unknown_declaration", `no declaration named ${name} in this environment; its prefix is declared in ${hint}`, { import: hint });
}

/**
 * A declaration's header as data: the parameters in quantification order,
 * the premises in the order a `with` list supplies them, and the conclusion,
 * read from the source so a file that does not yet check still answers.
 * With `elaborate: true` and a workspace or module, the kernel statement is
 * added when the environment checks.
 */
function signature(params: Params) {
  const name = requiredString(params, "name");
  const module = stringParam(params, "module");
  const files = hasWorkspace(params) ? filesParam(params) : [];
  const records = indexedRecords(files);
  const open = new Set(files.map(file => file.name));
  const all = matchingRecords(records, name);
  let matches = all.some(record => open.has(record.file)) ? all.filter(record => open.has(record.file)) : all;
  if (matches.length === 0) return generatedSignature(params, name, module, files, records);
  if (matches.length > 1 && module) {
    // The module's own declaration, else the one its imports reach.
    const own = matches.filter(record => record.module === module);
    if (own.length === 1) matches = own;
    else {
      const raw = rawCheckAny(moduleWorkspace(params, module));
      if (raw.ok) {
        const visible = new Set(raw.result.symbols.map(symbol => symbol.name));
        const reached = matches.filter(record => visible.has(qualifiedName(record)));
        if (reached.length === 1) matches = reached;
      }
    }
  }
  if (matches.length > 1) throw ambiguous(name, matches);
  const record = matches[0]!;
  const header = parseDeclarationHeader(record);
  const base = {
    name: qualifiedName(record), short: record.short, kind: record.kind, module: record.module, file: record.file, line: record.line,
    parameters: header.parameters,
    premises: header.premises,
    conclusion: header.conclusion,
    rings: header.rings,
    positional: { at: header.parameters.map(item => item.name), with: header.premises.map(item => item.name ?? null) },
    signature: record.signature,
    context: record.context,
    documentation: record.documentation,
  };
  if (!booleanParam(params, "elaborate", false)) return { ...base, elaborated: false };
  const workspace: Workspace = hasWorkspace(params) ? workspaceParam(params) : moduleWorkspace(params, module ?? record.module);
  const raw = rawCheckAny(workspace);
  if (!raw.ok) {
    const failure = raw.failure;
    return { ...base, elaborated: false, checkFailed: { file: failure.file ?? workspace.activeFile, line: failure.line, message: failure.message } };
  }
  const symbol = resolveSymbolCandidate(raw.result.symbols, base.name) ?? resolveSymbolCandidate(raw.result.symbols, record.name);
  const statement = symbol && "statement" in symbol ? symbol.statement : undefined;
  return { ...base, elaborated: statement !== undefined, ...(statement ? { statement, fullName: symbol!.name } : {}) };
}

/**
 * The signature of a generated theorem of a definition record, such as a
 * defgraph's `ident.value` or `ident.closed`, read from its elaborated
 * statement: the leading universal binders are its parameters, the
 * antecedents its premises, and the rest its conclusion. A typing premise
 * `Nat(n)` or `Real(x)` on a binder is that binder's type.
 */
function generatedSignature(params: Params, name: string, module: string | undefined, files: readonly WorkbenchFile[], records: readonly SearchDeclaration[]) {
  const owner = ownerOfGenerated(records, name);
  if (!owner) throw new MachineError("unknown_declaration", `no declaration named ${name}`);
  const workspace: Workspace = hasWorkspace(params) ? workspaceParam(params) : moduleWorkspace(params, module ?? owner.module);
  const raw = rawCheckAny(workspace);
  if (!raw.ok) throw checkFailed(raw, workspace.activeFile);
  const symbol = resolveSymbolCandidate(raw.result.symbols, name, { module: module ?? owner.module });
  if (!symbol) {
    const candidates = raw.result.symbols.filter(item => item.short === name || item.name.endsWith(`.${name}`));
    if (candidates.length) throw ambiguousSymbols(raw.result, records, name, candidates);
    throw new MachineError("unknown_declaration", `no declaration named ${name}; its prefix is declared in ${owner.module}`, { import: owner.module });
  }
  const described = describeWorkbenchStatement(workspace.files, symbol.name, workspace.profile, workspace.entry, { moduleRoots: workspace.moduleRoots });
  if (!described) throw new MachineError("unknown_declaration", `${symbol.name} is not a theorem of this environment`);
  const parameters: { name: string; type: string; binder: "explicit"; source: "declaration" }[] = [];
  const premises: { formula: string; source: "declaration" }[] = [];
  let node: Formula = described.statement;
  for (;;) {
    if (node.tag === "forall") { parameters.push({ name: node.variable, type: "Set", binder: "explicit", source: "declaration" }); node = node.body; continue; }
    if (node.tag !== "imp") break;
    const printed = described.print(node.left);
    const typing = /^(Nat|Real)\((\S+)\)$/.exec(printed);
    const typed = typing ? parameters.find(item => item.name === typing[2] && item.type === "Set") : undefined;
    if (typed) typed.type = typing![1]!;
    else premises.push({ formula: printed, source: "declaration" });
    node = node.right;
  }
  const statement = described.print(described.statement);
  return {
    name: symbol.name, short: symbol.name.slice(symbol.name.lastIndexOf(".") + 1), kind: "theorem", generated: true,
    definition: qualifiedName(owner), module: owner.module, file: owner.file, line: owner.line,
    parameters, premises, conclusion: described.print(node), rings: [],
    positional: { at: parameters.map(item => item.name), with: premises.map(() => null) },
    signature: statement, context: "", documentation: "", elaborated: true, statement, fullName: symbol.name,
  };
}

const PROBE_THEOREM = "g17probe.elaborate";

/**
 * The prefix of a file in which a probe theorem can stand at a line: the
 * lines before the declaration holding the line, with every proof before it
 * replaced by `sorry` (the definitions, notations, and section scope are
 * what the probe needs; the proofs are not), and the `end` lines that close
 * the sections and namespaces still open there.
 */
function probePrefix(source: string, line: number | undefined): { readonly lines: string[]; readonly line: number; readonly closers: string[] } {
  const lines = source.split(/\r?\n/);
  let at = Math.min(line ?? lines.length + 1, lines.length + 1);
  const ranges = theoremRanges(source);
  const holder = ranges.find(range => at >= range.lineStart && at <= range.lineEnd);
  if (holder) at = holder.lineStart;
  const kept = lines.slice(0, at - 1);
  for (const range of ranges) {
    if (range.lineEnd >= at) continue;
    let proofLine = -1;
    for (let index = range.lineStart; index <= range.lineEnd; index += 1) {
      if (/^\s*proof\s*(?:--.*)?$/.test(lines[index - 1]!)) { proofLine = index; break; }
    }
    if (proofLine < 0 || proofLine >= range.lineEnd) continue;
    for (let index = proofLine + 1; index <= range.lineEnd; index += 1) kept[index - 1] = "";
    kept[proofLine] = `${indentation(lines[proofLine - 1])}  sorry`;
  }
  let depth = 0;
  for (const text of kept) {
    const code = text.replace(/--.*$/, "");
    if (/^\s*(?:section|namespace)\b/.test(code)) depth += 1;
    else if (/^\s*end(?:\s|$)/.test(code)) depth = Math.max(0, depth - 1);
  }
  return { lines: kept, line: at, closers: Array.from({ length: depth }, () => "end") };
}

/** The function and predicate symbols a formula or term mentions, in first-use order. */
function symbolsOf(node: Formula | Term, found = new Map<string, "function" | "predicate">()): Map<string, "function" | "predicate"> {
  switch (node.tag) {
    case "var": case "nat": case "bottom": break;
    case "app": found.set(node.fn, "function"); node.args.forEach(argument => symbolsOf(argument, found)); break;
    case "pred": found.set(node.pred, "predicate"); node.args.forEach(argument => symbolsOf(argument, found)); break;
    case "eq": symbolsOf(node.left, found); symbolsOf(node.right, found); break;
    case "imp": case "and": case "or": case "iff": symbolsOf(node.left, found); symbolsOf(node.right, found); break;
    case "forall": case "exists": symbolsOf(node.body, found); break;
  }
  return found;
}

/**
 * Elaborate a written term or formula where a module reads it. The text
 * becomes the `shows` clause of a probe theorem admitted with `sorry`, placed
 * at the position in a copy of the file (or in a probe file importing the
 * module), and the kernel's statement is read back and printed both as the
 * goal pane prints it and with every symbol's full name.
 */
function elaborate(params: Params) {
  const text = requiredString(params, "text").trim();
  const requested = stringParam(params, "kind") ?? "auto";
  if (!["auto", "formula", "term"].includes(requested)) throw new MachineError("invalid_params", "kind must be formula, term, or auto");
  const variables = (stringParam(params, "variables") ?? "").trim();
  if (variables && parseHeaderBinders(variables, "declaration").rest) throw new MachineError("invalid_params", "variables must be binder groups such as (x y : Set)");
  const binderCount = variables ? parseHeaderBinders(variables, "declaration").parameters.length : 0;
  const module = stringParam(params, "module");
  let workspace: Workspace;
  let file: string;
  let prefix: ReturnType<typeof probePrefix>;
  let context: Record<string, unknown>;
  if (hasWorkspace(params)) {
    workspace = workspaceParam(params);
    file = stringParam(params, "file") ?? workspace.activeFile ?? (workspace.files.length === 1 ? workspace.files[0]!.name : "");
    if (!file) throw new MachineError("invalid_params", "file is required when the workspace has several files");
    const source = workspace.files.find(item => item.name === file)?.source;
    if (source === undefined) throw new MachineError("unknown_file", `${file} is not among the files`, { file });
    const line = integerParam(params, "line");
    prefix = probePrefix(source, line);
    context = { file, line: prefix.line };
  } else {
    workspace = moduleWorkspace(params, module);
    file = "Probe.g17";
    prefix = probePrefix(workspace.files[0]!.source, undefined);
    context = module ? { module } : {};
  }
  const attempt = (kind: "formula" | "term"): { readonly raw: RawCheck; readonly files: readonly WorkbenchFile[] } => {
    const shows = kind === "formula" ? text : `${text} = ${text}`;
    const probe = [...prefix.lines, `theorem ${PROBE_THEOREM}${variables ? ` ${variables}` : ""}`, `  shows ${shows}`, "proof", "  sorry", ...prefix.closers].join("\n");
    const files = workspace.files.map(item => item.name === file ? { name: file, source: probe } : item);
    return { raw: rawCheck({ ...workspace, files, activeFile: file, entry: [file] }, plainCheck), files };
  };
  const kinds: ("formula" | "term")[] = requested === "auto" ? ["formula", "term"] : [requested as "formula" | "term"];
  let last: { readonly raw: RawCheck & { readonly ok: false }; readonly kind: "formula" | "term" } | undefined;
  for (const kind of kinds) {
    const { raw, files } = attempt(kind);
    if (!raw.ok) {
      const inProbe = (raw.failure.file ?? file) === file && raw.failure.line !== undefined && raw.failure.line >= prefix.line;
      if (!inProbe) throw checkFailed(raw, file);
      last = { raw, kind };
      continue;
    }
    const described = describeWorkbenchStatement(files, PROBE_THEOREM, workspace.profile, [file], { moduleRoots: workspace.moduleRoots });
    if (!described) throw new MachineError("internal", "the probe theorem was not elaborated");
    // The trace's initial goal is the shows clause itself; without a trace,
    // strip the binders of the variables from the statement.
    let formula: Formula = described.goal ?? described.statement;
    if (!described.goal) for (let index = 0; index < binderCount && formula.tag === "forall"; index += 1) formula = formula.body;
    const node: Formula | Term = kind === "term" && formula.tag === "eq" ? formula.left : formula;
    const printed = node.tag === "var" || node.tag === "nat" || node.tag === "app" ? described.print.term(node) : described.print(node);
    const canonical = node.tag === "var" || node.tag === "nat" || node.tag === "app" ? described.canonical.term(node) : described.canonical(node);
    const symbols = [...symbolsOf(node)].map(([name, use]) => ({ name, ...(described.symbolKind(name) ?? { kind: use }) }));
    return { text, kind, ...context, ...(variables ? { variables } : {}), printed, canonical, symbols };
  }
  const failure = last!.raw.failure;
  throw new MachineError("elaboration_failed", `${text} does not elaborate as a ${requested === "auto" ? "formula or term" : last!.kind}: ${failure.message}`, {
    ...context, text, kind: last!.kind,
  });
}

function audit(workspace: Workspace, theorem: string) {
  try {
    const { ok: _ok, ...report } = auditWorkbenchTheorem(workspace.files, theorem, workspace.profile, workspace.entry, { moduleRoots: workspace.moduleRoots });
    return report;
  } catch (error) {
    throw auditError(error, theorem);
  }
}

function auditError(error: unknown, theorem: string): unknown {
  if (error instanceof SurfaceError) return new MachineError("check_failed", workbenchFailure(error).message, { file: error.file, line: error.line });
  const message = error instanceof Error ? error.message : String(error);
  if (/unknown|not found|no theorem/i.test(message)) return new MachineError("unknown_theorem", message, { theorem });
  return error;
}

function auditMethod(params: Params) {
  const workspace = workspaceParam(params);
  const names = stringsParam(params, "theorems");
  if (names) {
    // One environment, one entry per name in order; a name the environment
    // does not hold is an error entry, not a failure of the whole call.
    const audits = names.map(theorem => {
      try { return audit(workspace, theorem); }
      catch (error) {
        if (error instanceof MachineError && error.code === "unknown_theorem") return { theorem, error: { code: error.code, message: error.message } };
        throw error;
      }
    });
    return { foundation: workspace.profile, audits };
  }
  const theorem = requiredString(params, "theorem");
  return { foundation: workspace.profile, ...audit(workspace, theorem) };
}

function areaOf(key: string): string {
  const parts = key.split("/");
  if (parts[1] !== "Grace") return parts[1]?.replace(/\.g17$/, "") ?? "";
  const under = parts[2]!.replace(/\.g17$/, "");
  if (under === "Cumulus" && parts.length > 4) return parts[3]!.replace(/\.g17$/, "");
  return under;
}

function library(params: Params) {
  const area = stringParam(params, "area");
  const module = stringParam(params, "module");
  const includeDeclarations = booleanParam(params, "declarations", Boolean(area || module));
  const modules = [...standardLibraryFiles()].map(([file, source]) => {
    const document = moduleDocument(file, source);
    return { file, source, area: areaOf(file), module: document?.module, header: document?.header ?? "", line: document?.line };
  }).filter(item => (!area || item.area === area) && (!module || item.module === module || item.module?.startsWith(`${module}.`)));
  if (module && modules.length === 0) throw new MachineError("unknown_module", `no library module named ${module}`, { module });
  const areas = new Map<string, { name: string; modules: number; declarations: number }>();
  const described = modules.map(item => {
    const declarations = scanSearchDeclarations(item.file, item.source).map(({ file: _file, module: _module, ...record }) => record);
    const summary = areas.get(item.area) ?? { name: item.area, modules: 0, declarations: 0 };
    summary.modules += 1;
    summary.declarations += declarations.length;
    areas.set(item.area, summary);
    return {
      ...(item.module ? { module: item.module } : {}),
      file: item.file, area: item.area, header: item.header,
      ...(item.line ? { line: item.line } : {}),
      declarationCount: declarations.length,
      ...(includeDeclarations ? { declarations } : {}),
    };
  });
  return { ...(area ? { area } : {}), ...(module ? { module } : {}), areas: [...areas.values()], modules: described };
}

function notations(params: Params) {
  const module = stringParam(params, "module");
  const workspace: Workspace = hasWorkspace(params) ? {
    files: filesParam(params), activeFile: stringParam(params, "activeFile"),
    entry: stringParam(params, "activeFile") ? [stringParam(params, "activeFile")!] : undefined,
    profile: foundationParam(params), moduleRoots: rootsParam(params),
  } : moduleWorkspace(params, module);
  const single = workspace.entry ?? (workspace.files.length === 1 ? [workspace.files[0]!.name] : undefined);
  const raw = rawCheckAny({ ...workspace, entry: single });
  if (!raw.ok) throw checkFailed(raw, workspace.activeFile);
  return { ...(module ? { module } : {}), foundation: workspace.profile, notations: raw.result.notations, tactics: raw.result.tactics };
}

function pin(params: Params) {
  const enabled = booleanParam(params, "enabled", true);
  const files = pinWorkbenchDependencies(enabled);
  return { pinned: enabled, files };
}

function capabilities() {
  return {
    protocol: MACHINE_PROTOCOL_VERSION, grace17: grace17Version, methods: MACHINE_METHODS, foundations: FOUNDATIONS,
    ...(pinnedWorkbenchDependencies() ? { pinned: true } : {}),
  };
}

const handlers: Record<string, (params: Params) => unknown> = {
  capabilities, check, goal, suggest, search, declaration, signature, elaborate, audit: auditMethod, library, notations, pin,
};

/** Run one method; errors are thrown as MachineError. */
export function callMachineMethod(method: string, params: unknown = {}): unknown {
  const handler = Object.hasOwn(handlers, method) ? handlers[method] : undefined;
  if (!handler) throw new MachineError("unknown_method", `unknown method ${method}; see capabilities`);
  return handler(parameters(params));
}

/** The error object of a protocol response for any error a method throws. */
export function machineErrorBody(error: unknown): MachineErrorBody {
  if (error instanceof MachineError) return { code: error.code, message: error.message, ...(error.details ?? {}) };
  if (error instanceof SurfaceError) return { code: "surface", message: error.message, line: error.line, ...(error.file ? { file: error.file } : {}) };
  if (error instanceof KernelError) return { code: "kernel", message: error.message };
  return { code: "internal", message: error instanceof Error ? error.message : String(error) };
}

/** Answer one request object; never throws, never includes a stack trace. */
export function handleMachineRequest(request: unknown): MachineResponse {
  const version = MACHINE_PROTOCOL_VERSION;
  if (request === null || typeof request !== "object" || Array.isArray(request)) {
    return { id: null, version, ok: false, error: { code: "invalid_request", message: "a request is a JSON object with id and method" } };
  }
  const { id: rawId, method, params } = request as Partial<MachineRequest>;
  const id: MachineId = typeof rawId === "string" || typeof rawId === "number" ? rawId : null;
  if (typeof method !== "string" || !method) return { id, version, ok: false, error: { code: "invalid_request", message: "method must be a string" } };
  try {
    return { id, version, ok: true, method, result: callMachineMethod(method, params) };
  } catch (error) {
    return { id, version, ok: false, method, error: machineErrorBody(error) };
  }
}

export interface ServeOptions {
  /** Pin every dependency source read during the session to the content first seen. */
  readonly pin?: boolean;
}

/** Serve the protocol: one JSON request per input line, one JSON response per output line. */
export async function serveMachineInterface(input: NodeJS.ReadableStream, output: NodeJS.WritableStream, options: ServeOptions = {}): Promise<void> {
  if (options.pin) pinWorkbenchDependencies(true);
  const lines = createInterface({ input, crlfDelay: Infinity });
  for await (const line of lines) {
    if (!line.trim()) continue;
    let request: unknown;
    try { request = JSON.parse(line); }
    catch (error) {
      output.write(`${JSON.stringify({ id: null, version: MACHINE_PROTOCOL_VERSION, ok: false, error: { code: "invalid_request", message: `malformed JSON: ${error instanceof Error ? error.message : String(error)}` } })}\n`);
      continue;
    }
    output.write(`${JSON.stringify(handleMachineRequest(request))}\n`);
  }
}
