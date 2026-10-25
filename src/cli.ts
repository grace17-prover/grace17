#!/usr/bin/env node
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore


import { existsSync, readFileSync, writeFileSync } from "node:fs";
import { performance } from "node:perf_hooks";
import { resolve } from "node:path";
import {
  auditTheoremAxioms, callNative, compileProofModule, createSetTheoryKernel, encodeProofMachineBinary,
  exportKernelEnvironment, exportTheorem, exportTheoremForMachine, forkSurfaceEnvironment, KernelError, loadModuleGraph, loadModuleSourceGraph,
  moduleNameFromRoots, moduleReport, renderProofHtml, SurfaceError, verifyExportedProof, verifyProofMachineBinary,
  workbenchFailure, rememberFailureDisplay, renderCheckedWorkspace,
  type LoadedModule, type WorkbenchFile,
} from "./index.ts";
import { resolveImportName } from "./module-names.ts";
import {
  callMachineMethod, MACHINE_PROTOCOL_VERSION, MachineError, machineCheckFailure, machineErrorBody, presentCheckedWorkspace, serveMachineInterface,
  shadowedPropertyWarnings, transitiveImportNotes,
} from "./machine-interface.ts";
import { shadowedProperties } from "./workbench.ts";
import { setSurfaceTraceCapture } from "./surface.ts";
import { theoremDependencies } from "./export.ts";
import { buildModuleStore, createStoreKernel, declaredModule, loadModuleStore } from "./module-store.ts";
import { scanModule } from "./module-source-loader.ts";

type Kernel = ReturnType<typeof createSetTheoryKernel>;

/** Run the command line with its arguments; exit status is left in process.exitCode. */
export function runCli(args: readonly string[]): void {
  const command = args[0];
  if (!command || command === "help" || args.includes("--help") || args.includes("-h")) {
    usage(console.log);
    process.exitCode = command ? 0 : 2;
    return;
  }
  const json = args.includes("--json");
  const option = (name: string): string | undefined => {
    const index = args.indexOf(name);
    return index >= 0 ? args[index + 1] : undefined;
  };
  const options = (name: string): string[] => {
    const values: string[] = [];
    for (let index = 0; index < args.length; index += 1) {
      if (args[index] === name && args[index + 1]) values.push(args[index + 1]!);
    }
    return values;
  };
  const optionNames = new Set(["--theorem", "--out", "--machine", "--environment", "--foundation", "--module-root", "--function", "--args", "--artifacts",
    "--line", "--column", "--tactic", "--active", "--limit", "--module", "--area", "--file", "--kind", "--variables"]);
  const flagNames = new Set(["--json", "--text", "--verify", "--audit", "--declarations", "--continue", "--all", "--elaborate", "--pin", "--imports", "--quiet"]);
  const optionNames2 = ["--from"];
  optionNames2.forEach(name => optionNames.add(name));
  const modules: string[] = [];
  for (let index = 1; index < args.length; index += 1) {
    if (optionNames.has(args[index]!)) { index += 1; continue; }
    if (!flagNames.has(args[index]!)) modules.push(args[index]!);
  }

  if (machineCommands.has(command)) {
    runMachineCommand(command, modules, option, options, name => args.includes(name), !args.includes("--text"));
    return;
  }

  if (!["axiom-audit", "build", "check", "run", "export", "view", "compile", "verify-machine"].includes(command) || modules.length === 0) {
    usage(console.error);
    process.exitCode = 2;
  } else {
    let kernel: Kernel | undefined;
    const continuing = command === "check" && (args.includes("--continue") || args.includes("--all"));
    // --quiet keeps the per-module lines off the terminal: the failures and
    // the summary alone are printed, each failure once.
    const quiet = args.includes("--quiet");
    const importAudit = command === "check" && args.includes("--imports");
    let continued: ContinuedCheck | undefined;
    const started = performance.now();
    try {
      const requestedFoundation = option("--foundation") ?? "ZFG";
      if (!["ZF", "ZFC", "ZFG"].includes(requestedFoundation)) {
        throw new Error("--foundation must be ZF, ZFC, or ZFG");
      }
      const profile = requestedFoundation as "ZF" | "ZFC" | "ZFG";
      const requestedRoots = options("--module-root");
      const roots = requestedRoots.length > 0 ? requestedRoots : ["."];
      const store = option("--artifacts");
      if (continuing && store) throw new Error("check --continue elaborates from source; it does not take --artifacts");
      // A store replays its foundation image instead of elaborating the prelude.
      kernel = command === "build" || store ? createStoreKernel(store ?? "build/modules", profile) : createSetTheoryKernel({ profile });
      // The tactic trace of every successful proof serves the Workbench and
      // the machine interface, and `check` reports a failure from them; a
      // compile or an audit needs none, and over the whole library they are
      // a large share of the memory.
      if (["compile", "build", "axiom-audit", "verify-machine"].includes(command)) setSurfaceTraceCapture(kernel, false);
      // With an artifact store, every entry that is a library module under a
      // root is compiled to its artifact once and replayed afterwards; only
      // workspace files outside the roots are elaborated from source each time.
      let checked: readonly LoadedModule[] = [];
      if (command === "build" || store) {
        const storeDirectory = store ?? "build/modules";
        const named = modules.map(entry => entry.endsWith(".g17") ? declaredModule(entry, roots) : entry);
        const library = named.flatMap((name, index) => name && isLibraryFile(modules[index]!, name, roots) ? [name] : []);
        const workspace = modules.filter((entry, index) => !(named[index] && isLibraryFile(entry, named[index]!, roots)));
        if (command === "build" && workspace.length) throw new Error(`build takes library modules under a module root, not ${workspace.join(", ")}`);
        // A workspace file's library imports come from the store too.
        for (const entry of workspace) {
          for (const imported of scanModule(readFileSync(entry, "utf8")).imports) {
            if (!library.includes(imported) && resolvesUnderRoot(imported, roots)) library.push(imported);
          }
        }
        const report = buildModuleStore(library, {
          roots, store: storeDirectory, profile, verify: args.includes("--verify"),
          log: json ? undefined : line => console.log(line),
        });
        if (command === "build") {
          const result = { ok: true, operation: command, store: resolve(storeDirectory), built: report.built, reused: report.reused,
            milliseconds: Number((performance.now() - started).toFixed(3)) };
          if (json) console.log(JSON.stringify(result));
          else console.log(`built ${report.built.length} and reused ${report.reused.length} module artifacts in ${resolve(storeDirectory)}`);
        } else {
          const loaded = loadModuleStore(kernel, library, storeDirectory);
          kernel = loaded.kernel;
          checked = [...loaded.loaded, ...loadModuleGraph(kernel, workspace, roots)];
        }
      } else if (continuing) {
        continued = checkContinuing(kernel, modules, roots, json || quiet ? undefined : line => console.error(line));
        kernel = continued.kernel;
        checked = continued.loaded;
      } else {
        checked = loadModuleGraph(kernel, modules, roots);
      }

      if (command === "axiom-audit") {
        const name = option("--theorem");
        if (!name) throw new Error("axiom-audit requires --theorem <qualified-name>");
        const audit = auditTheoremAxioms(kernel, name);
        const result = { ok: true, operation: command, foundation: requestedFoundation, ...audit };
        if (json) console.log(JSON.stringify(result));
        else {
          console.log(`Axiom audit: ${name} (${audit.complete ? "complete" : "INCOMPLETE"})`);
          console.log(`Direct named axioms: ${audit.direct.join(", ") || "none"}`);
          console.log(`Hereditary named axioms: ${audit.hereditary.join(", ") || "none found"}`);
          for (const axiom of audit.axioms) console.log(`  ${axiom.name}: ${axiom.path.join(" → ")}`);
          console.log(`Definition/schema mechanisms: ${[...new Set(audit.mechanisms.map(m => m.kind))].join(", ") || "none"}`);
          console.log(`Classical double-negation elimination: ${audit.classicalLogic ? "used" : "not used"}`);
          for (const item of audit.unavailable) console.log(`  Unavailable proof: ${item.path.join(" → ")}`);
          console.log("Proof dependency audit; not a claim that these axioms are logically necessary.");
        }
        if (!audit.complete) process.exitCode = 1;
      } else if (command === "run") {
        const fn = option("--function");
        if (!fn) throw new Error("run requires --function <qualified-name>");
        const argumentText = option("--args") ?? "";
        const nativeArgs = argumentText.trim() === "" ? [] : argumentText.split(",").map(item => {
          const trimmed = item.trim();
          if (!/^\d+$/.test(trimmed)) throw new Error("native run arguments must currently be natural numerals");
          return BigInt(trimmed);
        });
        const native = callNative(kernel, fn, nativeArgs);
        if (typeof native.value !== "bigint") throw new Error("native run result is not yet printable as a natural numeral");
        const result = {
          ok: true, operation: command, function: fn, args: nativeArgs.map(String), value: String(native.value),
          stats: native.stats, milliseconds: Number((performance.now() - started).toFixed(3)),
        };
        if (json) console.log(JSON.stringify(result));
        else console.log(`${fn}(${result.args.join(", ")}) = ${result.value} (${result.stats.reductions.toLocaleString()} reductions, ${result.milliseconds.toFixed(1)} ms)`);
      } else if (command === "build") {
        // Reported above.
      } else if (command === "check") {
        const failures = continued?.failures ?? [];
        const skipped = continued?.skipped ?? [];
        if (json) {
          // The protocol's `check` result, rendered by the Workbench renderer
          // over the modules this loader checked; see docs/machine-interface.md.
          const entries = modules.filter(entry => entry.endsWith(".g17")).map(entry => resolve(entry));
          const sources: WorkbenchFile[] = entries.map(name => ({ name, source: readFileSync(name, "utf8") }));
          const rendered = renderCheckedWorkspace(kernel, checked, sources, profile, entries.filter(name => checked.some(item => item.file === name)), {
            includeKernelDetails: false, includeDependencies: true, includeEnvironmentDigest: true, includeReports: true, moduleRoots: roots,
            includeDirectDependencies: importAudit,
          });
          const checkedKernel = kernel;
          const presented = presentCheckedWorkspace(rendered, {
            imports: importAudit,
            ...(args.includes("--audit") ? { audit: (name: string) => auditTheoremAxioms(checkedKernel, name) } : {}),
          });
          // Under --continue every failure is a diagnostic, each with the
          // partial trace of its theorem, and the dependents it blocked are listed.
          const failed = failures.map(item => machineCheckFailure(item.error, [{ name: item.file, source: item.source }], roots));
          const result = {
            ok: failures.length === 0, version: MACHINE_PROTOCOL_VERSION, operation: command, ...presented,
            ...(failures.length ? { status: "failed" as const } : {}),
            diagnostics: [...failed.flatMap(item => item.diagnostics), ...presented.diagnostics],
            theorems: [...presented.theorems, ...failed.flatMap(item => item.theorems)],
            ...(continued ? {
              failures: failures.map((item, index) => ({ module: item.module, file: item.file, ...failed[index]!.diagnostics[0]! })),
              skipped,
            } : {}),
            milliseconds: Number((performance.now() - started).toFixed(3)),
          };
          console.log(JSON.stringify(result));
        } else {
          if (!quiet) {
            for (const item of checked) {
              console.log(`checked ${item.file || item.module || "<unnamed>"}${item.module && item.file ? ` [${item.module}]` : ""} (${item.definitions.length} definitions, ${item.theorems.length} theorems, ${item.evaluations.length} evaluations)`);
              item.evaluations.forEach(evaluation => console.log(`  eval ${evaluation.expression} ⇒ ${evaluation.value} (${evaluation.kind === "proposition" ? "checked proof" : `${evaluation.stats.reductions.toLocaleString()} reductions`})`));
              item.sorries.forEach(sorry => console.log(`  warning: sorry at ${item.file}:${sorry.line} admits ${sorry.axiom}`));
            }
          }
          // The entries' own modules: a theorem restating a generated
          // property under its name is warned about once per module, and
          // with --imports every declaration used through a transitive
          // import is noted.
          const entries = modules.filter(entry => entry.endsWith(".g17")).map(entry => resolve(entry));
          const own = checked.filter(item => entries.includes(item.file));
          for (const warning of shadowedPropertyWarnings(shadowedProperties(kernel, own))) {
            console.log(`warning: ${warning.file}:${warning.line}: ${warning.message}`);
          }
          if (importAudit) {
            const sources: WorkbenchFile[] = entries.map(name => ({ name, source: readFileSync(name, "utf8") }));
            const rendered = renderCheckedWorkspace(kernel, checked, sources, profile, own.map(item => item.file), {
              includeKernelDetails: false, includeDependencies: false, includeEnvironmentDigest: false, includeReports: true, moduleRoots: roots,
              includeDirectDependencies: true,
            });
            const notes = transitiveImportNotes(rendered);
            for (const note of notes) console.log(`note: ${note.file}:${note.line}: ${note.message}`);
            console.log(`${notes.length} transitive-import ${notes.length === 1 ? "note" : "notes"}`);
          }
          if (!quiet) console.log(`foundation ${kernel.foundationReport().profile}; environment ${kernel.digest()}`);
          const sorryCount = checked.reduce((count, item) => count + item.sorries.length, 0);
          if (sorryCount) console.log(`warning: ${sorryCount} ${sorryCount === 1 ? "proof obligation was" : "proof obligations were"} admitted with sorry`);
          // A complete proof that cites an admitted theorem, of this file or
          // an imported module, is dependent: not an obligation of its own,
          // but reported, with the admissions it rests on.
          if ([...kernel.axioms.keys()].some(name => name.startsWith("sorry."))) {
            const inherited = new Map<string, string[]>();
            for (const item of checked) {
              for (const name of item.theorems) {
                const admissions = theoremDependencies(kernel, name).axioms.filter(axiom => axiom.startsWith("sorry.") && !axiom.startsWith(`sorry.${name}.`));
                if (admissions.length) inherited.set(name, admissions);
              }
            }
            if (inherited.size) {
              const admissions = new Set([...inherited.values()].flat());
              console.log(`note: ${inherited.size} complete ${inherited.size === 1 ? "proof depends" : "proofs depend"} on ${admissions.size} ${admissions.size === 1 ? "admission" : "admissions"} elsewhere: ${[...admissions].join(", ")}`);
            }
          }
          if (continued) {
            for (const item of failures) console.log(`failed ${item.file} [${item.module}]: ${failureText(item.error)}`);
            for (const item of skipped) console.log(`skipped ${item.file} [${item.module}]: imports ${item.because}`);
            console.log(`${checked.length} modules checked, ${failures.length} failed, ${skipped.length} skipped`);
          }
        }
        if (failures.length) process.exitCode = 1;
      } else if (command === "compile") {
        const theoremNames = checked.flatMap(item => item.theorems);
        if (theoremNames.length === 0) throw new KernelError("No theorems to compile");
        // Each theorem is exported as it is appended to the tape, and the
        // program is not kept once encoded: the verify pass decodes its own.
        const exports = function* () { for (const name of theoremNames) yield exportTheoremForMachine(kernel, name); };
        const binary = encodeProofMachineBinary(compileProofModule(exports()));
        const verified = verifyProofMachineBinary(kernel, binary);
        const output = resolve(option("--out") ?? "module.g17m");
        writeFileSync(output, binary);
        const environmentOutput = option("--environment");
        if (environmentOutput) writeFileSync(resolve(environmentOutput), `${JSON.stringify(exportKernelEnvironment(kernel), null, 2)}\n`);
        const result = { ok: true, operation: command, output, ...(environmentOutput ? { environment: resolve(environmentOutput) } : {}), bytes: binary.length, ...verified };
        if (json) console.log(JSON.stringify(result));
        else console.log(`compiled ${verified.theorems} theorems → ${output} (${verified.instructions} instructions, ${binary.length} bytes)`);
      } else if (command === "verify-machine") {
        const machinePath = option("--machine");
        if (!machinePath) throw new Error("verify-machine requires --machine <module.g17m>");
        const verified = verifyProofMachineBinary(kernel, readFileSync(resolve(machinePath)));
        const result = { ok: true, operation: command, machine: resolve(machinePath), ...verified };
        if (json) console.log(JSON.stringify(result));
        else console.log(`verified ${verified.theorems} theorems (${verified.instructions} numeric instructions)`);
      } else {
        const theorem = option("--theorem");
        if (!theorem) throw new Error(`${command} requires --theorem <name>`);
        const exported = exportTheorem(kernel, theorem);
        verifyExportedProof(kernel, exported);
        const fallback = `${safeName(theorem)}.${command === "export" ? "g17proof.json" : "html"}`;
        const output = resolve(option("--out") ?? fallback);
        writeFileSync(output, command === "export" ? `${JSON.stringify(exported, null, 2)}\n` : renderProofHtml(exported));
        const result = {
          ok: true,
          operation: command,
          theorem,
          output,
          proofNodes: exported.proof.nodes.length,
          judgmentNodes: exported.trace.nodes.length,
          tacticSteps: exported.tactics?.steps.length ?? 0,
          digest: exported.digest,
        };
        if (json) console.log(JSON.stringify(result));
        else console.log(`${command === "export" ? "exported" : "rendered"} ${theorem} → ${output} (${result.proofNodes} proof nodes, ${result.judgmentNodes} judgments)`);
      }
    } catch (error) {
      const failure = {
        ok: false,
        kind: error instanceof SurfaceError ? "surface" : error instanceof KernelError ? "kernel" : "io",
        message: error instanceof Error ? error.message : String(error),
        ...(error instanceof SurfaceError ? { line: error.line } : {}),
        ...(error instanceof SurfaceError && error.file ? { file: error.file } : {}),
      };
      // A partial tactic trace shows the goals that remain where elaboration
      // stopped, with named hypotheses, so a reader need not reconstruct them.
      if (kernel) rememberFailureDisplay(error, kernel);
      const trace = error instanceof SurfaceError && error.partialTrace ? workbenchFailure(error).trace : undefined;
      if (json && command === "check") {
        // The JSON goes to standard output whatever the outcome, so a
        // redirection captures it; the exit status still says it failed.
        const sources = modules.filter(entry => entry.endsWith(".g17")).flatMap(entry => {
          try { return [{ name: resolve(entry), source: readFileSync(resolve(entry), "utf8") }]; } catch { return []; }
        });
        console.log(JSON.stringify({ ...failure, ...machineCheckFailure(error, sources, options("--module-root")), milliseconds: Number((performance.now() - started).toFixed(3)) }));
      } else if (json) console.error(JSON.stringify(trace ? { ...failure, trace } : failure));
      else {
        console.error(`${failure.kind} error${failure.file ? ` in ${failure.file}` : ""}: ${failure.message}`);
        const state = trace?.steps.at(-1)?.after ?? trace?.initial;
        if (state && state.goals.length > 0) {
          const where = trace?.steps.at(-1) ? `after line ${trace.steps.at(-1)!.line} (${trace.steps.at(-1)!.command})` : "at the start of the proof";
          console.error(`${state.goals.length} goal${state.goals.length === 1 ? " remains" : "s remain"} ${where}:`);
          state.goals.forEach((goal, index) => {
            console.error(`  ${index + 1}. ⊢ ${goal.goal}`);
            for (const local of goal.locals) console.error(`       ${local.name} : ${local.formula}`);
          });
        }
      }
      process.exitCode = 1;
    }
  }
}

function failureText(error: unknown): string {
  const kind = error instanceof SurfaceError ? "surface" : error instanceof KernelError ? "kernel" : "io";
  return `${kind} error: ${error instanceof Error ? error.message : String(error)}`;
}

interface ContinuedCheck {
  readonly kernel: Kernel;
  readonly loaded: readonly LoadedModule[];
  readonly failures: readonly { readonly module: string; readonly file: string; readonly source: string; readonly error: unknown }[];
  readonly skipped: readonly { readonly module: string; readonly file: string; readonly because: string }[];
}

/**
 * Check every module of the entries' import graph, going on past a failure:
 * each module is elaborated in a fork of the kernel, so a failed module
 * leaves nothing behind, and the modules that import a failed or skipped
 * module are skipped and reported with the import that blocked them.
 */
function checkContinuing(initial: Kernel, entries: readonly string[], roots: readonly string[], log?: (line: string) => void): ContinuedCheck {
  const resolvedRoots = roots.map(root => resolve(root));
  const derive = (file: string): string | undefined => moduleNameFromRoots(file, resolvedRoots);
  interface Source { readonly module: string; readonly file: string; readonly source: string; readonly imports: readonly string[] }
  const sources = new Map<string, Source>();
  const libraryFile = (name: string): string | undefined => {
    const relative = `${name.split(".").join("/")}.g17`;
    return resolvedRoots.map(root => resolve(root, relative)).find(candidate => existsSync(candidate));
  };
  const alreadyLoaded = new Set(moduleReport(initial).map(item => item.name));
  const exists = (name: string): boolean => sources.has(name) || alreadyLoaded.has(name) || libraryFile(name) !== undefined;
  const add = (file: string): Source => {
    const source = readFileSync(file, "utf8");
    const metadata = scanModule(source, file, derive);
    const module = metadata.name ?? file;
    const known = sources.get(module);
    if (known) return known;
    const item = { module, file, source, imports: metadata.imports.map(raw => resolveImportName(metadata.name, raw, exists) ?? raw) };
    sources.set(module, item);
    return item;
  };
  // Dependencies before dependents, each module once.
  const ordered: Source[] = [];
  const visited = new Set<string>();
  const visiting = new Set<string>();
  const visit = (item: Source): void => {
    if (visited.has(item.module)) return;
    if (visiting.has(item.module)) throw new SurfaceError(1, `cyclic module import involving ${item.module}`);
    visiting.add(item.module);
    for (const name of item.imports) {
      if (alreadyLoaded.has(name)) continue;
      const file = sources.get(name)?.file ?? libraryFile(name);
      if (!file) throw new SurfaceError(1, `${item.file}: cannot locate imported module ${name} as ${name.split(".").join("/")}.g17`);
      visit(add(file));
    }
    visiting.delete(item.module);
    visited.add(item.module);
    ordered.push(item);
  };
  entries.map(entry => add(resolve(entry))).forEach(visit);

  let kernel = initial;
  const loaded: LoadedModule[] = [];
  const failures: { module: string; file: string; source: string; error: unknown }[] = [];
  const skipped: { module: string; file: string; because: string }[] = [];
  const blocked = new Set<string>();
  for (const item of ordered) {
    const blocking = item.imports.find(name => blocked.has(name));
    if (blocking) {
      blocked.add(item.module);
      skipped.push({ module: item.module, file: item.file, because: blocking });
      log?.(`skipped ${item.file}: imports ${blocking}`);
      continue;
    }
    const attempt = kernel.fork();
    forkSurfaceEnvironment(kernel, attempt);
    try {
      loaded.push(...loadModuleSourceGraph(attempt, [{ file: item.file, source: item.source }], roots, undefined, [], derive));
      kernel = attempt;
    } catch (error) {
      if (!(error instanceof SurfaceError) && !(error instanceof KernelError)) throw error;
      rememberFailureDisplay(error, attempt);
      blocked.add(item.module);
      failures.push({ module: item.module, file: item.file, source: item.source, error });
      log?.(`failed ${item.file}: ${failureText(error)}`);
    }
  }
  return { kernel, loaded, failures, skipped };
}

const machineCommands = new Set(["serve", "goal", "suggest", "search", "declaration", "signature", "elaborate", "audit", "library", "notations", "closure"]);

/**
 * One method of the machine interface as a subcommand. Each prints the
 * protocol's response envelope without an id: `{ ok, version, method,
 * result }` on success, `{ ok, version, method, error }` with exit status 1
 * otherwise. Output is JSON unless --text asks for the readable rendering
 * that `search` and `goal` have.
 */
function runMachineCommand(
  command: string, positional: readonly string[],
  option: (name: string) => string | undefined, options: (name: string) => string[], flag: (name: string) => boolean, json: boolean,
): void {
  if (command === "serve") {
    if (positional.length) { usage(console.error); process.exitCode = 2; return; }
    serveMachineInterface(process.stdin, process.stdout, { pin: flag("--pin") }).catch(error => {
      console.error(`serve stopped: ${error instanceof Error ? error.message : String(error)}`);
      process.exitCode = 1;
    });
    return;
  }
  const integer = (name: string): number | undefined => {
    const value = option(name);
    if (value === undefined) return undefined;
    if (!/^\d+$/.test(value)) throw new MachineError("invalid_params", `${name} takes a positive integer`);
    return Number(value);
  };
  const workspace = (files: readonly string[]) => ({
    files: files.map(name => ({ name })),
    ...(option("--active") ? { activeFile: option("--active") } : {}),
    ...(option("--foundation") ? { foundation: option("--foundation") } : {}),
    ...(options("--module-root").length ? { moduleRoots: options("--module-root") } : {}),
  });
  const fileWorkspace = () => options("--file").length ? workspace(options("--file")) : {};
  const position = () => ({ line: integer("--line"), ...(integer("--column") !== undefined ? { column: integer("--column") } : {}) });
  let response: { ok: boolean; version: string; method: string; result?: unknown; error?: unknown };
  try {
    const params = command === "search" ? { query: positional.join(" "), ...fileWorkspace(), ...(integer("--limit") !== undefined ? { limit: integer("--limit") } : {}) }
      : command === "declaration" ? { name: positional[0] ?? "", ...(option("--module") ? { module: option("--module") } : {}), ...fileWorkspace() }
      : command === "signature" ? { name: positional[0] ?? "", ...(option("--module") ? { module: option("--module") } : {}), ...fileWorkspace(), ...(flag("--elaborate") ? { elaborate: true } : {}) }
      : command === "elaborate" ? {
        text: positional.join(" "), ...(option("--module") ? { module: option("--module") } : {}), ...fileWorkspace(),
        ...(integer("--line") !== undefined ? { line: integer("--line") } : {}), ...(option("--kind") ? { kind: option("--kind") } : {}),
        ...(option("--variables") ? { variables: option("--variables") } : {}),
      }
      : command === "library" ? { ...(option("--area") ? { area: option("--area") } : {}), ...(option("--module") ? { module: option("--module") } : {}), ...(flag("--declarations") ? { declarations: true } : {}) }
      : command === "notations" ? { ...(option("--module") ? { module: option("--module") } : {}), ...(positional.length ? workspace(positional) : {}) }
      : command === "closure" ? {
        ...(positional[0]?.endsWith(".g17") ? { file: positional[0] } : { module: positional[0] ?? "" }),
        ...(options("--module-root").length ? { moduleRoots: options("--module-root") } : {}),
        ...(option("--from") ? { from: option("--from") } : {}),
      }
      : command === "audit" ? { ...workspace(positional), ...(options("--theorem").length > 1 ? { theorems: options("--theorem") } : { theorem: option("--theorem") ?? "" }) }
      : command === "goal" ? { ...workspace(positional), ...(positional.length === 1 ? { file: positional[0] } : {}), ...position() }
      : { ...workspace(positional), ...(positional.length === 1 ? { file: positional[0] } : {}), ...position(), tactic: option("--tactic") ?? "" };
    if ((command === "goal" || command === "suggest" || command === "audit") && positional.length === 0) throw new MachineError("invalid_params", `${command} takes the workspace files to check`);
    response = { ok: true, version: MACHINE_PROTOCOL_VERSION, method: command, result: callMachineMethod(command, params) };
  } catch (error) {
    console.error(JSON.stringify({ ok: false, version: MACHINE_PROTOCOL_VERSION, method: command, error: machineErrorBody(error) }));
    process.exitCode = 1;
    return;
  }
  if (json || (command !== "search" && command !== "goal" && command !== "closure")) { console.log(JSON.stringify(response)); return; }
  const result = response.result as Record<string, unknown>;
  if (command === "closure") {
    const listed = result.modules as readonly { module: string; file: string; choiceFree: boolean }[];
    console.log(`${result.module}: ${listed.length} modules, ${result.choiceFree ? "choice-free" : `uses ${(result.choice as string[]).join(", ")}`}`);
    for (const item of listed) console.log(`${item.choiceFree ? "choice-free" : "choice     "}  ${item.module}  ${item.file}`);
    if (Array.isArray(result.chain)) console.log(`chain: ${(result.chain as string[]).join(" → ")}`);
    return;
  }
  if (command === "search") {
    const hits = result.results as readonly { name: string; kind: string; module: string; file: string; line: number }[];
    console.log(`${result.total} results, ${result.indexed} declarations indexed`);
    for (const hit of hits) console.log(`${hit.name}  ${hit.kind}  ${hit.module}  ${hit.file}:${hit.line}`);
    return;
  }
  if (result.kind === "evaluation") { console.log(`evaluation at line ${result.line}`); return; }
  if (result.kind !== "theorem") { console.log(String(result.message)); return; }
  console.log(`${result.theorem ?? "theorem"} (${result.theoremStatus}): ${result.caption}`);
  const state = result.state as { goals: readonly { goal: string; locals: readonly { name: string; formula: string }[] }[] } | null;
  if (!state || state.goals.length === 0) console.log(result.complete ? "No goals remain" : "No proof state at this position");
  state?.goals.forEach((goal, index) => {
    console.log(`  ${index + 1}. ⊢ ${goal.goal}`);
    for (const local of goal.locals) console.log(`       ${local.name} : ${local.formula}`);
  });
  const diagnostic = result.diagnostic as { line: number; message: string } | undefined;
  if (diagnostic) console.log(`error at line ${diagnostic.line}: ${diagnostic.message}`);
}

function resolvesUnderRoot(module: string, roots: readonly string[]): boolean {
  const relative = `${module.split(".").join("/")}.g17`;
  return roots.some(root => existsSync(resolve(root, relative)));
}

/** A `.g17` entry that resolves, as the module it declares, to itself under some root. */
function isLibraryFile(entry: string, module: string, roots: readonly string[]): boolean {
  if (!entry.endsWith(".g17")) return true;
  const relative = `${module.split(".").join("/")}.g17`;
  return roots.some(root => resolve(root, relative) === resolve(entry));
}

function safeName(name: string): string {
  return name.normalize("NFKD").replace(/[^A-Za-z0-9._-]+/g, "-").replace(/^-+|-+$/g, "") || "proof";
}

function usage(print: (line: string) => void): void {
  print("usage:");
  print("  g17 axiom-audit [--json] [--foundation ZF|ZFC|ZFG] [--module-root dir ...] <module.g17> --theorem <qualified-name>");
  print("  g17 check [--json] [--audit] [--imports] [--continue [--quiet]] [--foundation ZF|ZFC|ZFG] [--module-root dir ...] [--artifacts dir] <module.g17> [...]");
  print("  g17 build [--json] [--foundation ZF|ZFC|ZFG] [--module-root dir ...] [--artifacts dir] [--verify] <Module.Name|module.g17> [...]");
  print("  g17 run [--json] [--module-root dir ...] <module.g17> --function <name> --args <naturals>");
  print("  g17 export [--json] <module.g17> [...] --theorem <name> [--out proof.g17proof.json]");
  print("  g17 view [--json] <module.g17> [...] --theorem <name> [--out proof.html]");
  print("  g17 compile [--json] <module.g17> [...] [--out module.g17m] [--environment module.g17env]");
  print("  g17 verify-machine [--json] <module.g17> [...] --machine module.g17m");
  print("machine interface (docs/machine-interface.md); every method prints JSON, --text gives the readable form of search and goal:");
  print("  g17 serve [--pin]                          newline-delimited JSON requests on stdin, responses on stdout");
  print("  g17 goal [--text] [--foundation F] [--module-root dir ...] [--active file] <file.g17> [...] --line N [--column C]");
  print("  g17 suggest [--foundation F] [--module-root dir ...] [--active file] <file.g17> [...] --line N [--column C] --tactic exact?|apply?|rw?");
  print("  g17 search [--text] [--limit N] [--file file.g17 ...] <query>");
  print("  g17 declaration <Name> [--module Module.Name] [--file file.g17 ...]");
  print("  g17 signature <Name> [--module Module.Name] [--file file.g17 ...] [--elaborate]");
  print("  g17 elaborate <text> [--module Module.Name | --file file.g17 [--line N]] [--kind formula|term] [--variables '(x : Set)']");
  print("  g17 audit [--foundation F] [--module-root dir ...] [--active file] <file.g17> [...] --theorem <qualified-name> [--theorem ...]");
  print("  g17 library [--area Area] [--module Module.Name] [--declarations]");
  print("  g17 notations [--module Module.Name] [file.g17 ...]");
  print("  g17 closure [--text] [--module-root dir ...] <Module.Name|file.g17> [--from Module.Name]");
  print("  g17 --help                                 this text");
}
