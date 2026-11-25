#!/usr/bin/env node
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore


import { closeSync, existsSync, openSync, readFileSync, writeFileSync, writeSync } from "node:fs";
import { performance } from "node:perf_hooks";
import { resolve } from "node:path";
import {
  auditTheoremAxioms, callNative, compileProofModule, createSetTheoryKernel, encodeProofMachineBinary,
  exportedProofText, exportKernelEnvironment, exportTheorem, exportTheoremForMachine, KernelError, loadModuleGraph,
  renderProofHtml, SurfaceError, verifyExportedProof, verifyProofMachineBinary,
  workbenchFailure, rememberFailureDisplay, renderCheckedWorkspace,
  type LoadedModule, type WorkbenchFile,
} from "./index.ts";
import { checkContinuing, failureText, type ContinuedCheck } from "./continued-check.ts";
import {
  callMachineMethod, MACHINE_PROTOCOL_VERSION, MachineError, machineCheckFailure, machineErrorBody, presentCheckedWorkspace, serveMachineInterface, withoutProofStates, serveMachineInterfaceOnPort,
  shadowedPropertyWarnings, transitiveImportNotes,
} from "./machine-interface.ts";
import { shadowedProperties } from "./workbench.ts";
import { setSurfaceTraceCapture } from "./surface.ts";
import { theoremDependencies } from "./export.ts";
import { buildModuleStore, createStoreKernel, declaredModule, loadModuleStore } from "./module-store.ts";
import { scanModule } from "./module-source-loader.ts";
import { describeSettings, loadCliSettings } from "./cli-settings.ts";
import { getHeapStatistics } from "node:v8";
import { setDefaultModuleRoots } from "./machine-interface.ts";

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
  // The settings every command starts from; a wrong configuration is the
  // first thing reported.
  let settings: ReturnType<typeof loadCliSettings>;
  try { settings = loadCliSettings(args); } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    if (json) console.log(JSON.stringify({ ok: false, operation: command, message }));
    else console.error(`error: ${message}`);
    process.exitCode = 2;
    return;
  }
  setDefaultModuleRoots(settings.moduleRoots);
  if (command === "settings") {
    const described = describeSettings(settings, Math.floor(getHeapStatistics().heap_size_limit / 2 ** 20));
    if (json) console.log(JSON.stringify(described));
    else for (const [key, value] of Object.entries(described)) console.log(`${key}: ${Array.isArray(value) ? value.join(", ") || "(none)" : String(value)}`);
    return;
  }
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
    "--line", "--column", "--tactic", "--active", "--limit", "--module", "--area", "--file", "--kind", "--variables", "--heap", "--port"]);
  const flagNames = new Set(["--json", "--text", "--verify", "--audit", "--declarations", "--continue", "--all", "--elaborate", "--pin", "--imports", "--quiet", "--store", "--no-states"]);
  const optionNames2 = ["--from"];
  optionNames2.forEach(name => optionNames.add(name));
  const modules: string[] = [];
  for (let index = 1; index < args.length; index += 1) {
    if (optionNames.has(args[index]!)) { index += 1; continue; }
    if (!flagNames.has(args[index]!)) modules.push(args[index]!);
  }

  if (machineCommands.has(command)) {
    runMachineCommand(command, modules, option, options, name => args.includes(name), !args.includes("--text"), settings);
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
      const profile = settings.foundation;
      // The roots the settings resolved: the named or configured ones, then
      // the bundled library, so an import of the library needs no flag.
      const roots = settings.moduleRoots;
      // The store: named by --artifacts, asked for by --store or the
      // configuration, and for build the default store in any case.
      // Only a check or a build replays artifacts: a compile, an export, an
      // audit of retained proofs, or a run needs the proofs themselves,
      // which an artifact does not carry, so those elaborate from source
      // whatever the settings ask for.
      const store = command === "build" ? settings.artifacts ?? settings.storeDefault
        : command === "check" ? settings.artifacts : undefined;
      if (continuing && store) throw new Error("check --continue elaborates from source; it does not take --artifacts or --store");
      // A store replays its foundation image instead of elaborating the prelude.
      kernel = store ? createStoreKernel(store, profile) : createSetTheoryKernel({ profile });
      // The tactic trace of every successful proof serves the Workbench and
      // the machine interface, and `check` reports a failure from them; a
      // compile or an audit needs none, and over the whole library they are
      // a large share of the memory.
      if (["compile", "build", "axiom-audit", "verify-machine"].includes(command)) setSurfaceTraceCapture(kernel, false);
      // With an artifact store, every entry that is a library module under a
      // root is compiled to its artifact once and replayed afterwards; only
      // workspace files outside the roots are elaborated from source each time.
      let checked: readonly LoadedModule[] = [];
      if (store) {
        const storeDirectory = store;
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
        continued = checkContinuing(kernel, modules.map(entry => ({ file: resolve(entry) })), roots, json || quiet ? undefined : line => console.error(line));
        kernel = continued.kernel;
        checked = continued.loaded;
      } else {
        checked = loadModuleGraph(kernel, modules, roots);
      }

      if (command === "axiom-audit") {
        const name = option("--theorem");
        if (!name) throw new Error("axiom-audit requires --theorem <qualified-name>");
        const audit = auditTheoremAxioms(kernel, name);
        const result = { ok: true, operation: command, foundation: settings.foundation, ...audit };
        if (json) console.log(JSON.stringify(result));
        else {
          console.log(`Axiom audit: ${name} (${audit.complete ? "complete" : "INCOMPLETE"})`);
          console.log(`Direct named axioms: ${audit.direct.join(", ") || "none"}`);
          console.log(`Hereditary named axioms: ${audit.hereditary.join(", ") || "none found"}`);
          for (const axiom of audit.axioms) console.log(`  ${axiom.name}: ${axiom.path.join(" → ")}`);
          console.log(`Definition/schema mechanisms: ${[...new Set(audit.mechanisms.map(m => m.kind))].join(", ") || "none"}`);
          console.log(`Classical double-negation elimination: ${audit.classicalLogic ? "used" : "not used"}`);
          if (audit.largeCardinals.assumes.length === 0) console.log("Large cardinal hypotheses: none");
          for (const item of audit.largeCardinals.assumes) {
            console.log(`Large cardinal hypothesis: ${item.predicate} (${item.label})${item.path.length > 1 ? `, assumed by ${item.path.join(" → ")}` : ""}`);
          }
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
          // --no-states leaves out the proof states of the theorems that did not fail.
          const theorems = [...presented.theorems, ...failed.flatMap(item => item.theorems)];
          const result = {
            ok: failures.length === 0, version: MACHINE_PROTOCOL_VERSION, operation: command, ...presented,
            ...(failures.length ? { status: "failed" as const } : {}),
            diagnostics: [...failed.flatMap(item => item.diagnostics), ...presented.diagnostics],
            theorems: args.includes("--no-states") ? withoutProofStates(theorems) : theorems,
            admitted: [...presented.admitted, ...failed.flatMap(item => item.admitted)],
            ...(continued ? {
              failures: failures.map((item, index) => ({ module: item.module, file: item.file, ...failed[index]!.diagnostics[0]! })),
              skipped,
              skippedAfterFailure: continued.skippedAfterFailure,
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
          for (const item of own) {
            for (const warning of item.warnings) console.log(`warning: ${item.file}:${warning.line}: ${warning.message}`);
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
            for (const item of continued.skippedAfterFailure) {
              console.log(`skipped after failure ${item.file} [${item.module}]: ${item.theorems.join(", ")} after line ${item.line}`);
            }
            for (const item of skipped) console.log(`skipped ${item.file} [${item.module}]: imports ${item.because}`);
            const failedModules = new Set(failures.map(item => item.module)).size;
            console.log(`${checked.length} modules checked, ${failedModules} failed, ${skipped.length} skipped`);
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
        if (command === "export") writeTextPieces(output, exportedProofText(exported));
        else writeFileSync(output, renderProofHtml(exported));
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
        const failed = machineCheckFailure(error, sources, settings.moduleRoots);
        const theorems = args.includes("--no-states") ? withoutProofStates(failed.theorems) : failed.theorems;
        console.log(JSON.stringify({ ...failure, ...failed, theorems, milliseconds: Number((performance.now() - started).toFixed(3)) }));
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
  settings: ReturnType<typeof loadCliSettings>,
): void {
  if (command === "serve") {
    if (positional.length) { usage(console.error); process.exitCode = 2; return; }
    const port = option("--port");
    if (port !== undefined) {
      // The same protocol over a loopback TCP port: each connection is a
      // session of lines. The bound address is printed as one JSON line,
      // so a caller that asked for port 0 learns the port taken.
      if (!/^\d+$/.test(port) || Number(port) > 65535) {
        console.error("--port takes a port number from 0 to 65535");
        process.exitCode = 2;
        return;
      }
      serveMachineInterfaceOnPort({ port: Number(port), pin: flag("--pin") }).then(handle => {
        process.stdout.write(`${JSON.stringify({ version: MACHINE_PROTOCOL_VERSION, listening: { host: handle.host, port: handle.port } })}\n`);
        // A termination signal ends the process at once; a session in
        // flight loses its connection, as the stdio session does.
        const stop = (): void => { handle.close().catch(() => undefined); process.exit(0); };
        process.once("SIGINT", stop);
        process.once("SIGTERM", stop);
      }).catch(error => {
        console.error(`serve stopped: ${error instanceof Error ? error.message : String(error)}`);
        process.exitCode = 1;
      });
      return;
    }
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
    foundation: settings.foundation,
    moduleRoots: settings.moduleRoots,
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
        moduleRoots: settings.moduleRoots,
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
  print("  g17 check [--json [--no-states]] [--audit] [--imports] [--continue [--quiet]] [--foundation ZF|ZFC|ZFG] [--module-root dir ...] [--artifacts dir] <module.g17> [...]");
  print("  g17 build [--json] [--foundation ZF|ZFC|ZFG] [--module-root dir ...] [--artifacts dir] [--verify] <Module.Name|module.g17> [...]");
  print("  g17 run [--json] [--module-root dir ...] <module.g17> --function <name> --args <naturals>");
  print("  g17 export [--json] <module.g17> [...] --theorem <name> [--out proof.g17proof.json]");
  print("  g17 view [--json] <module.g17> [...] --theorem <name> [--out proof.html]");
  print("  g17 compile [--json] <module.g17> [...] [--out module.g17m] [--environment module.g17env]");
  print("  g17 verify-machine [--json] <module.g17> [...] --machine module.g17m");
  print("machine interface (docs/machine-interface.md); every method prints JSON, --text gives the readable form of search and goal:");
  print("  g17 serve [--pin] [--port N]               newline-delimited JSON requests on stdin, responses on stdout; --port N serves");
  print("                                             the same lines over TCP on 127.0.0.1:N (0 takes a free port, printed as JSON)");
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
  print("  g17 settings [--json]                      the module roots, store, foundation, and heap this run resolves");
  print("  g17 --help                                 this text");
  print("settings: --module-root dir, --artifacts dir or --store, --foundation F, and --heap MB on the command line; G17_MODULE_ROOTS,");
  print("  G17_ARTIFACTS, G17_FOUNDATION, G17_HEAP in the environment; then g17.json up from the working directory, then");
  print("  ~/.config/grace17/config.json; the bundled library is always a module root (docs/machine-interface.md, Settings).");
}

/** Write a text given in pieces, so a file may be larger than a string can be. */
function writeTextPieces(path: string, pieces: Iterable<string>): void {
  const file = openSync(path, "w");
  try {
    let pending = "";
    for (const piece of pieces) {
      pending += piece;
      if (pending.length >= 1 << 20) { writeSync(file, pending); pending = ""; }
    }
    if (pending) writeSync(file, pending);
  } finally {
    closeSync(file);
  }
}
