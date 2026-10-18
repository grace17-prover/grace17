// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// The natural predecessor, truncated subtraction, remainder, and quotient
// evaluate as one big-integer step each, and the computation certificates
// the runtime emits for them name a fixed dependency list that every
// reference checker recognizes in the same way: a module exercising the
// shortcuts on large and edge arguments compiles to the machine format and
// is accepted by the Python, Rust, and OCaml checkers, as are certificates
// that name only the definitions the general interpreter unfolds.

import assert from "node:assert/strict";
import { existsSync, mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { spawnSync } from "node:child_process";
import test from "node:test";
import { fileURLToPath } from "node:url";
import {
  app, compileProofModule, compute, createZfKernel, encodeProofMachineBinary, eq, evaluateNative,
  exportKernelEnvironment, exportTheorem, loadModuleSourceGraph, nat,
} from "../src/index.ts";

const root = fileURLToPath(new URL("..", import.meta.url));
const python = join(root, "checkers/python/g17check.py");
const rust = join(root, "build/rust/g17check");
const ocaml = join(root, "build/ocaml/g17check");
const cargoAvailable = spawnSync("cargo", ["--version"], { encoding: "utf8" }).status === 0;
const ocamlAvailable = spawnSync("ocamlopt", ["-version"], { encoding: "utf8" }).status === 0;

const predecessor = "Grace.Core.Nat.Rec.predecessor";
const sub = "Grace.Cumulus.Nat.Subtraction.sub";
const mod = "Grace.Cumulus.Nat.Mod.mod";
const quotient = "Grace.Cumulus.Nat.Division.quotientNat";
const remainderDefinitions = [
  mod, "Grace.Cumulus.Nat.Mod.nextRemainder", "Grace.Cumulus.Nat.Mod.chooseNat", "Grace.Cumulus.Nat.Mod.equalNat",
  "Grace.Cumulus.Nat.Mod.isZero", predecessor, "Grace.Core.Data.BoolOps.not", "Grace.Core.Data.BoolOps.and",
].sort();

// 2^128 − 1 and 2^64 − 1, with a prime divisor that fits no small table.
const big = 340282366920938463463374607431768211455n;
const small = 18446744073709551615n;
const divisor = 1000003n;

const source = `module EvaluationShortcuts
import Grace.Cumulus.Nat.Subtraction
import Grace.Cumulus.Nat.Division

eval ${big} - ${small}
eval predecessor(${big})
eval ${big} % ${divisor}
eval quotientNat(${big}, ${divisor})

theorem subLarge
  shows ${big} - ${small} = ${big - small}
proof
  compute

theorem subTruncated
  shows 3 - 5 = 0
proof
  compute

theorem subZero
  shows 7 - 0 = 7
proof
  compute

theorem subEqual
  shows ${big} - ${big} = 0
proof
  compute

theorem predecessorZero
  shows predecessor(0) = 0
proof
  compute

theorem predecessorLarge
  shows predecessor(${big}) = ${big - 1n}
proof
  compute

theorem modLarge
  shows ${big} % ${divisor} = ${big % divisor}
proof
  compute

theorem modByZero
  shows ${big} % 0 = ${big}
proof
  compute

theorem modZero
  shows 0 % 7 = 0
proof
  compute

theorem modEqual
  shows ${divisor} % ${divisor} = 0
proof
  compute

theorem quotientLarge
  shows quotientNat(${big}, ${divisor}) = ${big / divisor}
proof
  compute

theorem quotientByZero
  shows quotientNat(${big}, 0) = 0
proof
  compute

theorem quotientZero
  shows quotientNat(0, 7) = 0
proof
  compute

theorem quotientEqual
  shows quotientNat(${divisor}, ${divisor}) = 1
proof
  compute

theorem divisionIdentity
  shows ${big} = ${divisor} * quotientNat(${big}, ${divisor}) + ${big} % ${divisor}
proof
  compute
`;

function ensureRust(): void {
  if (existsSync(rust)) return;
  const build = spawnSync("bash", ["checkers/rust/build.sh"], { cwd: root, encoding: "utf8", timeout: 900_000 });
  assert.equal(build.status, 0, build.stderr);
}

function ensureOcaml(): void {
  if (existsSync(ocaml)) return;
  const build = spawnSync("bash", ["checkers/ocaml/build.sh"], { cwd: root, encoding: "utf8", timeout: 900_000 });
  assert.equal(build.status, 0, build.stderr);
}

function runChecker(name: "python" | "rust" | "ocaml", machine: string, environment: string): void {
  const command = name === "python" ? ["python3", [python, machine, "--environment", environment, "--json"]] as const
    : name === "rust" ? [rust, [machine, "--environment", environment, "--json"]] as const
    : [ocaml, [machine, "--environment", environment]] as const;
  const checked = spawnSync(command[0], [...command[1]], { cwd: root, encoding: "utf8", timeout: 600_000 });
  assert.equal(checked.status, 0, `${name}: ${checked.stderr}`);
  if (name !== "ocaml") assert.equal(JSON.parse(checked.stdout).ok, true);
}

function compiledModule(): { readonly machine: string; readonly environment: string } {
  const directory = mkdtempSync(join(tmpdir(), "g17-evaluation-shortcuts-"));
  const file = join(directory, "EvaluationShortcuts.g17");
  writeFileSync(file, source);
  const machine = join(directory, "module.g17m");
  const environment = join(directory, "module.g17env");
  const compile = spawnSync(process.execPath, ["bin/g17.ts", "compile", file,
    "--out", machine, "--environment", environment, "--module-root", "lib"],
  { cwd: root, encoding: "utf8", timeout: 600_000 });
  assert.equal(compile.status, 0, compile.stderr);
  return { machine, environment };
}

// The in-process kernel for the module, with its tape and environment.
function loaded(): { readonly kernel: ReturnType<typeof createZfKernel>; readonly names: string[] } {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "EvaluationShortcuts.g17", source }], ["lib"]);
  const names = [...kernel.theorems.keys()].filter(name => name.startsWith("EvaluationShortcuts."));
  assert.equal(names.length, 15);
  return { kernel, names };
}

function tape(kernel: ReturnType<typeof createZfKernel>, names: readonly string[], label: string): {
  readonly machine: string; readonly environment: string;
} {
  const directory = mkdtempSync(join(tmpdir(), `g17-evaluation-shortcuts-${label}-`));
  const machine = join(directory, "module.g17m");
  const environment = join(directory, "module.g17env");
  writeFileSync(machine, encodeProofMachineBinary(compileProofModule(names.map(name => exportTheorem(kernel, name)))));
  writeFileSync(environment, `${JSON.stringify(exportKernelEnvironment(kernel), null, 2)}\n`);
  return { machine, environment };
}

test("the shortcuts evaluate in one step and record their fixed dependency lists", () => {
  const { kernel } = loaded();
  const cases: [string, bigint[], bigint, string[]][] = [
    [predecessor, [0n], 0n, [predecessor]],
    [predecessor, [big], big - 1n, [predecessor]],
    [sub, [7n, 0n], 7n, [predecessor, sub]],
    [sub, [3n, 5n], 0n, [predecessor, sub]],
    [sub, [big, big], 0n, [predecessor, sub]],
    [sub, [big, small], big - small, [predecessor, sub]],
    [mod, [0n, 7n], 0n, remainderDefinitions],
    [mod, [big, 0n], big, remainderDefinitions],
    [mod, [divisor, divisor], 0n, remainderDefinitions],
    [mod, [big, divisor], big % divisor, remainderDefinitions],
    [quotient, [0n, 7n], 0n, [...remainderDefinitions, quotient].sort()],
    [quotient, [big, 0n], 0n, [...remainderDefinitions, quotient].sort()],
    [quotient, [divisor, divisor], 1n, [...remainderDefinitions, quotient].sort()],
    [quotient, [big, divisor], big / divisor, [...remainderDefinitions, quotient].sort()],
  ];
  for (const [fn, args, expected, definitions] of cases) {
    const result = evaluateNative(kernel, app(fn, ...args.map(value => nat(value))));
    assert.equal(result.value, expected, `${fn}(${args.join(", ")})`);
    assert.equal(result.stats.reductions, 1, `${fn}(${args.join(", ")}) took ${result.stats.reductions} reductions`);
    assert.deepEqual(result.definitions, definitions, `${fn}(${args.join(", ")}) dependency list`);
  }
  // A certificate that allows only the definitions the general interpreter
  // unfolds is also valid: the shortcut stays off and the lists still match.
  for (const [fn, args, expected, allowed] of [
    [mod, [0n, 7n], 0n, [mod]],
    [sub, [7n, 0n], 7n, [sub]],
    [sub, [5n, 2n], 3n, [predecessor, sub]],
    [quotient, [0n, 3n], 0n, [quotient]],
    [predecessor, [0n], 0n, [predecessor]],
  ] as [string, bigint[], bigint, string[]][]) {
    const result = evaluateNative(kernel, app(fn, ...args.map(value => nat(value))), undefined, { allowedDefinitions: new Set(allowed) });
    assert.equal(result.value, expected);
    assert.deepEqual(result.definitions, allowed);
  }
});

test("eval lines on the shortcuts print the values after one reduction each", () => {
  const directory = mkdtempSync(join(tmpdir(), "g17-evaluation-shortcuts-eval-"));
  const file = join(directory, "EvaluationShortcuts.g17");
  writeFileSync(file, source);
  const checked = spawnSync(process.execPath, ["bin/g17.ts", "check", "--module-root", "lib", file],
    { cwd: root, encoding: "utf8", timeout: 600_000 });
  assert.equal(checked.status, 0, checked.stderr);
  // The imported library prints its own eval lines first; the module's are the last four.
  const lines = checked.stdout.split("\n").filter(line => line.trimStart().startsWith("eval ")).slice(-4);
  assert.deepEqual(lines.map(line => line.trim()), [
    `eval ${big} - ${small} ⇒ ${big - small} (1 reductions)`,
    `eval predecessor(${big}) ⇒ ${big - 1n} (1 reductions)`,
    `eval ${big} % ${divisor} ⇒ ${big % divisor} (1 reductions)`,
    `eval quotientNat(${big}, ${divisor}) ⇒ ${big / divisor} (1 reductions)`,
  ]);
});

test("the Python checker accepts the compiled module and the plain-list certificates", () => {
  const compiled = compiledModule();
  runChecker("python", compiled.machine, compiled.environment);
  const plain = plainCertificates();
  runChecker("python", plain.machine, plain.environment);
});

test("the Rust checker accepts the compiled module and the plain-list certificates", { skip: !cargoAvailable && "cargo is not installed" }, () => {
  ensureRust();
  const compiled = compiledModule();
  runChecker("rust", compiled.machine, compiled.environment);
  const plain = plainCertificates();
  runChecker("rust", plain.machine, plain.environment);
});

test("the OCaml checker accepts the compiled module and the plain-list certificates", { skip: !ocamlAvailable && "ocamlopt is not installed" }, () => {
  ensureOcaml();
  const compiled = compiledModule();
  runChecker("ocaml", compiled.machine, compiled.environment);
  const plain = plainCertificates();
  runChecker("ocaml", plain.machine, plain.environment);
});

// The module's theorems together with certificates whose lists name only
// what the general interpreter unfolds, so a checker must both take the
// shortcut when its list is allowed and stay off it when it is not.
function plainCertificates(): { readonly machine: string; readonly environment: string } {
  const { kernel, names } = loaded();
  const extra: [string, string, bigint[], bigint, string[]][] = [
    ["modZeroPlain", mod, [0n, 7n], 0n, [mod]],
    ["subZeroPlain", sub, [7n, 0n], 7n, [sub]],
    ["subPlain", sub, [5n, 2n], 3n, [predecessor, sub]],
    ["quotientZeroPlain", quotient, [0n, 3n], 0n, [quotient]],
    ["predecessorPlain", predecessor, [0n], 0n, [predecessor]],
  ];
  const added: string[] = [];
  for (const [label, fn, args, value, definitions] of extra) {
    const left = app(fn, ...args.map(item => nat(item)));
    const name = `EvaluationShortcuts.${label}`;
    kernel.addTheorem(name, eq(left, nat(value)), compute(left, nat(value), definitions));
    added.push(name);
  }
  return tape(kernel, [...names, ...added], "plain");
}
