// The command line resolves its module roots, artifact store, foundation,
// and heap from the flags, the environment, a project g17.json, and the
// user's configuration, in that order, with the bundled library always a
// root; the launcher runs the command with the heap the settings ask for;
// and `g17 settings` prints what was resolved.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore
import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdirSync, mkdtempSync, realpathSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { delimiter, join, resolve } from "node:path";
import { defaultHeap, loadCliSettings } from "../src/cli-settings.ts";
import { projectRoot } from "../src/project-root.ts";

const library = resolve(projectRoot, "lib");

function scratch(): { root: string; home: string; project: string; nested: string } {
  const root = mkdtempSync(join(tmpdir(), "g17-settings-"));
  const home = join(root, "home"); const project = join(root, "project"); const nested = join(project, "a", "b");
  mkdirSync(join(home, ".config", "grace17"), { recursive: true });
  mkdirSync(nested, { recursive: true });
  return { root, home, project, nested };
}

const cleanEnv = { PATH: process.env.PATH ?? "" } as NodeJS.ProcessEnv;

test("without flags or configuration the working directory and the library are the roots", () => {
  const { home, nested } = scratch();
  const settings = loadCliSettings(["check", "Foo.g17"], { cwd: nested, env: cleanEnv, home, memory: 16384 });
  assert.deepEqual(settings.moduleRoots, [resolve(nested), library]);
  assert.equal(settings.artifacts, undefined);
  assert.equal(settings.storeDefault, join(home, ".cache", "grace17", "modules"));
  assert.equal(settings.foundation, "ZFG");
  assert.equal(settings.heap, 8192);
  assert.deepEqual(settings.configFiles, []);
});

test("a project g17.json is found walking up, its paths read relative to it, and the user configuration fills what it leaves", () => {
  const { home, project, nested } = scratch();
  writeFileSync(join(project, "g17.json"), JSON.stringify({ moduleRoots: ["src", "."], artifacts: "cache" }));
  writeFileSync(join(home, ".config", "grace17", "config.json"), JSON.stringify({ foundation: "ZF", heap: 3000, moduleRoots: ["elsewhere"] }));
  const settings = loadCliSettings(["check", "Foo.g17"], { cwd: nested, env: cleanEnv, home, memory: 16384 });
  assert.deepEqual(settings.moduleRoots, [join(project, "src"), project, library]);
  assert.equal(settings.artifacts, join(project, "cache"));
  assert.equal(settings.foundation, "ZF");
  assert.equal(settings.heap, 3000);
  assert.deepEqual(settings.configFiles, [join(project, "g17.json"), join(home, ".config", "grace17", "config.json")]);
});

test("the environment overrides the files and the flags override the environment", () => {
  const { home, project, nested } = scratch();
  writeFileSync(join(project, "g17.json"), JSON.stringify({ moduleRoots: ["src"], artifacts: true, foundation: "ZF", heap: 3000 }));
  const env = { ...cleanEnv, G17_MODULE_ROOTS: ["one", "two"].join(delimiter), G17_ARTIFACTS: "false", G17_FOUNDATION: "ZFC", G17_HEAP: "4000", XDG_CACHE_HOME: join(project, "xdg") };
  const byEnv = loadCliSettings(["check", "Foo.g17"], { cwd: nested, env, home, memory: 16384 });
  assert.deepEqual(byEnv.moduleRoots, [join(nested, "one"), join(nested, "two"), library]);
  assert.equal(byEnv.artifacts, undefined);
  assert.equal(byEnv.storeDefault, join(project, "xdg", "grace17", "modules"));
  assert.equal(byEnv.foundation, "ZFC");
  assert.equal(byEnv.heap, 4000);
  const byFlags = loadCliSettings(["check", "--module-root", "lib", "--store", "--foundation", "ZFG", "--heap", "5000", "Foo.g17"], { cwd: nested, env, home, memory: 16384 });
  assert.deepEqual(byFlags.moduleRoots, [join(nested, "lib"), library]);
  assert.equal(byFlags.artifacts, byFlags.storeDefault);
  assert.equal(byFlags.foundation, "ZFG");
  assert.equal(byFlags.heap, 5000);
  const named = loadCliSettings(["build", "--artifacts", "~/store", "Grace.Cumulus.Set"], { cwd: nested, env, home, memory: 16384 });
  assert.equal(named.artifacts, join(home, "store"));
});

test("the default heap is eight gigabytes or three quarters of the machine", () => {
  assert.equal(defaultHeap(32768), 8192);
  assert.equal(defaultHeap(8192), 6144);
  assert.equal(defaultHeap(512), 1024);
});

test("a configuration with a wrong key or value is refused with its file named", () => {
  const { home, project, nested } = scratch();
  writeFileSync(join(project, "g17.json"), JSON.stringify({ roots: ["src"] }));
  assert.throws(() => loadCliSettings(["check"], { cwd: nested, env: cleanEnv, home }), /g17\.json: unknown setting roots/u);
  writeFileSync(join(project, "g17.json"), JSON.stringify({ foundation: "ZFX" }));
  assert.throws(() => loadCliSettings(["check"], { cwd: nested, env: cleanEnv, home }), /foundation is ZF, ZFC, or ZFG/u);
  writeFileSync(join(project, "g17.json"), JSON.stringify({ foundation: "ZF" }));
  assert.throws(() => loadCliSettings(["check", "--heap", "lots"], { cwd: nested, env: cleanEnv, home }), /--heap: the heap is a positive number/u);
});

function g17(args: readonly string[], cwd: string, env: NodeJS.ProcessEnv) {
  return spawnSync(process.execPath, ["--disable-warning=ExperimentalWarning", join(projectRoot, "bin", "g17.ts"), ...args],
    { cwd, encoding: "utf8", env: { ...env, HOME: env.HOME ?? cwd } });
}

test("a file in another directory imports the library with no module root named, and settings reports the roots", () => {
  const { home, nested } = scratch();
  writeFileSync(join(nested, "Probe.g17"), `module Probe
import Grace.Cumulus.Set

theorem pair_left (a b : Set)
  shows a ∈ {a, b}
proof
  simp
`);
  const env = { ...cleanEnv, HOME: home, G17_HEAP: "2048" };
  const check = g17(["check", "--json", "Probe.g17"], nested, env);
  assert.equal(check.status, 0, check.stderr + check.stdout);
  const report = JSON.parse(check.stdout.trim().split("\n").at(-1)!) as { ok?: boolean; status?: string; theorems?: string[] };
  assert.ok(report.ok !== false && report.status !== "failed", check.stdout);
  const settings = g17(["settings", "--json"], nested, env);
  assert.equal(settings.status, 0, settings.stderr);
  const printed = JSON.parse(settings.stdout) as { moduleRoots: string[]; heap: number; heapLimit: number; libraryRoot: string };
  assert.deepEqual(printed.moduleRoots, [realpathSync(nested), library]);
  assert.equal(printed.libraryRoot, library);
  assert.equal(printed.heap, 2048);
});

test("the launcher runs the command with the heap the settings ask for", () => {
  const { home, nested } = scratch();
  const env = { ...cleanEnv, HOME: home, G17_HEAP: "6000" };
  const settings = g17(["settings", "--json"], nested, env);
  assert.equal(settings.status, 0, settings.stderr);
  const printed = JSON.parse(settings.stdout) as { heap: number; heapLimit: number };
  assert.equal(printed.heap, 6000);
  assert.ok(printed.heapLimit >= 6000 - 64, `the heap limit is ${printed.heapLimit}`);
});

test("a compile elaborates from source even when the configuration asks for the store", () => {
  const { home, nested } = scratch();
  writeFileSync(join(nested, "g17.json"), JSON.stringify({ artifacts: true, foundation: "ZF" }));
  writeFileSync(join(nested, "Probe.g17"), `module Probe
import Grace.Cumulus.Set.Core

theorem chain (A B C : Set)
  requires first : A ⊆ B
  requires second : B ⊆ C
  shows A ⊆ C
proof
  exact Subset.transitive with *
`);
  const env = { ...cleanEnv, HOME: home, G17_HEAP: "2048", XDG_CACHE_HOME: join(home, "cache") };
  const check = g17(["check", "Probe.g17"], nested, env);
  assert.equal(check.status, 0, check.stderr + check.stdout);
  const compile = g17(["compile", "Probe.g17", "--out", "probe.g17m", "--environment", "probe.g17env"], nested, env);
  assert.equal(compile.status, 0, compile.stderr + compile.stdout);
  assert.doesNotMatch(compile.stdout + compile.stderr, /no retained proof/u);
});
