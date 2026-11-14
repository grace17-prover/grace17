// The settings a command-line run resolves before it starts: the module
// roots, the artifact store, the foundation, and the heap. Each comes from
// the command line first, then the environment, then a project
// configuration file `g17.json` found by walking up from the working
// directory, then the user's `grace17/config.json` under the configuration
// home, and last from a default; the bundled library is always a root.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore
import { existsSync, readFileSync } from "node:fs";
import { homedir, totalmem } from "node:os";
import { delimiter, dirname, isAbsolute, join, resolve } from "node:path";
import { projectRoot } from "./project-root.ts";

export type Foundation = "ZF" | "ZFC" | "ZFG";
export const FOUNDATIONS: readonly Foundation[] = ["ZF", "ZFC", "ZFG"];

/** The resolved settings and where each came from. */
export interface CliSettings {
  /** Module roots in search order, absolute, the bundled library last. */
  readonly moduleRoots: readonly string[];
  /** The artifact store to use, or undefined when a check elaborates from source. */
  readonly artifacts: string | undefined;
  /** Where artifacts go when a store is wanted and none is named. */
  readonly storeDefault: string;
  readonly foundation: Foundation;
  /** The heap the launcher asks of the runtime, in megabytes. */
  readonly heap: number;
  /** The configuration files read, project first. */
  readonly configFiles: readonly string[];
  /** The library root the settings appended. */
  readonly libraryRoot: string;
}

/** The keys a configuration file may carry. */
export interface CliConfig {
  readonly moduleRoots?: readonly string[];
  readonly artifacts?: string | boolean;
  readonly foundation?: Foundation;
  readonly heap?: number;
}

export interface SettingsEnvironment {
  readonly cwd?: string;
  readonly env?: NodeJS.ProcessEnv;
  readonly home?: string;
  /** The project root whose `lib/` is the library; the installed package by default. */
  readonly library?: string;
  /** The machine's memory in megabytes, for the default heap. */
  readonly memory?: number;
}

export const PROJECT_CONFIG_FILE = "g17.json";
export const USER_CONFIG_RELATIVE = ["grace17", "config.json"];
/** The heap a run asks for when nothing says otherwise: eight gigabytes, or three quarters of the machine. */
export const DEFAULT_HEAP_MB = 8192;

class SettingsError extends Error {}

function readConfig(file: string): CliConfig {
  let parsed: unknown;
  try { parsed = JSON.parse(readFileSync(file, "utf8")); } catch (error) {
    throw new SettingsError(`${file}: ${error instanceof Error ? error.message : String(error)}`);
  }
  if (typeof parsed !== "object" || parsed === null || Array.isArray(parsed)) throw new SettingsError(`${file}: the configuration is a JSON object`);
  const config = parsed as Record<string, unknown>;
  const known = new Set(["moduleRoots", "artifacts", "foundation", "heap"]);
  for (const key of Object.keys(config)) {
    if (!known.has(key)) throw new SettingsError(`${file}: unknown setting ${key}; the settings are moduleRoots, artifacts, foundation, and heap`);
  }
  if (config.moduleRoots !== undefined && !(Array.isArray(config.moduleRoots) && config.moduleRoots.every(item => typeof item === "string"))) {
    throw new SettingsError(`${file}: moduleRoots is an array of directories`);
  }
  if (config.artifacts !== undefined && typeof config.artifacts !== "string" && typeof config.artifacts !== "boolean") {
    throw new SettingsError(`${file}: artifacts is a directory, true for the default store, or false`);
  }
  if (config.foundation !== undefined && !FOUNDATIONS.includes(config.foundation as Foundation)) throw new SettingsError(`${file}: foundation is ZF, ZFC, or ZFG`);
  if (config.heap !== undefined && !(typeof config.heap === "number" && Number.isInteger(config.heap) && config.heap > 0)) {
    throw new SettingsError(`${file}: heap is a positive number of megabytes`);
  }
  return config as CliConfig;
}

/** The project configuration nearest the directory, walking up to the root. */
export function findProjectConfig(cwd: string): string | undefined {
  let directory = resolve(cwd);
  for (;;) {
    const candidate = join(directory, PROJECT_CONFIG_FILE);
    if (existsSync(candidate)) return candidate;
    const parent = dirname(directory);
    if (parent === directory) return undefined;
    directory = parent;
  }
}

function expandHome(path: string, home: string): string {
  return path === "~" ? home : path.startsWith("~/") ? join(home, path.slice(2)) : path;
}

function userConfigHome(env: NodeJS.ProcessEnv, home: string): string {
  return env.XDG_CONFIG_HOME && isAbsolute(env.XDG_CONFIG_HOME) ? env.XDG_CONFIG_HOME : join(home, ".config");
}

function userCacheHome(env: NodeJS.ProcessEnv, home: string): string {
  return env.XDG_CACHE_HOME && isAbsolute(env.XDG_CACHE_HOME) ? env.XDG_CACHE_HOME : join(home, ".cache");
}

/** The heap a machine of this size gets by default. */
export function defaultHeap(memoryMb: number): number {
  return Math.max(1024, Math.min(DEFAULT_HEAP_MB, Math.floor(memoryMb * 0.75)));
}

function parseHeap(value: string, origin: string): number {
  if (!/^\d+$/.test(value) || Number(value) <= 0) throw new SettingsError(`${origin}: the heap is a positive number of megabytes, not ${value}`);
  return Number(value);
}

/**
 * The settings for a command line: `--module-root`, `--artifacts`, `--store`,
 * `--foundation`, and `--heap` first; then `G17_MODULE_ROOTS` (a path
 * list), `G17_ARTIFACTS`, `G17_FOUNDATION`, and `G17_HEAP`; then the
 * project and user configuration files; then the defaults.
 */
export function loadCliSettings(args: readonly string[], environment: SettingsEnvironment = {}): CliSettings {
  const cwd = resolve(environment.cwd ?? process.cwd());
  const env = environment.env ?? process.env;
  const home = environment.home ?? homedir();
  const libraryRoot = resolve(environment.library ?? projectRoot, "lib");
  const option = (name: string): string | undefined => {
    const index = args.lastIndexOf(name);
    return index >= 0 ? args[index + 1] : undefined;
  };
  const options = (name: string): string[] => args.flatMap((item, index) => item === name && args[index + 1] !== undefined ? [args[index + 1]!] : []);
  const configFiles: string[] = [];
  const layers: { config: CliConfig; base: string; origin: string }[] = [];
  const project = findProjectConfig(cwd);
  if (project) { configFiles.push(project); layers.push({ config: readConfig(project), base: dirname(project), origin: project }); }
  const user = join(userConfigHome(env, home), ...USER_CONFIG_RELATIVE);
  if (existsSync(user)) { configFiles.push(user); layers.push({ config: readConfig(user), base: dirname(user), origin: user }); }
  const configured = <K extends keyof CliConfig>(key: K): { value: NonNullable<CliConfig[K]>; base: string; origin: string } | undefined => {
    for (const layer of layers) {
      const value = layer.config[key];
      if (value !== undefined) return { value: value as NonNullable<CliConfig[K]>, base: layer.base, origin: layer.origin };
    }
    return undefined;
  };

  const flagRoots = options("--module-root");
  const envRoots = env.G17_MODULE_ROOTS?.split(delimiter).filter(Boolean);
  const configRoots = configured("moduleRoots");
  const chosenRoots = flagRoots.length ? flagRoots.map(root => resolve(cwd, expandHome(root, home)))
    : envRoots?.length ? envRoots.map(root => resolve(cwd, expandHome(root, home)))
    : configRoots ? configRoots.value.map(root => resolve(configRoots.base, expandHome(root, home)))
    : [cwd];
  const moduleRoots = [...new Set([...chosenRoots, libraryRoot])];

  const storeDefault = env.G17_CACHE_DIR ? resolve(cwd, expandHome(env.G17_CACHE_DIR, home)) : join(userCacheHome(env, home), "grace17", "modules");
  const flagStore = option("--artifacts");
  const configStore = configured("artifacts");
  const artifacts = flagStore !== undefined ? resolve(cwd, expandHome(flagStore, home))
    : args.includes("--store") ? storeDefault
    : env.G17_ARTIFACTS !== undefined ? (env.G17_ARTIFACTS === "" || env.G17_ARTIFACTS === "true" ? storeDefault : env.G17_ARTIFACTS === "false" ? undefined : resolve(cwd, expandHome(env.G17_ARTIFACTS, home)))
    : configStore ? (configStore.value === true ? storeDefault : configStore.value === false ? undefined : resolve(configStore.base, expandHome(configStore.value, home)))
    : undefined;

  const flagFoundation = option("--foundation");
  const envFoundation = env.G17_FOUNDATION;
  const configFoundation = configured("foundation");
  const foundationValue = flagFoundation ?? envFoundation ?? configFoundation?.value ?? "ZFG";
  if (!FOUNDATIONS.includes(foundationValue as Foundation)) {
    throw new SettingsError(`${flagFoundation ? "--foundation" : envFoundation ? "G17_FOUNDATION" : configFoundation!.origin}: the foundation is ZF, ZFC, or ZFG, not ${foundationValue}`);
  }

  const flagHeap = option("--heap");
  const configHeap = configured("heap");
  const heap = flagHeap !== undefined ? parseHeap(flagHeap, "--heap")
    : env.G17_HEAP !== undefined ? parseHeap(env.G17_HEAP, "G17_HEAP")
    : configHeap ? configHeap.value
    : defaultHeap(environment.memory ?? Math.floor(totalmem() / 2 ** 20));

  return { moduleRoots, artifacts, storeDefault, foundation: foundationValue as Foundation, heap, configFiles, libraryRoot };
}

/** The settings as the `settings` command prints them. */
export function describeSettings(settings: CliSettings, heapLimit: number): Record<string, unknown> {
  return {
    moduleRoots: settings.moduleRoots, libraryRoot: settings.libraryRoot,
    artifacts: settings.artifacts ?? null, storeDefault: settings.storeDefault,
    foundation: settings.foundation, heap: settings.heap, heapLimit, configFiles: settings.configFiles,
  };
}
