#!/usr/bin/env node
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { mkdirSync, readFileSync, readdirSync, writeFileSync } from "node:fs";
import { stripTypeScriptTypes } from "node:module";
import { basename, join, relative, sep } from "node:path";
import { fileURLToPath } from "node:url";
import { stageMonacoAssets } from "./monaco-assets.ts";
import { compileSeparateKernelModule, replaySeparateKernelModuleExact } from "../src/compiled-module.ts";
import { sha256Hex } from "../src/hash.ts";
import { loadModuleSourceGraph } from "../src/module-loader.ts";
import { exportSurfaceEnvironmentIndex, forkSurfaceEnvironment, setSurfaceTraceCapture } from "../src/surface.ts";
import { createSetTheoryKernel } from "../src/zfg.ts";

const project = fileURLToPath(new URL("..", import.meta.url));
const output = join(project, "workbench", "generated");
const sourceOutput = join(output, "src");
const shimOutput = join(output, "shims");
mkdirSync(sourceOutput, { recursive: true });
mkdirSync(shimOutput, { recursive: true });
const version = JSON.parse(readFileSync(join(project, "package.json"), "utf8")).version as string;

const monacoOutput = join(output, "monaco", "vs");
stageMonacoAssets(project, output);
const monacoAssets = walk(join(output, "monaco"))
  .map(file => `/${relative(join(project, "workbench"), file).replaceAll("\\", "/")}`);
writeFileSync(join(output, "monaco-assets.json"), JSON.stringify(monacoAssets, null, 2) + "\n");

for (const name of readdirSync(join(project, "src"))) {
  if (!name.endsWith(".ts")) continue;
  const source = readFileSync(join(project, "src", name), "utf8");
  const javascript = stripTypeScriptTypes(source, { mode: "transform" })
    .replaceAll(/(from\s+["'][^"']+)\.ts(["'])/g, "$1.js$2")
    .replaceAll('"node:fs"', '"../shims/fs.js"')
    .replaceAll('"node:path"', '"../shims/path.js"')
    .replaceAll('"node:url"', '"../shims/url.js"')
    .replaceAll('"node:perf_hooks"', '"../shims/perf_hooks.js"');
  writeFileSync(join(sourceOutput, `${basename(name, ".ts")}.js`), javascript);
}

const libraryFiles = walk(join(project, "lib"))
  .filter(file => file.endsWith(".g17"))
  .map(file => [relative(project, file).replaceAll("\\", "/"), readFileSync(file, "utf8")]);
writeFileSync(join(shimOutput, "standard-library.js"),
  `export const standardLibrary = new Map(${JSON.stringify(libraryFiles)});\n`);

const checkpointRoots = [
  "Grace.Cumulus.Rat.Operations",
  "Grace.Cumulus.Real.Embedding",
  "Grace.Cumulus.Real.Squares",
];
const checkpoints = checkpointRoots.map(rootModule => buildCheckpoint(rootModule));
writeFileSync(join(sourceOutput, "standard-checkpoints.js"),
  `export const standardDependencyCheckpoints = new Map(JSON.parse(${JSON.stringify(JSON.stringify(checkpoints.map(item => [item.rootModule, item])))}));\n`);

writeFileSync(join(shimOutput, "fs.js"), `import { standardLibrary } from "./standard-library.js";
const key = path => [...standardLibrary.keys()].find(candidate => String(path).replaceAll("\\\\", "/").endsWith(candidate));
export const existsSync = path => key(path) !== undefined;
export const readFileSync = (path, encoding) => {
  const found = key(path);
  if (!found) throw new Error("ENOENT: no embedded Grace17 module " + String(path));
  if (encoding !== undefined && encoding !== "utf8") throw new Error("Browser module files are UTF-8 text");
  return standardLibrary.get(found);
};
// Directory reads see the embedded library's tree: a directory is a prefix
// of some embedded path, and its entries are the next path segments.
const normalized = path => String(path).replaceAll("\\\\", "/").replace(/\\/$/, "");
const prefixOf = path => {
  const text = normalized(path);
  const root = [...standardLibrary.keys()].find(candidate => text.endsWith(candidate.split("/")[0]) || text.includes("/" + candidate.split("/")[0] + "/"));
  if (root === undefined) return undefined;
  const index = text.indexOf(root.split("/")[0]);
  return text.slice(index);
};
export const readdirSync = path => {
  const prefix = prefixOf(path);
  if (prefix === undefined) throw new Error("ENOENT: no embedded directory " + String(path));
  const entries = new Set();
  for (const candidate of standardLibrary.keys()) {
    if (candidate.startsWith(prefix + "/")) entries.add(candidate.slice(prefix.length + 1).split("/")[0]);
  }
  if (entries.size === 0 && !standardLibrary.has(prefix)) throw new Error("ENOENT: no embedded directory " + String(path));
  return [...entries];
};
export const statSync = path => {
  const prefix = prefixOf(path);
  if (prefix === undefined) throw new Error("ENOENT: no embedded entry " + String(path));
  const directory = [...standardLibrary.keys()].some(candidate => candidate.startsWith(prefix + "/"));
  if (!directory && !standardLibrary.has(prefix)) throw new Error("ENOENT: no embedded entry " + String(path));
  return { isDirectory: () => directory, isFile: () => !directory };
};
`);

writeFileSync(join(shimOutput, "path.js"), `
const normalize = value => {
  const absolute = String(value).startsWith("/");
  const parts = [];
  for (const part of String(value).replaceAll("\\\\", "/").split("/")) {
    if (!part || part === ".") continue;
    if (part === "..") parts.pop(); else parts.push(part);
  }
  return (absolute ? "/" : "") + parts.join("/");
};
export const resolve = (...values) => normalize(values.join("/"));
export const join = (...values) => normalize(values.join("/"));
export const relative = (from, to) => {
  const left = normalize(from).split("/").filter(Boolean);
  const right = normalize(to).split("/").filter(Boolean);
  while (left.length && right.length && left[0] === right[0]) { left.shift(); right.shift(); }
  return [...left.map(() => ".."), ...right].join("/");
};
`);
writeFileSync(join(shimOutput, "url.js"), "export const fileURLToPath = value => new URL(value).pathname;\n");
writeFileSync(join(shimOutput, "perf_hooks.js"), "export const performance = globalThis.performance;\n");

// The manifest lists every generated file apart from the editor's assets,
// so a page that must leave a stale build can refetch them past the HTTP
// cache before it reloads.
const generatedFiles = walk(output)
  .filter(file => !file.includes(`${sep}monaco${sep}`) && !file.endsWith("manifest.json"))
  .map(file => relative(output, file).replaceAll("\\", "/")).sort();
writeFileSync(join(output, "manifest.json"), JSON.stringify({
  version,
  modules: libraryFiles.length,
  files: generatedFiles,
}, null, 2) + "\n");
// The service worker caches the Workbench shell under a name that changes
// with every build, so a visitor who opened an earlier build is never left
// with a cached checker beside a fresh library.
const shellFiles = [
  ...readdirSync(join(project, "workbench")).filter(name => name.endsWith(".js") && name !== "service-worker.js")
    .map(name => join(project, "workbench", name)),
  ...walk(sourceOutput), ...walk(shimOutput), join(project, "workbench", "styles.css"), join(project, "workbench", "index.html"),
].sort();
const build = `${version}-${sha256Hex(shellFiles.map(file => readFileSync(file, "utf8")).join("\n")).slice(0, 12)}`;
writeFileSync(join(output, "version.js"), `export const version = ${JSON.stringify(version)};\nexport const build = ${JSON.stringify(build)};\n`);
writeFileSync(join(project, "workbench", "service-worker.js"),
  readFileSync(join(project, "workbench", "service-worker.template.js"), "utf8")
    .replaceAll("__GRACE17_VERSION__", build));
console.log(`built browser kernel, Monaco editor, and ${libraryFiles.length} embedded Grace17 modules (build ${build})`);

function buildCheckpoint(rootModule: string) {
  const foundation = createSetTheoryKernel({ profile: "ZFG" });
  const completed = foundation.fork();
  forkSurfaceEnvironment(foundation, completed);
  setSurfaceTraceCapture(completed, false);
  const checkpoint = foundation.admissionCheckpoint();
  const loaded = loadModuleSourceGraph(completed, [], [join(project, "lib")], [], [rootModule]);
  const sourceByModule = new Map(loaded.flatMap(item => item.module
    ? [[item.module, readFileSync(item.file, "utf8")] as const] : []));
  const syntheticModule = `Grace.Checkpoint.${rootModule}`;
  const compiled = compileSeparateKernelModule(foundation, foundation, completed, checkpoint, {
    module: syntheticModule,
    sourceDigest: sha256Hex(sourceByModule.get(rootModule) ?? rootModule),
  });
  const replayed = replaySeparateKernelModuleExact(foundation, compiled);
  forkSurfaceEnvironment(completed, replayed);
  const surface = exportSurfaceEnvironmentIndex(replayed, syntheticModule, compiled.digest);
  return {
    rootModule,
    sources: loaded.flatMap(item => item.module
      ? [[item.module, sha256Hex(sourceByModule.get(item.module)!)] as const] : []),
    compiled,
    surface,
    loaded: loaded.flatMap(item => item.module ? [{
      module: item.module, definitions: item.definitions, theorems: item.theorems,
    }] : []),
  };
}

function walk(directory: string): string[] {
  return readdirSync(directory, { withFileTypes: true }).flatMap(entry => {
    const path = join(directory, entry.name);
    return entry.isDirectory() ? walk(path) : [path];
  });
}
