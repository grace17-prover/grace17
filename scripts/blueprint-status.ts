// Report the state of a blueprint: for each of its modules, the theorems it
// states and how many are still admitted with sorry. With --write, the table
// replaces the status block of the blueprint's README.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore
import { spawnSync } from "node:child_process";
import { readdirSync, readFileSync, statSync, writeFileSync } from "node:fs";
import { join, relative, resolve } from "node:path";

const args = process.argv.slice(2);
const write = args.includes("--write");
const root = resolve(args.find(item => !item.startsWith("--")) ?? "blueprints/CycleDoubleCover");
const blueprintRoot = resolve("blueprints");

function walk(directory: string): string[] {
  return readdirSync(directory).flatMap(name => {
    const path = join(directory, name);
    return statSync(path).isDirectory() ? walk(path) : name.endsWith(".g17") ? [path] : [];
  }).sort();
}

const files = walk(root);
// A blueprint whose every module is promoted has nothing to check.
const run = files.length === 0 ? { status: 0, stdout: "{}", stderr: "" }
  : spawnSync("node", ["--disable-warning=ExperimentalWarning", "bin/g17.ts", "check", "--json", "--continue", "--quiet",
    "--module-root", blueprintRoot, "--module-root", "lib", ...files], { encoding: "utf8", maxBuffer: 1 << 28 });
if (run.status !== 0 && !run.stdout.trim().startsWith("{")) {
  console.error(run.stderr || run.stdout);
  process.exit(1);
}
interface Checked { file: string; module: string; theorems: string[]; sorries: { theorem: string }[] }
const report = JSON.parse(run.stdout) as { checked?: Checked[]; failed?: { file: string; error: string }[] };
const rows = (report.checked ?? []).filter(item => item.file.startsWith(root)).map(item => {
  const admitted = new Set(item.sorries.map(sorry => sorry.theorem)).size;
  return { module: relative(blueprintRoot, item.file).replace(/\.g17$/u, "").replaceAll("/", "."), theorems: item.theorems.length, admitted, proved: item.theorems.length - admitted };
});
const total = rows.reduce((sum, row) => ({ theorems: sum.theorems + row.theorems, admitted: sum.admitted + row.admitted, proved: sum.proved + row.proved }), { theorems: 0, admitted: 0, proved: 0 });
const failed = (report.failed ?? []).filter(item => item.file.startsWith(root));
const lines = [
  "| module | theorems | proved | admitted |",
  "|---|---:|---:|---:|",
  ...rows.map(row => `| ${row.module} | ${row.theorems} | ${row.proved} | ${row.admitted} |`),
  `| **total** | **${total.theorems}** | **${total.proved}** | **${total.admitted}** |`,
  ...failed.map(item => `| ${relative(blueprintRoot, item.file)} | failed | | ${item.error.slice(0, 80)} |`),
];
console.log(lines.join("\n"));
if (write) {
  const readme = join(root, "README.md");
  const text = readFileSync(readme, "utf8");
  const begin = "<!-- blueprint-status -->";
  const end = "<!-- /blueprint-status -->";
  const start = text.indexOf(begin);
  const stop = text.indexOf(end);
  if (start < 0 || stop < 0) throw new Error(`${readme} has no status block`);
  writeFileSync(readme, `${text.slice(0, start + begin.length)}\n${lines.join("\n")}\n${text.slice(stop)}`);
  console.log(`updated ${relative(process.cwd(), readme)}`);
}
process.exit(failed.length ? 1 : 0);
