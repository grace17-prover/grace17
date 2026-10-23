// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createHash, randomBytes } from "node:crypto";
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { sha256Bytes, sha256Hex, timingSafeBytesEqual } from "../src/hash.ts";
import { checkWorkbenchFiles as checkNative } from "../src/workbench.ts";
import { stageMonacoAssets } from "../scripts/monaco-assets.ts";

test("portable SHA-256 is byte-identical to the platform implementation", () => {
  for (const value of [Buffer.alloc(0), Buffer.from("abc"), Buffer.from("Grace17 🌟"), randomBytes(4097)]) {
    const expected = createHash("sha256").update(value).digest("hex");
    assert.equal(sha256Hex(value), expected);
    assert.equal(Buffer.from(sha256Bytes(value)).toString("hex"), expected);
  }
  assert.equal(timingSafeBytesEqual(Uint8Array.of(1, 2), Uint8Array.of(1, 2)), true);
  assert.equal(timingSafeBytesEqual(Uint8Array.of(1, 2), Uint8Array.of(1, 3)), false);
  assert.equal(timingSafeBytesEqual(Uint8Array.of(1), Uint8Array.of(1, 0)), false);
});

test("browser-generated kernel checks Core imports with the same environment digest", async () => {
  const browser = await import("../workbench/generated/src/workbench.js");
  const source = `module Browser.Smoke
namespace Browser.Smoke
import Grace.Core
open Grace.Core.Nat.Rec

theorem two
  shows add(1, 1) = 2
proof
  settle with add

end Browser.Smoke
`;
  const files = [{ name: "Browser.g17", source }];
  const native = checkNative(files, "ZFG", ["Browser.g17"]);
  const local = browser.checkWorkbenchFiles(files, "ZFG", ["Browser.g17"]);
  assert.equal(local.ok, true);
  assert.equal(local.digest, native.digest);
  assert.deepEqual(local.theorems.map((theorem: { name: string }) => theorem.name), ["Browser.Smoke.two"]);
  assert.equal(local.theorems[0].steps.at(-1).after.goals.length, 0);
});

test("dependency preparation retains imported names for completion during broken proofs", async () => {
  const browser = await import("../workbench/generated/src/workbench.js");
  const source = `module Browser.Completion
namespace Browser.Completion
import Grace.Cumulus.Main

end Browser.Completion
`;
  const prepared = browser.prepareWorkbenchFiles([{ name: "Completion.g17", source }], "ZFG", "Completion.g17");
  assert.equal(prepared.ok, true);
  assert.ok(prepared.symbols.includes("Grace.Cumulus.Cardinal.Finite.omega.infinite"));
});

test("browser Workbench checks Set/Order.g17 against its embedded Cumulus dependencies", async () => {
  const browser = await import("../workbench/generated/src/workbench.js");
  const { standardLibrary } = await import("../workbench/generated/shims/standard-library.js");
  const active = "lib/Grace/Cumulus/Set/Order.g17";
  const source = standardLibrary.get(active);
  assert.ok(source);
  const result = browser.checkWorkbenchFiles([{ name: active, source }], "ZFG", [active], { includeKernelDetails: false });
  assert.equal(result.ok, true);
  assert.ok(result.theorems.some((theorem: { name: string }) => theorem.name === "Grace.Cumulus.Set.Order.Chain.union"));
  const native = checkNative([{ name: active, source }], "ZFG", [active], { includeKernelDetails: false });
  assert.equal(native.ok, true);
  assert.deepEqual(result.theorems.map(t => t.name), native.theorems.map(t => t.name));
});

// Bundled checkpoint payloads live beside the index and are fetched by the
// worker on first use; here they are installed from disk the same way.
async function installBundledCheckpoint(rootModule: string) {
  const { standardDependencyCheckpoints, installStandardCheckpoint } = await import("../workbench/generated/src/standard-checkpoints.js");
  const entry = standardDependencyCheckpoints.get(rootModule);
  assert.ok(entry, `bundled checkpoint ${rootModule}`);
  if (!entry.compiled) installStandardCheckpoint({ ...entry, ...JSON.parse(readFileSync(new URL(`../workbench/generated/${entry.file}`, import.meta.url), "utf8")) });
}

test("browser Workbench replays an authenticated rational dependency checkpoint", async () => {
  const browser = await import("../workbench/generated/src/workbench.js");
  const { standardLibrary } = await import("../workbench/generated/shims/standard-library.js");
  const { standardDependencyCheckpoints } = await import("../workbench/generated/src/standard-checkpoints.js");
  assert.ok(standardDependencyCheckpoints.has("Grace.Cumulus.Rat.Operations"));
  const active = "lib/Grace/Cumulus/Rat/Density.g17";
  const source = standardLibrary.get(active);
  assert.ok(source);
  // Before the payload is installed the plan names the bundled prefix to fetch;
  // afterwards it is the installed prefix and nothing remains to load.
  const before = browser.dependencyCheckpointPlan([{ name: active, source }], "ZFG", active);
  assert.equal(before?.standard?.rootModule, "Grace.Cumulus.Rat.Operations");
  assert.equal(before?.standard?.file, "checkpoints/Grace.Cumulus.Rat.Operations.json");
  assert.equal(before?.installedPrefix, 0);
  await installBundledCheckpoint("Grace.Cumulus.Rat.Operations");
  const after = browser.dependencyCheckpointPlan([{ name: active, source }], "ZFG", active);
  assert.equal(after?.standard, undefined);
  assert.ok((after?.installedPrefix ?? 0) >= 30);
  const prepared = browser.prepareWorkbenchFiles([{ name: active, source }], "ZFG", active);
  assert.equal(prepared.ok, true);
  assert.ok(prepared.modules >= 30);
  assert.ok(prepared.milliseconds < 2_500, `rational dependency replay took ${prepared.milliseconds} ms`);
});

test("browser Workbench exposes cursor-addressable goals throughout the rational density proof", async () => {
  const browser = await import("../workbench/generated/src/workbench.js");
  const { standardLibrary } = await import("../workbench/generated/shims/standard-library.js");
  const active = "lib/Grace/Cumulus/Rat/Density.g17";
  const source = standardLibrary.get(active);
  assert.ok(source);
  const result = browser.checkWorkbenchFiles([{ name: active, source }], "ZFG", [active], { includeKernelDetails: false });
  const dense = result.theorems.find((theorem: { name: string }) => theorem.name.endsWith("rationalLess.dense"));
  assert.ok(dense);
  assert.match(dense.initial.goals[0].goal, /∃ s/);
  const step = dense.steps.filter((item: { line: number }) => item.line <= 63).at(-1);
  assert.equal(step?.line, 63);
  assert.match(step.after.goals[0].locals.at(-1).formula, /rationalClass\(.*\) : ℚ/);
});

test("Real/Addition cursor ranges stay aligned after instance declarations", async () => {
  const browser = await import("../workbench/generated/src/workbench.js");
  const { standardLibrary } = await import("../workbench/generated/shims/standard-library.js");
  const active = "lib/Grace/Cumulus/Real/Addition.g17";
  const source = standardLibrary.get(active);
  assert.ok(source);
  const result = browser.checkWorkbenchFiles([{ name: active, source }], "ZFG", [active], { includeKernelDetails: false });
  const downward = result.theorems.find((theorem: { name: string }) => theorem.name.endsWith("realAddCut.downward"));
  const noGreatest = result.theorems.find((theorem: { name: string }) => theorem.name.endsWith("realAddCut.no_greatest"));
  const zeroInstance = result.symbols.find((symbol: { name: string }) => symbol.name.endsWith("realZero.of_nat"));
  assert.deepEqual([downward?.lineStart, downward?.lineEnd], [87, 111]);
  assert.deepEqual([noGreatest?.lineStart, noGreatest?.lineEnd], [113, 138]);
  assert.equal(noGreatest?.steps[0]?.line, 119);
  assert.equal(noGreatest?.steps[0]?.after.goals.length, 1);
  assert.equal(zeroInstance?.kind, "theorem");
  assert.equal(zeroInstance?.line, 29);
});

test("browser build embeds every checked bootstrap source", () => {
  const library = readFileSync(new URL("../workbench/generated/shims/standard-library.js", import.meta.url), "utf8");
  for (const name of ["Aliases", "Nat", "OrderedPair", "Epsilon0"]) {
    assert.match(library, new RegExp(`lib/Grace/Bootstrap/${name}\\.g17`));
  }
});

test("opening a bootstrap proof checks its exact staged foundation in both kernels", async () => {
  const browser = await import("../workbench/generated/src/workbench.js");
  const files = ["Aliases", "Nat", "OrderedPair", "Epsilon0"].map(name => ({
    name: `Bootstrap/${name}.g17`,
    source: readFileSync(new URL(`../lib/Grace/Bootstrap/${name}.g17`, import.meta.url), "utf8"),
  }));
  const entries = ["Bootstrap/OrderedPair.g17"];
  const native = checkNative(files, "ZFG", entries, { includeKernelDetails: false });
  const local = browser.checkWorkbenchFiles(files, "ZFG", entries, { includeKernelDetails: false });
  assert.equal(native.context, "bootstrap");
  assert.equal(local.context, "bootstrap");
  assert.equal(local.digest, native.digest);
  assert.deepEqual(native.checkedFiles, entries);
  assert.deepEqual(native.theorems.map(theorem => theorem.name), [
    "bootstrap.pair.cancel_left",
    "bootstrap.orderedPair.first",
    "bootstrap.orderedPair.injective",
    "bootstrap.orderedPair.bounded",
  ]);
  assert.ok(native.theorems[0].steps.length > 0);
  assert.equal(native.theorems[0].steps.at(-1)?.after.goals.length, 0);
});

test("web workbench routes checking through its local worker rather than an HTTP API", () => {
  const app = readFileSync(new URL("../workbench/app.js", import.meta.url), "utf8");
  const worker = readFileSync(new URL("../workbench/browser-worker.js", import.meta.url), "utf8");
  assert.match(app, /requestWorkbench/);
  assert.doesNotMatch(app, /fetch\(path/);
  assert.match(worker, /generated\/src\/workbench\.js/);
  assert.match(worker, /prepareWorkbenchFiles/);
  assert.match(app, /function prepareThenCheckActive\(\)[\s\S]*activeFile\(\)\?\.id === fileId && activeFile\(\)\?\.source === sourceRevision/);
  assert.match(app, /generation === prepareGeneration && activeFile\(\)\?\.id === fileId/);
  assert.match(app, /if \(generation === checkGeneration\) document\.querySelector\("#check"\)\.disabled = false/);
  assert.match(app, /if \(activeId !== id\) \{[\s\S]*checkGeneration \+= 1;[\s\S]*prepareGeneration \+= 1;/);
});

test("web workbench uses a self-hosted Monaco editor for Grace17 source", () => {
  const html = readFileSync(new URL("../workbench/index.html", import.meta.url), "utf8");
  const app = readFileSync(new URL("../workbench/app.js", import.meta.url), "utf8");
  const loader = readFileSync(new URL("../workbench/generated/monaco/vs/loader.js", import.meta.url), "utf8");
  assert.match(html, /generated\/monaco\/vs\/loader\.js/);
  assert.match(html, /class="monaco-editor-host"/);
  assert.doesNotMatch(html, /<textarea/);
  assert.match(app, /createModel\(file\.source, "grace17"/);
  assert.match(app, /setMonarchTokensProvider\("grace17"/);
  assert.match(app, /setModelMarkers\(model, "grace17"/);
  assert.match(app, /registerHoverProvider\("grace17"/);
  assert.match(app, /id: "grace17\.goToDefinition"/);
  assert.match(app, /keybindings: \[monaco\.KeyCode\.F12\]/);
  assert.match(app, /onDidChangeCursorPosition\(scheduleCursorPosition\)/);
  assert.match(app, /onDidChangeCursorSelection\(scheduleCursorPosition\)/);
  assert.match(app, /if \(key === lastCursorGoalKey\) return/);
  assert.match(app, /notationAtTextOffset/);
  assert.match(app, /class=\"semantic-symbol \$\{symbol\.line \? \"navigable\" : \"\"\}\"/);
  assert.match(app, /goalView\.addEventListener\("click"/);
  assert.match(html, /id="goalSymbolTooltip"/);
  assert.doesNotMatch(app, /DAG nodes<\/span>/);
  assert.match(app, /unicodeHighlight: \{ nonBasicASCII: false, ambiguousCharacters: false/);
  assert.match(loader, /Microsoft Corporation/);
  assert.match(loader, /AMDLoader/);
});

test("desktop workbench uses the compact laptop density at 100 percent zoom", () => {
  const styles = readFileSync(new URL("../workbench/styles.css", import.meta.url), "utf8");
  const app = readFileSync(new URL("../workbench/app.js", import.meta.url), "utf8");
  assert.match(styles, /\.topbar \{ height: 42px/);
  assert.match(styles, /\.pane-heading \{ height: 45px; flex: 0 0 45px/);
  assert.match(styles, /\.file-tabs \{ min-height: 32px; flex: 0 0 32px/);
  assert.match(styles, /\.project-explorer \{ flex: 0 0 210px; width: 210px/);
  assert.match(app, /fontSize: 13,/);
  assert.match(app, /lineHeight: 21,/);
});

test("folder projects separate scoped files from open tabs and expose resizable panes", () => {
  const html = readFileSync(new URL("../workbench/index.html", import.meta.url), "utf8");
  const styles = readFileSync(new URL("../workbench/styles.css", import.meta.url), "utf8");
  const app = readFileSync(new URL("../workbench/app.js", import.meta.url), "utf8");
  assert.match(html, /id="projectExplorer"/);
  assert.match(html, /id="workspaceDivider"[^>]+role="separator"/);
  assert.match(app, /openIds\.map\(id => files\.find/);
  assert.match(app, /preferredProjectFile\(files\)/);
  assert.match(app, /data-project-file/);
  assert.match(app, /Foundation internals/);
  assert.match(app, /setPointerCapture/);
  assert.match(app, /grace17\.editorWidth/);
  assert.match(app, /const expandedProjectFolders = new Set\(\)/);
  assert.match(app, /data-project-folder/);
  assert.match(app, /expandedProjectFolders\.clear\(\)/);
  assert.doesNotMatch(app, /return `<details open><summary>/);
  assert.match(html, /<section class="proof-pane"[^>]*>\s*<button id="toggleProofPane"[^>]+aria-expanded="true"/);
  assert.match(html, /class="proof-pane-rail"[^>]*>[\s\S]*id="restoreProofPane"[^>]*>‹<\/button>/);
  assert.match(styles, /\.workspace\.proof-collapsed \{ grid-template-columns: minmax\(330px, 1fr\) 0 0 34px/);
  assert.match(styles, /\.workspace\.proof-collapsed \.proof-heading-content/);
  assert.match(styles, /\.proof-pane-toggle \{ position: absolute;[^}]*right: 4px/);
  assert.match(styles, /\.workspace\.proof-collapsed \.proof-pane-rail \{ display: block/);
  assert.match(styles, /\.proof-pane-rail \{[^}]*overflow: hidden;[^}]*border-left: 3px solid var\(--signal\)/);
  assert.match(styles, /\.proof-pane-rail button \{ width: 31px; height: 31px/);
  assert.match(styles, /\.project-explorer\.collapsed \{[^}]*flex-basis: 34px; width: 34px;[^}]*border-right: 3px solid var\(--signal\)/);
  assert.match(styles, /\.project-explorer\.collapsed \.explorer-heading \{[^}]*min-height: 31px; padding: 0; border-bottom: 0/);
  assert.match(styles, /\.project-explorer\.collapsed \.explorer-heading button \{[^}]*width: 31px; height: 31px/);
  assert.match(app, /#toggleExplorer[^\n]+setAttribute\("aria-expanded", String\(!explorerInitiallyCollapsed\)\)/);
  assert.match(app, /button\.setAttribute\("aria-expanded", String\(!collapsed\)\)/);
  assert.match(app, /localStorage\.removeItem\("grace17\.proofPaneCollapsed"\);\s*setProofPaneCollapsed\(false\);/);
  assert.match(app, /#restoreProofPane[^\n]+setProofPaneCollapsed\(false\)/);
  assert.doesNotMatch(app, /localStorage\.setItem\("grace17\.proofPaneCollapsed"/);
  assert.match(app, /setProofPaneCollapsed/);
});

test("the workbench permits zero tabs and offers an intentional empty state", () => {
  const html = readFileSync(new URL("../workbench/index.html", import.meta.url), "utf8");
  const styles = readFileSync(new URL("../workbench/styles.css", import.meta.url), "utf8");
  const app = readFileSync(new URL("../workbench/app.js", import.meta.url), "utf8");
  assert.match(html, /id="closeAllFiles"/);
  assert.match(html, /id="unsavedDialog"[^>]+aria-labelledby="unsavedTitle"/);
  assert.match(html, /value="cancel">Cancel<\/button>/);
  assert.match(html, /value="discard">Don’t Save<\/button>/);
  assert.match(html, /value="save" autofocus>Save<\/button>/);
  assert.match(html, /id="emptyWorkspace"/);
  assert.match(html, /class="empty-identity"/);
  assert.doesNotMatch(html, /workspace = ∅/);
  assert.match(html, /Welcome to Cantor's Paradise\./);
  assert.match(html, /It all starts with <code>∅<\/code>\./);
  assert.match(html, /id="emptyBrowseCumulus"/);
  assert.match(html, /id="savedSession"/);
  assert.match(html, /id="restoreSession"/);
  assert.match(html, /id="forgetSession"/);
  assert.match(html, /class="cumulative-universe"/);
  assert.match(html, /The cumulative hierarchy V - a\.k\.a\., the Universe/);
  assert.match(html, /V₀ = ∅/);
  assert.doesNotMatch(html, /sets, built in stages/);
  assert.doesNotMatch(html, /Write a first proof/);
  assert.doesNotMatch(html, /checks the active proof locally/);
  assert.doesNotMatch(html, /Write\.<br>Check\.<br>Inspect\./);
  assert.doesNotMatch(html, /17 \/ Workbench/);
  assert.doesNotMatch(html, /class="runbar"/);
  assert.doesNotMatch(html, /native evaluator ready/);
  assert.match(html, /class="universe-ellipsis"/);
  assert.match(html, /V<tspan baseline-shift="sub">ω\+1<\/tspan>/);
  assert.match(html, /V<tspan baseline-shift="sub">ω·ω<\/tspan>/);
  assert.match(html, /class<\/span> CumulativeUniverse \(x : Set\)/);
  assert.match(html, /∃ α, α ∈ Ordinal ∧ x ∈ V\(α\)/);
  assert.match(html, /noncomputable transfinite def<\/span> V \(α : Ordinal\)/);
  assert.ok(html.indexOf("noncomputable transfinite def") < html.indexOf("CumulativeUniverse"));
  assert.match(app, /async function closeAllFiles\(\)/);
  assert.match(app, /async function closeFile\(id\)/);
  assert.match(app, /if \(!file\.dirty\) return true/);
  assert.match(app, /choice === "discard"/);
  assert.match(app, /choice !== "save"/);
  assert.match(app, /return saveFile\(file\)/);
  assert.match(styles, /\.file-tab\.dirty \.tab-name::after/);
  assert.match(app, /function showEmptyWorkspace\(\)/);
  assert.match(app, /let files = \[\]/);
  assert.match(app, /let openIds = \[\]/);
  assert.doesNotMatch(app, /localStorage\.setItem\("grace17\.files"/);
  assert.doesNotMatch(app, /function restoreFiles\(/);
  assert.match(app, /const WORKSPACE_SESSION_KEY = "grace17\.workspaceSession"/);
  assert.match(app, /function restoreSavedSession\(\)/);
  assert.match(app, /function forgetSavedSession\(\)/);
  assert.doesNotMatch(app, /savedSession = candidate/);
  assert.match(app, /const session = savedSession;\s+savedSession = undefined;/);
  assert.match(app, /async function closeAllFiles\(\) \{[\s\S]*?showEmptyWorkspace\(\);\s+clearSavedSessionRecovery\(\);\s+\}/);
  assert.match(app, /refreshCumulusDistribution\(\)/);
  assert.match(styles, /\.saved-session \{/);
  assert.match(app, /source: `module Scratch\$\{number\}\nimport Grace\.Cumulus\.Main/);
  const scratchTemplate = /function newFile\(\) \{([\s\S]*?)\n\}/.exec(app)?.[1] ?? "";
  assert.doesNotMatch(scratchTemplate, /Copyright|Authors:|Apache License|Interactive scratch module/);
  assert.match(app, /classList\.add\("workspace-empty"\)/);
  assert.match(app, /function browseCumulus\(\)/);
  assert.match(app, /standardLibrary/);
  assert.match(app, /migratePersistedCumulusFiles/);
  assert.doesNotMatch(app, /distributionFiles\.find\(file => file\.projectPath === "Set\/Hierarchy\.g17"\)/);
  assert.match(app, /editor\.setModel\(null\)/);
  assert.doesNotMatch(app, /openIds\.length === 1/);
  assert.doesNotMatch(app, /function run\(\)/);
  assert.match(styles, /\.empty-workspace \{/);
  assert.match(styles, /\.proof-view\[hidden\] \{ display: none; \}/);
  assert.match(styles, /grid-template-columns: repeat\(2, 134px\)/);
});

test("the syntax theme reserves type color for actual built-in type names", () => {
  const app = readFileSync(new URL("../workbench/app.js", import.meta.url), "utf8");
  assert.match(app, /types: \["Set", "Nat", "Ordinal", "Class", "Prop", "ℕ"\]/);
  assert.doesNotMatch(app, /types: \[[^\]]*"Natural"/);
});

test("Symbols guide documents mathematical set notation input", () => {
  const html = readFileSync(new URL("../workbench/index.html", import.meta.url), "utf8");
  for (const entry of ["\\powerset", "\\bigcup", "\\cup", "\\cap", "\\setminus", "\\subset", "\\times", "\\quot"]) {
    assert.match(html, new RegExp(entry.replaceAll("\\", "\\\\")));
  }
  for (const symbol of ["𝒫", "⋃", "∪", "∩", "∖", "⊆", "×", "⧸"]) assert.match(html, new RegExp(symbol));
  assert.match(html, /<code>%<\/code> remainder/);
});

test("workbench About command reports identity, version, license, and project links", () => {
  const html = readFileSync(new URL("../workbench/index.html", import.meta.url), "utf8");
  const styles = readFileSync(new URL("../workbench/styles.css", import.meta.url), "utf8");
  const app = readFileSync(new URL("../workbench/app.js", import.meta.url), "utf8");
  assert.match(html, /id="aboutDialog"/);
  assert.match(html, /length\(\[ω, V\(ω\), 𝒫\(V\(ω\)\)\]\) = 3 by compute/);
  assert.match(html, /Copyright \(c\) 2026 Grant Olney Passmore\./);
  assert.match(html, /<p class="about-creator">Created by Grant Olney Passmore<\/p>/);
  assert.match(html, /Special thanks to <a href="https:\/\/imandra\.ai" target="_blank" rel="noopener noreferrer">Imandra Inc\.<\/a> for supporting my work\./);
  assert.match(html, /Apache License 2\.0/);
  assert.match(html, /https:\/\/grace17\.org/);
  assert.doesNotMatch(html, /apache\.org\/licenses/);
  assert.doesNotMatch(html, /0 = ∅ · from first principles/);
  assert.doesNotMatch(html, /SET THEORY|SMALL KERNEL|LOCAL FIRST/);
  assert.match(app, /id: "grace17\.about"/);
  const version = JSON.parse(readFileSync(new URL("../package.json", import.meta.url), "utf8")).version;
  const browserVersion = readFileSync(new URL("../workbench/generated/version.js", import.meta.url), "utf8");
  const serviceWorker = readFileSync(new URL("../workbench/service-worker.js", import.meta.url), "utf8");
  assert.match(app, /import \{ version as WORKBENCH_VERSION \} from "\.\/generated\/version\.js"/);
  assert.match(browserVersion, new RegExp(`export const version = "${version.replaceAll(".", "\\.")}"`));
  // The cache name carries a digest of the build, so every deploy starts a
  // fresh cache: the version alone did not change between deploys.
  const build = /export const build = "([^"]+)"/.exec(browserVersion)?.[1];
  assert.match(build ?? "", new RegExp(`^${version.replaceAll(".", "\\.")}-[0-9a-f]{12}$`));
  assert.ok(serviceWorker.includes("const cacheName = `${cachePrefix}v" + build + "`;"));
  assert.match(html, /The grace17 proof assistant for<br>mathematics based on set theory\./);
  assert.match(html, />grace17\.org <span>↗<\/span><\/a>/);
  assert.doesNotMatch(styles, /\.about-links a \{[^}]*text-transform:\s*uppercase/);
});

test("workbench exposes progressive, searchable Help", () => {
  const html = readFileSync(new URL("../workbench/index.html", import.meta.url), "utf8");
  const styles = readFileSync(new URL("../workbench/styles.css", import.meta.url), "utf8");
  const app = readFileSync(new URL("../workbench/app.js", import.meta.url), "utf8");
  const serviceWorker = readFileSync(new URL("../workbench/service-worker.js", import.meta.url), "utf8");
  assert.match(html, /<button id="tactics" class="quiet">Help<\/button>/);
  assert.match(html, /From a first definition to a checked inductive proof\./);
  assert.match(html, /id="tacticsDialog"/);
  assert.match(html, /id="tacticsSearch"/);
  assert.match(app, /import \{[^\n]*helpInferenceRule[^\n]*highlightGrace17[^\n]*tacticGuideSections[^\n]*\} from "\.\/tactics-guide\.js"/);
  assert.match(app, /function renderTacticsGuide/);
  assert.match(app, /id: "grace17\.help"/);
  assert.match(app, /qualifiedSymbolCompletions/);
  assert.match(styles, /\.tactic-entry \{/);
  assert.match(styles, /\.help-inference \{/);
  assert.match(styles, /\.g17-keyword \{/);
  assert.match(serviceWorker, /tactics-guide\.js/);
  const openFolder = html.indexOf('id="openFolder"');
  const openFile = html.indexOf('id="openFile"');
  const save = html.indexOf('id="saveFile"');
  const help = html.indexOf('id="tactics"');
  const about = html.indexOf('id="about"');
  const check = html.indexOf('id="check"');
  assert.ok(openFolder < openFile && openFile < save && save < help && help < about && about < check);
});

test("workbench uses the Empathy blue-cyan ANSI palette without purple accents", () => {
  const html = readFileSync(new URL("../workbench/index.html", import.meta.url), "utf8");
  const styles = readFileSync(new URL("../workbench/styles.css", import.meta.url), "utf8");
  const app = readFileSync(new URL("../workbench/app.js", import.meta.url), "utf8");
  const visualizer = readFileSync(new URL("../src/visualizer.ts", import.meta.url), "utf8");
  const wordmark = readFileSync(new URL("../workbench/assets/grace17-wordmark-dark.svg", import.meta.url), "utf8");
  assert.match(styles, /--ink-deep: #000000/);
  assert.match(styles, /--signal: #00c8d7/);
  assert.match(styles, /--blue: #2c77c7/);
  assert.match(app, /"editor\.selectionBackground": "#2C77C780"/);
  assert.match(app, /foreground: "57F4FF"/);
  assert.equal(html.match(/assets\/grace17-wordmark-dark\.svg/g)?.length, 3);
  assert.equal(wordmark.match(/stroke="#57f4ff"/g)?.length, 2);
  assert.doesNotMatch(wordmark, /#55b39e/i);
  assert.doesNotMatch(`${styles}\n${app}\n${visualizer}`, /#(?:5a45c7|b7a8ff|2d2942|29253c|efecff|f3f0ff)/i);
});

test("workbench uses a merged mono proof jump bar and removes redundant labels", () => {
  const html = readFileSync(new URL("../workbench/index.html", import.meta.url), "utf8");
  const styles = readFileSync(new URL("../workbench/styles.css", import.meta.url), "utf8");
  const app = readFileSync(new URL("../workbench/app.js", import.meta.url), "utf8");
  assert.match(styles, /\.pane-heading h1 \{[^}]*var\(--mono\)/);
  assert.match(styles, /\.proof-jump select \{[^}]*var\(--mono\)/);
  assert.match(html, /class="proof-jump"/);
  assert.doesNotMatch(`${html}\n${app}`, /CHECKED PROOF|PROJECT FILE|>KERNEL<|>Info<|CURRENT GOAL|FOCUSED|LAST VALID GOAL RETAINED|Click to reveal/);
  assert.match(styles, /\.goal-card \{[^}]*border-left: 3px solid var\(--signal\)/);
  assert.match(styles, /\.monaco-editor \.diagnostic-span \{[^}]*border-bottom: 2px solid var\(--red\)/);
  assert.match(app, /class="proof-position"/);
  assert.doesNotMatch(app, /class="proof-error"/);
  assert.match(app, /No goals remain: proof complete/);
  assert.match(app, /Proof complete, modulo \$\{count\}/);
  assert.match(app, /data-toggle-sorries/);
  assert.match(app, /data-sorry-site/);
  assert.match(app, /class="sorry-sites"/);
  assert.match(styles, /\.qed-state \{/);
  assert.match(styles, /\.position-mark \{[^}]*var\(--signal\)/);
  assert.doesNotMatch(styles, /\.goal-card\.remaining-goal/);
  assert.match(app, /Proof in progress/);
  assert.doesNotMatch(app, /Editing —/);
});

test("choosing a proof from the jump bar also reveals its source declaration", () => {
  const app = readFileSync(new URL("../workbench/app.js", import.meta.url), "utf8");
  assert.match(app, /theoremSelect\.addEventListener\("change", \(\) => \{[\s\S]*const theorem = selectedTheorem\(\);[\s\S]*renderTheorem\(\);[\s\S]*jumpToLine\(theorem\.lineStart\);[\s\S]*\}\);/);
});

test("kernel proof drawer presents a resizable Fitch-style derivation", () => {
  const html = readFileSync(new URL("../workbench/index.html", import.meta.url), "utf8");
  const styles = readFileSync(new URL("../workbench/styles.css", import.meta.url), "utf8");
  const app = readFileSync(new URL("../workbench/app.js", import.meta.url), "utf8");
  assert.match(html, /id="kernelResizeHandle"/);
  assert.match(html, /id="kernelScroller"/);
  assert.match(html, /aria-orientation="horizontal"/);
  assert.match(app, /kernelFitchOrder\(theorem\.kernel\)/);
  assert.match(app, /class="fitch-line/);
  assert.match(app, /class="fitch-rail"/);
  assert.match(app, /class="fitch-justification"/);
  assert.match(app, /class="fitch-arguments"/);
  assert.doesNotMatch(app, /class="fitch-context/);
  assert.match(app, /class="nd-inference"/);
  assert.match(app, /class="nd-premises"/);
  assert.match(app, /class="nd-rule-bar"/);
  assert.match(app, /class="nd-conclusion"/);
  assert.match(app, /class="nd-side-conditions"/);
  assert.match(app, /configureKernelDivider\(\)/);
  assert.match(app, /grace17\.kernelHeight/);
  assert.match(styles, /\.fitch-line > summary/);
  assert.match(styles, /\.kernel-resize-handle/);
  assert.match(styles, /\.kernel-drawer\[open\] > \.kernel-scroller \{[^}]*position: absolute;[^}]*inset: 32px 0 0;[^}]*overflow-y: scroll/);
  assert.match(styles, /\.nd-inference \{/);
  assert.doesNotMatch(app, /class="kernel-step"/);
});

test("qed marks use outlined letters, exact brand membership strokes, and admission rollups", () => {
  const app = readFileSync(new URL("../workbench/app.js", import.meta.url), "utf8");
  const styles = readFileSync(new URL("../workbench/styles.css", import.meta.url), "utf8");
  const proven = readFileSync(new URL("../workbench/assets/qed-mark.svg", import.meta.url), "utf8");
  const sorry = readFileSync(new URL("../workbench/assets/qed-mark-sorry.svg", import.meta.url), "utf8");
  for (const mark of [proven, sorry]) {
    assert.doesNotMatch(mark, /<text\b/);
    assert.match(mark, /M 310 77\.92 A 28 28 0 1 0 310 121\.92/);
    assert.match(mark, /M 269\.09 99\.92 L 311\.92 99\.92/);
    assert.match(mark, /stroke-width="9\.2"/);
  }
  assert.match(proven, /#f2ecdd/);
  assert.equal(proven.match(/#57f4ff/g)?.length, 2);
  assert.doesNotMatch(proven, /#55b39e/i);
  assert.match(styles, /--proven: #57f4ff/);
  assert.match(sorry, /#cfc8b8/);
  assert.match(sorry, /#d9a441/);
  assert.equal(sorry.match(/stroke-dasharray=/g)?.length, 1);
  assert.match(app, /function sorryDashArray/);
  assert.match(app, /class="rollup-mark \$\{state\}"/);
  assert.match(styles, /\.monaco-editor \.sorry-span/);
  assert.match(styles, /\.monaco-editor \.sorry-gutter-dot/);
  assert.match(styles, /@media \(prefers-reduced-motion: reduce\)/);
  assert.match(styles, /@keyframes qed-bar-upgrade/);
});

test("sorry lists navigate only after site selection and goal tooltips dismiss deterministically", () => {
  const app = readFileSync(new URL("../workbench/app.js", import.meta.url), "utf8");
  const styles = readFileSync(new URL("../workbench/styles.css", import.meta.url), "utf8");
  assert.match(app, /expandedSorryTheorems/);
  assert.match(app, /jumpToSorrySite\(selectedTheorem\(\), Number\(sorrySite\.dataset\.sorrySite\)\)/);
  assert.doesNotMatch(app, /jumpToNextSorry/);
  assert.match(styles, /\.sorry-sites li::before/);
  assert.match(app, /function dismissGoalSymbolTooltip/);
  assert.match(app, /goalView\.addEventListener\("pointerleave", dismissGoalSymbolTooltip\)/);
  assert.match(app, /hoveredGoalSymbol !== target/);
  assert.match(app, /dismissGoalSymbolTooltip\(\);\n  goToDefinition\(symbol\)/);
  assert.match(app, /class="semantic-symbol \$\{symbol\.line \? "navigable" : ""\}"/);
  assert.match(app, /resolveSymbolCandidate\(result\.symbols, name/);
  assert.match(app, /call: \/\^\\s\*\\\(\//);
  assert.match(app, /goalView\.addEventListener\("keydown"/);
  assert.match(app, /data-local-symbol=\"true\"/);
  assert.match(app, /kind: "local"/);
  assert.match(app, /goalView\.addEventListener\("focusin"/);
});

test("finite-set notation carries elaboration metadata in source and goals", () => {
  const app = readFileSync(new URL("../workbench/app.js", import.meta.url), "utf8");
  assert.match(app, /setNotation\.desugaring/);
  assert.match(app, /data-semantic-info/);
  assert.match(app, /target\.dataset\.semanticInfo/);
  assert.match(app, /"ext"/);
});

test("structured mathematical notation keeps its raw elaboration discoverable", () => {
  const app = readFileSync(new URL("../workbench/app.js", import.meta.url), "utf8");
  assert.match(app, /equivalenceClassNotationAtTextOffset/);
  assert.match(app, /equivalenceNotation\.desugaring/);
});

test("the Workbench fixes its foundation to ZFG without a crowded selector", () => {
  const html = readFileSync(new URL("../workbench/index.html", import.meta.url), "utf8");
  const app = readFileSync(new URL("../workbench/app.js", import.meta.url), "utf8");
  const worker = readFileSync(new URL("../workbench/browser-worker.js", import.meta.url), "utf8");
  const server = readFileSync(new URL("../bin/workbench.ts", import.meta.url), "utf8");
  assert.doesNotMatch(html, /id="foundation"/);
  assert.doesNotMatch(app, /querySelector\("#foundation"\)/);
  assert.match(worker, /checkWorkbenchFiles\(files, "ZFG", active, \{ includeKernelDetails: false, includeEnvironmentDigest: false \}\)/);
  assert.match(server, /checkWorkbenchFiles\(files, "ZFG"/);
});

test("local workbench launch bypasses stale PWA caches", () => {
  const app = readFileSync(new URL("../workbench/app.js", import.meta.url), "utf8");
  const serviceWorker = readFileSync(new URL("../workbench/service-worker.js", import.meta.url), "utf8");
  const launcher = readFileSync(new URL("../bin/workbench.ts", import.meta.url), "utf8");
  assert.match(app, /getRegistrations\(\)/);
  assert.match(app, /name\.startsWith\("grace17-workbench-"\)/);
  assert.match(serviceWorker, /fetch\(event\.request, \{ cache: "no-store" \}\)/);
  assert.match(launcher, /\?fresh=\$\{encodeURIComponent\(version\)\}/);
  assert.match(launcher, /location\.replace/);
});

test("browser builds retain complete vendored Monaco assets without node_modules", () => {
  const project = mkdtempSync(join(tmpdir(), "grace17-monaco-project-"));
  const output = join(project, "workbench", "generated");
  try {
    mkdirSync(join(output, "monaco", "vs", "editor"), { recursive: true });
    writeFileSync(join(output, "monaco", "vs", "loader.js"), "vendored loader");
    writeFileSync(join(output, "monaco", "vs", "editor", "editor.main.js"), "vendored editor");
    writeFileSync(join(output, "monaco", "LICENSE"), "MIT");
    writeFileSync(join(output, "monaco", "ThirdPartyNotices.txt"), "notices");
    assert.equal(stageMonacoAssets(project, output), "vendored");
    assert.equal(readFileSync(join(output, "monaco", "vs", "loader.js"), "utf8"), "vendored loader");
  } finally {
    rmSync(project, { recursive: true, force: true });
  }
});

test("Prime retains cursor goal states after dependency-only checking and cached rechecks", async () => {
  const browser = await import("../workbench/generated/src/workbench.js");
  const { standardLibrary } = await import("../workbench/generated/shims/standard-library.js");
  const { tacticStepAtCursor } = await import("../workbench/editor-utils.js");
  const name = "lib/Grace/Cumulus/NumberTheory/Prime.g17";
  const prime = { name, source: standardLibrary.get(name)! };
  const client = { name: "PrimeCursorClient.g17", source: `module PrimeCursor.Client
namespace PrimeCursor.Client
import Grace.Cumulus.NumberTheory.Prime
theorem reflexive (x : Set)
  shows x = x
proof
  rfl

end PrimeCursor.Client
` };
  browser.prepareWorkbenchFiles([prime], "ZFG", name);
  browser.prepareWorkbenchFiles([prime, client], "ZFG", client.name);
  const check = (file = prime) => browser.checkWorkbenchFiles([file], "ZFG", [name], { includeKernelDetails: false });
  const first = check();
  const verify = (result: any) => {
    const proof = result.theorems.find((item: any) => item.name.endsWith("Prime.positive_membership"));
    assert.ok(proof?.initial?.goals.length, "successful Prime proof must retain its initial goal");
    assert.ok(proof.steps.length > 5, "dependency-only cache must not erase interactive steps");
    const states = [proof.initial, ...proof.steps.map((step: any) => step.after)];
    assert.ok(states[tacticStepAtCursor(proof.steps, proof.lineStart, 1)].goals.length);
    assert.ok(states[tacticStepAtCursor(proof.steps, proof.steps[2].line, 100)].goals.length);
    assert.equal(states[tacticStepAtCursor(proof.steps, proof.steps.at(-1).line, 100)].goals.length, 0);
    return proof;
  };
  const original = verify(first);
  assert.deepEqual(verify(check()).steps, original.steps);
  assert.deepEqual(verify(check({ ...prime, source: prime.source + "\n-- cursor trace regression\n" })).steps, original.steps);
});

test("a larger checked prefix wins over a smaller bundled dependency checkpoint", async () => {
  const browser = await import("../workbench/generated/src/workbench.js");
  const { Kernel } = await import("../workbench/generated/src/kernel.js");
  const { standardDependencyCheckpoints } = await import("../workbench/generated/src/standard-checkpoints.js");
  assert.ok(standardDependencyCheckpoints.has("Grace.Cumulus.Real.Squares"));
  await installBundledCheckpoint("Grace.Cumulus.Real.Squares");
  const seed = { name: "PrefixSeed.g17", source: `module PrefixSeed
import Grace.Cumulus.Real.Squares
namespace PrefixSeed
theorem identity (x : Set)
  shows x = x
proof
  rfl
end PrefixSeed
` };
  const extra = { name: "PrefixExtra.g17", source: `module PrefixExtra
namespace PrefixExtra
theorem identity (x : Set)
  shows x = x
proof
  rfl
end PrefixExtra
` };
  const first = { name: "PrefixFirst.g17", source: "module PrefixFirst\nimport PrefixSeed\n" };
  const second = { name: "PrefixSecond.g17", source: "module PrefixSecond\nimport PrefixSeed\nimport PrefixExtra\n" };
  const files = [seed, extra, first, second];
  const prepared = browser.prepareWorkbenchFiles(files, "ZFG", first.name);
  assert.ok(prepared.symbols.includes("PrefixSeed.identity"));
  const original = Kernel.prototype.addTheoremMachineBatch;
  let replayedBatches = 0;
  Kernel.prototype.addTheoremMachineBatch = function (...args) {
    replayedBatches++;
    return original.apply(this, args);
  };
  try {
    const extended = browser.prepareWorkbenchFiles(files, "ZFG", second.name);
    assert.ok(extended.symbols.includes("PrefixSeed.identity"));
    assert.ok(extended.symbols.includes("PrefixExtra.identity"));
    assert.equal(replayedBatches, 0, "a smaller bundled prefix must not replace a larger already checked prefix");
    const changed = { ...seed, source: seed.source.replace("shows x = x", "shows x = ∅") };
    assert.throws(() => browser.prepareWorkbenchFiles([changed, extra, first, second], "ZFG", second.name),
      /reflex|rfl|equal|goal/i, "changed source must invalidate the checked prefix");
  } finally {
    Kernel.prototype.addTheoremMachineBatch = original;
  }
});

test("a library module checks as a workspace file over forked imports", () => {
  // Carrier annotations made while elaborating imports must reach a module
  // checked in a forked kernel, as the Workbench does for every opened file.
  const name = "lib/Grace/Cumulus/Real/Analysis/Integration/FTCFirst.g17";
  const result = checkNative([{ name, source: readFileSync(name, "utf8") }], "ZFG", [name], { includeKernelDetails: false });
  assert.equal(result.ok, true, result.message);
  assert.ok(result.theorems.some(theorem => theorem.name.endsWith("FTC.continuous_derivative")));
});

test("a kept checkpoint exported by the browser replays as a prefix for a later workspace", async () => {
  const browser = await import("../workbench/generated/src/workbench.js");
  const { standardLibrary } = await import("../workbench/generated/shims/standard-library.js");
  const active = "lib/Grace/Cumulus/Set/Hierarchy.g17";
  const source = standardLibrary.get(active);
  assert.ok(source);
  const prepared = browser.prepareWorkbenchFiles([{ name: active, source }], "ZFG", active);
  assert.ok(prepared.modules >= 5);
  const plan = browser.dependencyCheckpointPlan([{ name: active, source }], "ZFG", active);
  assert.equal(plan?.exact, true);
  assert.equal(plan?.elaborated, prepared.modules);
  assert.ok((plan?.elaboratedMilliseconds ?? 0) > 0);
  const kept = browser.exportDependencyCheckpoint([{ name: active, source }], "ZFG", active);
  assert.ok(kept);
  assert.equal(kept.rootModule, `kept:${plan!.key}`);
  assert.equal(kept.sources.length, prepared.modules);
  // Round trip through JSON as storage would, then install it and prepare a
  // file whose closure extends the kept one by the hierarchy module itself.
  browser.installStandardCheckpoint(JSON.parse(JSON.stringify(kept)));
  const extension = { name: "KeptSeed.g17", source: `module KeptSeed
import Grace.Cumulus.Set.Hierarchy
namespace KeptSeed
theorem identity (x : Set)
  shows x = x
proof
  rfl
end KeptSeed
` };
  const extended = browser.dependencyCheckpointPlan([extension], "ZFG", extension.name);
  assert.equal(extended?.installedPrefix, prepared.modules);
  assert.equal(extended?.standard, undefined);
  const preparedExtension = browser.prepareWorkbenchFiles([extension], "ZFG", extension.name);
  assert.equal(preparedExtension.modules, prepared.modules + 1);
  const checked = browser.checkWorkbenchFiles([extension], "ZFG", [extension.name], { includeKernelDetails: false });
  assert.equal(checked.ok, true);
  const identity = checked.theorems.find((theorem: { name: string }) => theorem.name.endsWith("KeptSeed.identity"));
  assert.ok(identity, "the extension's theorem is checked over the kept prefix");
  assert.deepEqual(identity.sorries, []);
});
