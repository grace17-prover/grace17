// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import {
  auditWorkbenchTheorem, checkWorkbenchFiles, dependencyCheckpointPlan, exportDependencyCheckpoint,
  installStandardCheckpoint, prepareWorkbenchFiles, runWorkbenchFiles, workbenchFailure,
} from "./generated/src/workbench.js";
import { standardDependencyCheckpoints } from "./generated/src/standard-checkpoints.js";

// Requests are answered in order. Before a workspace is prepared or checked,
// the best checkpoint for its dependency prefix is made available: one this
// browser kept from an earlier elaboration, or a bundled one fetched on first
// use. Both are installed as standard checkpoints, so the checker itself
// never waits on the network or on storage.
let queue = Promise.resolve();
self.addEventListener("message", event => {
  const { id, operation, body } = event.data;
  queue = queue.then(async () => {
    try {
      const files = workspaceFiles(body);
      const activeName = body.activeFile === undefined ? undefined : String(body.activeFile);
      const active = activeName === undefined ? undefined : [activeName];
      if (operation !== "run") await provideCheckpoint(files, activeName);
      const result = operation === "axiom-audit"
        ? auditWorkbenchTheorem(files, String(body.theorem ?? ""), "ZFG", active)
        : operation === "prepare"
        ? prepareWorkbenchFiles(files, "ZFG", activeName)
        : operation === "check"
        ? checkWorkbenchFiles(files, "ZFG", active, { includeKernelDetails: false, includeEnvironmentDigest: false })
        : operation === "inspect"
          ? checkWorkbenchFiles(files, "ZFG", active, { includeKernelDetails: true })
          : runWorkbenchFiles(files, String(body.function ?? ""), naturalArguments(body.args), "ZFG", active);
      self.postMessage({ id, result });
      if (operation === "prepare" || operation === "check") scheduleKeep(files, activeName);
    } catch (error) {
      self.postMessage({ id, result: workbenchFailure(error) });
    }
  });
});

function workspaceFiles(body) {
  if (!Array.isArray(body.files) || body.files.length === 0) throw new Error("Workspace has no files");
  return body.files.map(file => ({ name: String(file.name), source: String(file.source) }));
}

function naturalArguments(value) {
  const raw = Array.isArray(value) ? value : String(value ?? "").split(",").filter(Boolean);
  return raw.map(item => {
    const text = String(item).trim();
    if (!/^\d+$/.test(text)) throw new Error("Run arguments must be natural numerals");
    return BigInt(text);
  });
}

// Checkpoint provision: a kept checkpoint for exactly this dependency set
// wins; otherwise the largest bundled prefix whose payload is still on the
// server is fetched. A kept checkpoint stands on a bundled one, which is
// fetched first. Failures fall back to elaboration.
const fetching = new Map();
async function provideCheckpoint(files, activeName) {
  let plan;
  try { plan = dependencyCheckpointPlan(files, "ZFG", activeName); } catch { return; }
  if (!plan || plan.exact) return;
  if (plan.installedPrefix < plan.modules) {
    const kept = await readKept(plan.key).catch(() => undefined);
    if (kept) {
      installStandardCheckpoint(kept);
      await ensureInstalled(kept.rootModule);
      return;
    }
  }
  if (plan.standard) await ensureInstalled(plan.standard.rootModule);
}
async function ensureInstalled(rootModule) {
  const entry = standardDependencyCheckpoints.get(rootModule);
  if (!entry) return;
  if (entry.prefix !== undefined) await ensureInstalled(entry.prefix);
  if (entry.compiled || !entry.file) return;
  if (!fetching.has(rootModule)) {
    fetching.set(rootModule, (async () => {
      const response = await fetch(new URL(`generated/${entry.file}`, self.location.href));
      if (!response.ok) throw new Error(`checkpoint ${response.status}`);
      installStandardCheckpoint({ rootModule, ...await response.json() });
    })().catch(() => { fetching.delete(rootModule); }));
  }
  await fetching.get(rootModule);
}

// Keeping: once a prepared prefix has spent long enough elaborating modules
// from source, it is compiled and stored in this browser, in a quiet moment
// after the requests that needed it have been answered.
const keepThresholdMilliseconds = 1500;
const keepDatabase = "grace17-workbench-checkpoints";
const keepStore = "checkpoints";
const keepBudget = 400 * 1024 * 1024;
let keepTimer;
function scheduleKeep(files, activeName) {
  clearTimeout(keepTimer);
  keepTimer = setTimeout(() => { queue = queue.then(() => keep(files, activeName).catch(() => {})); }, 1500);
}
async function keep(files, activeName) {
  const plan = dependencyCheckpointPlan(files, "ZFG", activeName);
  if (!plan?.exact || (plan.elaboratedMilliseconds ?? 0) < keepThresholdMilliseconds) return;
  if (await hasKept(plan.key)) return;
  const exported = exportDependencyCheckpoint(files, "ZFG", activeName);
  if (!exported) return;
  const payload = JSON.stringify(exported);
  await writeKept({ key: plan.key, stored: Date.now(), bytes: payload.length, payload });
}

function openKept() {
  return new Promise((resolve, reject) => {
    if (!("indexedDB" in self)) return reject(new Error("no storage"));
    const request = indexedDB.open(keepDatabase, 1);
    request.onupgradeneeded = () => {
      const store = request.result.createObjectStore(keepStore, { keyPath: "key" });
      store.createIndex("stored", "stored");
    };
    request.onsuccess = () => resolve(request.result);
    request.onerror = () => reject(request.error);
  });
}
const settle = request => new Promise((resolve, reject) => {
  request.onsuccess = () => resolve(request.result);
  request.onerror = () => reject(request.error);
});
async function hasKept(key) {
  const database = await openKept().catch(() => undefined);
  if (!database) return false;
  const found = await settle(database.transaction(keepStore).objectStore(keepStore).getKey(key));
  database.close();
  return found !== undefined;
}
async function readKept(key) {
  const database = await openKept();
  const entry = await settle(database.transaction(keepStore).objectStore(keepStore).get(key));
  if (entry) {
    const touch = database.transaction(keepStore, "readwrite");
    touch.objectStore(keepStore).put({ ...entry, stored: Date.now() });
  }
  database.close();
  return entry ? JSON.parse(entry.payload) : undefined;
}
async function writeKept(entry) {
  const database = await openKept();
  const transaction = database.transaction(keepStore, "readwrite");
  const store = transaction.objectStore(keepStore);
  store.put(entry);
  // Evict the least recently used entries once the budget is exceeded.
  const all = await settle(store.getAll());
  let total = all.reduce((sum, item) => sum + (item.bytes ?? 0), 0);
  for (const item of all.sort((left, right) => left.stored - right.stored)) {
    if (total <= keepBudget || item.key === entry.key) continue;
    store.delete(item.key);
    total -= item.bytes ?? 0;
  }
  await new Promise((resolve, reject) => { transaction.oncomplete = resolve; transaction.onerror = () => reject(transaction.error); });
  database.close();
}
