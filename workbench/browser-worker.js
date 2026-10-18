// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { auditWorkbenchTheorem, checkWorkbenchFiles, prepareWorkbenchFiles, runWorkbenchFiles, workbenchFailure } from "./generated/src/workbench.js";

self.addEventListener("message", event => {
  const { id, operation, body } = event.data;
  try {
    const files = workspaceFiles(body);
    const active = body.activeFile === undefined ? undefined : [String(body.activeFile)];
    const result = operation === "axiom-audit"
      ? auditWorkbenchTheorem(files, String(body.theorem ?? ""), "ZFG", active)
      : operation === "prepare"
      ? prepareWorkbenchFiles(files, "ZFG", body.activeFile === undefined ? undefined : String(body.activeFile))
      : operation === "check"
      ? checkWorkbenchFiles(files, "ZFG", active, { includeKernelDetails: false, includeEnvironmentDigest: false })
      : operation === "inspect"
        ? checkWorkbenchFiles(files, "ZFG", active, { includeKernelDetails: true })
        : runWorkbenchFiles(files, String(body.function ?? ""), naturalArguments(body.args), "ZFG", active);
    self.postMessage({ id, result });
  } catch (error) {
    self.postMessage({ id, result: workbenchFailure(error) });
  }
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
