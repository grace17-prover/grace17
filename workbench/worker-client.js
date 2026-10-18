// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

let nextId = 1;
const pending = new Map();
const worker = new Worker(new URL("./browser-worker.js", import.meta.url), { type: "module", name: "grace17-kernel" });

worker.addEventListener("message", event => {
  const request = pending.get(event.data.id);
  if (!request) return;
  pending.delete(event.data.id);
  request.resolve(event.data.result);
});

worker.addEventListener("error", event => {
  for (const request of pending.values()) request.reject(new Error(event.message || "Grace17 browser worker failed"));
  pending.clear();
});

export function requestWorkbench(operation, body) {
  return new Promise((resolve, reject) => {
    const id = nextId++;
    pending.set(id, { resolve, reject });
    worker.postMessage({ id, operation, body });
  });
}
