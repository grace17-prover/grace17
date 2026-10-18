// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// One registry of deeply frozen certificates shared by the kernel, the proof
// machine, and the artifact loaders, so checked data is walked once.

const deeplyFrozenCertificates = new WeakSet<object>();

/**
 * Freeze a successfully checked certificate before retaining an identity
 * cache entry. Only objects with object-valued children are recorded in the
 * registry: a frozen container of primitives cannot change and is cheaper to
 * rescan than to keep as one of millions of weak entries, which otherwise
 * dominate garbage collection and rehashing when a whole library is compiled.
 */
export function deepFreeze(value: unknown): void {
  if (value === null || typeof value !== "object" || deeplyFrozenCertificates.has(value)) return;
  Object.freeze(value);
  // A container of primitives is frozen without touching the registry: the
  // arenas of a proof machine program hold millions of them, and adding each
  // only to drop it again keeps the weak table permanently rehashing.
  if (!hasObjectChild(value)) return;
  // Register before descending, so a shared or cyclic structure stops here.
  deeplyFrozenCertificates.add(value);
  if (Array.isArray(value)) {
    for (const child of value) deepFreeze(child);
  } else {
    for (const key in value) deepFreeze((value as Record<string, unknown>)[key]);
  }
}

function hasObjectChild(value: object): boolean {
  if (Array.isArray(value)) {
    for (const child of value) if (child !== null && typeof child === "object") return true;
    return false;
  }
  for (const key in value) {
    const child = (value as Record<string, unknown>)[key];
    if (child !== null && typeof child === "object") return true;
  }
  return false;
}

/** Whether `value` is a registered deeply frozen container. */
export function isDeeplyFrozen(value: object): boolean {
  return deeplyFrozenCertificates.has(value);
}
