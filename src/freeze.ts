// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// One mark of deeply frozen certificates shared by the kernel, the proof
// machine, and the artifact loaders, so checked data is walked once.
//
// The mark is a private field of a module-local class, installed on the
// certificate through the constructor's return override. Code outside this
// module can neither read nor forge it, as it could not a private weak set,
// and testing it is a property lookup rather than an ephemeron-table probe:
// a whole-library check spent nearly half its time in that table.

class Certificate { constructor(target: object) { return target; } }
class DeeplyFrozen extends Certificate {
  #deeplyFrozen = true;
  constructor(target: object) { super(target); }
  static has(target: object): boolean { return #deeplyFrozen in target; }
  /** Mark `target`; an exotic object that refuses the field is simply walked again next time. */
  static mark(target: object): void { try { new DeeplyFrozen(target); } catch { /* unmarked */ } }
}

/**
 * Freeze a successfully checked certificate before retaining an identity
 * cache entry. Only objects with object-valued children are marked: a frozen
 * container of primitives cannot change and is cheaper to rescan than to
 * carry a mark, and the arenas of a proof machine program hold millions.
 */
export function deepFreeze(value: unknown): void {
  if (value === null || typeof value !== "object" || DeeplyFrozen.has(value)) return;
  Object.freeze(value);
  if (!hasObjectChild(value)) return;
  // Mark before descending, so a shared or cyclic structure stops here.
  DeeplyFrozen.mark(value);
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

/** Whether `value` is a marked deeply frozen container. */
export function isDeeplyFrozen(value: object): boolean {
  return DeeplyFrozen.has(value);
}
