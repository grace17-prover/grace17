// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Preloaded by scripts/run-tests.ts: library imports in every test come
// from a module store under build/test-store, built on first use and reused
// while the sources are unchanged, instead of being elaborated per test file.

import { basename } from "node:path";
import { installLibraryStore } from "../../src/module-store.ts";

// These files examine source elaboration itself: admission streams and
// machine tapes, loader order, checker construction, checks with Choice
// absent, and source-level proof states. They load the library from source.
const fromSource = new Set([
  "compiled-module.test.ts", "core-library.test.ts", "cumulus.test.ts", "evidence-checking.test.ts",
  "module-loader.test.ts", "ordinal-hierarchy.test.ts", "python-g17c.test.ts", "rust-checker.test.ts", "type-system.test.ts", "unique-definitions.test.ts",
  "workbench.test.ts", "zf-library.test.ts",
]);
const testFile = process.argv.find(argument => argument.endsWith(".test.ts"));
if (!testFile || !fromSource.has(basename(testFile))) {
  installLibraryStore(process.env.G17_LIBRARY_STORE ?? "build/test-store", ["lib"]);
}
