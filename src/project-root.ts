// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { fileURLToPath } from "node:url";

// The repository root, from which the library and workbench are located. A
// prebuilt copy of the sources (scripts/build-cli.ts) rewrites the relative
// path below, so this is the only place that knows where the sources live.
export const projectRoot = fileURLToPath(new URL("..", import.meta.url));
