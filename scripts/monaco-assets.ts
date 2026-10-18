// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { cpSync, existsSync, rmSync } from "node:fs";
import { join } from "node:path";

/**
 * Refresh Monaco from an installed dependency when available. Release archives
 * deliberately exclude node_modules and carry the generated assets instead.
 */
export function stageMonacoAssets(project: string, output: string): "installed" | "vendored" {
  const packageRoot = join(project, "node_modules", "monaco-editor");
  const source = join(packageRoot, "min", "vs");
  const destination = join(output, "monaco", "vs");
  if (existsSync(source)) {
    rmSync(destination, { recursive: true, force: true });
    cpSync(source, destination, { recursive: true });
    cpSync(join(packageRoot, "LICENSE"), join(output, "monaco", "LICENSE"));
    cpSync(join(packageRoot, "ThirdPartyNotices.txt"), join(output, "monaco", "ThirdPartyNotices.txt"));
    return "installed";
  }
  const required = [
    join(destination, "loader.js"),
    join(destination, "editor", "editor.main.js"),
    join(output, "monaco", "LICENSE"),
    join(output, "monaco", "ThirdPartyNotices.txt"),
  ];
  if (!required.every(existsSync)) throw new Error("Monaco assets are missing; run npm install once to restore them");
  return "vendored";
}
