// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Module names. A file that declares `module Name` with a bare name takes its
// qualified name from its path under a module root, as OCaml takes a module's
// name from its file: lib/Grace/Cumulus/Real/FiniteSum.g17 declaring
// `module FiniteSum` is Grace.Cumulus.Real.FiniteSum. An import is resolved
// relative to the importing module: first inside the module itself, then in
// each enclosing namespace outward, and last as an absolute name.

const SEGMENT = /^[\p{L}_][\p{L}\p{M}\p{N}_]*$/u;

/** The qualified module name a `.g17` file under one of the roots denotes. */
export function moduleNameFromPath(file: string, roots: readonly string[]): string | undefined {
  const normal = file.replace(/\\/g, "/");
  if (!normal.endsWith(".g17")) return undefined;
  for (const root of roots) {
    const base = root.replace(/\\/g, "/").replace(/\/+$/, "");
    const prefix = base === "" || base === "." ? "" : `${base}/`;
    let relative: string | undefined;
    if (prefix === "") {
      relative = normal.startsWith("/") ? undefined : normal.slice(0, -4);
    } else if (normal.startsWith(prefix)) {
      relative = normal.slice(prefix.length, -4);
    } else {
      // A path written relative to the root's directory, such as the
      // browser's "lib/Grace/…" against a root ending in "lib", is matched
      // through that last directory name.
      const last = base.slice(base.lastIndexOf("/") + 1);
      if (normal.startsWith(`${last}/`)) relative = normal.slice(last.length + 1, -4);
      else {
        const marker = `/${last}/`;
        const position = normal.indexOf(marker);
        if (position >= 0) relative = normal.slice(position + marker.length, -4);
      }
    }
    if (relative === undefined) continue;
    const segments = relative.split("/");
    if (segments.every(segment => SEGMENT.test(segment))) return segments.join(".");
  }
  return undefined;
}

/** The names an import written as `raw` inside `current` may denote, innermost first. */
export function importCandidates(current: string | undefined, raw: string): string[] {
  const result: string[] = [];
  if (current) {
    const segments = current.split(".");
    for (let depth = segments.length; depth >= 1; depth--) result.push([...segments.slice(0, depth), raw].join("."));
  }
  result.push(raw);
  return [...new Set(result)];
}

/** Resolve an import name relative to the importing module; undefined when nothing exists. */
export function resolveImportName(current: string | undefined, raw: string, exists: (name: string) => boolean): string | undefined {
  return importCandidates(current, raw).find(exists);
}
