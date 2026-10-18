// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// How the Workbench maps a cursor to a proof state, a written name to a
// symbol, and a diagnostic to a source span. The editor (through
// workbench/editor-utils.js) and the machine interface share these so the
// two agree on what a position means.

export interface PositionedStep {
  readonly line: number;
  readonly columnStart?: number;
}

/**
 * The index of the proof state shown at a cursor: 0 is the state at theorem
 * start, and k is the state after the k-th checked step. A step counts once
 * the cursor is at or past the column where it starts.
 */
export function tacticStepAtCursor(steps: readonly PositionedStep[], line: number, column: number): number {
  let selected = 0;
  steps.forEach((step, index) => {
    if (line > step.line || (line === step.line && column >= (step.columnStart || 1))) selected = index + 1;
  });
  return selected;
}

export interface NavigableSymbol {
  readonly name: string;
  readonly short: string;
  readonly kind: string;
  readonly info: string;
  readonly file?: string;
  readonly line?: number;
  readonly directions?: { readonly forward: string; readonly backward: string };
}

export interface SymbolResolutionContext {
  readonly call?: boolean;
  readonly module?: string;
  readonly file?: string;
  readonly theorem?: string;
}

/** The symbol a written name denotes in the hover's context, or undefined when it stays ambiguous. */
export function resolveSymbolCandidate<S extends NavigableSymbol>(
  symbols: readonly S[], name: string, { call = false, module, file, theorem }: SymbolResolutionContext = {},
): S | undefined {
  const exact = symbols.filter(symbol => symbol.name === name);
  if (exact.length === 1) return exact[0];
  const direction = /\.(forward|backward)$/.exec(name)?.[1] as "forward" | "backward" | undefined;
  if (direction) {
    const base = resolveSymbolCandidate(symbols, name.slice(0, -(direction.length + 1)), { call, module, file, theorem });
    if (base?.directions?.[direction]) return {
      ...base, name: `${base.name}.${direction}`, short: `${base.short}.${direction}`,
      kind: "derived proof", info: `${direction === "forward" ? "Forward" : "Backward"} direction of ${base.name}\n${base.directions[direction]}`,
    };
  }
  const candidates = symbols.filter(symbol => symbol.short === name || symbol.name.endsWith(`.${name}`));
  if (candidates.length <= 1) return candidates[0];
  const theoremScope = theorem?.split(".").slice(0, -1) || [];
  const callable = new Set(["function", "definition", "predicate", "class"]);
  const ranked = candidates.map(symbol => {
    const parts = symbol.name.split(".");
    let common = 0;
    while (common < theoremScope.length && parts[common] === theoremScope[common]) common += 1;
    let score = common;
    if (file && symbol.file === file) score += 100;
    if (module && (symbol.name === module || symbol.name.startsWith(`${module}.`))) score += 40;
    if (call) score += callable.has(symbol.kind) ? 1000 : -1000;
    // A bare name is far more often a constant or class than a theorem whose
    // last segment happens to coincide, as `Universe` against `SubsetsOf.Universe`.
    else if (callable.has(symbol.kind)) score += 0.5;
    if (symbol.line) score += 1;
    return { symbol, score };
  }).sort((left, right) => right.score - left.score || left.symbol.name.localeCompare(right.symbol.name));
  return ranked[0]!.score > ranked[1]!.score ? ranked[0]!.symbol : undefined;
}

/** Extract the source token named by a surface diagnostic. */
export function diagnosticIdentifier(message: string | undefined): string | undefined {
  const match = /(?:unknown variable or constant|unknown theorem|unknown definition|unexpected token)\s+([^\s,;]+)/i.exec(message || "");
  if (!match) return undefined;
  const token = match[1]!.replace(/[.!:]$/, "");
  const quoted = /^([`'"])(.*)\1$/.exec(token);
  return quoted ? quoted[2] : token;
}

/** Return a clamped, one-based editor range for the offending source token. */
export function diagnosticSpan(lineText: string | undefined, message: string | undefined, column?: number): {
  readonly identifier: string | undefined; readonly startColumn: number; readonly endColumn: number;
} {
  const text = String(lineText || "");
  const identifier = diagnosticIdentifier(message);
  const inferred = identifier ? text.indexOf(identifier) + 1 : 0;
  const maxColumn = text.length + 1;
  const startColumn = Math.min(Math.max(1, column || inferred || 1), maxColumn);
  const endColumn = Math.min(startColumn + (identifier?.length || 1), maxColumn);
  return { identifier, startColumn, endColumn: Math.max(startColumn, endColumn) };
}
