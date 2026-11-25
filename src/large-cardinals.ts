// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Large cardinal hypotheses are predicates a module registers with
// `register largecardinal`. Grace17 has no large cardinal axiom: a theorem
// that needs one takes it as a premise, so its certificate is a ZF(C)
// certificate of the implication. Since ZF(C) proves no instance of such a
// hypothesis, a theorem that uses a lemma assuming one must assume it too,
// and the theorem's own statement shows every hypothesis its proof relies
// on. This reads them off the statement.

import type { Formula } from "./ast.ts";
import type { Kernel } from "./kernel.ts";
import { largeCardinalRegistrations } from "./surface.ts";

export interface LargeCardinalHypothesis {
  readonly predicate: string;
  /** What the hypothesis says, as its registration words it. */
  readonly label: string;
  readonly module?: string;
}

export interface LargeCardinalReport {
  /**
   * The hypotheses the statement assumes: those that occur negatively, as
   * a premise or under one. The theorem holds in ZF(C) for any universe
   * of sets in which they hold.
   */
  readonly assumes: readonly LargeCardinalHypothesis[];
  /** The hypotheses that occur only positively, as what the theorem proves about them. */
  readonly mentions: readonly LargeCardinalHypothesis[];
}

/** The registered large cardinal hypotheses in `statement`, by the polarity of their occurrences. */
export function largeCardinalOccurrences(kernel: Kernel, statement: Formula): LargeCardinalReport {
  const registered = new Map(largeCardinalRegistrations(kernel).map(item => [item.predicate, item]));
  if (registered.size === 0) return { assumes: [], mentions: [] };
  const negative = new Set<string>();
  const positive = new Set<string>();
  const visit = (formula: Formula, polarity: boolean): void => {
    switch (formula.tag) {
      case "pred":
        if (registered.has(formula.pred)) (polarity ? positive : negative).add(formula.pred);
        return;
      case "imp": visit(formula.left, !polarity); visit(formula.right, polarity); return;
      case "iff": for (const side of [formula.left, formula.right]) { visit(side, true); visit(side, false); } return;
      case "and": case "or": visit(formula.left, polarity); visit(formula.right, polarity); return;
      case "forall": case "exists": visit(formula.body, polarity); return;
      default: return;
    }
  };
  visit(statement, true);
  const ordered = (names: Iterable<string>) => [...names].sort().map(name => registered.get(name)!);
  return { assumes: ordered(negative), mentions: ordered([...positive].filter(name => !negative.has(name))) };
}

/** The registered large cardinal hypotheses a theorem's statement assumes and mentions. */
export function theoremLargeCardinals(kernel: Kernel, theorem: string): LargeCardinalReport {
  const statement = kernel.theorems.get(theorem);
  return statement ? largeCardinalOccurrences(kernel, statement) : { assumes: [], mentions: [] };
}
