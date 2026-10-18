#!/usr/bin/env node
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Rewrite proofs to the goal-directed application forms and the one-line
// `have h : P by tactic`, keeping only rewrites that still check. Modules
// are processed in import order on one kernel; each module is elaborated on
// a fork with every candidate applied, and a failing line reverts the
// rewrite it belongs to (or every rewrite in its theorem) before retrying.
//
//   node scripts/shorten-proofs.ts [--write] [--root lib] <entry.g17 or Module.Name> ...
//
// Without --write the script reports what it would change.

import { existsSync, readFileSync, writeFileSync } from "node:fs";
import { resolve } from "node:path";
import { createSetTheoryKernel } from "../src/zfg.ts";
import { elaborateModule, forkSurfaceEnvironment, setSurfaceTraceCapture, SurfaceError } from "../src/surface.ts";
import { scanModule } from "../src/module-source-loader.ts";
import { moduleNameFromPath, resolveImportName } from "../src/module-names.ts";
import type { Kernel } from "../src/kernel.ts";

interface Rewrite {
  readonly kind: "by" | "at" | "drop";
  /** Original line range, end exclusive. */
  readonly start: number;
  readonly end: number;
  readonly replacement: readonly string[];
  /** Weaker replacements to try, in order, when this one fails. */
  readonly fallbacks?: readonly (readonly string[])[];
}

const args = process.argv.slice(2);
const write = args.includes("--write");
const collapse = args.includes("--collapse");
const roots: string[] = [];
const entries: string[] = [];
for (let index = 0; index < args.length; index++) {
  if (args[index] === "--root") { roots.push(args[++index]!); continue; }
  if (args[index] === "--write" || args[index] === "--collapse") continue;
  entries.push(args[index]!);
}
if (roots.length === 0) roots.push("lib");

const indentOf = (line: string): number => line.length - line.trimStart().length;
const CONTINUES = /(?:\bat|\bwith|\busing|:=|=>|⇒|->|→|<->|↔|=|\+|-|\*|\/|∧|∨|\band|\bor|,)\s*$/u;
/** A local fact that only types a term: `have h : Nat(t)`, `have h : t ∈ ℝ by …`, a `.closed` instance. */
const CARRIER_HAVE = /^have\s+([\p{L}_][\p{L}\p{M}\p{N}_']*)\s*(?::\s*(?:Nat|Integer|Rational|Real)\([^:]*\)(?:\s+by\s.*|\s*:=.*)?|:\s*[^:]*\s∈\s[ℕℤℚℝ](?:\s+by\s.*|\s*:=.*)?|:=\s*(?:Naturals\.constructor\.(?:zero|succ)|\S+\.(?:closed|natural|integer|rational|real|nonneg))\b.*)$/u;
function balance(text: string): number {
  let depth = 0;
  for (const character of text) {
    if ("([{⟨".includes(character)) depth += 1;
    else if (")]}⟩".includes(character)) depth -= 1;
  }
  return depth;
}
function splitTopLevel(text: string, separator: string): string[] {
  const result: string[] = [];
  let depth = 0;
  let start = 0;
  for (let index = 0; index < text.length; index += 1) {
    const character = text[index]!;
    if ("([{⟨".includes(character)) depth += 1;
    else if (")]}⟩".includes(character)) depth -= 1;
    else if (character === separator && depth === 0) {
      result.push(text.slice(start, index));
      start = index + 1;
    }
  }
  result.push(text.slice(start));
  return result;
}
function topLevelHas(text: string, needle: string): boolean {
  let depth = 0;
  for (let index = 0; index < text.length; index++) {
    const character = text[index]!;
    if ("([{⟨".includes(character)) depth += 1;
    else if (")]}⟩".includes(character)) depth -= 1;
    else if (depth === 0 && text.startsWith(needle, index)) return true;
  }
  return false;
}

/**
 * Whole-proof candidates: a theorem's tactic block is replaced by `simp`, or
 * by `ext y` then `simp` for a set equality, when that checks. Tried before
 * the line-local rewrites, which then apply only to proofs that stay.
 */
/** Declared `requires` names of every library theorem, by short name; null marks a name declared with differing premises. */
const requiresIndex = new Map<string, string[] | null>();
function indexRequires(source: string): void {
  const lines = source.split("\n");
  for (let index = 0; index < lines.length; index++) {
    const head = /^(?:theorem|lemma)\s+([\p{L}_][\p{L}\p{M}\p{N}_.']*)/u.exec(lines[index]!);
    if (!head) continue;
    const names: string[] = [];
    for (let cursor = index + 1; cursor < lines.length && lines[cursor] !== "proof" && !/^\S/u.test(lines[cursor]!); cursor++) {
      const requirement = /^\s+requires\s+([\p{L}_][\p{L}\p{M}\p{N}_']*)\s*:/u.exec(lines[cursor]!);
      if (requirement) names.push(requirement[1]!);
    }
    const existing = requiresIndex.get(head[1]!);
    if (existing === undefined) requiresIndex.set(head[1]!, names);
    else if (existing !== null && existing.join(",") !== names.join(",")) requiresIndex.set(head[1]!, null);
  }
}

export function collapseRewrites(lines: readonly string[]): Rewrite[] {
  const rewrites: Rewrite[] = [];
  for (let index = 0; index < lines.length; index++) {
    if (!/^(theorem|lemma)\b/u.test(lines[index]!)) continue;
    let shows = "";
    let proofLine = -1;
    for (let cursor = index + 1; cursor < lines.length && (/^\s|^$/.test(lines[cursor]!) || lines[cursor] === "proof"); cursor++) {
      const text = lines[cursor]!.trim();
      if (text.startsWith("shows ")) shows = text.slice(6);
      if (lines[cursor] === "proof") { proofLine = cursor; break; }
    }
    if (proofLine < 0) continue;
    let end = proofLine + 1;
    while (end < lines.length && (lines[end]!.startsWith(" ") || lines[end] === "")) end += 1;
    while (end > proofLine + 1 && lines[end - 1] === "") end -= 1;
    const body = lines.slice(proofLine + 1, end);
    // Local have blocks of two or more lines try by simp, or by simp with the
    // block's own short rule list, before the whole proof is considered.
    for (let cursor = proofLine + 1; cursor < end; cursor++) {
      const local = /^(\s*)(?:\.\s+)?have\s+[\p{L}_][\p{L}\p{M}\p{N}_']*\s*:\s*(.+)$/u.exec(lines[cursor]!);
      if (!local || /:=|\bby\b/u.test(local[2]!) || CONTINUES.test(lines[cursor]!.trim())) continue;
      const depth = lines[cursor]!.length - lines[cursor]!.trimStart().length + (/^\s*\.\s+/u.test(lines[cursor]!) ? 2 : 0);
      let blockEnd = cursor + 1;
      while (blockEnd < end && (lines[blockEnd]!.trim() === "" || lines[blockEnd]!.length - lines[blockEnd]!.trimStart().length > depth)) blockEnd += 1;
      while (blockEnd > cursor + 1 && lines[blockEnd - 1]!.trim() === "") blockEnd -= 1;
      const block = lines.slice(cursor + 1, blockEnd).filter(item => item.trim());
      if (block.length < 2 || block.length > 12 || block.some(item => /\bsorry\b/.test(item))) continue;
      const blockNames: string[] = [];
      for (const item of block) {
        const reference = /^\s*(?:\.\s+)?(?:have\s+\S+\s*:=|exact|apply|unfold|rw|simp\s*\[?|settle\s+with)\s*([\p{L}_][\p{L}\p{M}\p{N}_']*(?:\.[\p{L}_][\p{L}\p{M}\p{N}_']*)+)/u.exec(item);
        const name = reference?.[1]?.replace(/\.(forward|backward|left|right)$/u, "");
        if (name && !blockNames.includes(name)) blockNames.push(name);
      }
      const fallbacks: string[][] = blockNames.length && blockNames.length <= 3 ? [[`${lines[cursor]} by simp [${blockNames.join(", ")}]`]] : [];
      rewrites.push({ kind: "by", start: cursor, end: blockEnd, replacement: [`${lines[cursor]} by simp`], fallbacks });
      cursor = blockEnd - 1;
    }
    if (body.length === 0 || body.length > 40) continue;
    if (body.length === 1 && /^\s*(simp|settle|rfl|compute|decide|arith|ring|tauto|cc|typecheck)\b/.test(body[0]!)) continue;
    if (body.some(line => /\bsorry\b/.test(line))) continue;
    // Names the proof already relies on (unfolded definitions and named
    // simp rules) give a second candidate, simp [names].
    const names: string[] = [];
    for (const line of body) {
      const unfold = /^\s*(?:\.\s+)?unfold\s+([^\s]+)(?:\s+at\s+\S+)?\s*$/u.exec(line);
      if (unfold && !names.includes(unfold[1]!)) names.push(unfold[1]!);
      const listed = /^\s*(?:\.\s+)?(?:simp|settle)\s*(?:\[(.*)\]|with\s+(.+))\s*$/u.exec(line);
      for (const item of (listed?.[1] ?? listed?.[2] ?? "").split(",").map(item => item.trim()).filter(Boolean)) {
        if (/^[\p{L}_][\p{L}\p{M}\p{N}_.']*$/u.test(item) && !names.includes(item)) names.push(item);
      }
    }
    // Library lemmas the proof applies are candidates too, as in Lean's
    // simp [defs, lemmas]; Subset is named when the statement mentions ⊆.
    const applied: string[] = [];
    for (const line of body) {
      const reference = /^\s*(?:\.\s+)?(?:have\s+\S+\s*:=|exact|apply|obtain\s+.+?:=)\s+([\p{L}_][\p{L}\p{M}\p{N}_']*(?:\.[\p{L}_][\p{L}\p{M}\p{N}_']*)+)(?:\.(?:forward|backward))?(?:\s|$)/u.exec(line);
      const name = reference?.[1]?.replace(/\.(forward|backward|left|right)$/u, "");
      if (name && name.includes(".") && !names.includes(name) && !applied.includes(name)) applied.push(name);
    }
    const statementNames = [...names, ...applied];
    if (/⊆/.test(shows) && !statementNames.includes("Subset")) statementNames.push("Subset");
    // A proof that shows its steps is worth keeping; only a short rule list
    // replaces one, so a long simp [...] never stands in for a structured proof.
    const withNames = names.length && names.length <= 3 ? `  simp [${names.join(", ")}]` : undefined;
    const withAll = statementNames.length && statementNames.length !== names.length && statementNames.length <= 3 ? `  simp [${statementNames.join(", ")}]` : undefined;
    const candidates: string[][] = [["  simp"]];
    if (withNames) candidates.push([withNames]);
    if (withAll) candidates.push([withAll]);
    if (/=/.test(shows) && !/[<≤]/.test(shows)) {
      candidates.push(["  ext y", "  simp"]);
      if (withNames) candidates.push(["  ext y", withNames]);
      if (withAll) candidates.push(["  ext y", withAll]);
    }
    rewrites.push({ kind: "at", start: proofLine + 1, end, replacement: candidates[0]!, fallbacks: candidates.slice(1) });
  }
  return rewrites;
}

/** Candidate rewrites of one source file, in line order. */
export function proofRewrites(lines: readonly string[]): Rewrite[] {
  const rewrites: Rewrite[] = [];
  let inProof = false;
  for (let index = 0; index < lines.length; index++) {
    const line = lines[index]!;
    const text = line.trim();
    if (/^(theorem|lemma|instance|def|predicate|class|eval|section|end|namespace|module|import|notation|tactic|datatype|open|export)\b/u.test(line)) inProof = /^(theorem|lemma|instance)\b/u.test(line);
    if (line === "proof") continue;
    if (!inProof || indentOf(line) === 0 || text.startsWith("--")) continue;
    const indent = indentOf(line);

    // have h : P by settle with rules is have h : P by simp [rules].
    const haveBySettle = /^(.*\bby\s+)settle(?:\s+with\s+(.+))?$/u.exec(line);
    if (haveBySettle && /^\s*(?:\.\s+)?have\b/u.test(line)) {
      rewrites.push({ kind: "at", start: index, end: index + 1, replacement: [`${haveBySettle[1]}simp${haveBySettle[2] ? ` [${haveBySettle[2]}]` : ""}`] });
      continue;
    }

    // have h : P followed by exactly one deeper tactic line, possibly bulleted.
    const have = /^have\s+[\p{L}_][\p{L}\p{M}\p{N}_']*\s*:(?!=)\s*(.+)$/u.exec(text);
    if (have && !topLevelHas(have[1]!, ":=") && !topLevelHas(have[1]!, " by") && !CONTINUES.test(text) && balance(text) === 0) {
      const next = lines[index + 1];
      const after = lines[index + 2];
      const nextText = next?.trim().replace(/^\.\s+/u, "") ?? "";
      if (next && nextText && indentOf(next) > indent && !/^(\||with\b|calc\b|--)/u.test(nextText) &&
          !CONTINUES.test(nextText) && balance(nextText) === 0 &&
          (after === undefined || after.trim() === "" || indentOf(after) <= indent) &&
          line.length + nextText.length + 4 <= 118) {
        rewrites.push({ kind: "by", start: index, end: index + 2, replacement: [`${line} by ${nextText}`] });
        index += 1;
        continue;
      }
      // have h : P whose body is apply X.backward, constructor, two one-line
      // bullets: have h : P := X.backward with ⟨a, b⟩.
      const body: string[] = [];
      let cursor = index + 1;
      while (lines[cursor] !== undefined && (lines[cursor]!.trim() === "" || indentOf(lines[cursor]!) > indent)) { if (lines[cursor]!.trim()) body.push(lines[cursor]!.trim()); cursor += 1; }
      const applyLine = body.length === 4 ? /^apply\s+(\S+\.(?:backward|forward))$/u.exec(body[0]!) : null;
      const bulletA = body.length === 4 ? /^\.\s+exact\s+(.+)$/u.exec(body[2]!) : null;
      const bulletB = body.length === 4 ? /^\.\s+exact\s+(.+)$/u.exec(body[3]!) : null;
      if (applyLine && body[1] === "constructor" && bulletA && bulletB && !/,/.test(bulletA[1]! + bulletB[1]!)) {
        rewrites.push({ kind: "by", start: index, end: cursor, replacement: [`${line} := ${applyLine[1]} with ⟨${bulletA[1]}, ${bulletB[1]}⟩`] });
        index = cursor - 1;
        continue;
      }
      // have h : P whose body is [unfold P], witness t, exact e: have h : P := ⟨t, e⟩.
      const witnessBody = body.filter(item => !/^unfold\s/u.test(item));
      const witnessLine = witnessBody.length === 2 ? /^(?:witness|use)\s+(.+)$/u.exec(witnessBody[0]!) : null;
      const exactLine = witnessBody.length === 2 ? /^exact\s+(.+)$/u.exec(witnessBody[1]!) : null;
      if (witnessLine && exactLine && !/,/.test(exactLine[1]!)) {
        rewrites.push({ kind: "by", start: index, end: cursor, replacement: [`${line} := ⟨${witnessLine[1]}, ${exactLine[1]}⟩`] });
        index = cursor - 1;
        continue;
      }
    }

    // settle with lemmas: the membership characterizations and Subset are
    // automatic now, so try the bare form first.
    // settle is simp: a bare simp when the automatic lemmas suffice, else
    // simp with the same rules.
    const settleWith = /^settle(?:\s+with\s+(.+))?$/u.exec(text);
    if (settleWith && !CONTINUES.test(text) && balance(text) === 0) {
      const alternatives = settleWith[1] ? [`simp`, `simp [${settleWith[1]}]`] : [`simp`];
      rewrites.push({ kind: "at", start: index, end: index + 1, replacement: [`${" ".repeat(indent)}${alternatives[0]}`],
        fallbacks: alternatives.slice(1).map(item => [`${" ".repeat(indent)}${item}`]) });
      continue;
    }

    // A bullet opens a branch; the command after it is matched without it,
    // and the following lines of the branch sit two columns deeper.
    const bullet = /^\.\s+/.exec(text)?.[0] ?? "";
    const core = text.slice(bullet.length);
    const branchIndent = indent + bullet.length;
    const sameBranch = (position: number): boolean =>
      lines[position] !== undefined && indentOf(lines[position]!) === branchIndent && !/^\.\s/.test(lines[position]!.trim());

    // have h := e then exact h is exact e.
    const haveThenExact = /^have\s+([\p{L}_][\p{L}\p{M}\p{N}_']*)\s*:=\s*(.+)$/u.exec(core);
    if (haveThenExact && !CONTINUES.test(text) && balance(text) === 0 && sameBranch(index + 1) &&
        lines[index + 1]!.trim() === `exact ${haveThenExact[1]}`) {
      const joined = `${" ".repeat(indent)}${bullet}exact ${haveThenExact[2]}`;
      if (joined.length <= 80) {
        rewrites.push({ kind: "by", start: index, end: index + 2, replacement: [joined] });
        index += 1;
        continue;
      }
    }

    // set.extensionality applied then intro p is ext p, with or without a
    // named have for the instance.
    const extHave = /^have\s+([\p{L}_][\p{L}\p{M}\p{N}_']*)\s*:=\s*set\.extensionality\b/u.exec(core);
    const extApply = /^apply\s+set\.extensionality\b/u.test(core);
    if ((extHave || extApply) && !CONTINUES.test(text) && balance(text) === 0) {
      let cursor = index + 1;
      if (extHave) {
        if (!sameBranch(cursor) || lines[cursor]!.trim() !== `apply ${extHave[1]}`) cursor = -1;
        else cursor += 1;
      }
      const introLine = cursor > 0 && sameBranch(cursor) ? /^intro\s+([\p{L}_][\p{L}\p{M}\p{N}_']*)$/u.exec(lines[cursor]!.trim()) : null;
      if (introLine) {
        rewrites.push({ kind: "by", start: index, end: cursor + 1, replacement: [`${" ".repeat(indent)}${bullet}ext ${introLine[1]}`] });
        index = cursor;
        continue;
      }
    }

    // Consecutive intro lines become one intros.
    const intro = /^intros?\s+(.+)$/u.exec(core);
    if (intro && !CONTINUES.test(text) && !/ at /.test(intro[1]!)) {
      const names: string[] = [intro[1]!.replace(/,/g, " ").trim()];
      let span = 1;
      while (sameBranch(index + span)) {
        const more = /^intros?\s+(.+)$/u.exec(lines[index + span]!.trim());
        if (!more || / at /.test(more[1]!)) break;
        names.push(more[1]!.replace(/,/g, " ").trim());
        span += 1;
      }
      if (span > 1) {
        rewrites.push({ kind: "by", start: index, end: index + span, replacement: [`${" ".repeat(indent)}${bullet}intros ${names.join(" ")}`] });
        index += span - 1;
        continue;
      }
    }

    // Consecutive rw lines on the same target become one rw list.
    const rewriteOne = /^rw\s+(?!\[)(.+?)(\s+at\s+[\p{L}_][\p{L}\p{M}\p{N}_']*)?$/u.exec(core);
    if (rewriteOne && !CONTINUES.test(text) && balance(text) === 0 && !/^under\b/.test(rewriteOne[1]!)) {
      const rules = [rewriteOne[1]!];
      const target = rewriteOne[2] ?? "";
      let span = 1;
      while (sameBranch(index + span)) {
        const more = /^rw\s+(?!\[)(.+?)(\s+at\s+[\p{L}_][\p{L}\p{M}\p{N}_']*)?$/u.exec(lines[index + span]!.trim());
        if (!more || (more[2] ?? "") !== target || /^under\b/.test(more[1]!) || CONTINUES.test(lines[index + span]!.trim())) break;
        rules.push(more[1]!);
        span += 1;
      }
      if (span > 1) {
        rewrites.push({ kind: "by", start: index, end: index + span, replacement: [`${" ".repeat(indent)}${bullet}rw [${rules.join(", ")}]${target}`] });
        index += span - 1;
        continue;
      }
    }

    // have h := e then rcases h with p (or obtain p := h) is obtain p := e.
    const haveLocal = /^have\s+([\p{L}_][\p{L}\p{M}\p{N}_']*)\s*:=\s*(.+)$/u.exec(text);
    if (haveLocal && !CONTINUES.test(text) && balance(text) === 0 && lines[index + 1] !== undefined && indentOf(lines[index + 1]!) === indent) {
      const nextText = lines[index + 1]!.trim();
      const destructure = new RegExp(`^(?:rcases\\s+${haveLocal[1]}\\s+with\\s+(.+)|obtain\\s+(.+?)\\s*:=\\s*${haveLocal[1]})$`, "u").exec(nextText);
      if (destructure) {
        rewrites.push({ kind: "by", start: index, end: index + 2, replacement: [`${" ".repeat(indent)}obtain ${destructure[1] ?? destructure[2]} := ${haveLocal[2]}`] });
        index += 1;
        continue;
      }
    }

    // unfold P at h is redundant when h is only applied to arguments afterwards:
    // a local predicate fact applies through its definition.
    if (/^unfold\s+\S+\s+at\s+\S+$/u.test(core)) {
      rewrites.push({ kind: "drop", start: index, end: index + 1, replacement: [] });
      continue;
    }

    // apply X.backward then refine ⟨…⟩ closing the goal is exact X.backward with ⟨…⟩;
    // the same two lines as the whole body of have h : P become have h : P := ….
    const applyBackward = /^apply\s+([^\s]+\.(?:backward|forward))$/u.exec(core);
    if (applyBackward && sameBranch(index + 1)) {
      const refineLine = /^refine\s+(⟨.*⟩)$/u.exec(lines[index + 1]!.trim());
      const after = lines[index + 2];
      if (refineLine && !/\?_|(?:^|[,⟨ ])_(?:[,⟩]|$)/u.test(refineLine[1]!) && (after === undefined || after.trim() === "" || indentOf(after) < branchIndent || /^\.\s/.test(after.trim()) || indentOf(after) === branchIndent)) {
        rewrites.push({ kind: "by", start: index, end: index + 2, replacement: [`${" ".repeat(indent)}${bullet}exact ${applyBackward[1]} with ${refineLine[1]}`] });
        index += 1;
        continue;
      }
    }
    if (have && !topLevelHas(have[1]!, ":=") && !topLevelHas(have[1]!, " by") && !CONTINUES.test(text) && balance(text) === 0) {
      const first = lines[index + 1];
      const second = lines[index + 2];
      const after = lines[index + 3];
      const applyLine = first && indentOf(first) > indent ? /^apply\s+([^\s]+\.(?:backward|forward))$/u.exec(first.trim()) : null;
      const refineLine = second && first && indentOf(second) === indentOf(first) ? /^refine\s+(⟨.*⟩)$/u.exec(second.trim()) : null;
      if (applyLine && refineLine && !/\?_|(?:^|[,⟨ ])_(?:[,⟩]|$)/u.test(refineLine[1]!) &&
          (after === undefined || after.trim() === "" || indentOf(after) <= indent) &&
          line.length + applyLine[1]!.length + refineLine[1]!.length + 12 <= 118) {
        rewrites.push({ kind: "by", start: index, end: index + 3, replacement: [`${line} := ${applyLine[1]} with ${refineLine[1]}`] });
        index += 2;
        continue;
      }
    }

    // witness t, constructor, and two one-line bullets become one refine.
    const witness = /^(?:witness|use)\s+(.+)$/u.exec(core);
    if (witness && !CONTINUES.test(text) && balance(text) === 0 && sameBranch(index + 1) && lines[index + 1]!.trim() === "constructor") {
      const first = lines[index + 2]?.trim();
      const second = lines[index + 3]?.trim();
      const firstBody = first && indentOf(lines[index + 2]!) === branchIndent ? /^\.\s+exact\s+(.+)$/u.exec(first)?.[1] : undefined;
      const secondBody = second && indentOf(lines[index + 3]!) === branchIndent ? /^\.\s+exact\s+(.+)$/u.exec(second)?.[1] : undefined;
      const after = lines[index + 4];
      if (firstBody && secondBody && !/^⟨/.test(firstBody) && !/^⟨/.test(secondBody) && !CONTINUES.test(first) && !CONTINUES.test(second) &&
          (after === undefined || after.trim() === "" || indentOf(after) <= branchIndent) &&
          `${witness[1]}, ${firstBody}, ${secondBody}`.length <= 100) {
        const component = (body: string): string => / with .*,/.test(body) ? `(${body})` : body;
        rewrites.push({ kind: "by", start: index, end: index + 4, replacement: [`${" ".repeat(indent)}${bullet}refine ⟨${witness[1]}, ${component(firstBody)}, ${component(secondBody)}⟩`] });
        index += 3;
        continue;
      }
    }

    // have h := e then specialize h with args is have h := e with args.
    const haveThenSpecialize = /^have\s+([\p{L}_][\p{L}\p{M}\p{N}_']*)\s*:=\s*(.+)$/u.exec(core);
    if (haveThenSpecialize && !CONTINUES.test(text) && balance(text) === 0 && sameBranch(index + 1)) {
      const following = new RegExp(`^specialize\\s+${haveThenSpecialize[1]}\\s+with\\s+(.+)$`, "u").exec(lines[index + 1]!.trim());
      if (following && !CONTINUES.test(lines[index + 1]!.trim())) {
        const body = haveThenSpecialize[2]!;
        const merged = topLevelHas(body, " with ") ? `${body}, ${following[1]}` : `${body} with ${following[1]}`;
        if (line.length + merged.length - body.length <= 118) {
          rewrites.push({ kind: "by", start: index, end: index + 2, replacement: [`${" ".repeat(indent)}${bullet}have ${haveThenSpecialize[1]} := ${merged}`] });
          index += 1;
          continue;
        }
      }
    }

    // Lines of the enclosing theorem, for scans of a name's other uses.
    const theoremRange = (): [number, number] => {
      let start = index;
      while (start > 0 && indentOf(lines[start]!) > 0) start -= 1;
      let end = index + 1;
      while (end < lines.length && (indentOf(lines[end]!) > 0 || lines[end]!.trim() === "")) end += 1;
      return [start, end];
    };
    const mentions = (name: string, from: number, to: number, except: number): number => {
      const word = new RegExp(`(?<![\\p{L}\\p{M}\\p{N}_.])${name}(?![\\p{L}\\p{M}\\p{N}_])`, "u");
      let count = 0;
      for (let position = from; position < to; position += 1) if (position !== except && word.test(lines[position]!)) count += 1;
      return count;
    };

    // An explicit at list before a library theorem gives way to inference
    // from the named premises: `Thm at a, b, c with *` becomes
    // `Thm with source, hom`, naming the callee's requirements that are in
    // scope; `Thm at a, b with h` becomes `Thm with h`.
    const atList = /^((?:have\s+.+?:=\s+|exact\s+|apply\s+)?)([\p{L}_][\p{L}\p{M}\p{N}_.']*?)(\.(?:forward|backward))?\s+at\s+(.+?)\s+with\s+(.+)$/u.exec(core);
    if (atList && (!CONTINUES.test(text) || /\swith\s+\*$/u.test(text)) && balance(text) === 0 && !/^(?:rw|rewrite|rwa|unfold|simp|specialize)\b/u.test(core)) {
      const requirements = atList[2]!.includes(".") ? requiresIndex.get(atList[2]!) : undefined;
      if (requirements) {
        const premises = atList[5]!.trim();
        const [from] = theoremRange();
        const inScope = requirements.filter(name => mentions(name, from, index, index) > 0);
        const prefix = `${" ".repeat(indent)}${bullet}${atList[1]}${atList[2]}${atList[3] ?? ""}`;
        const options: string[] = [];
        if (premises === "*") {
          options.push(`${prefix} with *`);
          // Bare at-list arguments often come with membership facts named
          // after them, hx for x; naming those pins the parameters.
          const guards = splitTopLevel(atList[4]!, ",").map(item => item.trim())
            .filter(item => /^[\p{L}_][\p{L}\p{M}\p{N}_']*$/u.test(item))
            .map(item => `h${item}`)
            .filter(name => mentions(name, from, index, index) > 0);
          if (guards.length) options.push(`${prefix} with ${guards.join(", ")}`, `${prefix} with ${guards.join(", ")}, *`);
          if (inScope.length) options.push(`${prefix} with ${inScope.join(", ")}`, `${prefix} with ${inScope.join(", ")}, *`);
        } else {
          options.push(`${prefix} with ${premises}`);
        }
        if (options.length) {
          rewrites.push({ kind: "at", start: index, end: index + 1, replacement: [options[0]!], fallbacks: options.slice(1).map(option => [option]) });
          continue;
        }
      }
    }

    // A trailing `with *` after an at list only discharges guards, which an
    // application does on its own; it is dropped when nothing else needs it.
    const atWithStar = /^((?:have\s+[^:]+:=\s+|exact\s+|apply\s+)\S.*\bat\b[^\n]*?)\s+with\s+(?:\*|assumption(?:,\s*assumption)*)$/u.exec(core);
    if (atWithStar && !/\bwith\b/u.test(atWithStar[1]!) && !CONTINUES.test(text) && balance(text) === 0) {
      rewrites.push({ kind: "at", start: index, end: index + 1, replacement: [`${" ".repeat(indent)}${bullet}${atWithStar[1]}`] });
      continue;
    }

    // unfold P before intro(s), witness, constructor, left, or right: the
    // tactic sees through a defined predicate.
    if (/^unfold\s+[^\s]+$/u.test(core) && sameBranch(index + 1) &&
        /^(?:intros?\s|witness\s|use\s|constructor$|split$|left$|right$)/u.test(lines[index + 1]!.trim())) {
      rewrites.push({ kind: "drop", start: index, end: index + 1, replacement: [] });
      continue;
    }
    // unfold P at h before cases h, obtain … := h, or h.left: the fact is
    // read through its definition.
    const unfoldAt = /^unfold\s+[^\s]+\s+at\s+([\p{L}_][\p{L}\p{M}\p{N}_']*)$/u.exec(core);
    if (unfoldAt && sameBranch(index + 1)) {
      const name = unfoldAt[1]!;
      const next = lines[index + 1]!.trim();
      if (new RegExp(`^(?:r?cases\\s+${name}\\s+with|obtain\\s+.*:=\\s*${name}$|exact\\s+${name}\\.(?:left|right))`, "u").test(next)) {
        rewrites.push({ kind: "drop", start: index, end: index + 1, replacement: [] });
        continue;
      }
    }

    // simp … at h then exact h is simpa … using h.
    const simpAt = /^simp(\s+\[[^\]]*\])?\s+at\s+([\p{L}_][\p{L}\p{M}\p{N}_']*)$/u.exec(core);
    if (simpAt && sameBranch(index + 1) && lines[index + 1]!.trim() === `exact ${simpAt[2]}`) {
      rewrites.push({ kind: "by", start: index, end: index + 2, replacement: [`${" ".repeat(indent)}${bullet}simpa${simpAt[1] ?? ""} using ${simpAt[2]}`] });
      index += 1;
      continue;
    }

    // A carrier fact, such as `have hk : Nat(k)` or a `.closed` instance,
    // that nothing names afterwards is found by the automation itself.
    const carrierHave = CARRIER_HAVE.exec(core);
    if (carrierHave) {
      const [from, to] = theoremRange();
      let end = index + 1;
      while (end < to && lines[end]!.trim() !== "" && indentOf(lines[end]!) > indent) end += 1;
      if (mentions(carrierHave[1]!, index + 1, to, index) === 0 && from <= index) {
        rewrites.push({ kind: "drop", start: index, end, replacement: [] });
        index = end - 1;
        continue;
      }
    }

    // unfold P before exact or assumption: a fact through a definition
    // closes the body, and the other way round.
    if (/^unfold\s+[^\s]+(?:\s+at\s+\S+)?$/u.test(core) && sameBranch(index + 1) &&
        /^(?:exact\s+[\p{L}_][\p{L}\p{M}\p{N}_'.]*|assumption)$/u.test(lines[index + 1]!.trim())) {
      rewrites.push({ kind: "drop", start: index, end: index + 1, replacement: [] });
      continue;
    }

    // exfalso before arith: arith refutes the hypotheses itself.
    if (core === "exfalso" && sameBranch(index + 1) && lines[index + 1]!.trim() === "arith") {
      rewrites.push({ kind: "drop", start: index, end: index + 1, replacement: [] });
      continue;
    }

    // The three-line zero/successor refutation is one arith.
    if (/^have\s+\S+\s*:=\s*Naturals\.disjoint\.zero\.succ\s+at\s+\S+$/u.test(core) && sameBranch(index + 1) && sameBranch(index + 2) &&
        /^apply\s+\S+$/u.test(lines[index + 1]!.trim()) && lines[index + 2]!.trim() === "simp") {
      rewrites.push({ kind: "by", start: index, end: index + 3, replacement: [`${" ".repeat(indent)}${bullet}arith`] });
      index += 2;
      continue;
    }

    // A guard fact `have h : Nat(t) by typecheck` is routine where it is a
    // with entry: the entry goes, then the fact once nothing mentions it.
    const guardFact = /^have\s+([\p{L}_][\p{L}\p{M}\p{N}_']*)\s*:\s*.+\s+by\s+typecheck$/u.exec(core);
    if (guardFact) {
      const [from, to] = theoremRange();
      if (mentions(guardFact[1]!, from, to, index) === 0) {
        rewrites.push({ kind: "drop", start: index, end: index + 1, replacement: [] });
        continue;
      }
    }
    {
      const [from, to] = theoremRange();
      const withList = /^(.*\swith\s+)(.+)$/u.exec(core);
      if (withList && !CONTINUES.test(text) && balance(text) === 0) {
        const entries = splitTopLevel(withList[2]!, ",").map(item => item.trim());
        const guardNames = new Set<string>();
        for (let position = from; position < to; position += 1) {
          const match = /^\s*(?:\.\s+)?have\s+([\p{L}_][\p{L}\p{M}\p{N}_']*)\s*:\s*.+\s+by\s+typecheck$/u.exec(lines[position]!)
            ?? CARRIER_HAVE.exec(lines[position]!.trim().replace(/^\.\s+/, ""));
          if (match) guardNames.add(match[1]!);
        }
        const kept = entries.filter(item => !guardNames.has(item) && item !== "assumption" && !/^\*\{\d+\}$/.test(item));
        if (kept.length < entries.length && kept.length > 0) {
          rewrites.push({ kind: "by", start: index, end: index + 1, replacement: [`${" ".repeat(indent)}${bullet}${withList[1]}${kept.join(", ")}`] });
          continue;
        }
      }
    }

    // The successor case written as arithmetic.
    const successorCase = /^\|\s*succ\(([\p{L}_][\p{L}\p{M}\p{N}_']*)\)\s+using\s+(\S+)\s*=>(.*)$/u.exec(core);
    if (successorCase) {
      rewrites.push({ kind: "by", start: index, end: index + 1, replacement: [`${" ".repeat(indent)}${bullet}| ${successorCase[1]} + 1 using ${successorCase[2]} =>${successorCase[3]}`] });
      continue;
    }

    // specialize h with x then contradiction: contradiction finds the pair itself.
    const specializeThenContradiction = /^specialize\s+[\p{L}_][\p{L}\p{M}\p{N}_']*\s+with\s+.+$/u.exec(core);
    if (specializeThenContradiction && !CONTINUES.test(text) && sameBranch(index + 1) && lines[index + 1]!.trim() === "contradiction") {
      rewrites.push({ kind: "drop", start: index, end: index + 1, replacement: [] });
      continue;
    }

    // specialize h with args then exact h with more is exact h with both.
    const specializeThenExactMore = /^specialize\s+([\p{L}_][\p{L}\p{M}\p{N}_']*)\s+with\s+(.+)$/u.exec(core);
    if (specializeThenExactMore && !CONTINUES.test(text) && balance(text) === 0 && sameBranch(index + 1)) {
      const name = specializeThenExactMore[1]!;
      const next = new RegExp(`^exact\\s+${name}\\s+with\\s+(.+)$`, "u").exec(lines[index + 1]!.trim());
      if (next && !CONTINUES.test(lines[index + 1]!.trim()) && balance(lines[index + 1]!) === 0) {
        const joined = `${" ".repeat(indent)}${bullet}exact ${name} with ${specializeThenExactMore[2]}, ${next[1]}`;
        if (joined.length <= 80) {
          rewrites.push({ kind: "by", start: index, end: index + 2, replacement: [joined] });
          index += 1;
          continue;
        }
      }
    }

    // specialize h with args then exact h is exact h with args.
    const specialize = /^specialize\s+([\p{L}_][\p{L}\p{M}\p{N}_']*)\s+with\s+(.+)$/u.exec(text);
    if (specialize && !CONTINUES.test(text) && lines[index + 1] !== undefined && indentOf(lines[index + 1]!) === indent &&
        lines[index + 1]!.trim() === `exact ${specialize[1]}`) {
      rewrites.push({ kind: "by", start: index, end: index + 2, replacement: [`${" ".repeat(indent)}exact ${specialize[1]} with ${specialize[2]}`] });
      index += 1;
      continue;
    }

    // rw h then exact hyp (or assumption) is rwa h.
    const rewriteLine = /^(rw|rewrite)\s+(.+)$/u.exec(text);
    if (rewriteLine && !CONTINUES.test(text) && balance(text) === 0) {
      const next = lines[index + 1];
      const closing = next && indentOf(next) === indent ? /^(?:exact\s+([\p{L}_][\p{L}\p{M}\p{N}_']*)|assumption)$/u.exec(next.trim()) : null;
      const target = /\s+at\s+([\p{L}_][\p{L}\p{M}\p{N}_']*)$/u.exec(rewriteLine[2]!)?.[1];
      if (closing && (!closing[1] || !target || closing[1] === target)) {
        rewrites.push({ kind: "by", start: index, end: index + 2, replacement: [`${" ".repeat(indent)}rwa ${rewriteLine[2]}`] });
        index += 1;
        continue;
      }
    }

    // exact/apply/show/have := thm at args [with premises], possibly continued
    // on deeper-indented lines after a trailing `with` or comma.
    let joined = text;
    let span = 1;
    while (CONTINUES.test(joined) && lines[index + span] !== undefined && indentOf(lines[index + span]!) > indent) {
      joined = `${joined} ${lines[index + span]!.trim()}`;
      span += 1;
    }
    const application = /^(exact|apply|show\s+.+?\s*:=|obtain\s+.+?\s*:=|have\s+[\p{L}_][\p{L}\p{M}\p{N}_']*(?:\s*:\s*.+?)?\s*:=)\s+([^\s{(⟨]+)\s+at\s+(.+?)(\s+with\s+(.+))?$/u.exec(joined);
    if (application && !CONTINUES.test(joined) && balance(joined) === 0 && !topLevelHas(application[3]!, " with ")) {
      const head = application[1]!;
      const name = application[2]!;
      const withPart = application[5];
      const keyword = head.split(/\s/)[0]!;
      const annotated = keyword === "exact" || keyword === "show" || (keyword === "have" && /:\s*.+:=$/u.test(head));
      // obtain destructures the result: named premises are enough to infer.
      {
        let replacement: string | undefined;
        if (withPart === undefined) {
          if (keyword === "apply" || annotated) replacement = `${" ".repeat(indent)}${head} ${name}`;
        } else {
          const entries = withPart.split(",").map(item => item.trim());
          const bareStar = entries.length === 1 && entries[0] === "*";
          const named = entries.some(item => /^[\p{L}_][\p{L}\p{M}\p{N}_'.]*$/u.test(item) && item !== "assumption");
          if (bareStar && annotated) replacement = `${" ".repeat(indent)}${head} ${name}`;
          else if (bareStar || named || annotated || keyword === "apply") replacement = `${" ".repeat(indent)}${head} ${name} with ${withPart}`;
        }
        if (replacement !== undefined) {
          // A joined replacement that would be too long keeps its with list on a continuation line.
          const lines_ = replacement.length <= 110 || !replacement.includes(" with ")
            ? [replacement]
            : [replacement.slice(0, replacement.indexOf(" with ") + 5), `${" ".repeat(indent + 2)}${replacement.slice(replacement.indexOf(" with ") + 6)}`];
          rewrites.push({ kind: "at", start: index, end: index + span, replacement: lines_ });
          index += span - 1;
        }
      }
    }
  }
  return rewrites;
}

function applyRewrites(lines: readonly string[], rewrites: readonly Rewrite[]): { text: string; owners: (Rewrite | undefined)[] } {
  const output: string[] = [];
  const owners: (Rewrite | undefined)[] = [];
  let cursor = 0;
  for (const rewrite of rewrites) {
    while (cursor < rewrite.start) { output.push(lines[cursor]!); owners.push(undefined); cursor += 1; }
    for (const line of rewrite.replacement) { output.push(line); owners.push(rewrite); }
    cursor = rewrite.end;
  }
  while (cursor < lines.length) { output.push(lines[cursor]!); owners.push(undefined); cursor += 1; }
  return { text: output.join("\n"), owners };
}

/** The original line index shown at `newLine` of the rewritten text, if it is an untouched line. */
function originalLineOf(lines: readonly string[], rewrites: readonly Rewrite[], newLine: number): number | undefined {
  let original = 0;
  let produced = 0;
  for (const rewrite of rewrites) {
    const untouched = rewrite.start - original;
    if (newLine < produced + untouched) return original + (newLine - produced);
    produced += untouched + rewrite.replacement.length;
    if (newLine < produced) return undefined;
    original = rewrite.end;
  }
  return original + (newLine - produced) < lines.length ? original + (newLine - produced) : undefined;
}

function theoremRange(lines: readonly string[], line: number): [number, number] {
  let start = line;
  while (start > 0 && !/^\S/u.test(lines[start]!)) start -= 1;
  let end = line + 1;
  while (end < lines.length && !/^\S/u.test(lines[end]!)) end += 1;
  return [start, end];
}

function tryElaborate(kernel: Kernel, text: string, file?: string): { kernel: Kernel } | { line: number; message: string } {
  const fork = kernel.fork();
  forkSurfaceEnvironment(kernel, fork);
  setSurfaceTraceCapture(fork, false);
  const name = file ? scanModule(text, file, path => moduleNameFromPath(path, roots.map(root => resolve(root)))).name : undefined;
  try { elaborateModule(fork, text, name ? { moduleName: name } : {}); return { kernel: fork }; }
  catch (error) {
    if (error instanceof SurfaceError) return { line: error.line, message: error.message };
    throw error;
  }
}

/**
 * A module that stops checking because automation now discharges a step it
 * used to prove by hand (an `assumption` or `exact` of a carrier fact, a
 * `typecheck`) is repaired by dropping the line the error names, until it
 * checks or the error is of another kind.
 */
function repairBaseline(kernel: Kernel, file: string, source: string, log: (line: string) => void): string {
  let lines = source.split("\n");
  const why = (message: string): string => { if (process.env.G17_SHORTEN_WHY) log(`  baseline: ${message}`); return source; };
  const failureOf = (text: string): { line: number; message: string } | undefined => {
    const result = tryElaborate(kernel, text, file);
    if ("kernel" in result) return undefined;
    const nested = [...result.message.matchAll(/line (\d+):/g)].map(match => Number(match[1]));
    return { line: (nested.length ? nested[nested.length - 1]! : result.line) - 1, message: result.message };
  };
  let previous = lines;
  for (let round = 0; round < 256; round += 1) {
    if (process.env.G17_SHORTEN_WHY === "2" && previous !== lines) {
      const gone = previous.filter(line => !lines.includes(line));
      const added = lines.filter(line => !previous.includes(line));
      log(`  repaired: -[${gone.map(line => line.trim()).join(" | ")}] +[${added.map(line => line.trim()).join(" | ")}]`);
      previous = lines;
    }
    const failure = failureOf(lines.join("\n"));
    if (!failure) { if (round) log(`${file}: ${round} hand-discharged steps dropped`); return lines.join("\n"); }
    const failing = failure.line;
    const text = lines[failing]?.trim().replace(/^\.\s+/, "") ?? "";
    if (process.env.G17_SHORTEN_WHY === "2") log(`  failure ${failing + 1}: ${failure.message} :: ${text}`);
    // A specialize that supplied a carrier fact now finds nothing to
    // supply it to: the argument goes, and the line with it when empty.
    const surplus = /has no remaining argument at (.+)$/u.exec(failure.message)
      ?? /^(?:line \d+: )?(\S+) proves .+, but application needs/u.exec(failure.message)
      ?? /named premise (\S+) does not match requirement/u.exec(failure.message);
    // The with list may continue on following lines after a trailing comma.
    let blockEnd = failing;
    while (blockEnd + 1 < lines.length && /(?:,|\bwith)\s*$/.test(lines[blockEnd]!) && indentOf(lines[blockEnd + 1]!) > indentOf(lines[failing]!)) blockEnd += 1;
    const joined = lines.slice(failing, blockEnd + 1).map((item, position) => position ? item.trim() : item).join(" ");
    const withList = /^(\s*(?:\.\s+)?(?:specialize|exact|apply|have|show|refine)\b.*?\bwith\s+)(.+)$/u.exec(joined);
    if (surplus && withList && balance(joined) === 0) {
      const entries = splitTopLevel(withList[2]!, ",").map(item => item.trim());
      // `*{n}` takes n premises by assumption; one fewer is needed now.
      const remaining = surplus[1]!.trim() === "assumption" && !entries.includes("assumption")
        ? entries.flatMap(item => {
            const star = /^\*\{(\d+)\}$/u.exec(item);
            if (star) return Number(star[1]) > 1 ? [`*{${Number(star[1]) - 1}}`] : [];
            return [item];
          })
        : entries.filter(item => item !== surplus[1]!.trim());
      if (remaining.join(",") === entries.join(",")) return why(`${failure.message} :: ${text}`);
      const isSpecialize = /^\s*(?:\.\s+)?specialize\b/.test(joined);
      const head = withList[1]!.replace(/\s+with\s+$/, "");
      const replacement = remaining.length
        ? [`${withList[1]}${remaining.join(", ")}`]
        : isSpecialize ? [] : [head];
      // A long list is reflowed under its head, within 80 columns.
      const fitted = replacement.flatMap(line => line.length <= 80 ? [line] : (() => {
        const split = /^(.*?\bwith)\s+(.+)$/u.exec(line)!;
        const pad = " ".repeat(indentOf(line) + 2);
        const rows: string[] = [];
        for (const entry of splitTopLevel(split[2]!, ",").map(item => item.trim())) {
          const current = rows[rows.length - 1];
          if (current !== undefined && `${current}, ${entry}`.length <= 80) rows[rows.length - 1] = `${current}, ${entry}`;
          else rows.push(`${pad}${entry}`);
        }
        return [split[1]!, ...rows.map((row, position) => position < rows.length - 1 ? `${row},` : row)];
      })());
      lines = [...lines.slice(0, failing), ...fitted, ...lines.slice(blockEnd + 1)];
      continue;
    }
    // Inside a block of bullets, the leading bullets that closed carrier
    // goals are gone: the shortest prefix of bullet units whose removal
    // checks, or moves the failure past the last bullet, is dropped.
    const [from, to] = theoremRange(lines, failing);
    const isBullet = (position: number): boolean => /^\s*\.\s/.test(lines[position] ?? "");
    let enclosing = failing;
    if (!isBullet(failing)) {
      const depth = indentOf(lines[failing] ?? "");
      enclosing = failing - 1;
      while (enclosing >= from && (lines[enclosing]!.trim() === "" || indentOf(lines[enclosing]!) >= depth)) enclosing -= 1;
      if (enclosing < from || !isBullet(enclosing)) enclosing = -1;
    }
    if (enclosing >= 0) {
      const indent = indentOf(lines[enclosing]!);
      const unitStart = (position: number): boolean => isBullet(position) && indentOf(lines[position]!) === indent;
      const inBlock = (position: number): boolean => position >= from && position < to && lines[position]!.trim() !== ""
        && (unitStart(position) || indentOf(lines[position]!) > indent);
      let first = enclosing;
      while (first - 1 >= from && inBlock(first - 1)) first -= 1;
      while (!unitStart(first)) first += 1;
      const bullets: number[] = [];
      for (let position = first; inBlock(position); position += 1) if (unitStart(position)) bullets.push(position);
      // Only the subgoals of an application are dropped this way; the
      // branches of a case split or a constructor are all needed.
      let head = first - 1;
      while (head >= from && (lines[head]!.trim() === "" || indentOf(lines[head]!) > indent)) head -= 1;
      const applied = head >= from && /^\s*(?:\.\s+)?apply\s/.test(lines[head]!);
      let repaired: string[] | undefined;
      if (!applied) bullets.length = 0;
      // Every bullet may go when the application left no subgoal.
      let blockEnd = bullets[bullets.length - 1] ?? first;
      while (inBlock(blockEnd + 1)) blockEnd += 1;
      for (let count = 1; count <= bullets.length && !repaired; count += 1) {
        const cut = count < bullets.length ? bullets[count]! : blockEnd + 1;
        const candidate = [...lines.slice(0, first), ...lines.slice(cut)];
        const next = failureOf(candidate.join("\n"));
        if (process.env.G17_SHORTEN_WHY === "2") log(`  bullets ${first}.. drop ${count}: ${next ? `${next.line}: ${next.message}` : "ok"} (theorem ${from}-${to})`);
        // A failure inside the last bullet's body is later repair work.
        if (!next || (next.line >= first && next.line > bullets[bullets.length - 1]! - (cut - first))) repaired = candidate;
      }
      if (repaired) { lines = repaired; continue; }
    }
    // A constructor whose first conjunct, a carrier guard on a witness, is
    // now discharged on its own: the constructor and its first bullet go,
    // and the second bullet's lines move up to the constructor's column.
    // Seen either at the constructor, when the remaining goal is no
    // conjunction, or at the first bullet, when its carrier fact meets the
    // mathematical goal.
    const removeConstructor = (at: number, firstUnitStands: boolean): boolean => {
      const indent = indentOf(lines[at]!);
      const bulletAt = (position: number): boolean => /^\s*\.\s/.test(lines[position] ?? "") && indentOf(lines[position]!) === indent;
      const unitEnd = (start: number): number => {
        let end = start + 1;
        while (end < lines.length && lines[end]!.trim() !== "" && indentOf(lines[end]!) > indent) end += 1;
        return end;
      };
      if (bulletAt(at + 1)) {
        const second = unitEnd(at + 1);
        if (bulletAt(second)) {
          const end = unitEnd(second);
          const moved = lines.slice(second, end).map((item, position) =>
            position === 0 ? `${" ".repeat(indent)}${item.trim().replace(/^\.\s+/, "")}` : item.slice(2));
          lines = [...lines.slice(0, at), ...moved, ...lines.slice(end)];
        } else {
          // One bullet, then the rest of the goals in sequence.
          lines = [...lines.slice(0, at), ...lines.slice(second)];
        }
        return true;
      }
      if (firstUnitStands && indentOf(lines[at + 1] ?? "") === indent &&
          /^(assumption|typecheck|exact\s+\S+|settle\b.*|simp\b.*|trivial)$/u.test(lines[at + 1]!.trim())) {
        // Without bullets the first goal's one-line proof follows directly.
        lines = [...lines.slice(0, at), ...lines.slice(at + 2)];
        return true;
      }
      if (!firstUnitStands) {
        // The first goal's proof is already gone; only the constructor is left.
        lines = [...lines.slice(0, at), ...lines.slice(at + 1)];
        return true;
      }
      return false;
    };
    if (/constructor requires a conjunction/.test(failure.message) && text === "constructor" && removeConstructor(failing, false)) continue;
    if (/(?:establishes|proves) .+ : [ℕℤℚℝ], but|typecheck requires a soft-type|no assumption proves/u.test(failure.message) && failing > 0 &&
        lines[failing - 1]!.trim() === "constructor" && indentOf(lines[failing - 1]!) <= indentOf(lines[failing]!) &&
        removeConstructor(failing - 1, true)) continue;
    // A refine entry that proved a carrier guard on a witness is now
    // routine: the entry leaves the tuple.
    const tupleEntry = /^(?:line \d+: )?(\S+) proves .+ : [ℕℤℚℝ], but refine needs/u.exec(failure.message);
    const tuple = /^(\s*(?:\.\s+)?(?:refine|exact)\s+⟨)(.*)(⟩.*)$/u.exec(lines[failing] ?? "");
    if (tupleEntry && tuple) {
      const entries = splitTopLevel(tuple[2]!, ",").map(item => item.trim());
      const kept = entries.filter(item => item !== tupleEntry[1]);
      if (kept.length < entries.length && kept.length > 0) {
        lines = [...lines.slice(0, failing), `${tuple[1]}${kept.join(", ")}${tuple[3]}`, ...lines.slice(failing + 1)];
        continue;
      }
    }
    // A line reached with no goal left is redundant whatever it says.
    if (/no goals remain|dedent after completing/.test(failure.message)) {
      lines = [...lines.slice(0, failing), ...lines.slice(failing + 1)];
      continue;
    }
    const stray = (/^(assumption|typecheck|exact\s+[\p{L}_][\p{L}\p{M}\p{N}_'.]*|trivial)$/u.test(text)
      && /no assumption proves|but the goal is|is not the goal|cannot close/.test(failure.message))
      // A rewrite that no longer matches was done by an earlier step.
      || (/^(rw|rewrite|rwa)\s/.test(text) && /rewrite rule does not match/.test(failure.message))
      || (text === "typecheck" && /could not infer|requires a soft-type/.test(failure.message))
      // A step that proved a carrier fact meets a goal of another kind now.
      || (/^(apply|exact)\s/.test(text) && /(?:concludes|establishes) .+ : [ℕℤℚℝ], (?:not|but the goal is)/u.test(failure.message));
    if (!stray) return why(`${failure.message} :: ${text}`);
    lines = [...lines.slice(0, failing), ...lines.slice(failing + 1)];
  }
  return source;
}

/** Shorten one module on `kernel`; returns the new source and the kernel with it loaded. */
export function shortenModule(kernel: Kernel, file: string, original: string, log: (line: string) => void): { source: string; kernel: Kernel; applied: number; dropped: number } {
  const source = repairBaseline(kernel, file, original, log);
  if (collapse) {
    const first = shortenWith(kernel, file, source, log, collapseRewrites);
    const second = shortenWith(kernel, file, first.source, log, proofRewrites);
    return { source: second.source, kernel: second.kernel, applied: first.applied + second.applied, dropped: first.dropped + second.dropped };
  }
  return shortenWith(kernel, file, source, log, proofRewrites);
}

function shortenWith(kernel: Kernel, file: string, source: string, log: (line: string) => void, candidates: (lines: readonly string[]) => Rewrite[]): { source: string; kernel: Kernel; applied: number; dropped: number } {
  const lines = source.split("\n");
  let rewrites = candidates(lines);
  const total = rewrites.length;
  let attempts = 0;
  // A file that does not check even unchanged (another foundation, a name
  // clash with an earlier entry) is skipped and the kernel left as it was.
  // When a failure cannot be attributed, the surviving rewrites are
  // bisected: each half is tried on its own and the passing subsets are
  // combined, so an unexplained interaction costs at most a few rewrites.
  const bisect = (candidates: readonly Rewrite[]): Rewrite[] => {
    if (candidates.length === 0) return [];
    const result = tryElaborate(kernel, applyRewrites(lines, candidates).text, file);
    if ("kernel" in result) return [...candidates];
    if (candidates.length === 1) {
      if (process.env.G17_SHORTEN_WHY) log(`  bisect drop: ${lines[candidates[0]!.start]!.trim()} -> ${candidates[0]!.replacement[0]?.trim() ?? "(drop)"} :: ${result.message}`);
      return [];
    }
    const middle = candidates.length >> 1;
    const left = bisect(candidates.slice(0, middle));
    const right = bisect(candidates.slice(middle));
    const union = [...left, ...right].sort((a, b) => a.start - b.start);
    if (union.length === left.length + right.length && union.length > 0) {
      const combined = tryElaborate(kernel, applyRewrites(lines, union).text, file);
      if ("kernel" in combined) return union;
    }
    return left.length >= right.length ? left : right;
  };
  const keepOriginal = (message: string) => {
    const original = tryElaborate(kernel, source, file);
    if (!("kernel" in original)) { log(`${file}: skipped, does not check here (${original.message})`); return { source, kernel, applied: 0, dropped: total }; }
    const salvaged = bisect(rewrites);
    if (salvaged.length) {
      const { text } = applyRewrites(lines, salvaged);
      const checked = tryElaborate(kernel, text, file);
      if ("kernel" in checked) {
        log(`${file}: ${salvaged.length} rewrites kept by bisection, ${total - salvaged.length} reverted, ${lines.length - text.split("\n").length} lines saved (${message})`);
        return { source: text, kernel: checked.kernel, applied: salvaged.length, dropped: total - salvaged.length };
      }
    }
    log(`${file}: giving up, original kept (${message})`);
    return { source, kernel: original.kernel, applied: 0, dropped: total };
  };
  for (;;) {
    const { text, owners } = applyRewrites(lines, rewrites);
    const result = tryElaborate(kernel, text, file);
    if ("kernel" in result) {
      const dropped = total - rewrites.length;
      log(`${file}: ${rewrites.length} rewrites kept, ${dropped} reverted, ${lines.length - text.split("\n").length} lines saved`);
      return { source: text, kernel: result.kernel, applied: rewrites.length, dropped };
    }
    attempts += 1;
    if (rewrites.length === 0 || attempts > total * 6 + 5) {
      return keepOriginal(result.message);
    }
    // A definition's obligation names the failing line of the proof it
    // refers to; the innermost line is the one to revert.
    const nested = [...result.message.matchAll(/line (\d+):/g)].map(match => Number(match[1]));
    const failingLine = nested.length ? nested[nested.length - 1]! : result.line;
    // Stronger automation can close a goal before a later line expects it:
    // that line is now redundant and is dropped.
    if (/no goals remain|dedent after completing local proof/.test(result.message) && !owners[failingLine - 1]) {
      const original = originalLineOf(lines, rewrites, failingLine - 1);
      if (original !== undefined && lines[original]!.trim() && !/^(\.|\|)/.test(lines[original]!.trim())) {
        rewrites = [...rewrites, { kind: "drop", start: original, end: original + 1, replacement: [] }]
          .sort((left, right) => left.start - right.start);
        continue;
      }
    }
    const owner = owners[failingLine - 1];
    // A rewrite that fails may only be missing a line dropped earlier in
    // its theorem (an unfold the application relied on): with that drop
    // restored, the rewrite is tried once more before it is blamed.
    if (owner) {
      const [ownerStart, ownerEnd] = theoremRange(text.split("\n"), failingLine - 1);
      const from = originalLineOf(lines, rewrites, ownerStart) ?? 0;
      const to = originalLineOf(lines, rewrites, failingLine - 1) ?? owner.start;
      const drops = rewrites.filter(item => item.kind === "drop" && item !== owner && item.start >= from && item.start < to);
      if (drops.length) {
        const restored = rewrites.filter(item => !drops.includes(item));
        const retry = tryElaborate(kernel, applyRewrites(lines, restored).text, file);
        const moved = "kernel" in retry || retry.line !== failingLine;
        if (process.env.G17_SHORTEN_WHY) log(`  restore ${drops.length} drops for ${owner.replacement[0]!.trim()}: ${moved ? "helps" : "no help"}`);
        if (moved) { rewrites = restored; continue; }
      }
      void ownerEnd;
    }
    if (process.env.G17_SHORTEN_WHY) log(`  revert: ${owner ? owner.replacement[0]!.trim() : "(downstream)"} :: ${result.message}`);
    if (owner) {
      const [next, ...rest] = owner.fallbacks ?? [];
      rewrites = next
        ? rewrites.map(item => item === owner ? { ...owner, replacement: next, fallbacks: rest } : item)
        : rewrites.filter(item => item !== owner);
      continue;
    }
    // The failure is downstream of a rewrite in the same theorem.
    const newLines = text.split("\n");
    const [start, end] = theoremRange(newLines, failingLine - 1);
    // A dropped line leaves no owner in the new text; it is found by its
    // original position inside the theorem's original range.
    const originalStart = originalLineOf(lines, rewrites, start) ?? 0;
    const originalFailing = originalLineOf(lines, rewrites, failingLine - 1) ?? Infinity;
    const droppedInTheorem = rewrites.filter(item => item.kind === "drop" && item.start >= originalStart && item.start < originalFailing);
    if (droppedInTheorem.length) {
      rewrites = rewrites.filter(item => item !== droppedInTheorem[droppedInTheorem.length - 1]);
      continue;
    }
    const inTheorem = new Set(owners.slice(start, end).filter(Boolean));
    // A dropped line (an unfold … at, a specialize) is the usual cause of a
    // later failure in the same theorem: revert those first, one at a time.
    const droppedBefore = [...inTheorem].filter(item => item.kind === "drop" && item.start < (originalLineOf(lines, rewrites, failingLine - 1) ?? Infinity));
    if (droppedBefore.length) {
      const last = droppedBefore[droppedBefore.length - 1]!;
      rewrites = rewrites.filter(item => item !== last);
      continue;
    }
    if (inTheorem.size === 0) {
      // An unattributable failure reverts the nearest rewrite before it
      // rather than the whole module.
      const before = owners.slice(0, failingLine - 1).filter(Boolean);
      const nearest = before[before.length - 1];
      if (!nearest) return keepOriginal(result.message);
      rewrites = rewrites.filter(item => item !== nearest);
      continue;
    }
    rewrites = rewrites.filter(item => !inTheorem.has(item));
  }
}

if (import.meta.url === `file://${process.argv[1]}`) {
  const resolvedRoots = roots.map(root => resolve(root));
  const sources = new Map<string, { file: string; source: string; imports: readonly string[] }>();
  const locate = (name: string): void => {
    if (sources.has(name)) return;
    const relative = `${name.split(".").join("/")}.g17`;
    const file = resolvedRoots.map(root => resolve(root, relative)).find(candidate => existsSync(candidate));
    if (!file) throw new Error(`cannot locate ${name}`);
    const source = readFileSync(file, "utf8");
    const meta = scanModule(source, file, path => moduleNameFromPath(path, resolvedRoots));
    const exists = (candidate: string): boolean => sources.has(candidate) ||
      resolvedRoots.some(root => existsSync(resolve(root, `${candidate.split(".").join("/")}.g17`)));
    const imports = meta.imports.map(raw => resolveImportName(name, raw, exists) ?? raw);
    sources.set(name, { file, source, imports });
    imports.forEach(locate);
  };
  // File entries are standalone documents such as examples: each is checked
  // on its own fork of the library kernel, after every library module.
  const standalone: { file: string; source: string }[] = [];
  // Library modules load in the import order of the entries, as g17 check
  // does; a file under a module root is the module it declares.
  const roots_ = roots.map(root => resolve(root));
  const rootNames: string[] = [];
  for (const entry of entries) {
    if (!entry.endsWith(".g17")) { locate(entry); rootNames.push(entry); continue; }
    const source = readFileSync(entry, "utf8");
    const meta = scanModule(source, resolve(entry), path => moduleNameFromPath(path, roots_));
    const asModule = meta.name && roots_.some(root => resolve(root, `${meta.name!.split(".").join("/")}.g17`) === resolve(entry));
    if (asModule) { locate(meta.name!); rootNames.push(meta.name!); continue; }
    standalone.push({ file: resolve(entry), source });
    const exists = (candidate: string): boolean => sources.has(candidate) ||
      roots_.some(root => existsSync(resolve(root, `${candidate.split(".").join("/")}.g17`)));
    meta.imports.map(raw => resolveImportName(meta.name, raw, exists) ?? raw).forEach(locate);
  }
  for (const item of sources.values()) indexRequires(item.source);
  for (const item of standalone) indexRequires(item.source);
  const order: string[] = [];
  const visited = new Set<string>();
  const visit = (name: string): void => {
    if (visited.has(name)) return;
    visited.add(name);
    sources.get(name)!.imports.forEach(visit);
    order.push(name);
  };
  rootNames.forEach(visit);
  for (const item of standalone) scanModule(item.source).imports.forEach(visit);

  let kernel = createSetTheoryKernel({ profile: "ZFG" });
  setSurfaceTraceCapture(kernel, false);
  let applied = 0, dropped = 0, saved = 0;
  const started = performance.now();
  const record = (file: string, source: string, result: ReturnType<typeof shortenModule>): void => {
    applied += result.applied;
    dropped += result.dropped;
    saved += source.split("\n").length - result.source.split("\n").length;
    if (write && result.source !== source) writeFileSync(file, result.source);
  };
  for (const name of order) {
    const item = sources.get(name)!;
    const result = shortenModule(kernel, item.file, item.source, line => console.log(line));
    kernel = result.kernel;
    record(item.file, item.source, result);
  }
  for (const item of standalone) record(item.file, item.source, shortenModule(kernel, item.file, item.source, line => console.log(line)));
  console.log(`${applied} rewrites applied, ${dropped} reverted, ${saved} lines saved in ${order.length} modules (${((performance.now() - started) / 1000).toFixed(0)}s)${write ? "" : "; rerun with --write to save"}`);
}
