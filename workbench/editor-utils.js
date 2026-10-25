// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Cursor-to-step, name-to-symbol, and diagnostic-span logic is shared with
// the machine interface in src/workbench-navigation.ts.
import { diagnosticIdentifier, diagnosticSpan, resolveSymbolCandidate, tacticStepAtCursor } from "./generated/src/workbench-navigation.js";
export { diagnosticIdentifier, diagnosticSpan, resolveSymbolCandidate, tacticStepAtCursor };

/** Return the identifier genuinely under the pointer, never its left neighbor. */
export function tokenAtTextOffset(text, offset) {
  if (!Number.isSafeInteger(offset) || offset < 0 || offset >= text.length) return undefined;
  const constituent = /[\p{L}\p{M}\p{N}_.?]/u;
  if (!constituent.test(text[offset] || "")) return undefined;
  let start = offset;
  let end = offset;
  while (start > 0 && constituent.test(text[start - 1])) start -= 1;
  while (end < text.length && constituent.test(text[end])) end += 1;
  return { text: text.slice(start, end), start, end };
}

/** Return a tactic name only when the token occurs in tactic-command position. */
export function tacticTokenAtTextOffset(text, offset, tacticNames = []) {
  const token = tokenAtTextOffset(text, offset);
  if (!token || !new Set(tacticNames).has(token.text)) return undefined;
  const lineStart = text.lastIndexOf("\n", token.start - 1) + 1;
  const prefix = text.slice(lineStart, token.start);
  return /(?:^|;|=>|⇒)\s*\.?\s*$/.test(prefix) ? token : undefined;
}

/** Locate the proof-producing declaration containing an error/cursor line. */
export function proofDeclarationContext(text, lineNumber) {
  const lines = String(text || "").split(/\r?\n/);
  const declaration = /^\s*(?:theorem|lemma|instance|defgraph)\b(?:\s+(\S+))?/;
  const boundary = /^\s*(?:noncomputable\s+(?:transfinite|foundation|well-founded)\s+def|datatype|class|defgraph|defchoose|defunique|def|define|predicate|theorem|lemma|instance|eval|notation|tactic|module|import|namespace|section|variable|hypothesis|export\s+open|open|end)\b/;
  let start = -1;
  for (let index = Math.min((lineNumber || lines.length) - 1, lines.length - 1); index >= 0; index -= 1) {
    if (!boundary.test(lines[index])) continue;
    if (declaration.test(lines[index])) start = index;
    break;
  }
  if (start < 0) return undefined;
  let end = lines.length;
  for (let index = start + 1; index < lines.length; index += 1) {
    if (boundary.test(lines[index])) { end = index; break; }
  }
  const shows = lines.slice(start + 1, end).find(line => /^\s*shows\s+/.test(line));
  return {
    name: declaration.exec(lines[start])?.[1] || "Incomplete proof",
    lineStart: start + 1,
    lineEnd: end,
    statement: shows ? shows.replace(/^\s*shows\s+/, "") : "Proof incomplete",
  };
}

/** Find a literal token at the top level of a line, skipping `::` and `:=` and bracketed text. */
function topLevelTokens(line, token) {
  const positions = [];
  let depth = 0;
  for (let index = 0; index < line.length; index += 1) {
    const character = line[index];
    if ("([{⟨".includes(character)) depth += 1;
    else if (")]}⟩".includes(character)) depth -= 1;
    else if (depth === 0 && line.startsWith(token, index)) {
      const before = line[index - 1] ?? " ";
      const after = line[index + token.length] ?? " ";
      const punctuation = /[^\p{L}\p{M}\p{N}\s_(),."]/u;
      if (!punctuation.test(before) && !punctuation.test(after)) positions.push(index);
    }
  }
  return positions;
}

const formulaConnectives = /[∧∨↔¬∈∉=≠⊆⊂≤<]|\b(and|or|in|not)\b/u;

/**
 * A mixfix notation such as `_ : _ → _` under the pointer: the pointer rests
 * on one of its literal tokens, and the line carries every literal in order
 * at the top level with only terms between them.
 */
export function mixfixAtTextOffset(text, offset, notation) {
  const literals = String(notation?.token ?? "").split("_").slice(1, -1).map(piece => piece.trim());
  if (literals.length === 0 || !literals.every(Boolean)) return undefined;
  // The pattern is matched inside the innermost bracket group around the
  // pointer, or else on the pointer's line, so `(g : B → C)` in a binder list
  // and `requires hf : f : A → B` are both found.
  let lineStart = text.lastIndexOf("\n", offset - 1) + 1;
  const lineEndIndex = text.indexOf("\n", offset);
  let lineEnd = lineEndIndex < 0 ? text.length : lineEndIndex;
  let depth = 0;
  for (let index = offset - 1; index >= lineStart; index -= 1) {
    const character = text[index];
    if (")]}⟩".includes(character)) depth += 1;
    else if ("([{⟨".includes(character)) {
      if (depth === 0) { lineStart = index + 1; break; }
      depth -= 1;
    }
  }
  depth = 0;
  for (let index = offset; index < lineEnd; index += 1) {
    const character = text[index];
    if ("([{⟨".includes(character)) depth += 1;
    else if (")]}⟩".includes(character)) {
      if (depth === 0) { lineEnd = index; break; }
      depth -= 1;
    }
  }
  // A `have` line ends its statement at `:=` or `by`.
  const statementEnd = text.slice(lineStart, lineEnd).search(/\s:=\s|\sby\s/u);
  if (statementEnd >= 0 && offset < lineStart + statementEnd) lineEnd = lineStart + statementEnd;
  const line = text.slice(lineStart, lineEnd);
  const local = offset - lineStart;
  // The implication arrow and the binder colon are ordinary syntax; only a
  // complete pattern on the line, with a term in every placeholder, makes the
  // literal under the pointer notation.
  const spellings = literal => literal === "→" ? ["→", "->"] : literal === "↔" ? ["↔", "<->"] : [literal];
  const occurrences = literal => spellings(literal)
    .flatMap(spelling => topLevelTokens(line, spelling).map(index => ({ index, length: spelling.length })))
    .sort((left, right) => left.index - right.index);
  const clean = piece => piece.trim() && !formulaConnectives.test(piece) &&
    literals.every(literal => spellings(literal).every(spelling => topLevelTokens(piece, spelling).length === 0));
  const complete = (found, from, remaining) => {
    if (remaining.length === 0) return clean(line.slice(from)) ? found : undefined;
    for (const occurrence of occurrences(remaining[0])) {
      if (occurrence.index <= from || !clean(line.slice(from, occurrence.index))) continue;
      const match = complete([...found, occurrence], occurrence.index + occurrence.length, remaining.slice(1));
      if (match) return match;
    }
    return undefined;
  };
  for (const first of occurrences(literals[0])) {
    // The text before the first literal may carry a binder or premise name
    // and its own colon; only the placeholder next to the literal is a term.
    if (first.index === 0 || !line.slice(0, first.index).trim()) continue;
    const found = complete([first], first.index + first.length, literals.slice(1));
    if (!found) continue;
    const hovered = found.find(item => local >= item.index && local < item.index + item.length);
    if (hovered) return { text: notation.token, start: lineStart + hovered.index, end: lineStart + hovered.index + hovered.length, mixfix: true };
  }
  return undefined;
}

/** Match the longest declared notation genuinely under the pointer. */
export function notationAtTextOffset(text, offset, notations = []) {
  if (!Number.isSafeInteger(offset) || offset < 0 || offset >= text.length) return undefined;
  for (const notation of notations) {
    if (notation?.fixity !== "mixfix") continue;
    const match = mixfixAtTextOffset(text, offset, notation);
    if (match) return match;
  }
  const tokens = [...new Set(notations.filter(notation => notation?.fixity !== "mixfix").map(notation => notation?.token).filter(Boolean))]
    .sort((left, right) => right.length - left.length);
  for (const token of tokens) {
    // A token under the pointer can begin at only token.length nearby offsets.
    // Never scan the source prefix: Monaco calls hover providers repeatedly as
    // text scrolls beneath a stationary pointer, so prefix scans turn an
    // otherwise local interaction into quadratic main-thread work.
    const first = Math.max(0, offset - token.length + 1);
    for (let start = first; start <= offset; start += 1) {
      if (text.startsWith(token, start) && offset < start + token.length) {
        return { text: token, start, end: start + token.length };
      }
    }
  }
  return undefined;
}

const subscriptValues = Object.freeze({
  "₀": "0", "₁": "1", "₂": "2", "₃": "3", "₄": "4", "₅": "5", "₆": "6", "₇": "7", "₈": "8", "₉": "9",
  "ₐ": "a", "ₑ": "e", "ₕ": "h", "ᵢ": "i", "ⱼ": "j", "ₖ": "k", "ₗ": "l", "ₘ": "m",
  "ₙ": "n", "ₒ": "o", "ₚ": "p", "ᵣ": "r", "ₛ": "s", "ₜ": "t", "ₓ": "x",
});

function pairIndexParts(index) {
  const parts = [];
  let depth = 0;
  let start = 0;
  for (let position = 0; position < index.length; position += 1) {
    const character = index[position];
    if ("([{⟨".includes(character)) depth += 1;
    else if (")]}⟩".includes(character)) depth -= 1;
    else if (character === "," && depth === 0) {
      parts.push(index.slice(start, position).trim());
      start = position + 1;
    }
  }
  parts.push(index.slice(start).trim());
  return parts.length === 2 && parts.every(Boolean) ? parts : undefined;
}

/** Typed parameters in the current declaration take precedence over index sugar. */
export function declaredParameterNames(text, offset) {
  const source = String(text);
  const starts = [...source.slice(0, offset + 1).matchAll(
    /^\s*(?:theorem|lemma|instance|def|define|predicate|class|defgraph|defchoose|defunique|module|namespace|section|variable|hypothesis|end)\b/gmu)];
  const start = starts.at(-1)?.index;
  if (start === undefined || /^\s*(?:module|namespace|section|variable|hypothesis|end)\b/u.test(source.slice(start))) return [];
  const header = source.slice(start).split(/\n\s*(?:requires|shows|proof)\b|:=/u)[0];
  const names = [];
  for (const binder of header.matchAll(/[({]\s*([^():{}\n]+?)\s*:\s*[\p{L}_][\p{L}\p{N}_.]*/gu)) {
    names.push(...(binder[1].match(/[\p{L}_][\p{L}\p{M}\p{N}_'.?]*/gu) || []));
  }
  return names;
}

/** Recognize the general postfix indexing sugar `uₙ` and `u[n]`. */
export function subscriptNotationAtTextOffset(text, offset, declaredNames = []) {
  if (!Number.isSafeInteger(offset) || offset < 0 || offset >= text.length) return undefined;
  const token = tokenAtTextOffset(text, offset);
  if (token) {
    const match = /^(.*?)([₀-₉ₐₑₒₓₕₖₗₘₙₚₛₜᵢᵣⱼ]+)$/u.exec(token.text);
    if (match?.[1] && [...match[2]].every(character => subscriptValues[character])) {
      if (declaredNames.includes(token.text) || declaredParameterNames(text, offset).includes(token.text)) return undefined;
      const index = [...match[2]].map(character => subscriptValues[character]).join("");
      return {
        text: token.text, start: token.start, end: token.end, target: "apply",
        literal: token.text, literalStart: token.start, literalEnd: token.end,
        desugaring: `apply(${match[1]}, ${index})`,
      };
    }
  }
  const lineStart = text.lastIndexOf("\n", offset - 1) + 1;
  const lineEndCandidate = text.indexOf("\n", offset);
  const lineEnd = lineEndCandidate < 0 ? text.length : lineEndCandidate;
  const line = text.slice(lineStart, lineEnd);
  for (const match of line.matchAll(/([\p{L}_][\p{L}\p{M}\p{N}_.]*)\[([^\[\]\n]+)\]/gu)) {
    const start = lineStart + match.index;
    const end = start + match[0].length;
    if (offset < start || offset >= end) continue;
    return {
      text: match[0], start, end, target: "apply",
      literal: match[0], literalStart: start, literalEnd: end,
      desugaring: (() => {
        const parts = pairIndexParts(match[2]);
        return parts
          ? `apply(${match[1]}, orderedPair(${parts[0]}, ${parts[1]}))`
          : `apply(${match[1]}, ${match[2].trim()})`;
      })(),
    };
  }
  return undefined;
}

/** Infer an overloaded notation's carrier from the rendered proof-state context. */
export function notationOperandTypeAtTextOffset(text, token, localSymbols = [], notations = []) {
  const candidates = notations.filter(item => item?.token === token?.text && item.operandType);
  if (candidates.length < 2) return candidates[0]?.operandType?.split(".").at(-1);
  const candidateTypes = new Set(candidates.map(item => item.operandType.split(".").at(-1)));
  const localTypes = new Map();
  for (const local of localSymbols) {
    const formula = String(local?.formula || "");
    const membership = /^\s*([\p{L}_][\p{L}\p{M}\p{N}_.'?-]*)\s*(?:∈|:)\s*([\p{L}_][\p{L}\p{M}\p{N}_.]*)\s*$/u.exec(formula);
    if (membership) localTypes.set(membership[1], membership[2].split(".").at(-1));
    if (local?.name && membership) localTypes.set(local.name, membership[2].split(".").at(-1));
  }
  const mentioned = new Set();
  const identifiers = new Set();
  for (const identifier of String(text).matchAll(/[\p{L}_][\p{L}\p{M}\p{N}_.'?-]*/gu)) {
    identifiers.add(identifier[0]);
    const type = localTypes.get(identifier[0]);
    if (candidateTypes.has(type)) mentioned.add(type);
  }
  // Explicit graph arguments such as realLe also reveal the elaborated
  // carrier even when the corresponding surface operator is not printed.
  for (const notation of notations) {
    const selected = notation.leadingArguments?.[0];
    const name = selected?.tag === "app" && selected.args?.length === 0 ? selected.fn : notation.target;
    const leaf = name?.split(".").at(-1);
    const type = notation.operandType?.split(".").at(-1);
    if (leaf && type && candidateTypes.has(type) && identifiers.has(leaf)) {
      mentioned.add(type);
    }
  }
  return mentioned.size === 1 ? [...mentioned][0] : undefined;
}

/** Select a typed infix implementation from the independently known operand types. */
export function notationForOperandTypes(candidates = [], leftType, rightType) {
  const short = type => type?.split(".").at(-1);
  const matches = candidates.filter(item => {
    const left = short(item?.leftOperandType || item?.operandType);
    const right = short(item?.rightOperandType || item?.operandType);
    if (!left || !right) return false;
    return (!leftType || left === leftType) && (!rightType || right === rightType) &&
      Boolean(leftType || rightType);
  });
  return matches.length === 1 ? matches[0] : undefined;
}

/** Human-readable carrier signature for notation diagnostics and hover menus. */
export function notationTypeLabel(notation) {
  const short = type => type?.split(".").at(-1);
  const left = short(notation?.leftOperandType || notation?.operandType);
  const right = short(notation?.rightOperandType || notation?.operandType);
  if (!left || !right) return "untyped";
  return left === right ? left : `${left}, ${right}`;
}


/**
 * The qualified module a workbench file declares. A bare `module Name` under
 * the library takes its qualification from the file's path, as the checker
 * does: lib/Grace/Cumulus/Real/FiniteSum.g17 is Grace.Cumulus.Real.FiniteSum.
 */
export function moduleNameOf(source, file = "") {
  const declared = /^\s*module\s+(\S+)/m.exec(source)?.[1];
  if (!declared || declared.includes(".")) return declared;
  const under = /(?:^|\/)lib\/(.+)\.g17$/.exec(String(file).replaceAll("\\", "/"));
  if (!under) return declared;
  const segments = under[1].split("/");
  return segments[segments.length - 1] === declared ? segments.join(".") : declared;
}

/**
 * Recover the most recent authored soft type for an identifier near an
 * overloaded notation token.  The binder grammar is scanned with one static
 * expression; identifier text is compared as data and is never interpolated
 * into executable regular-expression syntax.
 */
export function localTypeAtTextOffset(text, token) {
  if (!token || !Number.isSafeInteger(token.start) || token.start < 0 ||
      !/^[\p{L}_][\p{L}\p{M}\p{N}_.'?-]*$/u.test(token.text || "")) return undefined;
  const prefix = String(text).slice(0, token.start);
  const binder = /(?:^|[,(])\s*([^\n():,]*?)\s*:\s*([\p{L}_][\p{L}\p{M}\p{N}_.]*)/gmu;
  let inferred;
  for (const match of prefix.matchAll(binder)) {
    const names = match[1].match(/[\p{L}_][\p{L}\p{M}\p{N}_.'?-]*/gu) || [];
    if (names.includes(token.text)) inferred = match[2];
  }
  return inferred;
}

/** Recognize finite-set notation and expose its exact surface elaboration. */
export function setNotationAtTextOffset(text, offset) {
  if (!Number.isSafeInteger(offset) || offset < 0 || offset >= text.length) return undefined;
  if (text[offset] === "∅") return {
    text: "∅", start: offset, end: offset + 1, target: "empty",
    literal: "∅", literalStart: offset, literalEnd: offset + 1, elements: [], desugaring: "empty",
  };
  if (text[offset] !== "{" && text[offset] !== "}") return undefined;
  let start;
  let end;
  if (text[offset] === "{") {
    start = offset;
    let depth = 0;
    for (let index = start; index < text.length; index += 1) {
      if (text[index] === "{") depth += 1;
      else if (text[index] === "}" && --depth === 0) { end = index; break; }
    }
  } else {
    end = offset;
    let depth = 0;
    for (let index = end; index >= 0; index -= 1) {
      if (text[index] === "}") depth += 1;
      else if (text[index] === "{" && --depth === 0) { start = index; break; }
    }
  }
  if (start === undefined || end === undefined) return undefined;
  const body = text.slice(start + 1, end);
  let depth = 0;
  let elementStart = 0;
  const elements = [];
  for (let index = 0; index < body.length; index += 1) {
    const character = body[index];
    if (character === "(" || character === "{" || character === "[") depth += 1;
    else if (character === ")" || character === "}" || character === "]") depth -= 1;
    else if (depth === 0 && character === ",") {
      elements.push(body.slice(elementStart, index).trim());
      elementStart = index + 1;
    }
    else if (depth === 0 && (character === "|" || character === ":")) return undefined;
  }
  if (body.trim()) elements.push(body.slice(elementStart).trim());
  if (elements.some(element => !element)) return undefined;
  const target = elements.length === 0 ? "empty" : elements.length === 1 ? "singleton" : elements.length === 2 ? "pair" : "union2";
  return {
    text: text[offset], start: offset, end: offset + 1, target,
    literal: text.slice(start, end + 1), literalStart: start, literalEnd: end + 1,
    elements, desugaring: finiteSetDesugaring(elements),
  };
}

/** Recognize binary tuple punctuation without mistaking an ordinary call f(x, y). */
export function orderedPairNotationAtTextOffset(text, offset) {
  if (!Number.isSafeInteger(offset) || offset < 0 || offset >= text.length || !"(),".includes(text[offset])) return undefined;
  const lineStart = text.lastIndexOf("\n", offset - 1) + 1;
  const nextLine = text.indexOf("\n", offset);
  const lineEnd = nextLine < 0 ? text.length : nextLine;
  const stack = [];
  const pairs = [];
  for (let index = lineStart; index < lineEnd; index += 1) {
    if (text[index] === "(") stack.push(index);
    else if (text[index] === ")" && stack.length) {
      const start = stack.pop();
      if (start <= offset && offset <= index) pairs.push({ start, end: index });
    }
  }
  pairs.sort((left, right) => (left.end - left.start) - (right.end - right.start));
  for (const pair of pairs) {
    let before = pair.start - 1;
    while (before >= lineStart && /\s/u.test(text[before])) before -= 1;
    if (before >= lineStart && /[\p{L}\p{M}\p{N}_.?\)\]\}]/u.test(text[before])) continue;
    let depth = 0;
    let comma = -1;
    for (let index = pair.start + 1; index < pair.end; index += 1) {
      const character = text[index];
      if (character === "(" || character === "{" || character === "[") depth += 1;
      else if (character === ")" || character === "}" || character === "]") depth -= 1;
      else if (character === "," && depth === 0) {
        if (comma >= 0) { comma = -1; break; }
        comma = index;
      }
    }
    if (comma < 0) continue;
    const left = text.slice(pair.start + 1, comma).trim();
    const right = text.slice(comma + 1, pair.end).trim();
    if (!left || !right) continue;
    // A comma after a binder separates it from its body, as in
    // `(∃ m, Maximal(A, r, m))`: that group is a formula, not a pair.
    if (/^[∃∀λ∑∏⋃⋂]/u.test(left)) continue;
    const literal = text.slice(pair.start, pair.end + 1);
    return {
      text: text[offset], start: offset, end: offset + 1, target: "orderedPair",
      literal, literalStart: pair.start, literalEnd: pair.end + 1,
      elements: [left, right], desugaring: `orderedPair(${left}, ${right})`,
    };
  }
  return undefined;
}

/** Recognize ⟦x⟧[A, r] and expose the underlying ternary constructor. */
export function equivalenceClassNotationAtTextOffset(text, offset) {
  if (!Number.isSafeInteger(offset) || offset < 0 || offset >= text.length || !"⟦⟧".includes(text[offset])) return undefined;
  const left = text.lastIndexOf("⟦", offset);
  const middle = text.indexOf("⟧", left + 1);
  if (left < 0 || middle < 0 || (offset !== left && offset !== middle) || text[middle + 1] !== "[") return undefined;
  let depth = 0;
  let comma = -1;
  let right = -1;
  for (let index = middle + 1; index < text.length; index += 1) {
    if (text[index] === "[") depth += 1;
    else if (text[index] === "]" && --depth === 0) { right = index; break; }
    else if (text[index] === "," && depth === 1 && comma < 0) comma = index;
  }
  if (comma < 0 || right < 0) return undefined;
  const representative = text.slice(left + 1, middle).trim();
  const carrier = text.slice(middle + 2, comma).trim();
  const relation = text.slice(comma + 1, right).trim();
  if (!representative || !carrier || !relation) return undefined;
  const literal = text.slice(left, right + 1);
  return {
    text: text[offset], start: offset, end: offset + 1, target: "equivalenceClass",
    literal, literalStart: left, literalEnd: right + 1,
    desugaring: `equivalenceClass(${carrier}, ${relation}, ${representative})`,
  };
}

function finiteSetDesugaring(elements) {
  if (elements.length === 0) return "empty";
  if (elements.length === 1) return `singleton(${elements[0]})`;
  if (elements.length === 2) return `pair(${elements[0]}, ${elements[1]})`;
  return `union2(singleton(${elements[0]}), ${finiteSetDesugaring(elements.slice(1))})`;
}

export function shouldRetainLastGoal({ hasTrace, hasResult, errorBelongsToFile, theoremCount }) {
  return !hasTrace && hasResult && errorBelongsToFile && theoremCount > 0;
}

/**
 * Select editor buffers that override bundled modules.
 * Old persisted Core/Cumulus tabs are views and do not override dependencies.
 */
export function workspaceFilesForCheck(files, activeId, workbenchVersion) {
  return files.filter(file => {
    if (file.id === activeId || file.dirty) return true;
    // Clean Cumulus buffers are views of the embedded distribution and do not
    // override sources. Loading dependencies from the bundle prevents a recovered
    // session from assembling a theorem with clean files from another release.
    if (file.distribution === "cumulus") return false;
    if (file.openedIn === workbenchVersion) return true;
    const module = moduleNameOf(file.source, file.name) || "";
    return !/^Grace\.(?:Core|Cumulus)(?:\.|$)/.test(module);
  }).map(file => ({ name: file.name, source: file.source }));
}

/**
 * Return the post-0.98 location of a bundled number-system source file.
 * Only the former distribution root is recognized, so similarly named user
 * files are never rewritten.
 */
export function canonicalCumulusSourcePath(path) {
  return String(path || "").replaceAll("\\", "/").replace(
    /^lib\/Grace\/Cumulus\/Data\/(Nat|Int|Rat|Real)(?=\/|\.g17$)/,
    "lib/Grace/Cumulus/$1",
  );
}

/** Update module references inside an edited buffer without touching its proof. */
export function migrateCumulusModuleNames(source) {
  return String(source || "").replace(
    /Grace\.Cumulus\.Data\.(Nat|Int|Rat|Real)(?=\.|\b)/g,
    "Grace.Cumulus.$1",
  );
}

/**
 * Reconcile persisted bundled tabs with the distribution shipped by this
 * workbench. Clean tabs receive the exact current source. Dirty tabs retain
 * their authored text and get only the obsolete module-root migration.
 */
export function migratePersistedCumulusFiles(files, bundledLibrary, workbenchVersion) {
  for (const file of files) {
    const originalPath = file.sourceFile || file.name;
    const normalizedPath = String(originalPath || "").replaceAll("\\", "/");
    const bundledTab = file.distribution === "cumulus"
      || (normalizedPath.startsWith("lib/Grace/Cumulus/") && file.name === originalPath);
    if (!bundledTab) continue;

    const legacyProjectPath = file.distribution === "cumulus"
      ? normalizedPath.replace(/^Data\/(Nat|Int|Rat|Real)(?=\/|\.g17$)/, "lib/Grace/Cumulus/$1")
      : normalizedPath;
    const canonicalPath = canonicalCumulusSourcePath(legacyProjectPath);
    const bundledSource = bundledLibrary?.get?.(canonicalPath);
    if (bundledSource === undefined && canonicalPath === normalizedPath) continue;

    file.name = canonicalPath;
    file.sourceFile = canonicalPath;
    file.projectPath = canonicalPath === "lib/Grace/Cumulus.g17"
      ? "Cumulus.g17"
      : canonicalPath.replace(/^lib\/Grace\/Cumulus\//, "");
    file.source = file.dirty || bundledSource === undefined
      ? migrateCumulusModuleNames(file.source)
      : bundledSource;
    file.distribution = "cumulus";
    file.openedIn = workbenchVersion;
  }

  // A workspace may contain both sides of a distribution rename. Once both
  // names canonicalize to the same bundled file, keep an authored buffer over
  // a clean one, or the first clean view when neither was edited.
  const retained = new Map();
  for (const file of files) {
    if (file.distribution !== "cumulus" || !file.sourceFile) continue;
    const previous = retained.get(file.sourceFile);
    if (!previous) {
      retained.set(file.sourceFile, file);
      continue;
    }
    if (!previous.dirty && file.dirty) retained.set(file.sourceFile, file);
  }
  const discarded = new Set();
  const seen = new Set();
  for (const file of files) {
    if (file.distribution !== "cumulus" || !file.sourceFile) continue;
    if (seen.has(file.sourceFile) || retained.get(file.sourceFile) !== file) discarded.add(file);
    else seen.add(file.sourceFile);
  }
  if (discarded.size) files.splice(0, files.length, ...files.filter(file => !discarded.has(file)));
  return files;
}

export function isFoundationInternalFile(name) {
  return /(?:^|\/)(?:Bootstrap|Kernel)\//.test(String(name).replaceAll("\\", "/"));
}

/** Pick authored mathematics when a complete Grace library directory opens. */
export function preferredProjectFile(files) {
  if (!files.length) return undefined;
  if (!files.some(file => isFoundationInternalFile(file.name))) return files[0];
  const normalized = file => String(file.name).replaceAll("\\", "/");
  for (const suffix of ["Cumulus/Main.g17", "Core.g17"]) {
    const candidate = files.find(file => normalized(file) === suffix || normalized(file).endsWith(`/${suffix}`));
    if (candidate) return candidate;
  }
  return files.find(file => !isFoundationInternalFile(file.name)) ?? files[0];
}

/** Select the last tactic whose source span has begun at the cursor. */
/** Build an authored hierarchy and place each checked tactic in its narrowest section. */
export function proofMapSections(entries, steps) {
  const root = { notes: [], steps: [], sections: [] };
  const stack = [];
  const headings = [];
  for (const entry of entries) {
    if (entry.kind === "heading") {
      while (stack.length && stack.at(-1).indent >= entry.indent) stack.pop();
      const section = { ...entry, notes: [], steps: [], sections: [], endLine: Infinity };
      (stack.at(-1)?.sections || root.sections).push(section);
      stack.push(section);
      headings.push(section);
      continue;
    }
    const owner = [...stack].reverse().find(section => section.indent <= entry.indent);
    (owner?.notes || root.notes).push(entry);
  }
  headings.forEach((heading, index) => {
    heading.endLine = headings.slice(index + 1).find(next => next.indent <= heading.indent)?.line ?? Infinity;
  });
  for (const step of steps) {
    const owner = headings
      .filter(heading => heading.line <= step.line && step.line < heading.endLine)
      .sort((left, right) => right.indent - left.indent || right.line - left.line)[0];
    (owner?.steps || root.steps).push(step);
  }
  return root;
}

/** Number of leading checked tactic steps still present in edited source. */
export function matchingTacticPrefixLength(steps, text) {
  const lines = text.split("\n");
  let count = 0;
  for (const step of steps) {
    const line = lines[step.line - 1];
    if (line === undefined) break;
    const start = Math.max(0, (step.columnStart || 1) - 1);
    const end = step.columnEnd === undefined ? line.length : Math.max(start, step.columnEnd - 1);
    const expected = normalizeCommand(step.command);
    let actual = sourceTacticText(line.slice(start, end));
    let continuation = step.line;
    while (normalizeCommand(actual) !== expected && expected.startsWith(normalizeCommand(actual)) && continuation < lines.length) {
      actual += ` ${lines[continuation++].trim()}`;
    }
    if (normalizeCommand(actual) !== expected) break;
    count += 1;
  }
  return count;
}

/** Keep a checked trace cursor-navigable while an updated check is pending. */
export function visibleTacticSteps(steps, checkedSource, currentSource, hasStaleError = false) {
  if (checkedSource === currentSource || !hasStaleError) return steps;
  return steps.slice(0, matchingTacticPrefixLength(steps, currentSource));
}

/**
 * Linearize a kernel proof DAG in Fitch order: every cited premise appears
 * before the line that uses it. Shared proof nodes are emitted once, and the
 * source child order is retained so rule citations remain meaningful.
 */
export function kernelFitchOrder(nodes) {
  const byId = new Map(nodes.map(node => [node.id, node]));
  const cited = new Set(nodes.flatMap(node => node.children || []));
  const roots = nodes.filter(node => !cited.has(node.id));
  const emitted = new Set();
  const active = new Set();
  const ordered = [];
  const visit = node => {
    if (!node || emitted.has(node.id) || active.has(node.id)) return;
    active.add(node.id);
    for (const child of node.children || []) visit(byId.get(child));
    active.delete(node.id);
    emitted.add(node.id);
    ordered.push(node);
  };
  for (const root of roots) visit(root);
  for (const node of nodes) visit(node);
  return ordered.map((node, index) => ({ ...node, fitchLine: index + 1 }));
}

function normalizeCommand(value) { return String(value || "").trim().replace(/\s+/g, " "); }
function sourceTacticText(value) { return String(value || "").trim().replace(/^\.\s+/, ""); }

/** Split a changed goal for highlighting without inventing replacement text. */
export function changedTextParts(value, previous) {
  if (previous === undefined || previous === value) return { prefix: value, changed: "", suffix: "" };
  let prefixLength = 0;
  while (prefixLength < value.length && prefixLength < previous.length && value[prefixLength] === previous[prefixLength]) prefixLength += 1;
  let suffixLength = 0;
  while (suffixLength < value.length - prefixLength && suffixLength < previous.length - prefixLength && value.at(-suffixLength - 1) === previous.at(-suffixLength - 1)) suffixLength += 1;
  return {
    prefix: value.slice(0, prefixLength),
    changed: value.slice(prefixLength, value.length - suffixLength),
    suffix: value.slice(value.length - suffixLength),
  };
}

export const unicodeInputMap = Object.freeze({
  forall: "∀", all: "∀", exists: "∃", ex: "∃", in: "∈",
  to: "→", r: "→", imp: "→", rightarrow: "→", l: "←", leftarrow: "←",
  iff: "↔", lr: "↔", and: "∧", or: "∨", not: "¬", ne: "≠", notin: "∉", le: "≤", ge: "≥",
  empty: "∅", epsilon0: "ε₀", uplus: "⊎", langle: "⟨", rangle: "⟩", "<": "⟨", ">": "⟩",
  naturals: "ℕ", integers: "ℤ", rationals: "ℚ", reals: "ℝ",
  nat: "ℕ", N: "ℕ", Z: "ℤ", rat: "ℚ", q: "ℚ", Q: "ℚ", real: "ℝ", R: "ℝ",
  mathbbN: "ℕ", mathbbZ: "ℤ", mathbbQ: "ℚ", mathbbR: "ℝ", bbN: "ℕ", bbZ: "ℤ", bbQ: "ℚ", bbR: "ℝ",
  subset: "⊆", subseteq: "⊆", psubset: "⊂",
  simeq: "≃", preceq: "≼", prec: "≺", mapsto: "↦", bot: "⊥", false: "⊥", top: "⊤", times: "×", bigcup: "⋃", int: "∫", integral: "∫", powerset: "𝒫", quot: "⧸", restrict: "↾",
  cup: "∪", union: "∪", cap: "∩", intersection: "∩", setminus: "∖", prod: "∏", sum: "∑", sqrt: "√",
  prime: "′", dprime: "″", tprime: "‴", lsup: "⁽", rsup: "⁾", supplus: "⁺", supminus: "⁻",
  sup0: "⁰", sup1: "¹", sup2: "²", sup3: "³", sup4: "⁴", sup5: "⁵", sup6: "⁶", sup7: "⁷", sup8: "⁸", sup9: "⁹",
  supa: "ᵃ", supb: "ᵇ", supc: "ᶜ", supd: "ᵈ", supe: "ᵉ", supf: "ᶠ", supg: "ᵍ", suph: "ʰ", supi: "ⁱ", supj: "ʲ",
  supk: "ᵏ", supl: "ˡ", supm: "ᵐ", supn: "ⁿ", supo: "ᵒ", supp: "ᵖ", supr: "ʳ", sups: "ˢ", supt: "ᵗ", supu: "ᵘ",
  supv: "ᵛ", supw: "ʷ", supx: "ˣ", supy: "ʸ", supz: "ᶻ",
  llbracket: "⟦", rrbracket: "⟧",
  alpha: "α", beta: "β", gamma: "γ", delta: "δ", epsilon: "ε",
  lambda: "λ", mu: "μ", pi: "π", rho: "ρ", sigma: "σ", tau: "τ",
  phi: "φ", psi: "ψ", omega: "ω",
  Gamma: "Γ", Delta: "Δ", Lambda: "Λ", Pi: "Π", Sigma: "Σ", Omega: "Ω",
  _0: "₀", _1: "₁", _2: "₂", _3: "₃", _4: "₄",
  _5: "₅", _6: "₆", _7: "₇", _8: "₈", _9: "₉",
  _a: "ₐ", _e: "ₑ", _h: "ₕ", _i: "ᵢ", _j: "ⱼ", _k: "ₖ", _l: "ₗ", _m: "ₘ",
  _n: "ₙ", _o: "ₒ", _p: "ₚ", _r: "ᵣ", _s: "ₛ", _t: "ₜ", _x: "ₓ",
});

/** Expand the backslash command immediately before a collapsed cursor. */
export function unicodeCompletionAt(text, cursor) {
  if (!Number.isSafeInteger(cursor) || cursor < 0 || cursor > text.length) return undefined;
  const mathbb = /\\mathbb\{([NZQR])\}$/.exec(text.slice(0, cursor));
  if (mathbb) {
    const symbol = ({ N: "ℕ", Z: "ℤ", Q: "ℚ", R: "ℝ" })[mathbb[1]];
    return { start: cursor - mathbb[0].length, end: cursor, symbol, command: `mathbb{${mathbb[1]}}` };
  }
  const match = /\\([A-Za-z][A-Za-z0-9_]*|_[0-9aehijklmnoprstx]|[<>])$/.exec(text.slice(0, cursor));
  if (!match) return undefined;
  const symbol = unicodeInputMap[match[1]];
  if (!symbol) return undefined;
  return { start: cursor - match[0].length, end: cursor, symbol, command: match[1] };
}

/** Complete a dotted proof/symbol reference from canonical checked names. */
export function qualifiedSymbolCompletions(symbolNames, beforeCursor) {
  const match = /([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*\.([A-Za-z_][\w']*)?)$/.exec(beforeCursor);
  if (!match) return [];
  const typed = match[1];
  const typedParts = typed.split(".");
  const fragment = typedParts.pop() || "";
  const qualifier = typedParts;
  if (!qualifier.length) return [];
  const candidates = new Map();
  for (const canonical of symbolNames) {
    const parts = String(canonical).split(".");
    for (let start = 0; start + qualifier.length < parts.length; start += 1) {
      if (!qualifier.every((part, index) => parts[start + index] === part)) continue;
      const remaining = parts.slice(start + qualifier.length).join(".");
      if (!remaining.startsWith(fragment)) continue;
      const reference = [...qualifier, remaining].join(".");
      candidates.set(reference, {
        label: reference,
        insertText: remaining,
        replaceStart: beforeCursor.length - fragment.length,
        canonical,
      });
    }
  }
  return [...candidates.values()].sort((left, right) =>
    left.label.localeCompare(right.label) || left.canonical.localeCompare(right.canonical));
}

/** Resolve an authored reference without letting a same-named theorem shadow a call. */
/**
 * A successfully checked module is proven even when it is only an import
 * facade. The amber state marks the file's own obligations: a `sorry` in one
 * of its proofs. A proof that is complete but cites an admitted theorem of
 * another file is dependent, not admitted; the admissions it rests on are
 * reported on the theorem itself, not on the file.
 */
export function checkedFileProofState(summary) {
  if (!summary) return undefined;
  return summary.sorries ? "sorry" : "proven";
}
