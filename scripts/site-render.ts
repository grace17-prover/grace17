// Render repository Markdown into site pages with highlighted, runnable code.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore
import { Marked, Renderer } from "marked";
import { highlightGrace17 } from "../workbench/tactics-guide.js";
import { workbenchLink, workbenchSourceLink } from "../workbench/deep-links.js";

export const escape = (s: string) => s.replaceAll("&", "&amp;").replaceAll("<", "&lt;").replaceAll(">", "&gt;").replaceAll('"', "&quot;");
export const modulePage = (file: string) => file.replaceAll("/", ".") + ".html";
const repo = "https://github.com/grace17-prover/grace17/blob/main/";

export interface RenderContext {
  /** Renders the kernel proof of a theorem for a `g17-proof` fence. */
  renderProof?: (file: string, theorem: string, style: string, caption?: string) => string;
  /** Cumulus sources keyed by repository path, e.g. lib/Grace/Cumulus/Set/Zorn.g17. */
  readonly sources: ReadonlyMap<string, string>;
  /** Prefix from the rendered page to the site root, e.g. "../". */
  readonly prefix: string;
  /** Rendered pages for Markdown files outside docs/, keyed by their docs-relative link. */
  readonly external: ReadonlyMap<string, string>;
  /** Example sources keyed by repository path, e.g. examples/TheoremSections.g17. */
  readonly examples?: ReadonlyMap<string, string>;
  /** The field names of the library's structures: `one`, `mul`, `carrier`, which name a field, not a declaration, when written bare. */
  readonly fieldNames?: ReadonlySet<string>;
  /** Declarations by the names inline code may use; see declarationIndex. */
  readonly declarations?: ReadonlyMap<string, DeclarationLink>;
}

export interface DeclarationLink {
  readonly name: string;
  readonly kind: string;
  readonly signature: string;
  /** Module the declaration lives in, shown as the hover card's heading. */
  readonly module: string;
  /** Page of the declaration's source line, relative to cumulus/, or the library search when several share the name. */
  readonly href: string;
  /** Set when several declarations share the name: the link searches the library and the hover lists them. */
  readonly several?: boolean;
  /** The declarations sharing the name, when `several` is set. */
  readonly candidates?: readonly DeclarationLink[];
  /** How many arguments the declaration is applied to, when its header says. */
  readonly arity?: number;
}

/**
 * The number of arguments a declaration takes, read from its header: the
 * names in its binder groups, plus the section variables in scope for a
 * definition inside a section, plus one for a structure's value.
 */
export function declaredArity(kind: string, signature: string, context = ""): number | undefined {
  if (!["def", "defgraph", "defchoose", "defunique", "define", "predicate", "class", "structure"].includes(kind)) return undefined;
  const header = signature.split(/\s:=\s|\n\s*(?:where|\||requires|shows)\b/u)[0]!;
  const binders = [...header.matchAll(/\(([^():]+?)\s*(?::|∈)/gu)].flatMap(match => match[1]!.trim().split(/\s+/));
  const variables = [...context.matchAll(/^variable\s+(.*)$/gmu)]
    .flatMap(match => [...match[1]!.matchAll(/\(([^():]+?)\s*:/gu)].flatMap(group => group[1]!.trim().split(/\s+/)));
  return (kind === "structure" ? 1 : 0) + binders.length + variables.length;
}

/**
 * Index declarations by every name a document might write: the full name,
 * the short name, and every dotted suffix. A key that several declarations
 * share links to the library search for that name, with every candidate in
 * the hover, so an inline link never guesses. A single-word key links only
 * when it names a whole declaration.
 */
export function declarationIndex(records: readonly { name: string; short: string; kind: string; signature: string; module: string; href: string; context?: string }[]): Map<string, DeclarationLink> {
  const index = new Map<string, DeclarationLink[]>();
  const offer = (key: string, link: DeclarationLink) => {
    const existing = index.get(key);
    if (!existing) index.set(key, [link]);
    else if (!existing.some(item => item.href === link.href)) existing.push(link);
  };
  for (const record of records) {
    const link: DeclarationLink = {
      name: record.name, kind: record.kind, signature: record.signature, module: record.module, href: record.href,
      arity: declaredArity(record.kind, record.signature, record.context),
    };
    const parts = record.name.split(".");
    // A bare word links only when it is a declaration's whole short name;
    // the last segment of a dotted name (the `class` of `quotientMap.class`)
    // is not a name anyone writes for it.
    for (let start = 0; start + 1 < parts.length; start++) offer(parts.slice(start).join("."), link);
    // A one-letter bare name in prose code (the x of `x + y`) is a variable,
    // whatever declaration happens to share the letter.
    if ([...record.short].length > 1) offer(record.short, link);
  }
  return new Map([...index].filter(([key]) => !reservedWords.has(key)).map(([key, links]) => [key, links.length === 1 ? links[0]! : severalLink(key, links)]));
}

/** The link for a name several declarations share: the library search, with every candidate in the hover. */
export function severalLink(key: string, links: readonly DeclarationLink[]): DeclarationLink {
  return {
    name: key, kind: "several", module: `${links.length} declarations named ${key}`,
    signature: links.map(item => `${item.signature}\n  -- ${item.module}`).join("\n"),
    href: `?q=${encodeURIComponent(key)}`, several: true, candidates: links,
  };
}

/**
 * The declaration an applied name means: among several sharing the name,
 * the ones taking as many arguments as the code applies it to, so that
 * `Group(G)` is the structure and `IsGroup(A, op, unit, inv)` the predicate.
 */
export function resolveApplied(link: DeclarationLink, rest: string): DeclarationLink {
  if (!link.several || !rest.startsWith("(")) return link;
  let depth = 0, count = 1;
  for (const char of rest) {
    if (char === "(" || char === "[" || char === "{") depth++;
    else if (char === ")" || char === "]" || char === "}") { depth--; if (depth === 0) break; }
    else if (char === "," && depth === 1) count++;
  }
  if (rest.startsWith("()")) count = 0;
  const matching = (link.candidates ?? []).filter(item => item.arity === count);
  return matching.length === 1 ? matching[0]! : matching.length > 1 ? severalLink(link.name, matching) : link;
}

// Words of the language itself; inline code using them is not a reference.
const reservedWords = new Set([
  "module", "import", "open", "export", "namespace", "section", "variable", "hypothesis", "end",
  "def", "define", "defgraph", "defunique", "defchoose", "predicate", "class", "datatype", "structure", "theorem", "lemma",
  "instance", "notation", "tactic", "noncomputable", "transfinite", "foundation", "well-founded",
  "requires", "shows", "proof", "uniqueness", "with", "at", "using", "by", "descends", "over", "ordered", "certified",
  "forall", "exists", "and", "or", "not", "in", "Set", "Class", "Prop", "self",
  "intro", "intros", "exact", "show", "apply", "assumption", "rfl", "reflexivity", "have", "calc", "specialize",
  "constructor", "split", "refine", "left", "right", "witness", "use", "rcases", "cases", "obtain",
  "exfalso", "by_contra", "contradiction", "tauto", "symm", "rw", "rewrite", "simp", "simpa", "unfold", "ext",
  "clear", "rename", "revert", "settle", "typecheck", "synthesize", "cc", "congruence", "compute", "eval",
  "ring", "ring_nf", "linear_combination", "arith", "linarith", "decide", "sorry", "induction", "generalizing",
]);

const unescapeEntities = (s: string) => s.replace(/&#39;/g, "'").replace(/&quot;/g, '"').replace(/&lt;/g, "<").replace(/&gt;/g, ">").replace(/&amp;/g, "&");
export function slugify(text: string): string {
  return unescapeEntities(text.replace(/<[^>]+>/g, "")).normalize("NFKD").toLowerCase().replace(/[^\p{L}\p{N}\s-]/gu, "").trim().replace(/\s+/g, "-");
}

const declarationStart = /^\s*(module|import|namespace|theorem|lemma|def|predicate|class|datatype|structure|notation|eval|section|instance|variable|hypothesis|noncomputable|tactic|open|end|defgraph|defchoose|defunique|define|axiom)\b/m;
export function looksLikeGrace17(text: string): boolean {
  const first = text.split("\n").find(line => line.trim() && !line.trim().startsWith("--")) ?? "";
  return declarationStart.test(first) || /^proof$/m.test(text) || /^\s*\|\s.*=>/m.test(text);
}

export function rewriteHref(href: string, ctx: RenderContext): string {
  if (/^(https?:|mailto:|#)/.test(href)) return href;
  const [path, hash] = href.split("#");
  const suffix = hash ? `#${hash}` : "";
  if (ctx.external.has(path)) return ctx.external.get(path)! + suffix;
  if (path.endsWith(".md")) {
    const name = path.split("/").at(-1)!;
    if (name === "README.md") return (path.startsWith("../") ? ctx.prefix : "index.html") + suffix;
    return name.replace(/\.md$/, ".html") + suffix;
  }
  const lib = /^\.\.\/(lib\/.+\.g17)$/.exec(path);
  if (lib) return `${ctx.prefix}cumulus/modules/${modulePage(lib[1])}${suffix}`;
  const example = /^\.\.\/examples\/([^/]+)\.g17$/.exec(path);
  if (example) return `${ctx.prefix}examples/${example[1]}.html${suffix}`;
  if (path.startsWith("images/")) return path + suffix;
  if (path.startsWith("../")) return repo + path.slice(3) + suffix;
  return `${repo}docs/${path}${suffix}`;
}

function codeFigure(kind: string, label: string, body: string, actions: string): string {
  return `<figure class="code ${kind}"><div class="code-bar"><span class="code-lang">${escape(label)}</span><span class="code-spacer"></span>${actions}<button type="button" class="action copy">Copy</button></div><pre><code>${body}</code></pre></figure>`;
}

export function renderCode(text: string, info: string, ctx: RenderContext): string {
  const [lang = "", ...rest] = info.trim().split(/\s+/);
  const options = Object.fromEntries(rest.map(item => item.split("=") as [string, string]));
  // A `g17-proof` fence embeds the checked natural-deduction derivation of a
  // theorem, rendered at build time from its kernel proof.
  if (lang === "g17-proof") {
    if (!ctx.renderProof) return `<p class="muted">Proof rendering is unavailable here.</p>`;
    return ctx.renderProof(options.file ?? "", options.theorem ?? "", options.style ?? "fitch", text.trim() || undefined);
  }
  const grace = lang === "g17" || lang === "grace17" || ((lang === "" || lang === "text") && looksLikeGrace17(text));
  // Plain text blocks still get the Grace17 token colors: notation sketches
  // and rule schemas read better with their operators and keywords marked.
  if (!grace) return codeFigure("plain", lang || "text", lang === "" || lang === "text" ? highlightGrace17(text) : escape(text), "");
  const workbench = `${ctx.prefix}workbench/`;
  let actions = "";
  const excerpt = options.source;
  if (excerpt && ctx.examples?.has(excerpt)) {
    // An excerpt from an example opens the complete example at the excerpt's
    // line, so the reader lands in a file that checks, with its imports.
    const full = ctx.examples.get(excerpt)!;
    const firstLine = text.split("\n").find(line => line.trim()) ?? "";
    const index = full.split("\n").findIndex(line => line === firstLine);
    const name = excerpt.split("/").at(-1)!;
    actions += `<a class="action run" href="${workbenchSourceLink(name, full.replace(/\n?$/, "\n"), workbench, index >= 0 ? index + 1 : 1)}">Open in Workbench</a>`;
    actions += `<a class="action" href="${ctx.prefix}examples/${name.replace(/\.g17$/, "")}.html">View example</a>`;
  } else if (excerpt && ctx.sources.has(excerpt)) {
    const lines = ctx.sources.get(excerpt)!.split("\n");
    const firstLine = text.split("\n").find(line => line.trim()) ?? "";
    const index = lines.findIndex(line => line === firstLine);
    const line = index >= 0 ? index + 1 : 1;
    actions += `<a class="action run" href="${workbenchLink(excerpt, line, workbench)}">Open in Workbench</a>`;
    actions += `<a class="action" href="${ctx.prefix}cumulus/modules/${modulePage(excerpt)}#L${line}">View source</a>`;
  } else if (!("fragment" in options) && /^\s*module\s+\S+/m.test(text)) {
    const name = /^\s*module\s+(\S+)/m.exec(text)![1].split(".").at(-1)!;
    actions += `<a class="action run" href="${workbenchSourceLink(`${name}.g17`, text.replace(/\n?$/, "\n"), workbench)}">Open in Workbench</a>`;
  } else if (!("fragment" in options) && /^(theorem|lemma|def|predicate|class|datatype|structure|eval|notation|instance|noncomputable)\b/m.test(text)) {
    // A runnable fragment is wrapped in a scratch module. The fence may name
    // the imports it needs (`import=Grace.Cumulus.Real,Grace.Core.List`);
    // `fragment` marks an illustrative block that is not meant to check.
    const imports = (options.import || "Grace.Cumulus.Main").split(",").map(name => `import ${name}`).join("\n");
    const wrapped = `module Scratch\n${imports}\n\n${text.replace(/\n?$/, "\n")}`;
    actions += `<a class="action run" href="${workbenchSourceLink("Scratch.g17", wrapped, workbench)}" title="Opens this fragment inside a scratch module with the imports it needs">Try in Workbench</a>`;
  }
  return codeFigure("g17", "grace17", highlightGrace17(text), actions);
}

export function renderMarkdown(markdown: string, ctx: RenderContext): { html: string; title: string; headings: { depth: number; id: string; text: string }[] } {
  const source = markdown.replace(/<!-- cumulus-source: ([^\n]+) -->\n```(g17|grace17)\n/g, "```$2 source=$1\n");
  const used = new Map<string, number>();
  const headings: { depth: number; id: string; text: string }[] = [];
  let title = "";
  const renderer = new Renderer();
  renderer.heading = function ({ tokens, depth }) {
    const inner = this.parser.parseInline(tokens);
    const plain = inner.replace(/<[^>]+>/g, "");
    if (depth === 1 && !title) { title = plain; return `<h1>${inner}</h1>\n`; }
    let id = slugify(plain) || "section";
    const count = used.get(id) ?? 0; used.set(id, count + 1);
    if (count) id = `${id}-${count}`;
    headings.push({ depth, id, text: plain });
    return `<h${depth} id="${id}">${inner}<a class="anchor" href="#${id}" aria-label="Link to this section">#</a></h${depth}>\n`;
  };
  renderer.code = ({ text, lang }) => renderCode(text, lang ?? "", ctx) + "\n";
  // Inline code naming a library declaration links to its source line and
  // carries its module and signature for the hover card; anything else
  // stays plain.
  renderer.codespan = ({ text }) => {
    const raw = unescapeEntities(text);
    const head = /^[\p{L}_][\p{L}\p{N}_']*(?:\.[\p{L}_][\p{L}\p{N}_']*)*/u.exec(raw)?.[0];
    const found = head && ctx.declarations?.get(head);
    const link = found && resolveApplied(found, raw.slice(head.length));
    // A bare name is a declaration only when it stands alone or is applied:
    // `one : carrier` and `mul : carrier × carrier → carrier` spell a field
    // or a binder, whatever declaration happens to share the word.
    const rest = head ? raw.slice(head.length) : "";
    const bare = head && !head.includes(".") && ((rest !== "" && !rest.startsWith("(")) || ctx.fieldNames?.has(head));
    if (!link || bare) return `<code>${escape(raw)}</code>`;
    return `<code><a class="decl" href="${ctx.prefix}cumulus/${escape(link.href)}" data-module="${escape(link.module)}" data-signature="${escape(link.signature)}"${link.several ? ' data-several=""' : ""}>${escape(head)}</a>${escape(raw.slice(head.length))}</code>`;
  };
  // Illustrations live in docs/images and are copied beside the rendered pages.
  renderer.image = ({ href, text, title }) =>
    `<figure class="illustration"><img src="${escape(rewriteHref(href, ctx))}" alt="${escape(text)}" loading="lazy">${title ? `<figcaption>${escape(title)}</figcaption>` : ""}</figure>`;
  renderer.link = function ({ href, title, tokens }) {
    const inner = this.parser.parseInline(tokens);
    const target = rewriteHref(href, ctx);
    const external = /^https?:/.test(target) ? ' rel="noopener"' : "";
    return `<a href="${escape(target)}"${title ? ` title="${escape(title)}"` : ""}${external}>${inner}</a>`;
  };
  const marked = new Marked({ gfm: true, renderer });
  const html = marked.parse(source) as string;
  return { html, title, headings };
}
