// Static site: documentation, Cumulus browser, examples, and the browser Workbench from one source snapshot.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore
import { createHash } from "node:crypto";
import { cpSync, mkdirSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { scanModule } from "../src/module-source-loader.ts";
import { resolveImportName } from "../src/module-names.ts";
import { execFileSync } from "node:child_process";
import { basename, join, relative } from "node:path";
import { fileURLToPath } from "node:url";
import { scanSearchDeclarations } from "../workbench/library-search.js";
import { highlightGrace17 } from "../workbench/tactics-guide.js";
import { workbenchLink, workbenchSourceLink } from "../workbench/deep-links.js";
import { renderProof } from "./proof-render.ts";
import { theoremRanges } from "../src/workbench.ts";
import { declarationIndex, escape, modulePage, renderMarkdown, rewriteHref, type RenderContext } from "./site-render.ts";

const root = fileURLToPath(new URL("../", import.meta.url));
const out = join(root, "build/site");
const version = JSON.parse(readFileSync(join(root, "package.json"), "utf8")).version;
const walk = (dir: string): string[] => readdirSync(dir, { withFileTypes: true }).flatMap(e => e.isDirectory() ? walk(join(dir, e.name)) : [join(dir, e.name)]);
const sources = walk(join(root, "lib")).filter(p => p.endsWith(".g17")).sort().map(p => ({ file: relative(root, p).replaceAll("\\", "/"), source: readFileSync(p, "utf8") }));
const sourceMap = new Map(sources.map(s => [s.file, s.source]));
const modules = new Map(sources.map(s => [scanModule(s.source, s.file).name, modulePage(s.file)]));
// A content hash on the stylesheet and script links, so a deploy is never
// read through a browser's cached copy of the previous one.
const assetVersion = createHash("sha256").update(readFileSync(join(root, "site/site.css"))).update(readFileSync(join(root, "site/site.js"))).digest("hex").slice(0, 10);
const wordmark = readFileSync(join(root, "site/wordmark.svg"), "utf8").replace("<svg ", '<svg aria-hidden="true" focusable="false" ');
const analytics = readFileSync(join(root, "site/analytics.html"), "utf8");

// Markdown outside docs/ that documentation links to, rendered into docs/ under these names.
const externalDocs = new Map<string, { source: string; page: string }>([
  ["../CONTRIBUTING.md", { source: "CONTRIBUTING.md", page: "contributing.html" }],
  ["../AGENTS.md", { source: "AGENTS.md", page: "coding-agents.html" }],
  ["../checkers/ocaml/README.md", { source: "checkers/ocaml/README.md", page: "ocaml-checkers.html" }],
  ["../checkers/README.md", { source: "checkers/README.md", page: "checkers.html" }],
]);
const external = new Map([...externalDocs].map(([link, { page }]) => [link, page]));
const exampleSources = new Map(walk(join(root, "examples")).filter(p => p.endsWith(".g17")).map(p => [relative(root, p).replaceAll("\\", "/"), readFileSync(p, "utf8")] as const));
// Declarations are scanned before any page renders so inline code in the
// documentation can link to them.
const scanned = new Map(sources.map(({ file, source }) => [file, scanSearchDeclarations(file, source)] as const));
const records: any[] = [];
for (const { file } of sources) {
  records.push(...scanned.get(file)!.map(d => ({ ...d, href: `modules/${modulePage(file)}#L${d.line}`, run: workbenchLink(file, d.line, "../workbench/") })));
}
const declarations = declarationIndex(records);
// The field names of every structure in the library; written bare in prose
// they name the field, not whatever declaration shares the word.
const fieldNames = new Set(sources.flatMap(({ source }) =>
  [...source.matchAll(/^structure\s[^\n]*\n((?:\s*\|[^\n]*\n)+)/gm)].flatMap(match =>
    [...match[1]!.matchAll(/^\s*\|\s*\(?([^:()]+?)\s*:/gm)].flatMap(group => group[1]!.trim().split(/\s+/)))));
const docsContext: RenderContext = { sources: sourceMap, prefix: "../", external, examples: exampleSources, declarations, fieldNames, renderProof };

const navItems = [["docs/introduction.html", "Introduction"], ["docs/", "Docs"], ["cumulus/", "Cumulus"], ["workbench/", "Workbench"], ["workbench/game.html", "Game"], ["install.html", "Install"], ["docs/community.html", "Community"], ["https://github.com/grace17-prover/grace17", "GitHub"]];
// Last commit date of each tracked file, so a page's footer can say when its
// source was last edited. Uncommitted edits count as today.
const editDates = new Map<string, string>();
{
  // The root commit is the squashed release and carries no edit history of
  // its own, so a file it alone touches is dated by the build instead.
  const rootCommit = execFileSync("git", ["rev-list", "--max-parents=0", "HEAD"], { cwd: root, encoding: "utf8" }).trim().split("\n")[0] ?? "";
  let date = "";
  let skipping = false;
  for (const line of execFileSync("git", ["log", "--format=%H %cs", "--name-only"], { cwd: root, encoding: "utf8", maxBuffer: 1 << 28 }).split("\n")) {
    const commit = /^([0-9a-f]{40}) (\d{4}-\d{2}-\d{2})$/.exec(line);
    if (commit) { date = commit[2]!; skipping = commit[1] === rootCommit; }
    else if (line && !skipping && !editDates.has(line)) editDates.set(line, date);
  }
  for (const line of execFileSync("git", ["status", "--porcelain"], { cwd: root, encoding: "utf8" }).split("\n")) {
    const path = line.slice(3).split(" -> ").at(-1);
    if (path) editDates.set(path, new Date().toLocaleDateString("en-CA"));
  }
}
// The build date in the local calendar, as the commit dates are.
const today = new Date().toLocaleDateString("en-CA");
function editedOn(...paths: string[]): string {
  const dates = paths.map(path => editDates.get(path) ?? today);
  const latest = dates.sort().at(-1)!;
  const [year, month, day] = latest.split("-").map(Number);
  return new Date(Date.UTC(year, month - 1, day)).toLocaleDateString("en-GB", { day: "numeric", month: "long", year: "numeric", timeZone: "UTC" });
}

function page(title: string, body: string, prefix = "./", options: { sidebar?: string; wide?: boolean; description?: string; edited?: string } = {}): string {
  const nav = navItems.map(([href, label]) => `<a href="${href.startsWith("http") ? href : prefix + href}"${href.startsWith("http") ? ' rel="noopener"' : ""}>${label}</a>`).join("");
  const description = options.description ?? "Grace17 is an open source proof assistant for mathematics based on set theory.";
  return `<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>${escape(title)} · Grace17</title><meta name="description" content="${escape(description)}"><link rel="icon" type="image/svg+xml" href="${prefix}grace-icon.svg"><link rel="icon" type="image/png" sizes="32x32" href="${prefix}favicon-32.png"><link rel="apple-touch-icon" href="${prefix}favicon-180.png"><link rel="preconnect" href="https://fonts.googleapis.com"><link rel="preconnect" href="https://fonts.gstatic.com" crossorigin><link href="https://fonts.googleapis.com/css2?family=JetBrains+Mono:wght@400;500&display=swap" rel="stylesheet"><link rel="stylesheet" href="${prefix}site.css?v=${assetVersion}"></head><body>
<header class="site-header"><a class="brand" href="${prefix}" aria-label="Grace17 home">${wordmark}</a><nav class="site-nav" aria-label="Site">${nav}</nav></header>
<div class="layout${options.sidebar ? " with-sidebar" : ""}">${options.sidebar ?? ""}<main class="doc${options.wide ? " wide" : ""}">${body}</main></div>
<footer class="site-footer"><span>Grace17 · an open source proof assistant for mathematics based on set theory</span><span>Last edited ${options.edited ?? editedOn("scripts/build-site.ts")} by Grant Olney Passmore · Apache License 2.0</span></footer>
<script type="module" src="${prefix}site.js?v=${assetVersion}"></script>
${analytics}</body></html>`;
}

// Generated directories start empty, so a page that no longer exists does
// not survive from an earlier build.
for (const dir of ["cumulus/modules", "docs", "examples"]) rmSync(join(out, dir), { recursive: true, force: true });
mkdirSync(join(out, "cumulus/modules"), { recursive: true });
mkdirSync(join(out, "docs"), { recursive: true });
cpSync(join(root, "docs/images"), join(out, "docs/images"), { recursive: true });
mkdirSync(join(out, "examples"), { recursive: true });
cpSync(join(root, "workbench"), join(out, "workbench"), { recursive: true });
cpSync(join(root, "lib"), join(out, "sources/lib"), { recursive: true });
cpSync(join(root, "site"), out, { recursive: true });
writeFileSync(join(out, ".nojekyll"), "");

// Documentation sidebar from docs/README.md, with the current page marked by site.js.
const docsIndex = readFileSync(join(root, "docs/README.md"), "utf8");
// `toDocs` and `toRoot` are the paths from the page's directory to docs/ and
// to the site root, so the same sidebar can sit beside pages outside docs/.
function sidebar(toDocs = "", toRoot = "../"): string {
  const fix = (href: string) => href.startsWith("http") ? href : href.startsWith("../") ? toRoot + href.slice(3) : toDocs + href;
  let html = `<aside class="sidebar"><details open><summary>Documentation</summary><nav aria-label="Documentation"><h3>Start here</h3><ul><li><a href="${toDocs}introduction.html">Introduction</a></li><li><a href="${toRoot}install.html">Install</a></li><li><a href="${toRoot}workbench/game.html">The Set Theory Game</a></li><li><a href="${toDocs}contributing.html">Contributing</a></li></ul>`;
  let inGroup = false;
  for (const line of docsIndex.split("\n")) {
    const group = /^## (.+)/.exec(line);
    if (group) { html += `</ul><h3>${escape(group[1])}</h3><ul>`; inGroup = true; continue; }
    if (!inGroup) continue;
    for (const link of line.matchAll(/\[([^\]]+)\]\(([^)]+)\)/g)) {
      const label = link[1].charAt(0).toUpperCase() + link[1].slice(1);
      html += `<li><a href="${escape(fix(rewriteHref(link[2], docsContext)))}">${escape(label)}</a></li>`;
    }
  }
  // Restore the sidebar's scroll offset before the first paint; site.js keeps it.
  const restore = '<script>(function(){try{var d=document.querySelector(".sidebar details");var s=sessionStorage.getItem("grace17.sidebarScroll");if(d&&s!==null)d.scrollTop=Number(s);}catch(e){}})();</script>';
  return html + "</ul></nav></details></aside>" + restore;
}
const docsSidebar = sidebar();
const rootSidebar = sidebar("docs/", "./");
const examplesSidebar = sidebar("../docs/", "../");

// The tactic reference folds each tactic into its own collapsible section, so
// the page reads as a navigable list: open a tactic to see its description,
// example, and rule schema. Links to a tactic open it (site.js).
function foldTacticSections(html: string): string {
  return html.split(/(?=<h[23] id=")/).map(part => {
    const match = /^<h3 id="([^"]+)">([\s\S]*?)<\/h3>\n?([\s\S]*)$/.exec(part);
    if (!match) return part;
    const inner = match[2]!.replace(/<a class="anchor"[\s\S]*?<\/a>/, "");
    return `<details class="tactic" id="${match[1]}"><summary><h3>${inner}</h3><a class="anchor" href="#${match[1]}" aria-label="Link to this tactic">#</a></summary><div class="tactic-body">${match[3]}</div></details>\n`;
  }).join("");
}

function renderDoc(markdown: string, outName: string, fallbackTitle: string, source: string): string {
  const rendered = renderMarkdown(markdown, docsContext);
  const html = outName === "tactics.html" ? foldTacticSections(rendered.html) : rendered.html;
  const { title } = rendered;
  const name = title || fallbackTitle;
  const description = /^(?!#)([^\n]+)\n/m.exec(markdown.replace(/^# .*\n+/, ""))?.[1].replace(/[*_`\[\]]/g, "");
  writeFileSync(join(out, "docs", outName), page(name, html, "../", { sidebar: docsSidebar, description, edited: editedOn(source) }));
  return name;
}
let docCount = 0;
for (const file of readdirSync(join(root, "docs")).filter(f => f.endsWith(".md")).sort()) {
  const outName = file === "README.md" ? "index.html" : file.replace(/\.md$/, ".html");
  renderDoc(readFileSync(join(root, "docs", file), "utf8"), outName, file === "README.md" ? "Documentation" : basename(file, ".md"), `docs/${file}`);
  docCount++;
}
for (const { source, page: outName } of externalDocs.values()) { renderDoc(readFileSync(join(root, source), "utf8"), outName, outName, source); docCount++; }
// Former page names keep working as redirects to their current pages.
const movedDocs: readonly [string, string][] = [["scoped-ring-notation.html", "algebra.html#ring-scopes-over-separate-pieces"], ["scoped-structures.html", "algebra.html#ring-scopes-over-separate-pieces"]];
for (const [from, to] of movedDocs) {
  writeFileSync(join(out, "docs", from), `<!doctype html><meta charset="utf-8"><meta http-equiv="refresh" content="0; url=./${to}"><link rel="canonical" href="./${to}"><title>Moved</title><p>This page moved to <a href="./${to}">${to}</a>.</p>\n`);
}

// The library's subject areas, used by the module index and by breadcrumbs.
const areas: readonly { id: string; title: string; blurb: string; prefixes: readonly string[] }[] = [
  { id: "kernel", title: "Kernel and bootstrap", blurb: "The axioms, ordered pairs, the natural numbers, lists and trees, and the syntax everything else is written in.", prefixes: ["lib/Grace/Kernel", "lib/Grace/Bootstrap", "lib/Grace/Core"] },
  { id: "sets", title: "Sets, relations, and functions", blurb: "Set algebra, power sets and families, relations and their algebra, functions, images, orders, well-orders, choice, Zorn's lemma, and the well-ordering theorem.", prefixes: ["lib/Grace/Cumulus/Set", "lib/Grace/Cumulus/Relation", "lib/Grace/Cumulus/Function", "lib/Grace/Cumulus/Order"] },
  { id: "ordinals", title: "Ordinals and cardinals", blurb: "Transfinite recursion, ordinal arithmetic, order types, Hartogs' theorem, finiteness and counting, countability, dominance, and infinite cardinal arithmetic.", prefixes: ["lib/Grace/Cumulus/Ordinal", "lib/Grace/Cumulus/Set/Ordinal", "lib/Grace/Cumulus/Set/Hierarchy", "lib/Grace/Cumulus/Cardinal"] },
  { id: "numbers", title: "Natural numbers, integers, and rationals", blurb: "Arithmetic and order on ℕ with its everyday lemmas, the construction of ℤ with its order, signs, parity, and absolute value, the construction of ℚ, division, and the least-number principle.", prefixes: ["lib/Grace/Cumulus/Nat", "lib/Grace/Cumulus/Int", "lib/Grace/Cumulus/Rat"] },
  { id: "analysis", title: "Real analysis", blurb: "Sequences, continuity, the intermediate and extreme value theorems, differentiation, Riemann integration, and the fundamental theorem of calculus.", prefixes: ["lib/Grace/Cumulus/Real/Analysis"] },
  { id: "reals", title: "Real numbers", blurb: "The Dedekind reals: field and order structure, absolute value, the metric, square roots, uncountability, and the embedding of the rationals.", prefixes: ["lib/Grace/Cumulus/Real"] },
  { id: "complex", title: "Complex numbers", blurb: "The complex field, continuity and compactness in the plane, and the fundamental theorem of algebra.", prefixes: ["lib/Grace/Cumulus/Complex"] },
  { id: "groups", title: "Groups", blurb: "Bundled groups with a * b and a⁻¹, subgroups, cosets and Lagrange's theorem, homomorphisms f : G →* H, kernels, normal subgroups and quotients, the first isomorphism theorem, products, cyclic subgroups and element orders, and centers.", prefixes: ["lib/Grace/Cumulus/Algebra/Group"] },
  { id: "rings", title: "Rings and ideals", blurb: "Rings, ideals, quotients, prime and maximal ideals, determinants over rings, and the isomorphism theorems.", prefixes: ["lib/Grace/Cumulus/Algebra/Ring"] },
  { id: "fields", title: "Fields", blurb: "Fields and ordered fields, localisation, and integral descent.", prefixes: ["lib/Grace/Cumulus/Algebra/Field", "lib/Grace/Cumulus/Algebra/OrderedField"] },
  { id: "polynomials", title: "Polynomials", blurb: "Polynomial rings, Horner evaluation, roots and factors, variables, and the Nullstellensatz.", prefixes: ["lib/Grace/Cumulus/Algebra/Polynomial"] },
  { id: "algebra", title: "Modules and coefficients", blurb: "Coefficient maps, indexed lists, spans and annihilators, finite module towers, and integral extensions.", prefixes: ["lib/Grace/Cumulus/Algebra"] },
  { id: "linear", title: "Linear algebra", blurb: "Vectors, matrices, determinants, and spans.", prefixes: ["lib/Grace/Cumulus/LinearAlgebra"] },
  { id: "number-theory", title: "Number theory", blurb: "Divisibility, Bézout, the Euclidean algorithm, prime factorisation, modular arithmetic, the Chinese remainder theorem, Fermat, Euler, and Wilson.", prefixes: ["lib/Grace/Cumulus/NumberTheory"] },
  { id: "combinatorics", title: "Combinatorics", blurb: "Inclusion–exclusion, the pigeonhole principle, binomial identities, counting functions, injections, and permutations, Fibonacci, Lucas, Catalan, Stirling, and Bell numbers, the infinite Ramsey theorem, and Möbius inversion.", prefixes: ["lib/Grace/Cumulus/Combinatorics"] },
  { id: "probability", title: "Probability", blurb: "Finite probability spaces, events, uniform distributions, conditional probability and Bayes, independence, random variables, expectation and variance, and the Markov and Chebyshev inequalities.", prefixes: ["lib/Grace/Cumulus/Probability"] },
  { id: "geometry", title: "Geometry", blurb: "Coordinate geometry over the reals: distances, triangles, and the classical theorems.", prefixes: ["lib/Grace/Cumulus/Geometry"] },
  { id: "graphs", title: "Graph theory", blurb: "Graphs, walks, Eulerian trails, and shortest paths.", prefixes: ["lib/Grace/Cumulus/GraphTheory"] },
  { id: "lists", title: "Lists", blurb: "Lists as finite sequences: indexing, concatenation, reversal, take and drop, filtering, counts and permutations, sums, prefixes, sorting, and the bridge to functions on a natural number.", prefixes: ["lib/Grace/Cumulus/List"] },
  { id: "topology", title: "Topology", blurb: "Topological spaces, continuous maps, compactness, subspaces, separation, the standard topology on the line, and Heine–Borel.", prefixes: ["lib/Grace/Cumulus/Topology"] },
  { id: "metric", title: "Metric spaces", blurb: "Metrics and balls, the metric topology, closed sets and closure, ε–δ continuity, Lipschitz maps and isometries, Cauchy sequences and completeness, boundedness, and the real line, discrete, subspace, and product metrics.", prefixes: ["lib/Grace/Cumulus/Metric"] },
  { id: "fixed-points", title: "Fixed point theorems", blurb: "Knaster–Tarski on subsets, the fixed point theorem on a closed interval, Kuhn's lemma, and Brouwer's theorem for the cube and for products of simplices.", prefixes: ["lib/Grace/Cumulus/FixedPoint"] },
  { id: "game-theory", title: "Game theory", blurb: "Mixed strategy profiles on products of simplices, expected payoffs, Nash's map, and the existence of Nash equilibria.", prefixes: ["lib/Grace/Cumulus/GameTheory"] },
  { id: "lattices", title: "Lattices", blurb: "Ordered sets bundled as one set P with a ⊑ b, a ⊔ b, a ⊓ b, bot(P), top(P), and sSup(P)(S) read off the hypothesis: suprema and infima, lattices and their laws, bounded, complete, distributive, modular, and Boolean lattices, the powerset lattice, monotone maps and Galois connections, Knaster–Tarski on complete lattices, homomorphisms, sublattices, ideals, and filters.", prefixes: ["lib/Grace/Cumulus/Lattice"] },
  { id: "categories", title: "Category theory", blurb: "Small categories as bundled sets with hom-typed morphisms, isomorphisms, monomorphisms and epimorphisms, terminal and initial objects, functors F : C ⥤ D, natural transformations, opposite categories, products, example categories including the category of sets below a universe, hom functors, and the Yoneda lemma.", prefixes: ["lib/Grace/Cumulus/Category"] },
  { id: "roots", title: "Library roots", blurb: "The modules that import whole areas, so one import brings a subject in.", prefixes: ["lib/Grace/Cumulus"] },
];
// The longest matching prefix wins, so Set/Ordinal lands with the ordinals
// rather than with the sets.
const areaOf = (file: string): string => {
  let best: { id: string; length: number } | undefined;
  for (const area of areas) {
    for (const prefix of area.prefixes) {
      if ((file === `${prefix}.g17` || file.startsWith(`${prefix}/`)) && (!best || prefix.length > best.length)) best = { id: area.id, length: prefix.length };
    }
  }
  return best?.id ?? "roots";
};

// Cumulus browser: one page per module, plus a searchable index.
for (const { file, source } of sources) {
  const declarations = scanned.get(file)!;
  // Imports are written relative to the importing module; each one links to
  // the page of the module it resolves to, as the loader resolves it.
  const current = scanModule(source, file).name;
  const imports = [...source.matchAll(/^import\s+(\S+)/gm)].map(m => {
    const resolved = resolveImportName(current, m[1], name => modules.has(name));
    return resolved ? `<a href="${modules.get(resolved)}">${escape(m[1])}</a>` : escape(m[1]);
  });
  // A derivation link lands on the last line of the proof, where the
  // Workbench has the complete kernel proof to show.
  const sourceLines = source.split("\n");
  const proofEnd = new Map(theoremRanges(source).map(range => {
    let end = range.lineEnd;
    while (end > range.lineStart && /^\s*(--.*)?$/.test(sourceLines[end - 1] ?? "")) end -= 1;
    return [range.lineStart, end];
  }));
  const toc = declarations.map(d => `<li><a href="#L${d.line}">${escape(d.short)}</a> <small>${escape(d.kind)}</small>${d.kind === "theorem" || d.kind === "lemma" || d.kind === "instance" ? ` <a class="proof-link" href="${workbenchLink(file, proofEnd.get(d.line) ?? d.line, "../../workbench/", "kernel")}" title="Open the checked natural-deduction derivation of ${escape(d.short)} in the Workbench">derivation</a>` : ""}</li>`).join("");
  const lines = source.split("\n").map((line, i) => `<span class="source-line" id="L${i + 1}"><a class="line-number" href="#L${i + 1}" aria-label="Line ${i + 1}">${i + 1}</a>${highlightGrace17(line)}</span>`).join("");
  const title = file.replace(/^lib\//, "");
  // Breadcrumbs lead back up the hierarchy: the library, the subject area,
  // every enclosing namespace that is itself a module, then this module.
  const moduleName = scanModule(source, file).name ?? title;
  const area = areas.find(a => a.id === areaOf(file));
  const segments = moduleName.split(".");
  const ancestors = segments.slice(2, -1).map((_, index) => segments.slice(0, index + 3).join(".")).filter(name => name !== moduleName && modules.has(name));
  const crumbs = [`<a href="../../">Grace17</a>`, `<a href="../">Cumulus</a>`, ...(area ? [`<a href="../#${area.id}">${escape(area.title)}</a>`] : []), ...ancestors.map(name => `<a href="${modules.get(name)}">${escape(name.split(".").at(-1)!)}</a>`), `<span aria-current="page">${escape(segments.at(-1)!)}</span>`];
  const breadcrumbs = `<nav class="breadcrumbs" aria-label="Breadcrumb">${crumbs.join('<span class="sep" aria-hidden="true">›</span>')}</nav>`;
  const body = `${breadcrumbs}<h1>${escape(title)}</h1><p class="source-meta"><a class="action run" href="${workbenchLink(file, 1, "../../workbench/")}">Open in Workbench</a> <a class="action" href="../../sources/${file}" download>Download source</a></p><h2 id="imports">Imports</h2><p class="imports">${imports.join(" · ") || "None"}</p><h2 id="declarations">Declarations</h2><ul class="declarations">${toc}</ul><h2 id="source">Source</h2><pre class="source"><code>${lines}</code></pre>`;
  writeFileSync(join(out, "cumulus/modules", modulePage(file)), page(title, body, "../../", { wide: true, description: `Source of the Cumulus module ${title}.`, edited: editedOn(file) }));
}
writeFileSync(join(out, "cumulus/declarations.json"), JSON.stringify(records));
// The module index groups the library by subject. Each area is matched by
// its path under lib/; the first matching area wins, so narrower prefixes
// come first.
const grouped = new Map<string, typeof sources>(areas.map(a => [a.id, []]));
for (const entry of sources) grouped.get(areaOf(entry.file))!.push(entry);
const sectionNav = areas.filter(a => grouped.get(a.id)!.length > 0).map(a => `<li><a href="#${a.id}">${escape(a.title)}</a> <small>${grouped.get(a.id)!.length}</small></li>`).join("");
const sections = areas.filter(a => grouped.get(a.id)!.length > 0).map(a => {
  const entries = grouped.get(a.id)!;
  const declarationCount = entries.reduce((sum, { file }) => sum + scanned.get(file)!.length, 0);
  const items = entries.map(({ file }) => {
    const label = file.replace(/^lib\/Grace\/(Cumulus\/)?/, "").replace(/\.g17$/, "");
    return `<li><a href="modules/${modulePage(file)}">${escape(label)}</a> <small>${scanned.get(file)!.length}</small></li>`;
  }).join("");
  return `<section class="module-section" id="${a.id}"><h2>${escape(a.title)} <small>${entries.length} modules · ${declarationCount.toLocaleString()} declarations</small></h2><p class="muted">${escape(a.blurb)}</p><ul class="module-tree">${items}</ul></section>`;
}).join("");
writeFileSync(join(out, "cumulus/index.html"), page("Cumulus", `<h1>Explore Cumulus</h1><p class="lede">Cumulus is the Grace17 mathematics library. Search names and statements, follow imports, and open any declaration in the browser proof assistant.</p><label for="search" class="muted">Search names and statements</label><input id="search" type="search" placeholder="Try Zorn, Nullstellensatz, or derivative" autocomplete="off"><p id="search-status" role="status" class="muted">Loading declaration index…</p><div id="results"></div><h2 id="areas">Modules by area</h2><ul class="area-nav">${sectionNav}</ul>${sections}<script type="module" src="./search.js"></script>`, "../", { wide: true, description: "Browse and search Cumulus, the Grace17 mathematics library, by area." }));

// Examples: every checked example file, highlighted, with a one-click Workbench link.
const examples = readdirSync(join(root, "examples")).filter(f => f.endsWith(".g17")).sort();
for (const file of examples) {
  const source = readFileSync(join(root, "examples", file), "utf8");
  const name = basename(file, ".g17");
  const summary = (/^--\s*(.+)/.exec(source)?.[1] ?? "").replace(/\.$/, "");
  const lines = source.split("\n").map((line, i) => `<span class="source-line" id="L${i + 1}"><a class="line-number" href="#L${i + 1}" aria-label="Line ${i + 1}">${i + 1}</a>${highlightGrace17(line)}</span>`).join("");
  const body = `<h1>${escape(name)}</h1><p class="lede">${escape(summary)}</p><p class="source-meta"><a class="action run" href="${workbenchSourceLink(file, source, "../workbench/")}">Open in Workbench</a> <a class="action" href="https://github.com/grace17-prover/grace17/blob/main/examples/${file}" rel="noopener">View on GitHub</a></p><pre class="source"><code>${lines}</code></pre>`;
  writeFileSync(join(out, "examples", `${name}.html`), page(`${name} example`, body, "../", { sidebar: examplesSidebar, wide: true, edited: editedOn(`examples/${name}.g17`), description: summary || `The ${name} example.` }));
}
// The examples index page is retired; each example page remains reachable from the docs.

// Install page.
const install = `# Run Grace17 locally

You can start immediately in the [browser Workbench](../workbench/): the full proof assistant runs in your browser, and nothing is sent to a server. For command-line use and for developing your own libraries, install it locally.

## Requirements

- [Node.js](https://nodejs.org) 24 or later.
- Python 3, only for the independent Python checker.
- OCaml 5 with Zarith, only for the independent OCaml checker.

## Install

\`\`\`sh
git clone https://github.com/grace17-prover/grace17.git
cd grace17
npm ci
npm run workbench
\`\`\`

Open the local address the last command prints. Grace17 is not yet published as an npm package, though I hope to do that soon.

## With Claude Code

If you'd like to work with Grace17 through an AI agent, it is easy with Claude Code. Clone the repository as above, then install the Grace17 skill from inside Claude Code:

\`\`\`sh
/plugin install grace17 --marketplace grace17-prover/grace17
\`\`\`

The skill teaches the agent the write–check loop, the module conventions, and the pitfalls that cost the most time; inside a clone of the repository it loads automatically. The [guide for AI agents](agents.md) describes the JSON interfaces the agent then uses to check proofs and read goal states.

## Check a file from the command line

\`\`\`sh
node bin/g17.ts check --foundation ZF --module-root lib examples/Introduction.g17
\`\`\`

Add \`--json\` for structured output. To see exactly which axioms a theorem depends on:

\`\`\`sh
node bin/g17.ts axiom-audit --foundation ZF --module-root lib examples/Introduction.g17 --theorem Introduction.difference_of_squares
\`\`\`

## Next steps

- Read the [introduction](introduction.md) for a tour from first proofs to the Nullstellensatz.
- Browse [Cumulus](../cumulus/), the mathematics library; every module opens in the Workbench.
- See [building your own library](external-libraries.md) to develop mathematics outside the Grace17 checkout.
- See [contributing](../CONTRIBUTING.md) if you would like to help.
`;
{
  const { html } = renderMarkdown(install, { sources: sourceMap, prefix: "./", external: new Map([["../CONTRIBUTING.md", "docs/contributing.html"]]) });
  writeFileSync(join(out, "install.html"), page("Install", html.replaceAll('href="introduction.html"', 'href="docs/introduction.html"').replaceAll('href="external-libraries.html"', 'href="docs/external-libraries.html"').replaceAll('href="agents.html"', 'href="docs/agents.html"').replaceAll('href="../examples/"', 'href="examples/"').replaceAll('href="../cumulus/"', 'href="cumulus/"').replaceAll('href="../workbench/"', 'href="workbench/"'), "./", { sidebar: rootSidebar, description: "Install Grace17 locally or run it in the browser." }));
}

// Live proof page.
const hierarchy = sources.find(s => s.file === "lib/Grace/Cumulus/Set/Hierarchy.g17")!;
const hierarchyLine = scanSearchDeclarations(hierarchy.file, hierarchy.source).find(d => d.short === "V")!.line;
const demo = workbenchLink(hierarchy.file, hierarchyLine, "./workbench/");
writeFileSync(join(out, "try.html"), page("Explore a proof", `<h1>The cumulative hierarchy</h1><p class="lede">Edit and check the actual Cumulus source below. Proof execution happens in your browser. <a href="${demo}">Open the full Workbench</a>.</p><iframe title="Grace17 cumulative hierarchy proof Workbench" src="${demo}" loading="lazy" class="proof-frame"></iframe>`, "./", { wide: true }));

writeFileSync(join(out, "site-build.json"), JSON.stringify({ version, modules: sources.length, declarations: records.length, docs: docCount, examples: examples.length }, null, 2));
console.log(`Built static site: ${sources.length} modules, ${records.length} declarations, ${docCount} documentation pages, ${examples.length} examples → ${out}`);
