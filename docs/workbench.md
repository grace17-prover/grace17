# Grace17 browser Workbench

The web Workbench is the whole proof assistant. Parsing, elaboration, tactic
execution, kernel checking, evaluation, and standard-library loading run
inside a module Web Worker in your browser. Checking a proof sends nothing to
a server.

**The Workbench is live at [https://grace17.org/workbench/](https://grace17.org/workbench/).** Every
module of Cumulus opens there, and every theorem on the documentation pages
has a button that opens it there at its line.

## Build and run

```text
npm run build:browser
npm run workbench
```

The first command transforms the TypeScript kernel into browser ESM, embeds the
current `.g17` Core and Cumulus module sources from the `lib/` module root,
and vendors the Monaco version pinned in `package-lock.json`. Monaco and its
worker assets are self-hosted, so editing does not depend on a CDN. The second
command rebuilds those assets and serves the Workbench at
`http://127.0.0.1:1717`.

For `grace17.org`, run `npm run build:site` to generate the landing page,
Cumulus browser, and Workbench together in `build/site/`. See
[website integration](website.md). The Workbench also works as a
standalone static HTTPS site or beneath a path such as `/workbench/`. The Node `/api/check` and
`/api/run` endpoints remain useful for compatibility and testing, but the web
UI does not call them.

## The Set Theory Game

`game.html` beside the Workbench is a guided introduction: ten worlds of
levels, each a theorem with a hole, checked by the same kernel in the same
worker. Finite sets world works with concrete sets, first through `decide` and
then by hand from the lemmas that define union, intersection, difference, and
the powerset, with `decide` switched off; Logic world gives each connective its
introduction and elimination tactic; Membership world teaches `intros`, `with`,
`ext`, and `simp` on arbitrary sets; Paradox world proves that no set is a
member of itself, that there is no set of all sets, and Russell's argument;
Computation world shows definitions running under `compute` and the step to
induction; Function world works with `f : A → B` and `synthesize`; Algebra world
proves the first lemmas of group theory for an arbitrary group; Finite, Ordinal,
and Infinite worlds apply Cumulus results up to ω as a limit ordinal, the
Burali-Forti paradox, Schröder–Bernstein, Cantor's theorem, and the
uncountability of ℝ. Progress and drafts stay in the
browser's local storage, and every level opens as a file in the full Workbench.
The levels live in `workbench/game-levels.js`; `tests/set-theory-game.test.ts`
checks each starter and solution and that solutions respect a level's
switched-off tactics.

## Local projects

On browsers implementing the File System Access API, **Open Folder** grants the
Workbench access only to the directory you select. Grace17 reads its
`.g17` files into project scope and shows them in a collapsible tree; only a
selected file becomes an editor tab. **Save** or Cmd/Ctrl-S writes the active
file through its authorized handle. The editor/proof divider is resizable and
remembers its position. Other browsers retain multi-file import and
download-based saving. Recovery snapshots live in local storage; native file
handles are not serialized there.

Editor notation resolves to its underlying declaration on hover and
Command/Ctrl-click. The same semantic links are present in rendered goal states,
so displayed predicates, functions, and notation lead back to their definitions.

Opening **Kernel proof** linearizes the checked proof DAG as a Fitch-style
natural-deduction derivation. Each premise occurs before the conclusion that
cites it, assumption contexts form visible subproof rails, and introduction or
case rules cite complete line ranges. Select a proof line to see the conventional
inference-rule fraction, including discharged assumptions, exact premises,
conclusion, and any checked freshness side conditions; its full kernel arguments
follow below. Open assumptions are not repeated as a separate Γ list: in this
Fitch presentation, assumption lines and their vertical scope rails are the
context. The derivation scrolls independently. Drag the slim
handle above the drawer, or use Up/Down while it is focused, to give the
derivation as much vertical space as needed; the chosen height is remembered
locally.

The PWA service worker caches the application shell immediately and caches the
editor, kernel, and library modules as they are first used. After one successful check,
the same Workbench can reopen without a network connection.

## Soundness boundary

The browser build changes how the code is delivered and nothing else.
`src/hash.ts` gives the same synchronous SHA-256 result in Node and browsers,
and the generated browser kernel must produce the same authenticated
environment digest for a module importing `Grace.Core` as the native
Workbench does.

The browser, desktop shell, editor, and AI agents are untrusted proof
producers. A theorem counts as proved when the Grace17 kernel accepts its
certificate, and optionally when an independent external checker has replayed
it.
