# Website, Cumulus browser, and embedded Workbench

The static site is built from the same source snapshot as the proof assistant:

```sh
npm ci
npm run build:site
npm run check:site
```

The output is `build/site/`. For local review, `npm run serve:site` serves it
at `http://127.0.0.1:8017/` with `cache-control: no-store`, so a rebuilt
bundle is what the browser runs after a reload; a generic static server sends
only a modification date, which browsers cache heuristically, and a hard
reload does not refetch the module scripts the Workbench's worker imports.
The Workbench requires HTTP(S); opening `index.html` as a `file:` URL will
not load its module workers correctly.

## Visitor paths

- `index.html`: the grace17.org landing page, with links to everything below.
- `docs/`: every Markdown document in `docs/`, plus `CONTRIBUTING.md`,
  `AGENTS.md`, and the checker guides, rendered with the site design,
  a sidebar generated from `docs/README.md`, highlighted code, and heading
  anchors. Grace17 code blocks carry an "Open in Workbench" button; sh, json,
  and other blocks carry a copy button.
- `cumulus/`: search declaration names and statements (a `?q=` parameter
  makes a search shareable), browse source modules with highlighting, follow
  imports, use line permalinks, or download a source file.
- `examples/`: every `examples/*.g17` file, highlighted, each opening in the
  Workbench with one click.
- `workbench/`: the full browser editor, local proof worker, search, hover and
  definition navigation, goal states, and axiom audit.
- `try.html`: a page embedding the Workbench on the cumulative hierarchy.
- `install.html`: clone, Node.js 24+, `npm ci`, `npm run workbench`, and a
  CLI example. Installation is a clone of the repository; there is no npm
  package.

Rendering lives in `scripts/site-render.ts`. Links between documents are
rewritten to the rendered pages: `.md` to `.html`, `lib/` sources to Cumulus
module pages, `examples/` to example pages, and other repository paths to
GitHub. The static design tokens, fonts, and code colors are in
`site/site.css`; code colors match the Workbench editor theme.

The browsing index is extracted from source declarations, including section
context. It says nothing about proof status and omits elaborator-generated
declarations. For semantic navigation and generated names, open the module in
the Workbench and check it. Search matches words in names, statements, and
section context.

## Proof links and embedding

Links address a bundled source file and its line, or carry a source of their
own:

```html
<a href="./workbench/#file=lib%2FGrace%2FCumulus%2FSet%2FHierarchy.g17&line=45">
  Open the hierarchy in Grace17
</a>
```

The site generator derives line numbers from the current source. For a named
entry, use `symbol=` with the declaration's unique short or full name instead
of `line=`. A link opens a bundled source locally and starts preparation and
checking. Unknown files and ambiguous names give an error. Following a link
does not overwrite an existing edited file in the workspace.

An inline link carries the code itself, as base64url-encoded UTF-8 in the
`source` parameter, with an optional `name` ending in `.g17`:

```html
<a href="./workbench/#name=FirstSteps.g17&source=bW9kdWxlIEZpcnN0U3RlcHMK...">
  Open this example
</a>
```

`workbenchSourceLink` in `workbench/deep-links.js` builds these. The Workbench
creates or replaces a workspace file of that name with the linked text and
checks it. This is how documentation code blocks and example pages open in the
Workbench without being part of the bundled library.

Embed the same URL in an iframe with a descriptive title and a full-window
fallback link. `try.html` is a working source example. Each iframe runs its own
editor and proof worker, so prefer one live example per page and lazy loading.
No postMessage integration or remote proof service is required. Workbench
assets, Monaco, and library sources are self-hosted. Site prose and static
source browsing do not initialize the proof kernel.

## Hosting and gh-pages

The Workbench supports root hosting, `/workbench/`, and deeper preview paths.
Its entry assets, Monaco configuration, PWA manifest, and service-worker cache
resolve within its own directory. Its service worker does not intercept sibling
Cumulus pages. The build includes `.nojekyll` for GitHub Pages.
The public site at [grace17.org](https://grace17.org) is served by GitHub
Pages from a separate repository, `grace17-prover/grace17.org`. To publish a
new build, copy the contents of `build/site/` into that repository without
disturbing its `CNAME` file. The generator does not write a CNAME or push a
branch.

## Before publishing

Automated checks cover link validity, scoped asset caching, and Unicode proof
links. Before publishing a build, also exercise it in a real browser:

- search, open a source module, and follow a declaration into the Workbench;
- move the cursor through a proof and confirm goal states update;
- hover and jump to definitions; edit a file and recheck it;
- the embedded iframe layout on `try.html`;
- reopening the Workbench offline after a first visit.
