# Machine interface

The machine interface exposes what the Workbench shows, as structured data
with the same semantics: the goal state after every step, printed exactly as
the goal pane prints it; the suggestions of `exact?`, `apply?`, and `rw?`;
library search with the Workbench query language; the declaration hover; the
axiom audit; the library's modules; and the notation table. Every method is
implemented by the functions the Workbench itself calls, so a tool reading
the protocol and a person reading the Workbench see the same strings.

There are two ways in:

- **`g17 serve`** speaks a JSON protocol over standard input and output.
  Each request is one JSON object on one line, each response is one JSON
  object on one line. A process that keeps `serve` running keeps the
  checked environments cached, so a loop of check, goal, and suggest calls
  on one file costs a fraction of a second per call after the first.
- **Subcommands** run one method and exit: `g17 check --json`, `g17 goal`,
  `g17 suggest`, `g17 search`, `g17 declaration`, `g17 signature`,
  `g17 elaborate`, `g17 audit`, `g17 library`, `g17 notations`, and
  `g17 closure`. They print the same result objects. Every method
  subcommand prints JSON; `--text` asks `search`, `goal`, and `closure`
  for their readable rendering, and
  `--json` is accepted everywhere as a no-op, so a tool can pass it
  uniformly. `g17 --help`, or `--help` after any subcommand, prints the
  usage. A one-shot subcommand loads the environment each time it runs
  (several seconds for a deep import closure); a loop of calls on one file
  belongs in `serve`, or in one `check --json --audit` call.

The JSON Schema for every shape is
[schemas/machine-interface.schema.json](../schemas/machine-interface.schema.json).
The TypeScript entry points are `handleMachineRequest`, `callMachineMethod`,
and `serveMachineInterface` in `src/machine-interface.ts`, exported from
`src/index.ts`.

## Framing

A request carries an `id`, a `method`, and `params`:

```json
{"id": 1, "method": "goal", "params": {"files": [{"name": "Probe.g17"}],
  "line": 11, "column": 12}}
```

A response repeats the `id` and carries `version`, the protocol version,
on success and on failure:

```json
{"id": 1, "version": "1", "ok": true, "method": "goal", "result": {...}}
{"id": 1, "version": "1", "ok": false, "method": "goal",
  "error": {"code": "unknown_file", "message": "Probe.g17 is not among the files",
            "file": "Probe.g17"}}
```

Errors are JSON with a `code` and a `message`, never a stack trace. A line
that is not JSON, or not an object with a string `method`, answers with
`code: "invalid_request"` and `id: null`. The codes are:

| Code | Meaning |
| --- | --- |
| `invalid_request` | Malformed JSON or no `method` |
| `unknown_method` | No such method; see `capabilities` |
| `invalid_params` | A parameter is missing or has the wrong type |
| `unknown_file` | A file cannot be read, or `activeFile` or `file` is not among the files |
| `check_failed` | The method needs a checked environment and the workspace does not check; `declaration` and `signature` answer from what did load and raise it only when no environment was built at all (see those methods) |
| `no_theorem_at_position` | `suggest` was asked outside every theorem |
| `after_failure` | `suggest` was asked at or after the step that failed, or past the failing theorem; `failureLine` says where (`goal` answers `ok: true` with `code: "after_failure"` instead) |
| `dependency_failed` | A dependency of the position's file fails, at `failureFile` and `failureLine` |
| `no_proof_block` | `suggest` was asked in a theorem without a `proof` block |
| `elaboration_failed` | `elaborate` could not read the text as a formula or term in that context |
| `bad_query` | The search query does not parse |
| `unknown_declaration`, `ambiguous_name` | `declaration` or `signature` found no name, or several (`candidates` lists them, `modules` their modules, `declarations` each candidate with its `module`, `file`, and `line`); an `import` detail names the module that declares the name's prefix |
| `unknown_theorem` | `audit` names no theorem in the environment |
| `unknown_module` | `library` or `closure` names no module, or `closure`'s `from` is not in the closure |
| `surface`, `kernel`, `internal` | An unexpected elaboration, kernel, or program error |

A proof that does not check is not an error of the protocol: `check`
answers `ok: true` with `status: "failed"` and a diagnostic.

The subcommands print the response without an `id`: `g17 signature X`
prints `{"ok": true, "version": "1", "method": "signature", "result":
{...}}`, and the object each method's section below shows is that
`result`. The one exception is `check --json`, which prints the check
result's fields at the top level with `ok`, `version`, and `operation`
(see `check`). On failure the method subcommands print the error object
to standard error and exit with status 1; `check --json` prints its
failure object to standard output, so a redirection captures it, and
exits with status 1.

### Workspaces

Methods that check files take the same workspace the Workbench takes:

| Parameter | Meaning |
| --- | --- |
| `files` | An array of `{ "name", "source" }`. A file without `source` is read from disk at `name`, relative to the working directory. |
| `activeFile` | The file whose theorems are reported; the others are context. With one file it is that file. With several files and no `activeFile`, every file is reported. |
| `foundation` | `ZF`, `ZFC`, or `ZFG` (the default). |
| `moduleRoots` | Directories searched, before the library root, for the files that imports name. The bundled library under `lib/` is always a root. |

A file named by its path under `lib/` is the library module that path
denotes, so `{ "name": "lib/Grace/Cumulus/Set/Core.g17" }` checks that
module in place. Name an `activeFile` whenever the workspace has several
files: it lets the checker keep the dependency environment and recheck only
the edited file.

## Methods

### capabilities

Request:

```json
{"id": 1, "method": "capabilities"}
```

Result: the protocol version, the Grace17 version, the methods with a
one-line description each, and the foundation profiles.

```json
{"protocol": "1", "grace17": "1.0.1",
 "methods": [{"name": "check", "description": "Check a workspace: ..."}, ...],
 "foundations": ["ZF", "ZFC", "ZFG"]}
```

### check

Request: a workspace, and optionally `audit: true` to add each theorem's
axiom audit, `dependencies: false` to skip each theorem's dependency lists,
`kernel: true` to add the kernel derivation of each theorem, `symbols: true`
to add the symbol table the hover uses, `digest: true` to add the
environment digest, and `imports: true` to audit the imports (see below).

```json
{"id": 2, "method": "check",
 "params": {"files": [{"name": "Probe.g17", "source": "module Probe\n..."}]}}
```

Result, abridged, for a file whose proof stops one step short:

```json
{"status": "failed",
 "foundation": {"profile": "ZFG"},
 "files": [{"name": "Probe.g17", "status": "failed"}],
 "theorems": [{"name": "Probe.subset_chain", "kind": "theorem",
   "file": "Probe.g17", "lineStart": 4, "lineEnd": 12, "status": "failed",
   "initial": {"goals": [{"goal": "A ⊆ C",
     "assumptions": ["A ⊆ B", "B ⊆ C"],
     "locals": [{"name": "first", "formula": "A ⊆ B"},
                {"name": "second", "formula": "B ⊆ C"}]}]},
   "steps": [
     {"line": 9, "columnStart": 3, "columnEnd": 16, "command": "unfold Subset",
      "before": {"goals": [...]},
      "after": {"goals": [{"goal": "∀ x ∈ A, x ∈ C", ...}]}},
     {"line": 10, "command": "intro x", ...},
     {"line": 11, "command": "intro hx",
      "after": {"goals": [{"goal": "x ∈ C",
        "assumptions": ["A ⊆ B", "B ⊆ C", "x ∈ A"],
        "locals": [{"name": "first", "formula": "A ⊆ B"},
                   {"name": "second", "formula": "B ⊆ C"},
                   {"name": "hx", "formula": "x ∈ A"}]}]}}],
   "sorries": [], "proofMap": []}],
 "diagnostics": [{"severity": "error", "kind": "surface",
   "file": "Probe.g17", "line": 11, "column": 1, "endColumn": 2,
   "message": "1 goal remains; next is x ∈ C",
   "theorem": "Probe.subset_chain"}],
 "checked": [], "modules": [], "notations": [], "sorries": [],
 "evaluations": [], "milliseconds": 0}
```

The shape:

- `status` is `checked` when every file elaborates, `failed` otherwise.
  Elaboration stops at the first error, so a failed result has exactly one
  diagnostic of severity `error`. Its `theorems` are the theorems of the
  workspace files that completed before the failure, each `proved`,
  `dependent`, or `admitted` with its statement, states, and dependencies
  as in a checked result, followed by the one that failed, carrying the
  partial trace: the
  steps up to and including the one that failed, each with its `before`
  and `after` state. A step that failed repeats its `before` state as its
  `after` state; a proof that ends with goals remaining has every step
  checked and the diagnostic on its last line. Theorems after the failure
  are not reported: nothing past it was checked. A `sorry` in a completed
  theorem is still a warning diagnostic.
- `foundation` is the kernel's foundation report: `profile`, and when the
  check succeeded, `axioms` and `schemaInstances`.
- `files` summarizes each workspace file: `status` is `checked`, `context`
  (loaded as a dependency, not reported), `failed`, or `unchecked`; a
  checked file also carries its `module`, and counts of `definitions`,
  `theorems`, `evaluations`, `sorries` (the `sorry` lines in the file's
  own proofs: its own obligations), `admittedSorries` (the distinct
  admissions its theorems rest on, own or inherited through citation),
  `admittedTheorems` (its theorems with a `sorry` of their own), and
  `dependentTheorems` (its complete proofs that cite an admitted theorem).
  A file with `sorries: 0` and `admittedSorries: 5` has met every
  obligation of its own and rests on five admissions elsewhere.
- `theorems` holds one record per theorem, lemma, and instance of the
  reported files, in source order. `status` is `proved` (the kernel
  accepted the proof and it rests on no admission), `admitted` (the proof
  has a `sorry` of its own), `dependent` (the proof is complete with no
  `sorry` of its own, but a theorem it cites, in this file or an imported
  module, is admitted), or `failed`. A theorem's `sorries` lists every
  admission it rests on, so a `dependent` theorem's list names the
  admitted theorems, with their files and lines, that it depends on; its
  `dependencies.axioms` carries the same admissions by axiom name.
  `statement` is the
  theorem printed as the Workbench prints it. `initial` is the state at the
  start of the proof and `steps` the checked tactic steps, each with its
  one-based `line`, `columnStart`, `columnEnd`, the `command` as written,
  the state `before` and `after`, and, for a query tactic, `info` (see
  `suggest`). `dependencies` lists the axioms, theorems, and definitions
  the proof uses; `sorries` the admissions it contains; `proofMap` the
  authored headings; `audit` the axiom audit when requested. `scope` lists
  the names the proof can use without naming a declaration, each with its
  `kind` (`section variable`, `section hypothesis`, `binder`, or
  `premise`), the one-based `line` that binds it, and for a variable or
  binder the `sort` as written; the locals a proof binds itself are in the
  step states. A tool resolving a name on a proof line looks it up in the
  state before the step on that line and then in `scope`, before any
  declaration of the same name.
- A state is `{ "goals": [...] }`. Each goal has `goal`, the formula to
  prove; `locals`, the hypotheses by name in context order; and
  `assumptions`, the same formulas without names. No goals means the proof
  is complete at that point. These strings are the ones the Workbench goal
  pane renders.
- `diagnostics` carries one entry per error and one warning per `sorry`,
  each with `file`, `line`, `column`, `endColumn`, `message`, and the
  `theorem` it falls in. The column span is the one the editor underlines.
  Two further kinds never fail a check. A `warning` of kind
  `shadowed-property`, once per reported module, says that theorems of the
  module restate generated properties of its definitions under the same
  name (a theorem `rationalCut.membership` beside the definition
  `rationalCut`, whose record already carries `membership`): the name then
  resolves to the theorem and hides the property. It stands at the first
  such theorem and lists every one in `theorems`, with the first's
  `definition`. With `imports: true`, a `note` of kind `transitive-import`
  for every declaration a reported module uses whose module is neither
  the module itself, one of its direct imports, nor the core
  (`Grace.Core` and the bootstrap): `declaration`, its `module`, the direct
  import `via` which that module is reached, and the import `path` from
  that import to it, at the first theorem that uses it. Such a use breaks
  when an unrelated module drops the import it travels through; the message
  names the module to import directly. The audit reads each theorem's
  own certificate and statement, not the dependencies of the theorems it
  cites.
- `checked` summarizes every loaded module, dependencies included: `file`,
  `module`, and the names of its `definitions` and `theorems`. `modules`
  is the module report of the environment, `notations` its notation table,
  `sorries` and `evaluations` those of the reported files, `digest` the
  environment digest when requested.

`g17 check --json file...` prints the same object, with `ok: true`,
`version`, and `operation: "check"` added, over the checker's own loader:
it honors `--foundation`, `--module-root`, `--artifacts`, `--audit`, and
`--imports`. Without `--json`, `--imports` prints each note as
`note: <file>:<line>: <message>` and a count, and a shadowed-property
warning prints as `warning: <file>:<line>: <message>`; neither changes the
exit status.
On failure it prints the checker's failure object (`ok: false`, `kind`,
`message`, `line`, `file`) with `status`, `diagnostics`, `theorems`
(completed, then failed), and `milliseconds` added, to standard output
like a success, and exits with status 1: `g17 check --json f.g17 >
out.json` always leaves the JSON in `out.json`, and the exit status says
whether it checked. Standard error carries nothing in JSON mode. Without
`--json` a failure prints `surface error in <file>: line N: ...` and the
goals that remain to standard error, so the file is named for a
dependency's failure too.

`--audit` is the way to audit many theorems at once: one load of the
environment, one `audit` record per theorem. `g17 audit` with several
`--theorem` options does the same for named theorems (see `audit`).

`g17 check --continue file...` (or `--all`) goes on past a failing module:
every module of the import graph is elaborated in its own fork of the
kernel, a module whose import failed or was skipped is skipped, and the
end of the run lists every failure with its file, line, and message and
every skipped module with the import that blocked it. The exit status is 1
when anything failed. With `--json` the result carries `failures` (each a
diagnostic with `module` and `file`), `skipped` (`module`, `file`,
`because`), the `diagnostics` and partial-trace `theorems` of every
failure, and `status: "failed"`; without it, `failed ...` and
`skipped ...` lines and a count follow the checked modules. With
`--quiet`, only the failures, the skipped modules, and the final count are
printed, each failure once, without the per-module `checked` and `eval`
lines. The flag takes no `--artifacts`: it elaborates from source.
`npm run check:cumulus -- --continue` is the whole library in one run.

### goal

Request: a workspace, the `file` (optional with one file), a one-based
`line`, and an optional `column` (default 1).

```json
{"id": 3, "method": "goal",
 "params": {"files": [{"name": "Probe.g17"}], "line": 11, "column": 12}}
```

Result: the state the Workbench's goal pane shows with the cursor at that
position. The state after step k is shown once the cursor is at or past the
column where step k starts; before the first step it is the theorem's
initial state.

```json
{"file": "Probe.g17", "line": 11, "column": 12, "status": "failed",
 "kind": "theorem", "theorem": "Probe.subset_chain",
 "theoremStatus": "failed", "lineStart": 4, "lineEnd": 12,
 "step": 3, "stepLine": 11, "command": "intro hx",
 "caption": "Current position, after line 11",
 "state": {"goals": [{"goal": "x ∈ C",
   "assumptions": ["A ⊆ B", "B ⊆ C", "x ∈ A"],
   "locals": [{"name": "first", "formula": "A ⊆ B"},
              {"name": "second", "formula": "B ⊆ C"},
              {"name": "hx", "formula": "x ∈ A"}]}]},
 "complete": false, "sorries": [],
 "diagnostic": {"severity": "error", "kind": "surface", "file": "Probe.g17",
   "line": 11, "column": 1, "endColumn": 2,
   "message": "1 goal remains; next is x ∈ C",
   "theorem": "Probe.subset_chain"}}
```

`kind` is `theorem` inside a proof, `evaluation` on an `eval` line (with
the `evaluation` record), or `none` elsewhere. A proof block of a
definition is a proof like a theorem's: inside a `defgraph`'s codomain
proof the position is in the theorem `ident.closed`, inside a `def` with
a `proof` block in `ident.type`, with the definition's whole source range
as `lineStart` and `lineEnd`, in a checked file and in the file whose
failure is in that proof. `step` is 0 for the initial
state and k for the state after the k-th step; `caption` is the goal pane's
caption: `Current goal, at theorem start` for step 0, `Current goal, after
line N` after a step, and `Current position, after line N` at a failed
step. `info` is present when the step at the cursor is a query tactic.
`complete` is true when no goal remains. `scope` is the theorem's scope
table, as in `check`.

In a file that does not check, `goal` answers from what was checked: a
theorem that completed before the failure has its states as usual, and the
failing theorem has its partial trace up to the failed step. A position
after the step that failed answers `kind: "theorem"` with
`code: "after_failure"`, the caption `After the failure at line N`, the
state where the proof stopped (the failed step's `before`), and a
`message`; a position in a later theorem, or anywhere past the failure
outside the failing theorem, answers `kind: "none"` with
`code: "after_failure"` and the `diagnostic`. When a dependency fails, the
answer is `kind: "none"` with `code: "dependency_failed"`. A proof that
ran out of steps with goals remaining has no failed step: the line after
its last step is a position like any other, and a tactic can go there. A
failure inside a `have … by …` block traces that block alone: the trace's
initial state is the block's goal and the steps before the block are
absent, so step 0 is captioned `Current goal, at the start of the block on
line N` rather than as the theorem's start, at every position before the
block's first step.

### suggest

Request: a workspace, a position as for `goal`, and `tactic`: `exact?`,
`apply?`, or `rw?` (the question mark may be omitted).

```json
{"id": 4, "method": "suggest",
 "params": {"files": [{"name": "Probe.g17"}], "line": 10, "tactic": "exact?"}}
```

The query tactic is inserted, in a copy of the file, so that it runs at the
state `goal` reports for the position: before the step that follows the
cursor's state, after the last step when the cursor is past it, or as the
first line of an empty proof block. The file on disk is never written.
`inserted` says where the line went and what it was, so a tool can paste a
suggestion at the same place.

Result for a theorem whose goal is `f(X(k)) ∈ B`:

```json
{"file": "Probe.g17", "line": 10, "column": 1, "tactic": "exact?",
 "theorem": "Probe.image_in",
 "inserted": {"line": 10, "text": "  exact?"},
 "goal": {"goals": [{"goal": "f(Xₖ) ∈ B",
   "assumptions": ["f : A → B", "∀ k ∈ A, Xₖ ∈ A", "k ∈ A"],
   "locals": [{"name": "fFunction", "formula": "f : A → B"},
              {"name": "inA", "formula": "∀ k ∈ A, Xₖ ∈ A"},
              {"name": "hk", "formula": "k ∈ A"}]}]},
 "suggestions": [
   {"command": "exact FunctionBetween.apply_closed at f, A, B, Xₖ with fFunction, (inA at k with hk)",
    "tactic": "exact",
    "name": "Grace.Cumulus.Set.Function.FunctionBetween.apply_closed",
    "reference": "FunctionBetween.apply_closed", "source": "theorem",
    "arguments": ["f", "A", "B", "Xₖ"],
    "premises": [
      {"formula": "f : A → B", "evidence": "fFunction", "routine": false},
      {"formula": "Xₖ ∈ A", "evidence": "(inA at k with hk)", "routine": false}],
    "closes": true}],
 "items": ["exact FunctionBetween.apply_closed at f, A, B, Xₖ with fFunction, (inA at k with hk)"],
 "after": {"goals": []}}
```

Each suggestion carries:

- `command`, the line that pastes, exactly as the Workbench's suggestion
  button inserts it;
- `name`, the full name of the declaration applied, or the name of a local
  fact; `reference`, the name as the command writes it, a short name or a
  `_root_.` form when the short name is not in scope; `source`, one of
  `local`, `theorem`, `axiom`, `definition`;
- `arguments`, the instantiation terms the command's `at` list shows;
- `premises`, in order, each with its `formula` and, when the search
  discharged it, the `evidence` as written in the command (a local fact by
  name, a specialized fact in parentheses, or `assumption`) and whether
  that evidence was `routine` typing; for `apply?` the premises stay as new
  goals and carry no evidence;
- `closes`, whether the suggestion leaves no goal;
- for `rw?`, `reverse` (the rule was used right to left) and `goal`, the
  goal the rewrite produces.

The order is the Workbench's: for `exact?`, results whose premises are the
mathematics in scope before those closed by typing, and a declaration the
module can only reach as a `_root_.` name is offered only when nothing it
can name closes the goal; for `rw?`, rewrites that close the goal first,
then those that shrink it most. `items` repeats the commands alone, in the same order,
and `after` is the state after the first suggestion, which is the one the
query tactic applied. When the search finds nothing, `suggestions` is empty
and `message` carries the checker's message, such as `rw? found no rewrite
rule that changes this goal`.

In a file that does not check, the query runs wherever a state exists: in
a theorem that completed before the failure, or in the failing theorem at
any position before its failed step. At or after the failed step, and in
any theorem after the failure, the answer is the error `after_failure`
with `failureLine` and the `theorem`; when a dependency fails it is
`dependency_failed`.

### search

Request: `query` in the Workbench's query language (see
[library search](library-search.md)), optional `files` whose declarations
are indexed too, overriding library modules of the same name, and an
optional `limit` (default 60, at most 200).

```json
{"id": 5, "method": "search",
 "params": {"query": "name:transitive module:Set.Core"}}
```

Result:

```json
{"query": "name:transitive module:Set.Core", "limit": 60,
 "total": 1, "indexed": 12337, "candidates": 1, "cached": false,
 "milliseconds": 0.22,
 "results": [{"name": "Subset.transitive", "short": "Subset.transitive",
   "kind": "theorem", "file": "lib/Grace/Cumulus/Set/Core.g17",
   "module": "Grace.Cumulus.Set.Core", "line": 15,
   "signature": "theorem Subset.transitive (A B C : Set)\nrequires hAB : A ⊆ B\nrequires hBC : B ⊆ C\nshows (A ⊆ C)",
   "conclusion": "(A ⊆ C)", "documentation": "", "context": ""}]}
```

Results are source declarations, ranked as the Workbench ranks them. `name`
is the namespace-qualified name as written in the file, without the module
prefix; `module` is the module; `file` is the path from the repository
root; `signature` is the declaration header, `conclusion` its `shows`
clause, `documentation` the comment above it, and `context` the section
variables and hypotheses in scope.

### declaration

Request: `name`, and either a workspace (`files`, `activeFile`) or a
`module` to import, or neither.

```json
{"id": 6, "method": "declaration",
 "params": {"name": "Subset.transitive", "module": "Grace.Cumulus.Set.Core"}}
```

With a workspace or a module, the name is resolved in the checked
environment as the hover resolves it, short names included, and the result
is what the hover shows. A workspace whose active file does not check
still answers, from the environment that did load: the dependencies, and
the active file's declarations before the failure point. Such an answer
carries `partial: true` and `checkFailed` with the failure's `file`,
`line`, and `message`; a library name resolves as usual, an earlier theorem
of the file resolves as usual, and a name declared after the failure
answers with `inScope: false` and a `message` saying it is declared after
the failure; after an import that cannot be resolved, nothing of the file
loaded, and a library name answers `inScope: false` with `checkFailed`
naming the import. `check_failed` is raised only when no environment was
built at all, as after a kernel error. The result:

```json
{"elaborated": true,
 "name": "Grace.Cumulus.Set.Core.Subset.transitive", "short": "transitive",
 "kind": "theorem",
 "info": "∀ A, ∀ B, ∀ C, A ⊆ B → B ⊆ C → A ⊆ C",
 "statement": "∀ A, ∀ B, ∀ C, A ⊆ B → B ⊆ C → A ⊆ C",
 "module": "Grace.Cumulus.Set.Core",
 "file": "/.../lib/Grace/Cumulus/Set/Core.g17", "line": 15,
 "signature": "theorem Subset.transitive (A B C : Set)\nrequires hAB : A ⊆ B\nrequires hBC : B ⊆ C\nshows (A ⊆ C)",
 "conclusion": "(A ⊆ C)", "context": ""}
```

`info` is the hover text: the documentation comment, when there is one,
followed by the statement. `statement` is the printed proposition of a
theorem or axiom; `documentation` the comment; `directions` the forward
and backward implications of an equivalence. `kind` is `instance` for an
instance declaration. Without a workspace or module, the result comes from
the library source alone, with `elaborated: false` and no `statement`.

Names resolve as the hover resolves them: by full name, then by suffix or
short name, with the workspace file's own module preferred. With `module`,
that module's own declarations are preferred, so `one_mul` with
`module: "Grace.Cumulus.Rotation.Orthogonal"` is `matrixRing.one_mul`
there and `orderedPair.injective` with `module: "Grace.Cumulus.Set.Relation"`
is the Relation theorem rather than the bootstrap one; a name several
modules declare is `ambiguous_name` without such a choice, and the error's
`declarations` lists each candidate with its `module`. Three cases go
further:

- A generated fact, such as `Bool.inductive.disjoint.false.true` or
  `List.inductive.injective.cons`, is a property of a definition's kernel
  record rather than a declaration. It answers with `generated: true`,
  `kind: "property"`, the `definition` it belongs to, the `property`, the
  printed `statement`, and the `canonical` form with full names. Without a
  workspace or module, the module that declares the name's longest named
  prefix (`Bool`) is loaded to resolve it. The theorems a definition
  generates, such as a `defgraph`'s `ident.closed`, `ident.function`, and
  `ident.value`, resolve the same way and answer as theorems. One whose
  definition is outside the environment, such as `inclusionMap.value`
  under `module: "Grace.Cumulus.Set.Core"`, is resolved in its own module
  and answers with `inScope: false` and the `import` to add.
- A name that is not in the environment but is declared in the library
  answers `ok: true` with the source form, `elaborated: false`,
  `inScope: false`, and `import`, the module to import:

  ```json
  {"elaborated": false, "inScope": false,
   "import": "Grace.Cumulus.Algebra.Group.Homomorphism",
   "message": "GroupHom.map_mem is not in this environment; import Grace.Cumulus.Algebra.Group.Homomorphism",
   "name": "Grace.Cumulus.Algebra.Group.Homomorphism.GroupHom.map_mem",
   "kind": "instance", ...}
  ```
- A name declared in several modules is `ambiguous_name`, with
  `candidates` and `modules`.
- A theorem whose name is also a generated property of a definition
  (`rationalCut.membership` declared as a theorem beside the definition
  `rationalCut`) answers with the theorem and carries `shadows`, an array
  holding the generated property's record as the first case describes it,
  so a caller sees both and knows the name resolves to the theorem.
  `check` warns once per module about such names.

### signature

Request: `name`, optionally a workspace (`files`, `activeFile`) or a
`module`, and optionally `elaborate: true`.

```json
{"id": 10, "method": "signature",
 "params": {"name": "keep.sub", "files": [{"name": "Sec.g17"}]}}
```

Result: the declaration's header as data, read from the source, so a file
that does not yet check still answers. For

```g17 fragment
section Facts
variable (A B : Set)
hypothesis sub : A ⊆ B

theorem keep.sub (C : Set)
  requires more : B ⊆ C
  shows A ⊆ C
```

the result is

```json
{"name": "Sec.keep.sub", "short": "keep.sub", "kind": "theorem",
 "module": "Sec", "file": "Sec.g17", "line": 8,
 "parameters": [
   {"name": "A", "type": "Set", "binder": "explicit", "source": "section"},
   {"name": "B", "type": "Set", "binder": "explicit", "source": "section"},
   {"name": "C", "type": "Set", "binder": "explicit", "source": "declaration"}],
 "premises": [
   {"name": "sub", "formula": "A ⊆ B", "source": "section"},
   {"name": "more", "formula": "B ⊆ C", "source": "declaration"}],
 "conclusion": "A ⊆ C",
 "rings": [],
 "positional": {"at": ["A", "B", "C"], "with": ["sub", "more"]},
 "signature": "theorem keep.sub (C : Set)\nrequires more : B ⊆ C\nshows A ⊆ C",
 "context": "variable (A B : Set)\nhypothesis sub : A ⊆ B",
 "documentation": "", "elaborated": false}
```

`parameters` are in the order the statement quantifies them: the section
variables of every enclosing section first, then the header's own binder
groups, each with its `type` as written and `binder` `explicit` (`(x : T)`)
or `implicit` (`{x : T}`); a group may hold several comma-separated
segments, `(u : Set, n : Nat)`, and a bounded binder `(a b ∈ O)` has the
type `∈ O`. `premises` are in the order an `at`/`with` list
supplies them: the section hypotheses in scope, which the elaborator
inserts before the header's `requires` clauses, then those clauses; a
`requires` without a name has no `name`. `positional.at` and
`positional.with` repeat the names alone, with `null` for an unnamed
premise. A typed binder such as `(xs : List(A))` or `(g : G)` adds its
typing fact to the statement; `with` lists do not name those, the
elaborator discharges them from the context. `rings` lists the
`notation ring` scopes in force. With `elaborate: true` and a workspace or
module, `statement` and `fullName` are added from the checked environment
and `elaborated` is true; when the environment does not check, the
statement is taken from what did load (the dependencies and the
declarations before the failure), with `partial: true`, and `checkFailed`
carries the failure's `file`, `line`, and `message`; a declaration the
failure keeps out of the environment leaves the header fields standing
alone. Definitions and predicates answer with their
parameters and the header text after them as `conclusion`.

A theorem generated from a definition, such as a `defgraph`'s
`ident.value` or `ident.closed`, has no header in the source: it answers
with `generated: true`, the `definition` it belongs to, and parameters,
premises, and conclusion read from its elaborated statement (the leading
binders, the antecedents, and the rest; a typing premise `Nat(n)` or
`Real(x)` becomes the binder's type), with `elaborated: true`, the
`statement`, and the `fullName`; its premises carry no names, so
`positional.with` is a list of `null`. With a `module` and a short name
several modules declare, the module's own declaration is chosen, else the
one declaration its imports reach; otherwise the answer is
`ambiguous_name` with `declarations`.

### elaborate

Request: `text`, the term or formula as a module would write it; a context,
which is a workspace with `file` (optional with one file) and an optional
`line`, or a `module` to import, or neither for the core prelude;
optionally `kind` (`formula`, `term`, or `auto`, the default) and
`variables`, binder groups for the free variables of the text.

```json
{"id": 11, "method": "elaborate",
 "params": {"text": "pair(A, B)", "variables": "(A B : Set)",
            "module": "Grace.Cumulus.Set.Core"}}
```

Result: what the kernel received, printed twice.

```json
{"text": "pair(A, B)", "kind": "term", "module": "Grace.Cumulus.Set.Core",
 "variables": "(A B : Set)",
 "printed": "{A, B}",
 "canonical": "{A, B}",
 "symbols": [{"name": "pair", "kind": "function", "arity": 2}]}
```

`printed` is the form the goal pane shows, with the shortest unambiguous
names and the notations in scope; `canonical` is the printer's plain form,
every symbol by its full kernel name and only the printer's built-in forms
(the core set operations keep their glyphs); `symbols` lists the function and predicate
symbols the elaborated form mentions, in first-use order, each with its
`kind` (`function`, `predicate`, `definition`, `class`, `datatype`) and
`arity`. `kind` says which reading succeeded: with `auto`, the text is read
as a formula first, then as a term.

The text is elaborated where the context reads it: it becomes the `shows`
clause of a probe theorem admitted with `sorry`, in a copy of the file at
the given `line` (before the declaration holding that line, with every
proof before it replaced by `sorry` and the open sections still open, so
section variables, hypotheses, and `notation ring` scopes apply and the
file need not check), or in a probe file importing the `module`. The
result's `file` and `line` say where the probe stood. Nothing on disk is
written. A text that does not elaborate answers `elaboration_failed` with
the elaborator's message. With typed `variables` such as `(n : Nat)`, the
typing facts of the binders stay in front of a formula's printed form.

### audit

Request: a workspace and the full `theorem` name, or `theorems`, an array
of full names audited over one loaded environment (the result is then
`{ "foundation", "audits": [...] }`, one entry per name in order; a name
the environment does not hold is the entry `{ "theorem", "error": {
"code": "unknown_theorem", "message" } }` and the other audits stand).
`g17 audit file --theorem A --theorem B` prints that result.

```json
{"id": 7, "method": "audit",
 "params": {"files": [{"name": "Probe.g17"}], "theorem": "Probe.image_in"}}
```

Result: the [axiom audit](axiom-audit.md). `direct` lists the named axioms
the theorem's own certificate uses and `hereditary` every named axiom
reachable through the theorems and definitions it cites; `axioms` gives
each one's statement and a dependency path; `mechanisms` the schema
mechanisms used; `classicalLogic` whether double-negation elimination
occurs; `unavailable` any missing provenance, which makes `complete` false.
A `sorry` is an axiom and appears here. The checked environment is kept
between calls on the same workspace, so a run of audits after a check costs
milliseconds each in `serve`; a one-shot `g17 audit` process loads the
environment every time, which is why many audits belong in one
`check --json --audit` or one `audit` with `theorems`.

```json
{"foundation": "ZFG", "theorem": "Probe.image_in", "complete": true,
 "direct": ["sorry.Probe.image_in.10.1"],
 "hereditary": ["sorry.Probe.image_in.10.1"],
 "axioms": [{"name": "sorry.Probe.image_in.10.1", "statement": "...",
   "direct": true, "path": ["Probe.image_in", "axiom sorry.Probe.image_in.10.1"]}],
 "mechanisms": [], "unavailable": [], "classicalLogic": false, "visited": 1}
```

### library

Request: optionally `area` (`Set`, `Real`, `Algebra`, ..., the directory
under `lib/Grace/Cumulus/`, or `Core`, `Bootstrap`, `Kernel`), optionally
`module` (a module name, or a prefix of one), and optionally
`declarations`, which defaults to true when an area or module is given.

```json
{"id": 8, "method": "library", "params": {"area": "Set"}}
```

Result:

```json
{"area": "Set",
 "areas": [{"name": "Set", "modules": 33, "declarations": 699}],
 "modules": [{"module": "Grace.Cumulus.Set.Algebra",
   "file": "lib/Grace/Cumulus/Set/Algebra.g17", "area": "Set",
   "header": "The Boolean algebra of sets: union, intersection, ...",
   "line": 8, "declarationCount": 76,
   "declarations": [{"name": "symmetricDifference.membership",
     "short": "symmetricDifference.membership", "kind": "theorem",
     "line": 14,
     "signature": "theorem symmetricDifference.membership (x A B : Set)\nshows x ∈ A △ B ↔ ¬(x ∈ A ↔ x ∈ B)",
     "conclusion": "x ∈ A △ B ↔ ¬(x ∈ A ↔ x ∈ B)",
     "documentation": "", "context": ""}, ...]}, ...]}
```

`header` is the module's leading comment, as the import hover shows it.
Declarations are the search index's records for the file.

### notations

Request: a workspace, or a `module` to import, or neither for the core
prelude.

```json
{"id": 9, "method": "notations", "params": {"module": "Grace.Cumulus.Set.Core"}}
```

Result: `notations`, the notation table in scope, exactly the records the
Workbench receives, and `tactics`, the tactic macros in scope.

```json
{"module": "Grace.Cumulus.Set.Core", "foundation": "ZFG",
 "notations": [{"token": "⊆", "precedence": 50, "associativity": "none",
   "kind": "predicate", "reversed": false,
   "target": "Grace.Cumulus.Set.Basic.Set.Subset",
   "module": "Grace.Cumulus.Set.Basic"}, ...],
 "tactics": [...]}
```

Each notation has its `token`, `precedence`, `associativity`, `kind`
(`function` or `predicate`), the `target` declaration, and the `module`
that declares it; a non-infix form carries `fixity` (`prefix`, `postfix`,
`mixfix`, `binder`, `numeral`, `coercion`, `scoped`, ...), a scoped form
its `parameters` and `expansion`, and the typed forms carry
`operandType`, `leftOperandType`, `rightOperandType`, or `resultType`. A
tool that prints or parses with this table agrees with the Workbench.

### pin

Request: optionally `enabled` (default true).

```json
{"id": 12, "method": "pin", "params": {"enabled": true}}
```

Result: `pinned` and `files`, the dependency files pinned so far. While
pinned, every library or module-root file the incremental loader reads for
an `activeFile`'s imports keeps the content first seen in this process, so
a request does not change its answer while another process edits a
dependency; `enabled: false` releases them, and `capabilities` reports
`pinned: true` while a pin holds. `g17 serve --pin` pins from the start.
The pin covers the dependency closure of a single active file (the
incremental path); a workspace checked without an `activeFile` and with
several files reads its dependencies from disk each time.

### closure

Request: `module`, a module name or a unique suffix of one such as
`Topology.Tube`, or `file`, a `.g17` file; optionally `moduleRoots` as for
a workspace, and `from`, a dependency named the same way.

```json
{"id": 13, "method": "closure",
 "params": {"module": "Grace.Cumulus.Topology.Tube", "from": "Set.Choice"}}
```

Result: the import closure read from the sources without elaboration,
dependencies before dependents and the module itself last, each with its
resolved `imports` and whether it is `choiceFree`, that is, reaches none of
`Grace.Cumulus.Set.Choice`, `Grace.Cumulus.Set.ChoiceFunctions`, and
`Grace.Cumulus.Set.WellOrdering`; `choice` lists those of them in the
closure. With `from`, `chain` is the shortest import chain from the module
to that dependency, both included. A `from` outside the closure is
`unknown_module`.

```json
{"module": "Grace.Cumulus.Topology.Tube",
 "file": "lib/Grace/Cumulus/Topology/Tube.g17",
 "choiceFree": false, "count": 61, "choice": ["Grace.Cumulus.Set.Choice"],
 "modules": [{"module": "Grace.Cumulus.Set.Basic",
   "file": "lib/Grace/Cumulus/Set/Basic.g17", "imports": [],
   "choiceFree": true}, ...],
 "from": "Grace.Cumulus.Set.Choice",
 "chain": ["Grace.Cumulus.Topology.Tube", "Grace.Cumulus.Set.Choice"]}
```

`g17 closure Topology.Tube --from Set.Choice` prints it; `--text` prints
one line per module, `choice-free` or `choice` first, and the chain.
A module that is choice-free loads under `--foundation ZF`.

## A session

The loop an agent runs, over `g17 serve`. The file is `Probe.g17`:

```g17
module Probe
import Grace.Cumulus.Set.Function

theorem image_in (f X A B k : Set)
  requires fFunction : f : A → B
  requires inA : ∀ k ∈ A, X(k) ∈ A
  requires hk : k ∈ A
  shows f(X(k)) ∈ B
proof
  sorry
```

Check it. The proof is complete modulo its `sorry`, which is a warning:

```json
{"id": 1, "method": "check", "params": {"files": [{"name": "Probe.g17"}]}}
```

```json
{"id": 1, "version": "1", "ok": true, "method": "check",
 "result": {"status": "checked",
   "theorems": [{"name": "Probe.image_in", "status": "admitted", ...}],
   "diagnostics": [{"severity": "warning", "kind": "sorry",
     "file": "Probe.g17", "line": 10, "column": 1, "endColumn": 1,
     "message": "sorry admits f(Xₖ) ∈ B", "theorem": "Probe.image_in"}],
   ...}}
```

Read the goal at the `sorry`:

```json
{"id": 2, "method": "goal", "params": {"files": [{"name": "Probe.g17"}],
  "line": 10}}
```

```json
{"id": 2, "version": "1", "ok": true, "method": "goal",
 "result": {"kind": "theorem", "theorem": "Probe.image_in", "step": 0,
   "caption": "Current goal, at theorem start",
   "state": {"goals": [{"goal": "f(Xₖ) ∈ B",
     "locals": [{"name": "fFunction", "formula": "f : A → B"},
                {"name": "inA", "formula": "∀ k ∈ A, Xₖ ∈ A"},
                {"name": "hk", "formula": "k ∈ A"}], ...}]},
   "complete": false, ...}}
```

Ask for suggestions at the same position:

```json
{"id": 3, "method": "suggest", "params": {"files": [{"name": "Probe.g17"}],
  "line": 10, "tactic": "exact?"}}
```

The first suggestion is `exact FunctionBetween.apply_closed at f, A, B, Xₖ
with fFunction, (inA at k with hk)` and `closes` is true. Paste it over the
`sorry`, at the `inserted` line with the `inserted` indentation, and check
again, sending the edited source:

```json
{"id": 4, "method": "check", "params": {"files": [{"name": "Probe.g17",
  "source": "module Probe\n...\nproof\n  exact FunctionBetween.apply_closed at f, A, B, Xₖ with fFunction, (inA at k with hk)\n"}],
  "audit": true}}
```

```json
{"id": 4, "version": "1", "ok": true, "method": "check",
 "result": {"status": "checked",
   "theorems": [{"name": "Probe.image_in", "status": "proved",
     "audit": {"complete": true, "direct": [], "hereditary": [], ...},
     ...}],
   "diagnostics": [], ...}}
```

The theorem is proved, and the audit shows it uses no named axiom.

## A fast loop

A one-shot subcommand loads the environment each time it runs: on a deep
import closure that is tens of seconds per call, all of it spent before
the method runs. `serve` loads it once. The checked environment is kept
by workspace, whatever the method and its options, so a `check`, `goal`,
`suggest`, `audit`, `signature`, `declaration`, or `elaborate` request on
the same files after the first answers in milliseconds (a `suggest` or
`elaborate` rechecks only the probe copy of the file). A scripted batch
is one `serve` process fed the requests, one per line; the responses come
out in the same order:

```sh
node --disable-warning=ExperimentalWarning bin/g17.ts serve <<'EOF'
{"id": 1, "method": "check", "params": {"files": [{"name": "lib/Grace/Cumulus/Geometry/BanachTarski.g17"}], "moduleRoots": ["lib"]}}
{"id": 2, "method": "goal", "params": {"files": [{"name": "lib/Grace/Cumulus/Geometry/BanachTarski.g17"}], "moduleRoots": ["lib"], "line": 85}}
{"id": 3, "method": "suggest", "params": {"files": [{"name": "lib/Grace/Cumulus/Geometry/BanachTarski.g17"}], "moduleRoots": ["lib"], "line": 85, "tactic": "exact?"}}
EOF
```

`serve` exits when its input ends. A loop that decides each request
from the previous answer keeps the process open and reads one response
line per request; in Node:

```js
import { spawn } from "node:child_process";
import { createInterface } from "node:readline";
const serve = spawn("node", ["--disable-warning=ExperimentalWarning",
  "bin/g17.ts", "serve"], { stdio: ["pipe", "pipe", "inherit"] });
const replies = createInterface({ input: serve.stdout });
const lines = replies[Symbol.asyncIterator]();
const ask = async request => {
  serve.stdin.write(`${JSON.stringify(request)}\n`);
  return JSON.parse((await lines.next()).value);
};
const files = [{ name: "lib/Grace/Cumulus/Geometry/BanachTarski.g17" }];
const params = { files, moduleRoots: ["lib"] };
const checked = await ask({ id: 1, method: "check", params });
console.log(checked.result.status);
const at = { ...params, line: 85 };
const goal = await ask({ id: 2, method: "goal", params: at });
console.log(goal.result.state);
serve.stdin.end();
```

Send an edited file as `source` in the next request; the dependency
environment stays, and only the edited file is rechecked.

## Semantics

- **Printing.** Every formula and term string comes from the Workbench's
  printer with the Workbench's options: the shortest unambiguous names, the
  notations in scope, and the operations, carriers, and function forms
  that a theorem's hypotheses supply. A string in a protocol result is the
  string the goal pane, the hover, or the suggestion button shows.
- **Positions.** Lines and columns are one-based. The state at a position
  is selected as the editor selects it: a step counts once the cursor is at
  or past the column where it starts.
- **Caching.** Checking is incremental. The dependency environment of an
  `activeFile` is kept between calls and the edited file is rechecked over
  it; identical workspaces return the same result without work, whichever
  method asked, and the methods that need only the environment reuse any
  check of the same workspace. A kept result remembers the dependency
  files its check read, with their sizes and modification times, and is
  not reused once one of them has changed on disk, or a file that was
  missing has appeared: a dependency rewritten between two requests of one
  `serve` session is read again by the next, unless the session is
  pinned. Nothing is cached on disk by the protocol itself.
- **Trust.** The protocol is an untrusted client of the kernel, like the
  Workbench. A theorem counts as proved when `status` is `proved`, which
  means the kernel accepted its certificate; suggestions and search are
  conveniences and admit nothing.

## Limits

- `serve` handles one request at a time, in order. No request ends the
  session: a malformed line, a method that throws, a result that cannot be
  serialized, and an error raised outside any handler while the session
  runs are each answered with an error object (`id` null when no request
  can be blamed), and the next line is read. The session ends with its
  input, or when its output can no longer be written.
- A failed check stops at the first error. To see every theorem's first
  error in a module, end each unfinished proof with `sorry` and read the
  warnings, or run `python3 scripts/all-errors.py`; to see every failing
  module of an import graph, run `g17 check --continue`.
- `suggest` inserts the query tactic as a whole line. A position inside a
  `by` block on the same line as its `have` is treated as the line's
  position.
- `declaration` without a workspace or module reads the library source and
  cannot print the elaborated statement, except for a generated name,
  which loads the module of its prefix.
- `elaborate` reads the text as a `shows` clause: a formula, or a term as
  the left side of an equation. Binders of `variables` typed other than
  `Set` leave their typing facts in the printed formula.
- `pin` covers the dependency reads of the incremental loader only; see
  the method.
