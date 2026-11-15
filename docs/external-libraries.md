# Build your own Grace17 library

Your mathematical sources can live outside the Grace17 checkout. Imports use
module names; the bundled library is always found, and a `g17.json` in your
project, or `--module-root` on the command line, tells the checker where
your own modules are (see the [settings](machine-interface.md#settings)).
This guide uses a Grace17 checkout and Node.js 24 or later.
The examples are exercised by `npm run check:external-projects` (which also
requires Python 3 for independent proof-tape checking).

## Two projects

Create sibling directories `library` and `client` in your own workspace.
Save this as `library/Shared/Sets.g17`:

```g17
module Sets
import Grace.Cumulus.Set.Core

theorem subset_chain (A B C : Set)
  requires first : A ⊆ B
  requires second : B ⊆ C
  shows A ⊆ C
proof
  exact Subset.transitive with *
```

The file `library/Shared/Sets.g17` is the module `Shared.Sets` once `library`
is a module root; the module's own namespace gives the theorem its name,
`Shared.Sets.subset_chain`, and importers see it as `subset_chain`. Writing
`module Shared.Sets` instead of `module Sets` is allowed and means the same;
Cumulus spells its module names out, and your library may choose either.

Save this as `client/Main.g17`:

```g17 fragment
module Client
import Shared.Sets

theorem subset_three_steps (A B C D : Set)
  requires first : A ⊆ B
  requires second : B ⊆ C
  requires third : C ⊆ D
  shows A ⊆ D
proof
  have middle : A ⊆ C := subset_chain with *
  exact subset_chain with *
```

The annotated intermediate fact supplies the expected conclusion for inference.
The final application uses the goal and available hypotheses.

## Check and reuse

Set `GRACE17_ROOT` to the absolute path of your extracted Grace17 checkout,
and put a `g17.json` in the directory containing `library` and `client`:

```json
{ "moduleRoots": ["library"], "foundation": "ZF", "artifacts": true }
```

Then, from that directory:

```sh
export GRACE17_ROOT=/absolute/path/to/grace17
node "$GRACE17_ROOT/bin/g17.ts" check client/Main.g17

node "$GRACE17_ROOT/bin/g17.ts" axiom-audit client/Main.g17 \
  --theorem Client.subset_three_steps
```

The configuration names your shared library as a module root, chooses the
foundation, and asks for the shared artifact store, so a second check of a
file that imports Cumulus replays the library in a fraction of a second;
the bundled library is a root in any case. `g17 settings` prints what a
run resolved. For a one-off the same choices go on the command line:
`--foundation ZF --module-root library`, and `--module-root
"$GRACE17_ROOT/lib"` is accepted and redundant. Imports are resolved
locally and nothing is downloaded.
Keep module names distinct across dependencies, and give each collaborator
the exact source versions and root configuration used to check your work.
The current workflow does not provide a package resolver or a lockfile for
mathematical libraries. Pin the Grace17 commit and library revisions in
your own repository or archive.

## Export and independently check a proof tape

```sh
node "$GRACE17_ROOT/bin/g17.ts" compile client/Main.g17 \
  --out Client.g17m --environment Client.g17env

python3 "$GRACE17_ROOT/checkers/python/g17check.py" Client.g17m \
  --environment Client.g17env
```

This checks the proof tape against the exported environment. It does not
independently reconstruct the environment's declaration history. For that
separate validation task, see the [foundation contract](foundations.md) and
[independent checker documentation](../checkers/README.md), whose
`g17c_check` entry points replay a compiled module from the bare foundation.
