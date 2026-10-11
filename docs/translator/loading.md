<!-- File: docs/translator/loading.md -->

# Loading and dependency closure

The executable loads compiled Lean modules, selects declarations, and
prints their dependency closure.  This is the input to the later naming
and expression-printing passes.  Issue [#15] implements this stage;
issues [#16] and [#17] add those passes, and [#22] adds Agda module emission.

## Command line

For a first run, start at the repository root, as follows:

```sh
nix develop
make lean-build
cd translator
lake exe lean2agda --stats Init.Data.Nat.Gcd -- Nat.gcd_self
```

This core Lean input needs no Mathlib cache.  For a Mathlib input, first
run `make lean-cache` from the repository root.  To select an entire
module instead, use `lake exe lean2agda Init.Data.Nat.Gcd`.

Run from `translator/` inside the pinned Nix shell, as follows:

```sh
lake exe lean2agda [--profile U] [--root NAME] [--out DIR] [--stats] MODULE... [-- DECL...]
```

At least one module is required.  Modules before `--` are imported with
their transitive imports.  Declarations after it are exact Lean names in
that environment; Lean's name-literal decoder preserves quoted components
such as `A.«b.c».2`.  With no declarations, including an empty `--` suffix,
the roots are every declaration owned by the named modules.  Their private
and generated declarations are included.  Transitive imports contribute
dependencies, rather than becoming additional roots.

`--profile` defaults to `U`.  Other profiles are rejected until their
translation passes exist.  `--out DIR` creates the directory and writes
`closure.txt` and module-specific `.names.ndjson` reverse maps.  `--root
NAME` supplies the reverse maps' module-tree root, defaulting to `U`.
[`naming.md`] specifies the identifier encoding and sidecar format.
Standard output always includes the same listing, followed
by statistics when `--stats` is given; the file contains only the listing.
`--help` prints usage without loading an environment.  Invalid arguments
exit with status 2; import, selection, and output failures exit with status
1 and a diagnostic on standard error.  Explicit declarations may belong
to a transitive import.  One missing declaration fails the entire
selection.  Existing output files at the selected paths are overwritten;
writing happens
before the listing is sent to standard output, so a file-write failure
produces no listing there.

## Dependencies and ordering

`importEnvironment` initializes the search path from the pinned Lean
sysroot and Lake's `LEAN_PATH`, enables imported initializers, and calls
`importModules` with environment extensions loaded.  The executable has
Lake's `supportInterpreter` enabled.  Building it imports Lean only;
Mathlib's compiled modules are read when requested at run time.

The pure `dependencyClosure` function reads an `Environment` and returns
either an error or a `Closure`.  It follows dependencies as follows:

+  Every constant's type and its value, including opaque values.
+  Structure names in projection expressions, and the implicit `Nat` and
   `String` types of literal expressions.  Shared subexpressions are
   visited once per expression traversal.
+  An inductive type's constructors, its mutual inductive companions, and
   every primitive recursor associated with it.  A single index built
   from the environment includes auxiliary recursors of nested types.
+  A constructor's parent type; a recursor's inductive types, rule
   constructors, and the expressions on its reduction-rule right sides.
+  Mutual definition, theorem, and opaque companions named by their
   `ConstantInfo.all` fields.  Matchers and private helpers are followed
   through the expressions that reference them.
+  The entire primitive quotient package, `Quot`, `Quot.mk`, `Quot.lift`,
   and `Quot.ind`, whenever one of those constants is reached.

An explicit work queue computes reachability before ordering.  Missing
dependencies cause an error.  An inductive type and its constructors
depend on each other, so there is no ordering of individual constants that
puts every dependency first.  Lean's Tarjan algorithm instead computes
strongly connected components: groups in which every declaration can reach
every other through dependencies.  Dependencies outside a group precede
that group.  Names inside it are sorted by their printed strings; their
order carries no claim about dependencies within the group.  Sorting roots
and dependencies makes the output independent of hash iteration, root
order, and duplicate roots.

## API and diagnostic output

`Core/Types.lean` defines types as follows:

+  `Declaration`: the original `Name` and `ConstantInfo`, an optional
   `sourceModule`, and sorted direct `dependencies`.  Constants imported
   from compiled modules have a source module; a locally added constant
   may have none.
+  `Closure`: deduplicated `roots` and dependency-ordered `groups`, each an
   array of declarations.  `Closure.declarations` flattens the groups and
   `Closure.size` counts their members.
+  `Kind`: the eight `ConstantInfo` kinds.  `Core/Stats.lean` counts them
   individually, including constructors and recursors.

The listing starts with `# profile U`, followed by `# group N` for each
group, numbered from zero.  Each declaration occupies one tab-separated
row: kind, source module (or `<local>`), and original Lean name.  Source
modules stay on individual declarations, including dependencies from
different modules; later passes can map them to Agda modules.  This listing
is diagnostic text; its names have not yet been mapped to Agda identifiers.
Its format may change as the Agda printer develops.  Later translator
passes should use the `Closure` API.

For `Nat.gcd_self`, the listing begins as follows:

```text
# profile U
# group 0
inductive	Init.Prelude	Add
constructor	Init.Prelude	Add.mk
recursor	Init.Prelude	Add.rec
```

This first group contains `Add` and its generated constructor and primitive
recursor.  Its tab-separated rows retain their owning module,
`Init.Prelude`.  The statistics begin as follows:

```text
# stats
constants	334
groups	278
axiom	2
```

These are the exact lines retained in `tests/expected/gcd-self.txt` at
the pinned Lean version.  The remaining rows count each other kind;
constructors and recursors count as constants in their own right.

## Tests and the atlas

`make test-translator` runs `translator/tests/run.sh`.  It builds the
executable, small fixture modules, and `Atlas.Graph`, all against core Lean.
It then runs semantic checks and checks the command line as follows:

+  Two golden outputs: `Nat.gcd_self` and a fixture with a private helper
   and a dependency in another module.  Golden files start with a `File:`
   comment, which the harness removes before comparing output bytes.
+  Output directories, including one with spaces; statistics stay out of
   `closure.txt`.
+  Usage and import errors, their exit statuses, and `--help`.
+  A 60-second deadline for the acceptance command on `Nat.gcd_self`.

The semantic checks verify closedness and ordering of every tested group,
module ownership and selection, private helpers, mutual inductives,
matchers, opaque values, recursor rules, projections, literals, statistics,
and output stability under duplicate and reordered roots.  They also
compare the axioms in `Nat.gcd_self`'s closure with the atlas's saved record
in `tests/atlas-gcd-self.json` and recompute the axiom set through the
independent `Atlas.Graph.axiomSets` implementation.

The atlas records reachable axioms, rather than every dependency constant.
The comparison therefore projects the closure to its axioms.  Its graph
follows types, values, and inductive constructors; the translator also
follows recursor rules and the companions needed for emission.  For this
fixture both give exactly `Quot.sound` and `propext`.  The record was copied
from atlas format 0 at Lean 4.33.1 and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`; those pins are retained beside
the original record in the fixture.  Agreement validates this fixture's
axiom set; it does not establish equality for arbitrary inputs.  The
translator's additional edges can reach further axioms, so a difference
on another input requires comparing the two graphs.

CI runs the harness through `make test` in the existing Nix lane and
shellchecks its script.  No Mathlib interfaces are needed for these tests;
Lake still clones the source dependencies on a fresh checkout.  For a
Mathlib input outside this harness, fetch its prebuilt interfaces with
`make lean-cache`, as [`pinning.md`] describes.

[#15]: https://github.com/formalverification/lean2agda/issues/15
[#16]: https://github.com/formalverification/lean2agda/issues/16
[#17]: https://github.com/formalverification/lean2agda/issues/17
[#22]: https://github.com/formalverification/lean2agda/issues/22
[`pinning.md`]: ../pinning.md
[`naming.md`]: naming.md
