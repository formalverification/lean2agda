<!-- File: corpus/SCHEMA.md -->

# The corpus schema

This file defines what a corpus entry contains, the fields of
`manifest.json`, and what makes an entry malformed.
`scripts/python/corpus_check.py` enforces every rule stated here, with
the rules themselves in `scripts/python/corpus_manifest.py`; the Python
standard library has no JSON Schema validator, so the rules are written
as prose and as code, and the two must change together.
[`README.md`](README.md) lists the entries and says how to translate
one.

## An entry's directory

An entry whose id is `<id>` lives in `corpus/<id>/`, which holds the
following:

+  `lean/Statement.lean`: the declaration's statement, quoted from its
   source file with the path and line at the pinned Lean or Mathlib,
   followed by the `#check` and `#print axioms` commands that reproduce
   the manifest's `lean_name` and `axioms`.  Run it from `translator/`
   as `lake env lean ../corpus/<id>/lean/Statement.lean`.
+  `lean/term.ndjson`: the kernel term, exported by lean4export in its
   NDJSON format.  The export holds the declaration and everything it
   depends on, down to Lean's prelude.  It is produced from
   `translator/` as follows:

   ```sh
   lake exe lean4export <lean_module> -- <lean_name> > ../corpus/<id>/lean/term.ndjson
   ```

   Its first line records the exporter's version and the Lean commit
   that ran it.  At the pinned versions the export is deterministic: two
   runs give the same bytes.
+  `lean/term.sidecar.json`, in place of `term.ndjson` (never beside
   it), when the export is larger than 1 MB (1,000,000 bytes).  A
   `term.ndjson` over that size is malformed.  The repository then records
   the export's size, its SHA-256 and the command that regenerates it,
   so that the layout stays the one the issue, the README and this file
   describe without committing megabytes of NDJSON per entry.  It is a
   JSON object with exactly the following three fields:

   ```json
   {
     "bytes": 12345678,
     "sha256": "64 lowercase hexadecimal digits",
     "command": "lake exe lean4export <lean_module> -- <lean_name>"
   }
   ```

   `command` runs from `translator/` and writes the export to standard
   output; `sha256sum` of that output must print `sha256`.
+  `agda/`: the hand-written Agda, one or more plain `.agda` files
   directly in `agda/` (no subdirectories, no literate files), every
   one of them listed in the entry's `agda_files`.  Each declares its
   flags in a single `OPTIONS` pragma at the top, before the module
   declaration: Agda ignores an `OPTIONS` pragma inside a comment, and
   one after the module header with only a warning (both measured with
   Agda 2.8.0, where a file that postulated passed with the ignored
   `--safe`), so the checker reads the pragma only where Agda does.
   Two files are usual when one translation targets two profiles, as
   issue M1-8's entries do.
+  `notes.md`: what the translation needed, written from
   [`notes-template.md`](notes-template.md).

Generated files never enter the repository: Agda writes `.agdai`
interface files beside the sources, and `.gitignore` excludes them.

## The manifest

`manifest.json` is a JSON array with one object per entry.  Every
object has exactly the fields below, no others.

| Field | Type | Meaning |
| --- | --- | --- |
| `id` | string | The entry's directory name: lowercase kebab-case (`[a-z0-9]+(-[a-z0-9]+)*`), unique in the manifest. |
| `theme` | string | The selection theme the entry stands for, in a few words (issue M1-6's list of themes). |
| `lean_name` | string | The fully qualified name of the declaration translated.  For an entry that translates a definition together with one of its equations, the equation, whose closure contains the definition. |
| `lean_module` | string | The module that declares `lean_name` at the pinned revision, in Lean's core library (`Init.*`) or in Mathlib; the module lean4export is given. |
| `axioms` | array of strings | What `#print axioms` prints for `lean_name` at the pinned revision, in its order; empty when it prints that the declaration depends on no axioms.  No repeats. |
| `tier` | string | `T0`, `T1`, `T2` or `T3` (the roadmap's Layers section), which must be the tier the axioms imply (below). |
| `features` | array of strings | The gap-catalog features the entry exercises, from the vocabulary below; at least one, no repeats. |
| `agda_files` | array of objects | The Agda files of the entry, each with the three fields of the next table; at least one when `status` is `translated`. |
| `status` | string | `planned` (selected, not translated yet) or `translated` (the files exist and the checker type-checks them).  The result of a check is the checker's output, never a field here. |
| `issue` | integer | The number of the issue that translates the entry (7, 8 or 9 for the first twelve). |

Each object in `agda_files` has exactly the following fields:

| Field | Type | Meaning |
| --- | --- | --- |
| `path` | string | The file's name in the entry's `agda/` directory: it ends in `.agda` and has no directory part.  Agda requires the module to be named after the file; the corpus names both after the id in UpperCamelCase (`ListReverseReverse`), with a `Cubical` suffix for a cubical variant. |
| `flags` | array of strings | The file's `OPTIONS` pragma, token for token and in the same order. |
| `profile` | string | `K`, `CC` or `CU` (the roadmap's Target profiles), agreeing with `flags` as the next table says. |

| Profile | `flags` must contain | `flags` must not contain |
| --- | --- | --- |
| `K` | `--safe` | `--cubical-compatible`, `--without-K`, `--cubical`, `--erased-cubical` |
| `CC` | `--safe`, `--cubical-compatible` | `--cubical`, `--erased-cubical` |
| `CU` | `--safe`, `--cubical` | `--erased-cubical` |

Profile U (`--type-in-type`, postulates allowed) is scaffolding for the
translator and never a corpus profile; `--safe`, which every profile
requires, rejects it.  A file that imports the cubical library also
needs `--guardedness`, because the library's own flags include it and
Agda treats it as infective; the checker does not add it, so a file
that leaves it out fails the check, as it should.

For a `planned` entry, `agda_files` names the files and profiles the
translation is planned to have, and nothing is compared with files on
disk.  The session that translates the entry may change the plan (a
proof that needs K records profile `K`, and says why in `notes.md`); it
never weakens a flag to make a file check.

### Tiers from axioms

The tier is computed from `axioms` as follows; the first rule that
applies decides:

+  `T3` if any axiom is not one of `propext`, `Quot.sound` and
   `Classical.choice`: `sorryAx`, `Lean.ofReduceBool`,
   `Lean.trustCompiler`, any other declared axiom, and the axioms that
   `native_decide` now generates (at Lean v4.33.1, `#print axioms` on a
   theorem proved by `native_decide` prints an auxiliary axiom named
   `<theorem>._native.native_decide.ax_1_1`, not `Lean.ofReduceBool`);
+  `T2` if `Classical.choice` is among them;
+  `T1` if `propext` or `Quot.sound` is;
+  `T0` if the list is empty.

The axioms were measured with `#print axioms` at Mathlib v4.33.1 (the
pin in [`../docs/pinning.md`](../docs/pinning.md)) for every entry,
planned ones included.  When the pin moves, they are measured again;
the atlas of issue M1-11 computes the same sets for all of Mathlib and
should agree with them.

### Features

The vocabulary is provisional: it is the list of entries that issue
M1-5's gap catalog (`docs/foundations/gap-catalog.md`, not written yet)
is to have, each under a kebab-case slug.  The first ten are the rows
of the README's table "What the translation has to bridge"; the last
three are entries the catalog's issue lists that the table does not.
When the catalog exists, its entries become the vocabulary, and the
slugs here, the `FEATURES` constant in `corpus_manifest.py` and the
manifest change together.

| Slug | README row | Gap-catalog entry (issue M1-5) |
| --- | --- | --- |
| `impredicative-prop` | Universe of propositions | impredicative `Prop` (and `imax`) |
| `proof-irrelevance` | Proof irrelevance | definitional proof irrelevance |
| `k-and-uip` | K and UIP | K-like reduction and UIP |
| `large-elimination` | Large elimination from `Prop` | large elimination from `Prop` for subsingletons |
| `quotients` | Quotients | primitive quotients and their computation rule |
| `axioms` | Axioms | `propext`, `Quot.sound`, `Classical.choice` |
| `universe-levels` | Universe levels | universe polymorphism and level arithmetic |
| `structure-eta` | Eta | structure eta and unit eta |
| `literals` | Literals | `Nat` literals with GMP-accelerated kernel operations, and `String` literals |
| `trust-escape-hatches` | Trust escape hatches | `Lean.ofReduceBool`, `implemented_by`, `partial`, `unsafe`, `sorryAx` |
| `decidable-and-noncomputable` | (none) | `Decidable` and `noncomputable` |
| `nested-and-mutual-inductives` | (none) | nested and mutual inductives |
| `projections-and-let` | (none) | projections and `let` |

An entry exercises a feature when its kernel term (the declaration,
the definitions it unfolds, and the lemmas it cites) uses the feature
in a way the translation has to handle.  For a `planned` entry,
`features` is what the selection expects; the translating session
corrects it and gives the evidence in `notes.md`.

## What makes an entry malformed

The checker reports an entry as malformed, prints why, and exits with
status 1 when any of the following holds:

+  a field is missing, unknown, or of the wrong type, or a value breaks
   a rule in the tables above (an id that is not kebab-case or not
   unique, a tier the axioms do not imply, an unknown feature or
   profile, a repeated feature, axiom or file, flags that disagree with
   the profile);
+  the entry is `translated` and one of the following holds: it lists
   no Agda file; a listed file is missing, has no `OPTIONS` pragma
   before its module declaration, has more than one there, declares
   flags that differ from the manifest's, or has an `OPTIONS` pragma
   after its module header; its `agda/` directory holds an Agda source
   file, plain or literate and at any depth, that the manifest does not
   list; `lean/Statement.lean` or `notes.md` is missing; `lean/` holds
   neither `term.ndjson` nor `term.sidecar.json`, or both; `term.ndjson`
   is larger than 1 MB; or the sidecar breaks its rules above.

Two conditions concern the corpus as a whole and also fail the check:
`manifest.json` is missing or is not a JSON array, or `corpus/` holds a
directory that is not the id of an entry (it would never be checked).
