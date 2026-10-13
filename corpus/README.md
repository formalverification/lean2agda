<!-- File: corpus/README.md -->

# corpus

Mathlib declarations translated into Agda by hand, before any translator
exists, so that the project learns what translation involves and the
translator has an oracle to reproduce.  Issue M1-6 ([#6]) fixed the layout,
selected the twelve entries below, and wrote the checker; issues M1-7, M1-8
and M1-9 ([#7], [#8], [#9]) translated them, and M1-10 ([#10]) collected
their notes into the gap report,
[`gap-report-corpus.md`](../docs/foundations/gap-report-corpus.md).

## Layout

One directory per entry, `corpus/<id>/`, holds the Lean statement and
its exported kernel term (`lean/`), the hand-written Agda (`agda/`),
and notes on what the translation needed (`notes.md`, from
[`notes-template.md`](notes-template.md)).  [`manifest.json`](manifest.json)
lists every entry with its Lean name and module, its axioms and tier,
the gap-catalog features it exercises, its Agda files with their flags
and profiles, its status, and its issue.  [`SCHEMA.md`](SCHEMA.md)
defines each field and the rules the checker enforces.

## The entries

| Id | Lean declaration | Module | Theme | Tier | Issue |
| --- | --- | --- | --- | --- | --- |
| `list-reverse-reverse` | `List.reverse_reverse` | `Init.Data.List.Lemmas` | constructive arithmetic and lists | T1 | [#7] |
| `nat-gcd-self` | `Nat.gcd_self` | `Init.Data.Nat.Gcd` | constructive arithmetic and lists | T1 | [#7] |
| `nat-gcd-succ` | `Nat.gcd_succ` | `Init.Data.Nat.Gcd` | well-founded recursion | T1 | [#7] |
| `lists-subset-refl` | `Lists'.Subset.refl` | `Mathlib.SetTheory.Lists` | mutual inductive types | T1 | [#7] |
| `multiset-map-map` | `Multiset.map_map` | `Mathlib.Data.Multiset.MapFold` | a quotient (`Quot`) | T1 | [#8] |
| `set-ext` | `Set.ext` | `Mathlib.Data.Set.Defs` | set extensionality | T1 | [#8] |
| `finset-card-image` | `Finset.card_image_of_injective` | `Mathlib.Data.Finset.Card` | a `Decidable` instance in a `Finset` statement | T2 | [#9] |
| `real-sqrt-nonneg` | `Real.sqrt_nonneg` | `Mathlib.Analysis.Real.Sqrt` | real numbers | T2 | [#9] |
| `subgroup-card-dvd` | `Subgroup.card_subgroup_dvd_card` | `Mathlib.GroupTheory.Coset.Card` | Lagrange's theorem | T2 | [#9] |
| `order-hom-map-lfp` | `OrderHom.map_lfp` | `Mathlib.Order.FixedPoints` | lattices (Knaster and Tarski) | T1 | [#9] |
| `subtype-coe-eta` | `Subtype.coe_eta` | `Mathlib.Data.Subtype` | structure eta | T0 | [#9] |
| `substructure-closure-le` | `FirstOrder.Language.Substructure.closure_le` | `Mathlib.ModelTheory.Substructures` | model theory (agda-algebras) | T2 | [#9] |

The table records the selection.  The current state of each entry, its status
included, is `manifest.json`, and `make corpus-check` prints it; a session
that translates an entry updates the manifest, not this table.  The coverage
table below is printed from the manifest by `make corpus-tables`, and a test
fails when the two differ, so a session that changes an entry's features
prints it again.

Every name, module and axiom set was checked on 2026-10-07 against
Lean v4.33.1 and Mathlib v4.33.1, the pins of
[`../docs/pinning.md`](../docs/pinning.md), with `#check` and
`#print axioms` in `translator/`'s Lake package.  Three of the twelve
live in Lean's core library rather than Mathlib; what matters for the
corpus is the translation, not the library.  The following facts about
the selection are not obvious from the names:

+  **Eleven themes, twelve entries**.  Issue M1-6 names ten themes, the
   first of which (arithmetic and lists) takes two entries.  The
   twelfth, `Lists'.Subset.refl`, was chosen to exercise nested and
   mutual inductive types, a gap-catalog entry no other entry touches.
   A scan of every inductive type in the pinned environment found no
   nested inductive type in Mathlib's mathematics (only
   `Mathlib.Tactic.Translate.ArgReorder`, in tactic code) and one
   mutual block outside tactic code, `Lists.Equiv` with
   `Lists'.Subset` in `Mathlib.SetTheory.Lists`; Lean's `Init` adds
   `Lean.Syntax`, nested.  The corpus therefore takes the one mutual
   block Mathlib's mathematics has.
+  **Tiers lower and higher than they look**.  `List.reverse_reverse`
   is T1, not T0, only because `simp` closes a goal with `eq_self`,
   which is proved from `propext` (the seed entry's notes trace it).
   `Nat.gcd_self` is T1 through `eq_self` too, and through the lemmas
   its proof cites: `Nat.mod_self` (`propext`) and `Nat.gcd_succ`
   (`Quot.sound`).  `OrderHom.map_lfp`, Knaster and Tarski, is T1;
   `Subtype.coe_eta` is T0.
+  **The gcd equation**.  `Nat.gcd` is defined by well-founded
   recursion (`termination_by`, compiled at this version through the
   fuel-based `WellFounded.Nat.fix`) and is T0; the entry translates it
   with its defining equation at a successor, `Nat.gcd_succ`, which is
   not definitional and is T1 through `Quot.sound` (`funext` in the
   unfolding lemma).

## Coverage

Each feature of the gap catalog
([`gap-catalog.md`](../docs/foundations/gap-catalog.md)), named by its slug
([`SCHEMA.md`](SCHEMA.md), Features), and the entries whose manifest object
lists it are as follows.  The translating sessions listed a feature when
anything in the entry's export uses it, which is the closure rule of
[`SCHEMA.md`](SCHEMA.md), so a feature one shared lemma brings in counts for
every entry whose closure reaches that lemma; the gap report separates each
entry's own uses from those.

<!-- Generated by python3 scripts/python/corpus_tables.py --table coverage -->

| Feature | Entries | Count |
| --- | --- | --- |
| `impredicative-prop` | `multiset-map-map`, `set-ext`, `finset-card-image`, `real-sqrt-nonneg`, `subgroup-card-dvd`, `order-hom-map-lfp`, `substructure-closure-le` | 7 |
| `proof-irrelevance` | `finset-card-image`, `subtype-coe-eta` | 2 |
| `k-and-uip` | every entry but `list-reverse-reverse` and `set-ext` | 10 |
| `large-elimination` | every entry but `list-reverse-reverse` and `set-ext` | 10 |
| `quotients` | `multiset-map-map`, `set-ext`, `finset-card-image`, `real-sqrt-nonneg`, `subgroup-card-dvd`, `order-hom-map-lfp`, `substructure-closure-le` | 7 |
| `axioms` | every entry but `subtype-coe-eta` | 11 |
| `universe-levels` | every entry | 12 |
| `structure-eta` | `lists-subset-refl`, `finset-card-image`, `real-sqrt-nonneg`, `subgroup-card-dvd` | 4 |
| `literals` | every entry but `list-reverse-reverse`, `multiset-map-map`, `set-ext`, and `subtype-coe-eta` | 8 |
| `trust-escape-hatches` | none | 0 |
| `decidable-and-noncomputable` | every entry but `list-reverse-reverse`, `multiset-map-map`, `set-ext`, and `subtype-coe-eta` | 8 |
| `nested-and-mutual-inductives` | `lists-subset-refl`, `finset-card-image`, `real-sqrt-nonneg`, `subgroup-card-dvd`, `order-hom-map-lfp`, `substructure-closure-le` | 6 |
| `projections-and-let` | every entry | 12 |

No entry exercises the trust escape hatches (`native_decide`,
`implemented_by`, `partial`, `unsafe`, `sorryAx`), and none can: a
declaration that uses one is T3, which the translator refuses and reports, so
there is no translation to write.  Testing the refusal is the work of M7's
soundness-bug suite.  Two expectations of the selection rested on secondary
sources, and the translations settled both.  The first, that the defining
equation of `Nat.gcd` needs K-like reduction in Lean's kernel (Lean4Less's
README says so), does not hold at the pin: the equation is not definitional
there, and no K-like reduction is involved
([`nat-gcd-succ/notes.md`](nat-gcd-succ/notes.md)).  The second, that the
lattice and model-theory entries use impredicativity essentially, holds only
for the definitions of the model-theory entry: Mathlib's infimum of
substructures and its `closure` have no predicative assignment of levels,
while `closure_le` itself, and the lattice entry's theorem, hold at a choice
of levels
([`substructure-closure-le/notes.md`](substructure-closure-le/notes.md),
[`order-hom-map-lfp/notes.md`](order-hom-map-lfp/notes.md)).

## Checking

`make corpus-check`, in the default shell (`nix develop`), runs
`scripts/python/corpus_check.py`.  It validates the manifest against the
rules of [`SCHEMA.md`](SCHEMA.md), runs the shell's `agda` on every file of
every `translated` entry from that entry's `agda/` directory, under the flags
the file declares and no others, with a per-file timeout (`CORPUS_TIMEOUT`,
300 seconds by default), and prints one row per entry and a summary.  It
exits with status 1 if a checked entry fails or an entry is malformed;
`planned` entries are listed, not failed.  `--json` prints the same report as
JSON, with a record for every file.  On 2026-10-12, with all twelve entries
translated, it printed the following (Agda 2.8.0, with no `.agdai` interface
files of the corpus left from an earlier run, at load averages of 1.51 before
and 3.48 after):

```text
$ make corpus-check
| id                      | status     | result | seconds |
| ----------------------- | ---------- | ------ | ------- |
| list-reverse-reverse    | translated | pass   | 4.9     |
| nat-gcd-self            | translated | pass   | 4.5     |
| nat-gcd-succ            | translated | pass   | 4.4     |
| lists-subset-refl       | translated | pass   | 2.6     |
| multiset-map-map        | translated | pass   | 17.5    |
| set-ext                 | translated | pass   | 4.7     |
| finset-card-image       | translated | pass   | 9.2     |
| real-sqrt-nonneg        | translated | pass   | 0.3     |
| subgroup-card-dvd       | translated | pass   | 11.7    |
| order-hom-map-lfp       | translated | pass   | 0.4     |
| subtype-coe-eta         | translated | pass   | 0.6     |
| substructure-closure-le | translated | pass   | 1.2     |

12 entries: 12 checked (12 passed, 0 failed), 0 planned, 0 malformed.
```

When a file fails, the row names its first error, and Agda's whole
output for the file follows the table; a malformed entry's row names
its first problem, and every problem is listed below the table.

## Translating an entry

A session that translates a planned entry does the following, from the
repository root, inside `nix develop`:

1. Write `corpus/<id>/lean/Statement.lean`: the statement quoted from
   its source with path and line, and `#check` and `#print axioms` for
   the declaration (the seed entry's file is the model).  Run it from
   `translator/` with `lake env lean ../corpus/<id>/lean/Statement.lean`
   and correct the manifest's `axioms` and `tier` if they differ.
2. Export the kernel term, from `translator/`, as follows:

   ```sh
   lake exe lean4export <lean_module> -- <lean_name> > ../corpus/<id>/lean/term.ndjson
   ```

   If the export is larger than 1 MB, replace it by
   `lean/term.sidecar.json` ([`SCHEMA.md`](SCHEMA.md) says what goes in
   it).  Mathlib's cache must be in place first (`make lean-cache`; see
   [`../translator/README.md`](../translator/README.md)).
3. Write the Agda files the manifest names under `corpus/<id>/agda/`,
   each with its `OPTIONS` pragma at the top, before the module
   declaration, or change `agda_files` if the plan was wrong.
4. Write `corpus/<id>/notes.md` from the template, and correct the
   manifest's `features` by what the kernel term turned out to use.
5. Set the entry's `status` to `translated` and run
   `make corpus-check`.

[#6]: https://github.com/formalverification/lean2agda/issues/6
[#7]: https://github.com/formalverification/lean2agda/issues/7
[#8]: https://github.com/formalverification/lean2agda/issues/8
[#9]: https://github.com/formalverification/lean2agda/issues/9
[#10]: https://github.com/formalverification/lean2agda/issues/10
