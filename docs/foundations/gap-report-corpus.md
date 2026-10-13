<!-- File: docs/foundations/gap-report-corpus.md -->

# The gap report from the hand translations

What the twelve hand translations of the corpus needed, feature by feature of
the gap catalog ([`gap-catalog.md`][catalog]): for every catalog entry, how
many corpus entries exercised it, what it cost, and what the translator will
have to do (issue [#10]).  ADR 0001 ([#12]) is to cite it as evidence, and its
section on the two encodings of `Prop` is the corpus's evidence for [#27].

Everything here was read on 2026-10-12 from the repository at commit `9f83acd`,
whose pins are Lean v4.33.1, Mathlib v4.33.1, Agda 2.8.0, agda-stdlib 2.3 and
the cubical library 0.9 ([`../pinning.md`][pinning]).  No figure was measured
for this report beyond the sizes of the corpus's own files, which a script
prints.  The text names the source of every other figure, and the sources are
as follows:

+  [`corpus/manifest.json`][manifest], for each entry's features, tier and Agda
   files;
+  each entry's `notes.md`, cited as "the notes of `<id>`" with the section,
   and its Agda files;
+  the gap catalog and its probes, and the register of findings about Lean's
   internals, [`lean-findings.md`][lean-findings], cited by entry (LF-n);
+  the printer's report, [`printing-blowup-2026-10-12.md`][blowup], and its
   companion [`printing.md`][printing], for the only mechanical renderings at
   the pin.

The tables marked as generated are printed by `make corpus-tables`
([`corpus_tables.py`][tables-script]) from the manifest and the entries' files,
each under a comment that names the command; a ratio is computed from the
figures beside it.

**Terms**.  The catalog's Terms take the first three of these from the roadmap
and the related-work survey; in brief, they are as follows:

+  A **profile** is a set of Agda flags and what stays a module parameter: U is
   `--type-in-type` with postulates allowed, scaffolding only; K is `--safe`,
   with Agda's default K; CC is `--safe --cubical-compatible`, which implies
   `--without-K`; CU is `--safe --cubical`.  A file may add flags its profile
   allows, as `SubtypeCoeEtaProp.agda` adds `--prop` under CC.
+  A declaration's **tier** follows from its axioms: T0 none, T1 `propext` or
   `Quot.sound`, T2 `Classical.choice`, T3 anything else.
+  **K-like reduction** lets the recursor of an inductive proposition with one
   constructor and no fields, such as `Eq.rec`, reduce on any major premise
   whose type is the constructor's, not only on the constructor; **Lean4Less**,
   Deducteam's normalizer, removes it and definitional proof irrelevance from
   Lean terms by inserting casts.

This report adds the following:

+  An **entry** is a directory of the corpus, which translates one Lean
   declaration (`nat-gcd-succ` translates `Nat.gcd` together with its equation
   `Nat.gcd_succ`).
+  The entries come in groups, named by the issue that translated them, which
   the matrix's Issue column shows: [#7] owns `list-reverse-reverse`,
   `nat-gcd-self`, `nat-gcd-succ` and `lists-subset-refl` ([#70]; the first was
   translated on its behalf by M1-6, [#6], in [#66]); [#8] `multiset-map-map`
   and `set-ext` ([#69]); and [#9] the other six in two parts, part 1
   `finset-card-image`, `order-hom-map-lfp` and `subtype-coe-eta` ([#75]), and
   part 2 `real-sqrt-nonneg`, `subgroup-card-dvd` and `substructure-closure-le`
   ([#76]).  The **core-Lean entries** are the three whose declarations are in
   Lean's core library: `list-reverse-reverse`, `nat-gcd-self` and
   `nat-gcd-succ`.
+  An entry's **export** is lean4export's NDJSON of the declaration and of
   every constant it reaches through types, values, constructors and recursors,
   which is its **closure**.  An export over 1 MB is recorded by a sidecar that
   keeps its size and hash ([`SCHEMA.md`][schema]).
+  An entry **exercises** a feature when the manifest lists it.  The manifest
   follows the schema's **closure rule**: a feature counts when "the
   declaration, the definitions it unfolds, and the lemmas it cites" use it in
   a way the translation has to handle, and the translating sessions applied
   the rule to the whole export.
+  A **carrier** is a shared declaration that brings a feature into many
   closures though no entry's statement mentions it: `eq_of_heq`, `funext`, the
   syntax tree of a tactic default, a generic lemma used where an `imax` is
   zero, the machinery of a tactic library, `simp`'s `eq_self`, and the
   recursion and matchers Lean compiles for every inductive type.  A use is
   **carried** when the notes attribute it only to carriers, even one the proof
   names, **unclassified** when they count it over the closure without
   attributing it, and the entry's **own** otherwise: its statement, the
   definitions the statement names, or the lemmas other than carriers that its
   proof rests on.  The classes follow what the notes recorded, since that is
   where the evidence is.
+  The **idiomatic Agda** is an entry's hand-written files; a **direct** proof
   in them follows the kernel term step by step.  Sizes count a file's lines,
   its **lines of code** (lines holding a token other than whitespace or a
   comment, the `OPTIONS` pragma included) and its bytes.
+  A **mechanical rendering** is Agda printed from a kernel term by a program.
   The **scaffold** is what the printer of [#17] writes with `--out`: every
   type of the closure and the value of the root, under profile U, with
   postulates standing for the other values.
+  **Encoding A** and **encoding B** are [#27]'s.  A maps each proposition to
   an h-proposition in `Set`, a type with a witness that any two of its
   elements are equal, written `Ω p = Σ (Set p) Irrelevant` in the corpus; B
   maps it to Agda's `Prop` universe under `--prop`.  The catalog's entries
   `proof-irrelevance` and `large-elimination` use the two letters the other
   way round (Corrections, below).

## Findings

+  **The coverage table is nearly flat, and a few carriers make it so**.  By
   the manifest, `universe-levels` and `projections-and-let` are exercised by
   all twelve entries, `axioms` by eleven, and `k-and-uip` and
   `large-elimination` by ten.  `eq_of_heq`, whose proof is K-like reduction on
   a universe, is in ten closures, and so is `funext`, whose proof computes
   with `Quot.lift`; the syntax trees of tactic defaults bring a nested
   inductive type and string literals into five.  A translator meets each
   carrier once, in the declaration that carries it, not once per entry.
+  **What the mathematics needed is short**.  Impredicativity as a choice of
   level in five entries, essential only in the definitions of
   `substructure-closure-le`; the computation rule of `Quot.lift` in three,
   each use made a rewrite by the parameter record's `lift-β`; K-like reduction
   in one Mathlib proof (`Lists'.of_toList`), replaced by Hedberg's theorem for
   `Bool`; definitional proof irrelevance in the two proofs where the corpus
   read it (`Subtype.ext` and `Finset.eq_of_veq`, of which the Agda translates
   the first), though no tool measured it anywhere; structure eta in Mathlib's
   own proofs in three entries, which Agda's records give for free; and
   `Classical.choice` in the data of two entries' definitions (`NNReal.sqrt`,
   `Nat.card` with `Quotient.out`) and in the proofs only of two more.
+  **The Agda needed no postulate, no K and few parameters**.  All sixteen
   files check under `--safe`, fourteen under profile CC and two under CU, with
   no postulate.  Four entries take principles as module parameters (`set-ext`,
   `multiset-map-map`, `finset-card-image`, `subgroup-card-dvd`).  Three T2
   statements are proved with no classical principle, each in its own way:
   `finset-card-image` by Lean's proof with its classical lemmas proved
   constructively, `substructure-closure-le` for two predicative closures in
   place of Mathlib's impredicative one, and `real-sqrt-nonneg` over a record
   of the reals, which a one-point instance shows adds no logical strength.
   The fourth, `subgroup-card-dvd`, has a constructive file for finite groups
   beside its classical one.
+  **The closure, not the statement, sets the export's size**.  Exports run
   from 29,267 bytes (`set-ext`) to 41,933,263 (`real-sqrt-nonneg`), while
   the idiomatic files hold 16 to 289 lines of code; the largest export's
   file has 50.
+  **No mechanical rendering of a whole entry checks yet**.  The printer of
   [#17] renders every type and value of the three core-Lean closures in 0.22
   (`list-reverse-reverse`), 0.49 (`nat-gcd-succ`) and 0.61 (`nat-gcd-self`) of
   their exports' bytes, and Agda, under profile U's `--type-in-type`, checks
   17 of 21, 104 of 201 and 139 of 266 of their values.  The scaffolds of all
   twelve entries take 0.08 to 0.19 of their exports' bytes and pass Agda's
   scope check, but only the three core-Lean ones are type-checked, each with
   refusals, and the scope check alone grows much faster than the scaffold: 6.0
   seconds for 0.7 MB, 186.5 for 3.0 MB and 1,652.4 for 7.5 MB.  The ratio
   [#10] asks for, against the renderings attempted, is 0.08 to 0.19 for the
   scaffolds and 0.22 to 0.61 for the three full renderings; against a
   rendering Agda accepts it is not yet measurable.  M2-9 ([#23]) and M5-2
   ([#44]) will measure that, and M5-1 ([#43]) the cost of checking.
+  **On the two encodings, the corpus shows the costs, not the verdict**.
   Seven entries read Lean's `Prop` as encoding A does, though only three files
   use its witnesses in a proof; five read Lean's propositions as
   proof-relevant types in `Set` with no witness; and one entry was written
   under encoding B as well.  B gave that entry's one proof-irrelevance
   conversion by `refl` where A needed its witness, and it would give two of
   A's other lemmas by definition; it needed a second copy where a level may be
   zero, and under `--cubical-compatible` it meets matches that Agda warns
   about or, on one probe, refuses.  The counts that decide are [#27]'s, and
   the encodings section lists the ones the corpus could not take, in the order
   that saves work.
+  **Corrections**.  The manifest omits `quotients` for three of the four
   entries of [#7], whose closures hold `funext`; the catalog still swaps the
   encoding letters; and four smaller items are listed under Corrections.

## The coverage table

<!-- Generated by python3 scripts/python/corpus_tables.py --table matrix -->

Columns: `imp` `impredicative-prop`, `pi` `proof-irrelevance`, `K` `k-and-uip`,
`elim` `large-elimination`, `quot` `quotients`, `ax` `axioms`, `lvl`
`universe-levels`, `eta` `structure-eta`, `lit` `literals`, `hatch`
`trust-escape-hatches`, `dec` `decidable-and-noncomputable`, `mut`
`nested-and-mutual-inductives`, `proj` `projections-and-let`.

| Entry | Issue | Tier | imp | pi | K | elim | quot | ax | lvl | eta | lit | hatch | dec | mut | proj | Features |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `list-reverse-reverse` | [#7] | T1 |  |  |  |  |  | ✓ | ✓ |  |  |  |  |  | ✓ | 3 |
| `nat-gcd-self` | [#7] | T1 |  |  | ✓ | ✓ |  | ✓ | ✓ |  | ✓ |  | ✓ |  | ✓ | 7 |
| `nat-gcd-succ` | [#7] | T1 |  |  | ✓ | ✓ |  | ✓ | ✓ |  | ✓ |  | ✓ |  | ✓ | 7 |
| `lists-subset-refl` | [#7] | T1 |  |  | ✓ | ✓ |  | ✓ | ✓ | ✓ | ✓ |  | ✓ | ✓ | ✓ | 9 |
| `multiset-map-map` | [#8] | T1 | ✓ |  | ✓ | ✓ | ✓ | ✓ | ✓ |  |  |  |  |  | ✓ | 7 |
| `set-ext` | [#8] | T1 | ✓ |  |  |  | ✓ | ✓ | ✓ |  |  |  |  |  | ✓ | 5 |
| `finset-card-image` | [#9] | T2 | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |  | ✓ | ✓ | ✓ | 12 |
| `real-sqrt-nonneg` | [#9] | T2 | ✓ |  | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |  | ✓ | ✓ | ✓ | 11 |
| `subgroup-card-dvd` | [#9] | T2 | ✓ |  | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |  | ✓ | ✓ | ✓ | 11 |
| `order-hom-map-lfp` | [#9] | T1 | ✓ |  | ✓ | ✓ | ✓ | ✓ | ✓ |  | ✓ |  | ✓ | ✓ | ✓ | 10 |
| `subtype-coe-eta` | [#9] | T0 |  | ✓ | ✓ | ✓ |  |  | ✓ |  |  |  |  |  | ✓ | 5 |
| `substructure-closure-le` | [#9] | T2 | ✓ |  | ✓ | ✓ | ✓ | ✓ | ✓ |  | ✓ |  | ✓ | ✓ | ✓ | 10 |
| Entries | | | 7 | 2 | 10 | 10 | 7 | 11 | 12 | 4 | 8 | 0 | 8 | 6 | 12 | |

The same counts, with each feature's entries named, are
[`corpus/README.md`][corpus-readme]'s Coverage table, which
`make corpus-tables` prints too and a test keeps equal to the manifest.
Reading the marks needs five cautions, as follows:

+  **A mark counts the closure**.  It says that something in the export uses
   the feature, which is what a translator of the whole closure meets.  The
   notes say, feature by feature, which uses are an entry's own and which come
   with the closure; the next two sections and the gap sections use that split.
+  **Definitional proof irrelevance is measured nowhere**.  The kernel's
   diagnostics count reductions, not the conversions proof irrelevance decides,
   and the elaborator's switch `proofIrrelevance := false` still identifies
   proofs in argument position (LF-4).  The two marks in that column are read
   from terms (`Subtype.ext`'s match, `Finset.eq_of_veq`), so its blanks mean
   not read and its count is a lower bound, not a frequency; Lean4Less ([#26])
   is the instrument that will count the rest.
+  **A `k-and-uip` mark is a reading of a count**.  The kernel counts every
   reduction of a recursor that admits K-like reduction, ordinary ones
   included, so a zero is conclusive (`list-reverse-reverse`, `set-ext`) and a
   positive count was read in the term.  The readings are `eq_of_heq` in ten
   entries and `Lists'.of_toList` in one; 2, 7, 16 and 16 further declarations
   that reduce `Eq.rec` in `lists-subset-refl`, `finset-card-image`,
   `real-sqrt-nonneg` and `subgroup-card-dvd` were not read, the last two left
   for Lean4Less to classify.
+  **A blank in the `eta` column is a measurement or a reading**.  The
   elaborator's test with `etaStruct := .none` found no use in six closures,
   and `multiset-map-map` and `set-ext` were read and not tested (the
   `structure-eta` section).
+  **The rule was applied unevenly once**.  Three of the four entries of [#7]
   (all but `list-reverse-reverse`) carry `funext`, whose proof computes with
   `Quot.lift` (measured in `set-ext`'s closure, and among the refusals of
   `nat-gcd-self`'s rendered values in [`printing.md`][printing]), but do not
   list `quotients`, which two entries of [#9] count for the same carrier
   (`order-hom-map-lfp`, `substructure-closure-le`).  By their reading
   `quotients` would count ten entries, not seven.

## Where the features come from

The carriers, what each brings, which closures it reaches, and what the hand
translations did with it, from each entry's notes (What the kernel term
needed):

| Carrier | Features it brings | Closures it reaches | In the hand translations |
| --- | --- | --- | --- |
| `eq_of_heq`, whose proof is K-like reduction of `Eq.rec` on a variable `h : α = α` (uniqueness of identity proofs on a universe, LF-5), with `cast` | `k-and-uip`, `large-elimination` | 10: every entry but `list-reverse-reverse` and `set-ext` | never cited; it arrives through compiled matchers on indexed families (`Nat.le_trans`), constructor injectivity (`Option.some.inj`, `List.cons.inj`) and `noConfusion`, which Agda's pattern matching replaces |
| `funext`, whose proof reduces `Quot.lift` twice under a binder | `quotients`, and `Quot.sound` under `axioms` | 10: every entry but `list-reverse-reverse` and `subtype-coe-eta` | a parameter `FunExt` (`set-ext`, `finset-card-image`, `subgroup-card-dvd`) or not cited; a propositional `lift-β` cannot replay its proof (the notes of `set-ext`) |
| `autoParam` and `f._auto_<n>`, a tactic default's `Lean.Syntax` tree in a field's or an argument's type | `nested-and-mutual-inductives`, string `literals`, `decidable-and-noncomputable`; in `order-hom-map-lfp` also `k-and-uip` and `large-elimination` | 5: `finset-card-image`, `real-sqrt-nonneg`, `subgroup-card-dvd`, `order-hom-map-lfp`, `substructure-closure-le` | absent: Agda's records carry no tactic defaults |
| a generic lemma used where an `imax` in its type is zero (`Option.noConfusion`, `List.cons.noConfusion.{0,u_1}`, `implies_congr.{0, 0}`) | `impredicative-prop` | 5: `multiset-map-map`, `finset-card-image`, `real-sqrt-nonneg` (131 uses), `subgroup-card-dvd` (83), `substructure-closure-le` (10) | not cited |
| tactic libraries: `grind`'s ring solver, `omega`, `Nat.Internal.Linear`, `Lean.Data.AC` | `structure-eta` (two `Nat.Internal.Linear` lemmas), `literals`, unclassified `Eq.rec` reductions, two opaque constants (`String.Internal.append`, `Lean.opaqueId`) | 4: `finset-card-image`, `real-sqrt-nonneg`, `subgroup-card-dvd`, and `substructure-closure-le` through `Lean.Data.AC` | not cited |
| `simp`'s `eq_self`, which closes `a = a` by rewriting it to `True` | `axioms` (`propext`) | the only source of `list-reverse-reverse`'s T1; among the sources in `nat-gcd-self`, `lists-subset-refl` and `multiset-map-map` | `refl` |
| recursion and matchers compiled for every inductive type (`brecOn` with its `PProd` projections, `ctorIdx`, `noConfusionType`) | `projections-and-let`, `literals` and `decidable-and-noncomputable` (in `lists-subset-refl`) | every entry with a structural recursion or a constructor case | pattern matching, and constructor disjointness in unification |

Cutting `autoParam` from the closure was measured in all five (the notes of
each, What the kernel term needed): from 514 constants to 194 in
`order-hom-map-lfp`, and by 0.3 to 2.4 percent in the others, 3,267 to 3,258
(`finset-card-image`, the field form only), 10,721 to 10,628
(`real-sqrt-nonneg`), 6,684 to 6,618 (`subgroup-card-dvd`) and 1,767 to 1,725
(`substructure-closure-le`).  So the syntax trees make `order-hom-map-lfp`'s
closure large and not the others'; of the four whose notes name what remains,
`funext` stays in all four and `eq_of_heq` in all but `order-hom-map-lfp`'s.

## Sizes

<!-- Generated by python3 scripts/python/corpus_tables.py --table sizes -->

| Entry | Export bytes | Agda file | Profile | Lines | Code lines | Agda bytes |
| --- | --- | --- | --- | --- | --- | --- |
| `list-reverse-reverse` | 56,062 | `ListReverseReverse.agda` | CC | 50 | 18 | 2,062 |
| `nat-gcd-self` | 684,821 | `NatGcdSelf.agda` | CC | 45 | 16 | 2,118 |
| `nat-gcd-succ` | 527,857 | `NatGcdSucc.agda` | CC | 113 | 40 | 5,079 |
| `lists-subset-refl` | 441,284 | `ListsSubsetRefl.agda` | CC | 198 | 90 | 8,914 |
| `multiset-map-map` | 236,925 | `MultisetMapMap.agda` | CC | 139 | 63 | 6,724 |
| | | `MultisetMapMapCubical.agda` | CU | 124 | 66 | 5,353 |
| `set-ext` | 29,267 | `SetExt.agda` | CC | 69 | 29 | 2,508 |
| | | `SetExtCubical.agda` | CU | 92 | 45 | 3,796 |
| `finset-card-image` | 13,406,809 (sidecar) | `FinsetCardImage.agda` | CC | 397 | 233 | 18,745 |
| `real-sqrt-nonneg` | 41,933,263 (sidecar) | `RealSqrtNonneg.agda` | CC | 133 | 50 | 5,533 |
| `subgroup-card-dvd` | 24,928,106 (sidecar) | `SubgroupCardDvd.agda` | CC | 495 | 289 | 21,441 |
| | | `SubgroupCardDvdFinite.agda` | CC | 421 | 280 | 17,822 |
| `order-hom-map-lfp` | 964,985 | `OrderHomMapLfp.agda` | CC | 149 | 74 | 6,090 |
| `subtype-coe-eta` | 46,536 | `SubtypeCoeEta.agda` | CC | 76 | 25 | 3,169 |
| | | `SubtypeCoeEtaProp.agda` | CC | 78 | 31 | 3,004 |
| `substructure-closure-le` | 4,267,999 (sidecar) | `SubstructureClosureLe.agda` | CC | 273 | 100 | 12,114 |

The export bytes are the size of the committed `lean/term.ndjson` or the size
its sidecar records.  The lines of code differ by one from the notes of
`real-sqrt-nonneg`, `subgroup-card-dvd` (both files) and
`substructure-closure-le`, which do not count the `OPTIONS` line.

The mechanical renderings at the pin are the scaffolds of [#17], printed and
scope-checked for every entry by `make scaffold-corpus`
([`printing-blowup-2026-10-12.md`][blowup], Every corpus entry):

| Entry | Export bytes | Scaffold constants | Scaffold bytes | Over the export | Scope check, seconds |
| --- | --- | --- | --- | --- | --- |
| `list-reverse-reverse` | 56,062 | 41 | 6,123 | 0.11 | 0.1 |
| `nat-gcd-self` | 684,821 | 334 | 84,449 | 0.12 | 0.9 |
| `nat-gcd-succ` | 527,857 | 271 | 63,073 | 0.12 | 0.9 |
| `lists-subset-refl` | 441,284 | 219 | 44,773 | 0.10 | 0.5 |
| `multiset-map-map` | 236,925 | 110 | 19,935 | 0.08 | 0.2 |
| `set-ext` | 29,267 | 26 | 3,978 | 0.14 | 0.1 |
| `finset-card-image` | 13,406,809 | 3,367 | 1,147,851 | 0.09 | 49.8 |
| `real-sqrt-nonneg` | 41,933,263 | 11,036 | 7,529,204 | 0.18 | 1,652.4 |
| `subgroup-card-dvd` | 24,928,106 | 6,918 | 3,040,759 | 0.12 | 186.5 |
| `order-hom-map-lfp` | 964,985 | 570 | 185,528 | 0.19 | 0.6 |
| `subtype-coe-eta` | 46,536 | 20 | 4,957 | 0.11 | 0.0 |
| `substructure-closure-le` | 4,267,999 | 1,879 | 692,061 | 0.16 | 6.0 |

The scaffold's constants are counted by the printer's own selection of the
closure, and the closures in the notes by their probe's walk, which misses the
constants lean4export adds for a string literal (the notes of
`order-hom-map-lfp`); the two are not compared here.

Full renderings, every type and every value at the default sharing threshold of
32, exist for the three core-Lean entries (the same report, Size against the
threshold): 12,401, 257,530 and 417,558 bytes for `list-reverse-reverse`,
`nat-gcd-succ` and `nat-gcd-self`, which are 0.22, 0.49 and 0.61 of their
exports and 6.0, 50.7 and 197.1 times the bytes of their idiomatic files.  Agda
checks 17 of the 21 values of the first, 104 of 201 and 139 of 266; it refuses
4, 41 and 54, every one a conversion that needs a definition unfolded or a
recursor computed, the emitters' work in [#18] to [#21], and leaves 0, 56 and
73 unchecked behind a refused type.  The one other mechanical rendering on
record is lyphyser's `examples/Nat.gcd_self.agda`, 6,942 lines made under an
older Lean whose `gcd` compiled through `WellFounded.fix`, against the 45
lines, 16 of them code, of `NatGcdSelf.agda` (the notes of `nat-gcd-self`,
Sizes and Remarks).

Reading these figures as ratios needs four cautions, as follows:

+  a scaffold holds types and one value, so its share of the export (0.08 to
   0.19) is not the share a rendering of the proofs would take;
+  the export is a text format (63 to 67 bytes a record for the three core-Lean
   entries, by the same report), not the `.olean` term size the roadmap names,
   which [#44] is to use;
+  the idiomatic files are about half comments and blank lines (1,449 of their
   2,852 lines are code) and abstract what the closure builds (the reals record
   of `real-sqrt-nonneg` stands for 10,169 declarations), so their size
   measures the distance between Mathlib's proof and a proof by hand, not a
   translation's overhead;
+  Agda's scope check grows faster than the scaffold, and not with its size
   alone: 6.0 seconds for `substructure-closure-le`'s 0.7 MB, 49.8 for
   `finset-card-image`'s 1.1 MB, 186.5 for `subgroup-card-dvd`'s 3.0 MB and
   1,652.4 for `real-sqrt-nonneg`'s 7.5 MB, each in one module, which the
   modules per Lean module of [#22] and the performance study of [#43] are to
   address.

## The gaps at a glance

For each feature, the entries that exercise it, where the notes trace those
uses, and its smallest example: the entry with the smallest export among those
whose own statement or proof uses it, with the sizes of its export, its
scaffold and its idiomatic Agda (lines of code, then bytes).

| Feature | Entries | Own, carried, unclassified | Smallest example | Export bytes | Scaffold bytes (share) | Idiomatic Agda |
| --- | --- | --- | --- | --- | --- | --- |
| `impredicative-prop` | 7 | 5 own, 2 carried | `set-ext` | 29,267 | 3,978 (0.14) | 29 (2,508) |
| `proof-irrelevance` | 2 | 2 own, read in terms; measured nowhere | `subtype-coe-eta` | 46,536 | 4,957 (0.11) | 25 (3,169) under A, 31 (3,004) under B |
| `k-and-uip` | 10 | 1 own, 7 carried, 2 unclassified | `lists-subset-refl` | 441,284 | 44,773 (0.10) | 90 (8,914) |
| `large-elimination` | 10 | 4 own, 4 carried, 2 unclassified | `lists-subset-refl` | 441,284 | 44,773 (0.10) | 90 (8,914) |
| `quotients` | 7 | 4 own, 3 carried | `multiset-map-map` | 236,925 | 19,935 (0.08) | 63 (6,724) under CC, 66 (5,353) under CU |
| `axioms` | 11 | principles as parameters in 4 entries' Agda, the reals as a record in 1, none in 6 | `set-ext` | 29,267 | 3,978 (0.14) | 29 (2,508) |
| `universe-levels` | 12 | 11 own, 1 unclassified | `set-ext` | 29,267 | 3,978 (0.14) | 29 (2,508) |
| `structure-eta` | 4 | 3 own, 1 carried | `lists-subset-refl` | 441,284 | 44,773 (0.10) | 90 (8,914) |
| `literals` | 8 | 3 own, 3 carried, 2 unclassified | `nat-gcd-succ` | 527,857 | 63,073 (0.12) | 40 (5,079) |
| `trust-escape-hatches` | 0 | none, by design | none | | | |
| `decidable-and-noncomputable` | 8 | 6 own, 2 carried | `nat-gcd-succ` | 527,857 | 63,073 (0.12) | 40 (5,079) |
| `nested-and-mutual-inductives` | 6 | 1 own, 5 carried | `lists-subset-refl` | 441,284 | 44,773 (0.10) | 90 (8,914) |
| `projections-and-let` | 12 | own in most statements (class and structure projections); carried by compiled recursion | `set-ext` | 29,267 | 3,978 (0.14) | 29 (2,508) |

The gap sections name every entry behind each count.

## The gaps

### `impredicative-prop`

(See also [`impredicative-prop`][cat-impredicative-prop], [#28] and [#29].)

+  **Exercised by** seven entries.  In five the statement, or a definition it
   names, quantifies over a type inside a proposition, and the Agda places the
   result at a level: `set-ext` (Lean's `Set α` lives in the universe of `α`,
   the Agda `ℙ A p` in `Set (a ⊔ suc p)`), `finset-card-image`
   (`Function.Injective f` at `a ⊔ b`), `subgroup-card-dvd`
   (`Subgroup p : Set (a ⊔ suc p)`), `order-hom-map-lfp` (the infimum's
   subsets, its law, and the pointwise order on maps) and
   `substructure-closure-le` (the infimum of substructures).  In
   `multiset-map-map` and `real-sqrt-nonneg` the feature is carried, by
   `Option.noConfusion` used at a proposition and by 131 such uses in lemmas
   about sets and filters.
+  **What it cost**.  In four of the five the use is inessential: the statement
   holds at every level, and the file leaves the level free (`set-ext`'s
   `ℙ A p`, `subgroup-card-dvd`'s `Subgroup p`), lets Agda compute it
   (`finset-card-image`), or picks one and splits a law whose statement lands a
   level up (`order-hom-map-lfp` takes `isGLB_sInf` as its two halves,
   `⋀-lower` and `⋀-greatest`, because `lowerBounds` is a subset one level
   above the ones its `⋀` takes).  The fifth is essential in its definitions:
   Mathlib's `Substructure.instInfSet` and `closure` have no predicative
   assignment of levels, since the infimum's carrier would have to land at the
   level it ranges over, `suc p ≤ p`.  The theorem `closure_le` survives in two
   predicative forms, the infimum one universe up and agda-algebras's inductive
   `Sg`, which stays at the absorbing level `u ⊔ w ⊔ p` and is the lower
   adjoint (the notes of `substructure-closure-le`, Impredicativity and
   levels).  That is the settlement `corpus/README.md`'s Coverage section now
   records: `order-hom-map-lfp`'s use is inessential, and
   `substructure-closure-le`'s is essential in its definitions only.  The
   kernel term records none of these levels, since the kernel computes
   `imax (u+1) 0 = 0` itself (the notes of `order-hom-map-lfp`).
+  **What the translator will have to do**.  Specialize each constant by which
   of its level parameters are zero, which removes the carried `imax` uses
   (M3-3, [#28]); compute the level of every proposition whether or not an
   `imax` marks it, choose the level of each record's infimum from its uses,
   and report `instInfSet` and `closure` as essentially impredicative (M3-4,
   [#29]).

### `proof-irrelevance`

(See also [`proof-irrelevance`][cat-proof-irrelevance], [#26] and [#27].)

+  **Exercised by** two entries, both read from terms.  In `subtype-coe-eta`
   the match of `Subtype.ext` has one case, `rfl`, which the kernel accepts
   only by identifying two proofs of `p val`; in `finset-card-image`,
   `Finset.eq_of_veq` matches two finite sets the same way, reached through the
   coercion `↑s` in the proof.  The corpus measured the rule nowhere else, for
   the reason under The coverage table, and the old compilation of `Nat.gcd`
   shows where it hides: a copy compiled through `WellFounded.fix` satisfies
   its equation by `Eq.refl` only because proof irrelevance identifies two
   `Acc` proofs (the notes of `nat-gcd-succ`; LF-6).
+  **What it cost**.  Under encoding A, one use of the witness that `Ω`
   carries, `cong (mk v) (proj₂ (P v) h₁ h₂)` in `SubtypeCoeEta.agda`'s `ext`,
   where Lean's kernel identifies the proofs by definition; under encoding B,
   nothing, since `coe-eta-direct` is `refl` in `SubtypeCoeEtaProp.agda`.
   `FinsetCardImage.agda` never compares two finite sets, so it needed no
   counterpart.  Where Lean's kernel would identify two `Acc` proofs,
   `NatGcdSucc.agda` proves instead that `gcd`'s result does not depend on its
   accessibility proof (`gcd-acc-irrelevant`), by an induction that needs
   neither K nor `funext`.
+  **What the translator will have to do**.  Make each use an explicit cast
   through Lean4Less, recording the casts per constant (M3-1, [#26]); choose
   the encoding that receives them (M3-2, [#27], and the section on the
   encodings below).

### `k-and-uip`

(See also [`k-and-uip`][cat-k-and-uip], [#19], [#34] and [#55].)

+  **Exercised by** ten entries.  One is the entry's own: `lists-subset-refl`'s
   proof cites `Lists'.of_toList`, which generalizes the index of
   `Lists' α true` to `h : true = b` and transports along it, so that in the
   cases `nil` and `cons'` the kernel reduces a transport along a variable
   `h : true = true` only by K-like reduction (LF-7).  Seven are carried: by
   `eq_of_heq` alone in six (`nat-gcd-self`, `nat-gcd-succ`,
   `multiset-map-map`, `order-hom-map-lfp`, `subtype-coe-eta`,
   `substructure-closure-le`), and in `finset-card-image` by `eq_of_heq` and
   seven equation lemmas of `grind`'s matchers that reduce `Eq.rec` and were
   not read.  Two are unclassified beyond `eq_of_heq`: `real-sqrt-nonneg` and
   `subgroup-card-dvd`, with 16 further declarations each, among them
   `PSigma.eta` and lemmas about `Multiset.pmap`.  In `subtype-coe-eta` the
   matcher uses `eq_of_heq` at level 0, where `cast h a = a` holds by proof
   irrelevance, so a specialization by zero levels removes even that use.
+  **What it cost**.  No Agda file uses K.  `ListsSubsetRefl.agda`'s direct
   proof replaces the K-like step by Hedberg's theorem for `Bool`
   (agda-stdlib's `Decidable⇒UIP`, in `subst-true`), the catalog's strategy for
   profile CC in a concrete case; its idiomatic proof matches at the index
   `true` instead, which needs no K but draws `UnsupportedIndexedMatch` under
   `--cubical-compatible`, a warning the file keeps and its notes report.  The
   uniqueness of identity proofs that Lean has for every type also came due
   through the quotient record (next section): `multiset-map-map`'s `squash`, a
   field of the record; `finset-card-image`'s `ℕ-uip`, agda-stdlib's
   `≡-irrelevant`; and the `Ω-uip` of `finset-card-image` and
   `subgroup-card-dvd`, proved without K from `propext` and `funext` by
   agda-stdlib's `Constant⇒UIP`.
+  **What the translator will have to do**.  Replace the compiled matchers that
   cite `eq_of_heq` by Agda's own pattern matching, as every hand translation
   does, since `eq_of_heq` is uniqueness of identity proofs on a universe and
   has no proof under profile CC (M2-5, [#19]); infer an `isSet` proof for each
   remaining use, by Hedberg's theorem where equality is decidable (M3-9,
   [#34]); list the uses on types that are not sets (M6-5, [#55]).

### `large-elimination`

(See also [`large-elimination`][cat-large-elimination] and [#32].)

+  **Exercised by** ten entries.  Four are the entries' own: the zero case of
   the fuel-based `WellFounded.Nat.fix.go`, which eliminates `False` into
   `Nat`, in the definition of `Nat.gcd` (`nat-gcd-succ`, and `nat-gcd-self`,
   whose statement names `gcd`); the transport `Eq.symm h ▸ l` into the type
   `Lists' α true` in `Lists'.of_toList` (`lists-subset-refl`); and an `Eq.mpr`
   that casts `Equiv.refl` along an equation between types in the data of
   `groupEquivQuotientProdSubgroup` (`subgroup-card-dvd`).  Four are carried by
   `cast` in `eq_of_heq` or by the `autoParam` tree (`multiset-map-map`,
   `finset-card-image`, `order-hom-map-lfp`, `subtype-coe-eta`), and two are
   counts over the closure, 23 uses in `real-sqrt-nonneg` and 13 in
   `substructure-closure-le`.  `Acc` occurs in neither gcd export: at the pin
   `Nat.gcd` recurses on fuel.
+  **What it cost**.  Nothing that needs a principle: `_≡_`, `Acc` and `⊥` are
   in `Set` on the Agda side, where large elimination is pattern matching.
   `NatGcdSucc.agda` writes the fuel's zero case as an absurd pattern and its
   idiomatic `gcd` by recursion on agda-stdlib's `Acc`; `ListsSubsetRefl.agda`
   transports with `subst (Lists′ A)`; `SubgroupCardDvd.agda` uses the
   exactness of the quotient instead and casts no type.  One cost is of time,
   not principle: agda-stdlib's `<-wellFounded` builds accessibility proofs in
   unary, so `gcd 1000000007 998244353 ≡ 1` did not check in 120 seconds, where
   `<-wellFounded-fast` takes about 2 (the notes of `nat-gcd-succ`,
   `literals`).
+  **What the translator will have to do**.  Emit `Eq`, `HEq`, `Acc` and the
   other subsingleton eliminators as types in `Set` and well-founded recursion
   through `Acc` or the fuel-based fixpoint (M3-7, [#32]); a cast between types
   such as `subgroup-card-dvd`'s needs uniqueness of identity proofs on a
   universe under CC and belongs to M6-5 ([#55]).  agda-stdlib's
   `FixPoint.unfold-wfRec` does not fit Lean's pair and measure, an input for
   [#32] (the notes of `nat-gcd-succ`).

### `quotients`

(See also [`quotients`][cat-quotients], [#21], [#30], [#33] and [#52].)

+  **Exercised by** seven entries.  Four are the entries' own:
   `multiset-map-map` (`Multiset` is `Quot` and `map` is `Quot.lift`),
   `finset-card-image` (a finite set is a multiset with a proof),
   `real-sqrt-nonneg` (ℝ is a quotient of Cauchy sequences) and
   `subgroup-card-dvd` (`α ⧸ s`, and cardinals as a quotient of types).  Three
   are carried by `funext` alone: `set-ext`, whose proof names it, and
   `order-hom-map-lfp` and `substructure-closure-le`; and three of the four
   entries of [#7] carry `funext` without listing the feature (The coverage
   table).  By the notes of each (What the kernel term needed), the kernel
   reduces `Quot.lift` in 2 declarations of `multiset-map-map`'s closure (5
   times), 1 of `set-ext`'s (2), 9 of `finset-card-image`'s (24), 53 of
   `real-sqrt-nonneg`'s (136) and 102 of `subgroup-card-dvd`'s (429), and in
   `funext` only in the other two.
+  **What it cost**.  The CC files take Lean's primitives as a parameter
   record, `Quotients`, with seven fields, `Quot`, `mk`, `lift`, `ind`,
   `sound`, the computation rule `lift-β` and `squash`, where a word-for-word
   rendering of Lean's primitives has the first six, because Lean's `Prop` is
   proof irrelevant and Agda's `Set` is not: `ind`'s motive takes values in
   `Ω`, since a motive in all of `Set` proves a section of every quotient map,
   which is Mathlib's `Quot.out` and needs `Classical.choice`; `lift` asks that
   its target be a set; and `squash` makes the quotient one.  Each use of the
   computation rule became a rewrite by the record's `lift-β`: three in
   `multiset-map-map`, through `map-β`; in `finset-card-image`, one at each of
   the three reductions of Lean's `Multiset.card_map` and more in the lemmas
   about `Nodup` and deduplication; and two in `subgroup-card-dvd`, both in
   `exact`.  Lean's proof of `funext` cannot be replayed with rewrites, since
   `lift-β` holds under the binder only pointwise, so `funext` is a parameter
   of its own.  Under CU, the cubical library's set quotients instantiate the
   CC record with `lift-β` by reflexivity, so the record asks for nothing a
   constructive, univalent setting lacks.  The record cannot translate a lift
   into a universe, which is not a set under univalence; none of the corpus's
   Agda files needs one.
+  **What the translator will have to do**.  Postulate the primitives with a
   rewrite rule under profile U (M2-7, [#21]); emit the seven-field record and
   a rewrite by `lift-β` at each reduction the kernel performs (M3-5, [#30]);
   map Lean's `funext` to a parameter beside `propext` rather than translate
   its proof (M3-8, [#33]), which bears on [#30]'s task of checking
   `Init.Core`'s `funext` under profile K with no postulates (the notes of
   `set-ext` leave open whether that task should change); use the cubical set
   quotients under CU (M6-2, [#52]).

### `axioms`

(See also [`axioms`][cat-axioms], [#33], [#36], [#38] and [#39].)

+  **Exercised by** eleven entries, every one but the T0 `subtype-coe-eta`;
   `propext` and `Quot.sound` are in ten axiom sets each and `Classical.choice`
   in four.  Each entry's export declares exactly the axioms `#print axioms`
   prints (the notes' Sizes tables count them), so the under-report of Lean
   issue 15226 affects no entry.
+  **What it cost**.  Six of the eleven entries' Agda takes no principle as a
   parameter, and `real-sqrt-nonneg`'s takes a record of the reals, not a
   principle.  `list-reverse-reverse` is T1 only because `simp` closes a goal
   with `eq_self`, whose proof uses `propext`; `nat-gcd-succ` because its
   equation lemma uses `funext`; `order-hom-map-lfp` through an instance's
   proof field and a lemma's proof the Agda does not cite; and
   `substructure-closure-le` is T2 in Lean and T0 in Agda.  The four that take
   parameters take them as records in `Setω`, each standing for a Lean
   primitive, axiom, theorem or definition: `PropExt` and `FunExt` (`set-ext`,
   `finset-card-image`, `subgroup-card-dvd`), `Quotients` (`multiset-map-map`,
   `finset-card-image`, `subgroup-card-dvd`), and in `subgroup-card-dvd`
   `Truncation` for Lean's `Nonempty`, `Choice` and `Card` for `Nat.card`.
   `propext` must be stated over `Ω`: over all of `Set` it is refutable, since
   `Bool ⇔ ⊤` and a scratch module derived `⊥` from it (the notes of
   `set-ext`).  The two CU files build their entries' CC records (`Quotients`,
   `PropExt`, `FunExt`) with no classical principle, so those parameters are
   jointly satisfiable in a constructive, univalent setting.
+  **What the translator will have to do**.  Thread the parameter records so
   that a module takes only what its declarations use (M3-8, [#33]; M4-3,
   [#38]), and count the declarations whose tier comes from a tactic's
   `eq_self` alone, which would take a parameter for nothing (no open issue
   owns that count; the notes of `list-reverse-reverse` assign it to the atlas
   of M1-11, [#11], now closed).  `Classical.choice` is the next section's.

### `universe-levels`

(See also [`universe-levels`][cat-universe-levels], [#28] and [#29].)

+  **Exercised by** all twelve.  Eleven are the entries' own: nine statements
   have universe parameters, one to three of them, and the statements of
   `nat-gcd-self` and `nat-gcd-succ`, which have none, name `Nat.gcd`, whose
   definition instantiates the polymorphic `WellFounded.Nat.fix.{u, v}`.
   `real-sqrt-nonneg`'s statement has none either, and its notes count 7,372
   universe-polymorphic constants in the closure without attributing them.
+  **What it cost**.  Every level parameter became an Agda `Level`, and the
   records that quantify over levels live in `Setω` (`Quotients`, `PropExt`,
   `FunExt`, `Card`), as Lean's `Quot` serves every universe.  Lean's
   `Sort u_1` ranges over propositions too: under encoding A one statement over
   `A : Set a` covers both cases, while under encoding B
   `SubtypeCoeEtaProp.agda` needs a second record and theorem for `u_1 = 0`.
   One Agda trap is worth a line: a generalized variable `A : Set a` named
   beside the level `a` gets a level of its own, so the corpus binds
   `{A : Set a}` explicitly (the notes of `finset-card-image`).
+  **What the translator will have to do**.  Specialize by zero levels and
   lazily emit the instances (M3-3, [#28]); solve level constraints for the
   rest (M3-4, [#29]).

### `structure-eta`

(See also [`structure-eta`][cat-structure-eta], [#18] and [#32].)

+  **Exercised by** four entries, by the elaborator's test with
   `etaStruct := .none` and its controls.  Three are the entries' own:
   Mathlib's `Lists'.to_ofList` holds at `head :: tail` only by eta for `Sigma`
   (`lists-subset-refl`, LF-7), and the closures of `real-sqrt-nonneg` (29
   declarations, lemmas about Cauchy sequences among them) and
   `subgroup-card-dvd` (19, among them the proofs of `Equiv.sigmaEquivProd` and
   `Equiv.sigmaCongrRight` that `groupEquivQuotientProdSubgroup` composes) use
   it in their mathematics.  In `finset-card-image` it is carried, by two
   `Nat.Internal.Linear` lemmas.  `subtype-coe-eta`, the entry chosen for it,
   does not use it: its statement is eta's content, but Mathlib's proof goes
   through `Subtype.ext`'s match, so the feature was removed from its manifest
   object; `order-hom-map-lfp` and `substructure-closure-le` measured none, as
   did the other three entries of [#7] (LF-7), `multiset-map-map` and `set-ext`
   were read and not measured, and the test could not judge some equation
   lemmas of tactic libraries (30 in `finset-card-image`, 40 in
   `real-sqrt-nonneg`, 31 in `subgroup-card-dvd`, 3 in
   `substructure-closure-le`).
+  **What it cost**.  Nothing: agda-stdlib's `Σ` and `_×_` are records with
   eta, so every use checks as it does in Lean, and `subtype-coe-eta`'s direct
   proofs use record eta on purpose.
+  **What the translator will have to do**.  Emit structure-like inductive
   types as records with eta (M2-4, [#18]) and confirm that record eta covers
   each use the normalizer reports (M3-7, [#32]).

### `literals`

(See also [`literals`][cat-literals], [#17] and [#31].)

+  **Exercised by** eight entries.  Three are the entries' own: the literals
   `0` and `1` of `Nat.gcd`'s definition, which the kernel computes with GMP on
   literal arguments (`nat-gcd-succ`); `Nat.casesAuxOn`'s minor premises at `0`
   and `n + 1`, which the kernel identifies with `Nat.zero` and `Nat.succ n`
   (`nat-gcd-self`); and 338 `Nat` and 116 `String` literals in
   `substructure-closure-le`'s closure, which its notes attribute to `Fin`,
   `Lean.Data.AC` and tactic syntax.  Three are carried: `ctorIdx` numbers for
   the no-confusion machinery (`lists-subset-refl`) and the tactic libraries
   and syntax trees (`finset-card-image`, `order-hom-map-lfp`).  Two are counts
   over the closure: `real-sqrt-nonneg`'s 5,988 `Nat` and 616 `String`
   literals, the `String` ones mostly tactic syntax by its notes, and
   `subgroup-card-dvd`'s 2,668 and 354, unattributed.
+  **What it cost**.  Agda's builtin naturals cover the corpus: both `gcd`
   translations compute `gcd 1000000007 998244353 ≡ 1` by `refl` in about 2
   seconds.  Agda has no builtin `gcd`, so it unfolds where Lean's kernel calls
   GMP.  The premise that `Nat.gcd`'s equation needs K-like reduction does not
   hold at the pin: since Lean v4.27.0 `Nat.gcd` compiles through the
   fuel-based `WellFounded.Nat.fix`, its equation is not definitional, and
   computing it reduces no recursor that admits K-like reduction (LF-6).
+  **What the translator will have to do**.  Literals through `BUILTIN NATURAL`
   and the builtin string type, which [#17] prints; the table of accelerated
   operations, with `Nat.gcd` treated as an ordinary function whose equation is
   a theorem (M3-6, [#31], whose description still says the equation needs
   K-like reduction).  Erasing `autoParam` removes the string literals of the
   syntax trees, which the notes of `order-hom-map-lfp` and `real-sqrt-nonneg`
   find to be most of theirs.

### `trust-escape-hatches`

(See also [`trust-escape-hatches`][cat-trust-escape-hatches], [#20] and [#37].)

+  **Exercised by** no entry, by design: a T3 declaration is refused and
   reported, not translated, so there is nothing to write by hand.  The
   closures hold near misses that are not hatches, as follows: 13 opaque
   constants in `real-sqrt-nonneg`'s, ten of them the `Real.wrapped…` constants
   that `private irreducible_def` makes for Mathlib's real operations, which
   the kernel never unfolds; `String.Internal.append` in four closures and
   `Lean.opaqueId` in three; and five constants with `implemented_by` in each
   of the closures of `real-sqrt-nonneg` and `subgroup-card-dvd` and four in
   `substructure-closure-le`'s, which only compiled code sees (the notes of
   each, What the kernel term needed).  The closures of the three part-2
   entries of [#9] have no `partial` and no `unsafe` constant.
+  **What it cost**.  Nothing.  `RealSqrtNonneg.agda` makes `sqrt`
   Agda-`opaque` and proves its lemma in an `unfolding sqrt` block, mirroring
   Lean's `unfold sqrt`; a control without the clause fails.
+  **What the translator will have to do**.  Refuse T3 with the hatch named
   (M4-2, [#37]); emit Lean's opaque constants as Agda's `opaque` (M2-6,
   [#20]).

### `decidable-and-noncomputable`

(See also [`decidable-and-noncomputable`][cat-decidable-and-noncomputable],
[#39], [#40] and [#53].)

+  **Exercised by** eight entries.  Six are the entries' own: `Nat.gcd`'s
   `if m = 0`, which decides by `instDecidableEqNat` and computes
   (`nat-gcd-succ`, and `nat-gcd-self` through it); the hypothesis
   `[DecidableEq β]` and the classical proofs of `finset-card-image`;
   `Real.sqrt`, `noncomputable`, whose `NNReal.sqrt` reaches `Classical.choice`
   through data (`real-sqrt-nonneg`); `Nat.card`, classical in its definition,
   and `Quotient.out` (`subgroup-card-dvd`); and a `by_cases` in the proof
   field of `Substructure.instInfSet` (`substructure-closure-le`).  Two are
   carried, by `noConfusionType`'s decision on constructor indices
   (`lists-subset-refl`) and by the `autoParam` tree (`order-hom-map-lfp`).
+  **What it cost**.  Where choice sits decided it.  In proofs only, it was
   dropped: `finset-card-image` is T2 through `by_cases` in core's
   `List.perm_iff_count` (LF-10) and through `List.perm_ext_iff_of_nodup`'s
   `classical`, and `FinsetCardImage.agda` proves every such lemma
   constructively, with the decidable equality as a module parameter, the seed
   of [#39]; `substructure-closure-le` is T2 through three proofs, a second
   instance of LF-10 among them, and its Agda is T0.  The type ℝ is T2 only
   through proofs, along a shortest path through one in
   `Rat.instIsStrictOrderedRing`, so every statement mentioning ℝ is T2
   whatever its proof does.  In data, it was a parameter or a different
   statement: `NNReal.sqrt` became the field `nnsqrt` of the reals record, and
   `Nat.card` the record `Card`, which implies weak excluded middle
   (`card-wlem`), beside a constructive Lagrange theorem for groups enumerated
   by `Fin n` that computes the index by `refl`.  A count from the notes of
   `finset-card-image`: of Mathlib's 439,939 theorems, at least 304,066 are T2
   and 1,465 cite a classical decidability constant in their statement
   directly.
+  **What the translator will have to do**.  Detect classical instances in
   statements and proofs, abstract them into hypotheses, and look for them
   through the definitions a statement names, not by axiom sets (M4-4, [#39]);
   promote the theorems with hand-written constructive proofs,
   `finset-card-image` first (M4-5, [#40]); sort choice in data from choice in
   proofs before CU (M6-3, [#53]).

### `nested-and-mutual-inductives`

(See also [`nested-and-mutual-inductives`][cat-nested-and-mutual-inductives],
[#18] and [#19].)

+  **Exercised by** six entries.  One is the entry's own: `Lists.Equiv` with
   `Lists'.Subset`, the one mutual block of Mathlib's mathematics, which
   `lists-subset-refl` was chosen for.  Five carry `Lean.Syntax`, a nested
   type, through `autoParam` (the carrier table).
+  **What it cost**.  Little.  The proof of `Lists'.Subset.refl` never applies
   the block's recursors, and `ListsSubsetRefl.agda` translates the block as an
   Agda `mutual` block of two `Set`-valued data types, with its recursor
   written as two mutually recursive functions over the same motives and minor
   premises, whose motives land in any `Set ℓ` where Lean's land in `Prop`.
   The entry chosen for the block found its K-like reduction, not the block, to
   be the work.
+  **What the translator will have to do**.  Emit mutual and nested blocks
   directly (M2-4, [#18]) and their recursors by mutual pattern matching (M2-5,
   [#19]); erase `autoParam` so that `Lean.Syntax` leaves the closures (no
   roadmap issue names this yet; the field form reaches the output through
   [#18]'s records and the argument form through [#20]'s definitions).

### `projections-and-let`

(See also [`projections-and-let`][cat-projections-and-let], [#17] and [#44].)

+  **Exercised by** all twelve.  The statements project through classes and
   structures (`Membership.mem`, `Subtype.val`, `Finset.val`, `DFunLike.coe` to
   `OrderHom.toFun`, `LowerAdjoint.toFun`, `SetLike.coe`), and the closures add
   the `PProd` projections of compiled recursion and the `let`s of proofs: from
   2 projections and no `let` (`list-reverse-reverse`) to 1,424 projections in
   1,151 constants and 1,098 `let` expressions in 499 (`real-sqrt-nonneg`).
   `nat-gcd-self`'s proof uses none of its own, and `Nat.gcd`'s definition
   none.
+  **What it cost**.  Nothing in the hand translations: projections are record
   fields or plain functions, and Agda's pattern matching replaces `brecOn` and
   its projections.  The cost is a mechanical rendering's, since Agda's `let`
   gives the checker no sharing: the three core-Lean terms are barely shared
   (2.0, 3.6 and 4.4 printed nodes per distinct subterm), so the printer's
   sharing pass at its default threshold takes their renderings from 12,401,
   270,502 and 431,486 bytes only to 12,401, 257,530 and 417,558
   ([`printing-blowup-2026-10-12.md`][blowup]).
+  **What the translator will have to do**.  Print `Expr.proj` and `let` with
   the sharing pass, done in [#17], and emit projections as record fields once
   [#18] emits records; keep the output near-linear across declarations (M5-2,
   [#44]).

## The two encodings of `Prop`

(See also [#27], [`proof-irrelevance`][cat-proof-irrelevance] and
[`large-elimination`][cat-large-elimination].)

[#27] is to decide between encoding A, h-propositions in `Set`, and encoding B,
Agda's `Prop`, by measurement on the corpus and `Init`.  The corpus did not run
that experiment; it wrote eleven entries one way and one entry both ways, and
its notes record what each choice cost.  This section collects that record.

### What the corpus wrote

| Entry | How its Agda reads Lean's `Prop` | What the reading cost |
| --- | --- | --- |
| `list-reverse-reverse` | only an equation, `_≡_` in `Set` | nothing |
| `nat-gcd-self` | only an equation | nothing |
| `nat-gcd-succ` | an equation; `_<_` and `Acc` in `Set` | the irrelevance of the accessibility proof as a lemma, `gcd-acc-irrelevant` |
| `lists-subset-refl` | the mutual inductive propositions as proof-relevant data types in `Set`, with no witness | nothing: the theorem builds a proof and never compares two |
| `multiset-map-map` | `Ω` for `ind`'s motive (A); the relation proof-relevant | the motive in `Ω`, while `squash` is needed under either encoding; "this entry cannot tell the encodings apart", since its motive is an equation |
| `set-ext` | `Ω`, with `propext` over `Ω` (A) | `propext` stated over `Ω` only |
| `finset-card-image` | `Ω` (A) | `Ω-uip` from `propext` and `funext`; `funext` for the irrelevance of `Unique xs` and of implications |
| `real-sqrt-nonneg` | the order with a field `≤-irrelevant` (A) | one field, unused by the proof |
| `subgroup-card-dvd` | `Ω` and `ℙ` (A), and a `Truncation` record for `Nonempty` and `∃` | `Ω-uip`, equality in a subtype by `Ω`'s witness, and the truncation parameter |
| `order-hom-map-lfp` | subsets in `Ω` (A), with a field `≤-prop` | one field, which makes `{x \| f x ≤ x}` a subset |
| `subtype-coe-eta` | both: `SubtypeCoeEta.agda` (A) and `SubtypeCoeEtaProp.agda` (B) | A: one use of the witness; B: a second record for `u_1 = 0`, and a substitution in place of Lean's match |
| `substructure-closure-le` | agda-stdlib's `Pred`, proof-relevant, by choice | nothing; under `Ω` the infimum would need `funext` and `Sg` a truncation |

So seven entries read Lean's `Prop` as encoding A does.  The witness is used in
a proof in three files (`SubtypeCoeEta.agda`'s `ext`; `FinsetCardImage.agda`'s
`Ω-uip` and `Unique-irrelevant`; `SubgroupCardDvd.agda`'s `⟨⟩-≡` and `Ω-uip`),
keeps a statement consistent or a subset well formed in three (`SetExt.agda`'s
`propext`, `MultisetMapMap.agda`'s `ind`, `OrderHomMapLfp.agda`'s `≤-prop`),
and goes unused in one (`RealSqrtNonneg.agda`'s `≤-irrelevant`).  Five entries
read Lean's propositions as proof-relevant types in `Set` with no witness, a
third reading.  That reading is not an encoding a translator can use
throughout: it gives up what Lean's proof irrelevance provides, and in
`subgroup-card-dvd` it would make `Nonempty A` the type `A` itself, so that
`Classical.choice` is trivial, and `∃ x, mk x ≡ q` no proposition, so that
`Quot.ind` could not prove it (the notes of `subgroup-card-dvd`, The Agda
version).  It served where a theorem builds a proof and never compares two.

### The evidence for encoding B

+  **Definitional irrelevance where Lean uses it**.  Of the two
   proof-irrelevance conversions the corpus read, the one its Agda translates,
   in `Subtype.ext`, is `refl` under B and one explicit use of the witness
   under A; the author of that entry would emit B for it (the notes of
   `subtype-coe-eta`).
+  **Two lemmas by definition**.  Under A the corpus needed `funext` to show
   that a function type into a proposition is one (`finset-card-image`), and
   took a `Truncation` record for `Nonempty` and `∃` (`subgroup-card-dvd`).
   Under B both hold by definition: a function type into `Prop` is in `Prop`,
   and `Squash` truncates, with an eliminator the catalog's probe `P25PropCC`
   shows working under `--cubical-compatible --prop`.  Two other lemmas are not
   B's for free: `propext` stays a parameter under either encoding, and a lift
   of a quotient into propositions needs uniqueness of identity proofs for the
   type of propositions, which the corpus proved for `Ω` twice, in parallel
   (`Ω-uip`, in `finset-card-image` and `subgroup-card-dvd`), and which
   `--cubical-compatible` does not give for `Prop` by definition either.

### The evidence for encoding A

+  **Every profile the corpus checked, and no refused match**.  A's files check
   under CC, and their records are instantiated under CU from the cubical
   library's `hProp` and set quotients (`set-ext`, `multiset-map-map`), the
   dialect [#27] credits to agda-unimath and the cubical library.  B's one file
   checks under CC, but Lean's match form of `Subtype.ext`, which matches
   `refl` with a `Prop` field in scope, is accepted under
   `--cubical-compatible --prop` only with `UnsupportedIndexedMatch` ("relies
   on substitution in Setω"), even with every level fixed.  A match on an
   indexed family in `Set` draws the same warning under `--cubical-compatible`
   (`ListsSubsetRefl.agda`'s idiomatic proof, which its direct proof avoids
   through Hedberg's theorem), so the difference is in `Prop`: the catalog's
   probe `P25bPropEqCC` refuses a match on a `Prop`-valued indexed family with
   a `Prop` motive outright (`CannotGenerateTransportClause`), and
   `P25cPropEqCubical` does the same under `--cubical`, where `--prop` itself
   is accepted (`P18PropCubical`).  The probe matches `refl` on one
   equality-shaped family, `_≐_ : A → A → Prop`; whether every indexed family
   is refused was not measured.  The corpus's closures hold such matches:
   `nat-gcd-succ`'s cites `Nat.le_trans`, whose compiled match on the indexed
   proposition `Nat.le` is how `eq_of_heq` enters it.
+  **No copies by level**.  A covers a `Sort u_1` that may be `Prop` with one
   statement over `Set a`; B needs a copy for `u_1 = 0`.  The printer measured
   what happens without that specialization: printing `Prop` for every sort at
   level zero, under `--prop --type-in-type`, raised the refusals of the
   `nat-gcd-succ` and `nat-gcd-self` scaffolds from 6 to 17 and from 7 to 20,
   every new one an `UnequalSorts Prop != Set` ([`printing.md`][printing]), so
   B needs the specialization of [#28] first.
+  **Some of A's costs are paid once**.  `Ω-uip`, the irrelevance of a function
   type into a proposition, and the truncation record would sit in a shared
   prelude like the one the notes of `multiset-map-map` and `set-ext` ask for
   (`Ω`, `Quotients`, `PropExt`, `FunExt`).  Two costs recur: a witness
   wherever Lean identifies two proofs, the cast Lean4Less would insert; and,
   for each inductive proposition Lean declares, either a generated proof that
   it is a proposition or the truncation, which [#27]'s task for encoding A
   names; the corpus met it for `Nodup` (`Unique-irrelevant` in
   `finset-card-image`), for two orders as record fields (`≤-prop`,
   `≤-irrelevant`), and for `Nonempty` and `∃` (the truncation).

### What neither encoding changes

+  **Predicativity**.  Agda's `Prop` is predicative too (`Prop₀ : Set₁`, probe
   `P08Impredicativity`), so `ℙ A p` lands a universe above `p` under either
   encoding, and every level cost of the `impredicative-prop` section stands
   under both.
+  **Equations that are eliminated**.  `Eq` eliminates into `Type`, so an
   equation that is transported along stays in `Set` under either encoding, and
   the uniqueness of identity proofs it needs under CC ([#34]) is the same
   under both; `multiset-map-map`'s motive is such an equation, which is why
   that entry cannot tell the encodings apart.  Where an equation stands in a
   position Lean types as a proposition, the encodings differ (next section).
+  **The quotient record's `squash`**, which makes a quotient a set, is needed
   under both.
+  **`Acc`**, which also eliminates largely, stays in `Set` under both.

### What [#27] has to measure

The corpus supports neither encoding outright.  B wins where a term identifies
two proofs, which the corpus read twice and translated once, in an entry chosen
for it; A wins for constants polymorphic in a level that may be zero, which
every closure has, and meets no refused match under CC.  Which wins overall
depends on counts the corpus cannot take; taken in the order that saves work,
they are as follows:

+  **whether B can match under CC at all**: render the matches on indexed
   propositions in the corpus's closures, `Nat.le_trans`'s first, under
   `--cubical-compatible --prop` and `--cubical --prop`; if the refusal of
   `P25bPropEqCC` holds for every indexed family, B is ruled out for profiles
   CC and CU whatever the other counts say;
+  **the casts, by kind**: the casts Lean4Less ([#26]) inserts per constant,
   split by whether the proposition eliminates largely (`Eq`, `HEq`, `Acc`,
   `And`, `True`, `False`), which stay in `Set` under B as well, so that only
   the others count in B's favor; `subtype-coe-eta`'s casts against the one
   witness its encoding A file needed are a first point;
+  **B's equations in positions typed as propositions**: under B `Eq` is in
   `Set`, so an equation used where Lean expects a proposition (a predicate's
   body, an `∃`, an argument of a constant polymorphic over `Prop`) needs a
   squash, and a later transport along it needs uniqueness of identity proofs
   on its carrier; the corpus did not try this;
+  **A's inductive propositions**: those in the closures that need a generated
   proof of irrelevance, and those that need the truncation.

## Instance arguments

The notes of the three part-2 entries of [#9] count instance arguments in two
ways and ask this report to tabulate one ([#9]'s third task).  The count the
part-1 notes use too, the instance-implicit binders and the occurrences of
instance constants in a declaration's type and value, counted as trees, is as
follows:

| Entry | Type: binders, occurrences | Value: binders, occurrences | In the Agda |
| --- | --- | --- | --- |
| `finset-card-image` | 1, 0 | not recorded, 4 | a module parameter `_≟_` |
| `real-sqrt-nonneg` | 0, 3 | 0, 16 | fields of the parameter record `Reals` |
| `subgroup-card-dvd` | 1, 3 | 2, 31 | an instance argument `⦃ G : Group A ⦄` |
| `order-hom-map-lfp` | 1, 109 | 1, 478 | a module parameter `L : CompleteLattice A ℓ` |
| `subtype-coe-eta` | 0, 0 | 0, 0 | none |
| `substructure-closure-le` | 1, 14 | 1, 9 | an instance argument `⦃ 𝑴 : Structure L ρ M ⦄` |

The other count, arguments at instance-implicit positions of applications,
gives 3, 7 and 27 for the statements of `real-sqrt-nonneg`, `subgroup-card-dvd`
and `substructure-closure-le`, and 1,357,155, 451,949 and 44,193 for their
closures.  The statements of the six entries of [#7] and [#8] carry one
instance argument or none, and none of their Agda files takes an instance
argument except agda-stdlib's irrelevant `.{{NonZero n}}` for `_%_` in
`NatGcdSucc.agda`.  The structure classes the corpus met (`Group`,
`CompleteLattice`, `L.Structure`, the instances of ℝ) became records, taken as
module parameters or instance arguments; the notation classes (`Membership`,
`HasSubset`, `SetLike`, `HasQuotient`, `Setoid`) became plain functions,
projections or definitions.  No Agda file reproduces the instance chains Lean's
search recorded, such as `order-hom-map-lfp`'s path through
`ChainCompletePartialOrder`.

## What M2-9 will measure

[#10] asks for the ratio between a kernel term's size and a mechanical Agda
rendering's.  At the pin the scaffolds and the three full renderings above are
the only renderings, and none is a rendering of a whole entry that Agda
accepts.  The issues that will take the measurement are as follows:

+  M2-9 ([#23]) commits golden outputs for every corpus entry under profile U,
   checks them with Agda in CI, and starts `docs/performance.md` with term
   sizes and Agda's time and memory per module, the first point at which a
   whole entry's rendering checks;
+  M5-2 ([#44]) tracks the blowup factor, output bytes over `.olean` bytes, per
   module in CI, the measure this report could take only against the export;
+  M2-10 ([#24]) compares output size, Agda time and failures with lyphyser's
   tool on the corpus and `Nat.gcd_self`, whose 6,942-line rendering is the one
   Agda rendering of a corpus declaration a predecessor left;
+  M3-1 ([#26]) and M3-2 ([#27]) count the casts each encoding needs, the cost
   this report could only describe.

## Corrections

Found while reading the sources, and left as they are, since the documents
belong to the issues that wrote them; the pull request that added this report
lists each.  The corrections are as follows:

+  **`quotients` in three entries of [#7]**: `nat-gcd-self`, `nat-gcd-succ` and
   `lists-subset-refl` carry `funext` and do not list the feature, which two
   entries of [#9] count for the same carrier (The coverage table).  Adding it
   to their manifest objects is one line each; the report prints the manifest
   as the translating sessions left it.
+  **The catalog's encoding letters**: its `proof-irrelevance` and
   `large-elimination` entries call Agda's `Prop` encoding A and h-propositions
   encoding B, the reverse of [#27], the roadmap and the corpus; the notes of
   `multiset-map-map` said so on 2026-10-08 and the catalog still does.
+  **The catalog's quotient record**: the `quotients` entry's line for profile
   K describes the record of its probe `P24QuotParam`, whose `ind` takes a
   motive in all of `Set` and so proves `Quot.out`; the corpus's record, in
   `multiset-map-map`, takes it in `Ω` and adds `squash`.
+  **[#31]'s description** still says that `Nat.gcd`'s defining equation needs
   K-like reduction, which LF-6 refutes at the pin.
+  **[#30]'s task** "`Init.Core`'s `funext` check under profile K with no
   postulates" bears on `funext` as a parameter, the course [#33] takes; the
   notes of `set-ext` leave open whether the task should change.
+  **Lines of code**: the notes of the three part-2 entries of [#9] leave the
   `OPTIONS` line out of their counts and the others include it; the generated
   sizes table counts it everywhere.

## References

+  Issues and pull requests: [#7], [#8] and [#9] translated the entries in
   [#70], [#69], [#75] and [#76]; [#5] wrote the catalog; [#17] the printer, in
   [#77].
+  Documents: [`gap-catalog.md`][catalog], [`corpus/README.md`][corpus-readme],
   [`corpus/SCHEMA.md`][schema], [`corpus/manifest.json`][manifest],
   [`lean-findings.md`][lean-findings], [`printing.md`][printing],
   [`printing-blowup-2026-10-12.md`][blowup], [`pinning.md`][pinning].
+  Code: [`scripts/python/corpus_tables.py`][tables-script], which prints the
   generated tables; the probes each entry's notes print under Remarks, which
   measured its closure.

[#5]: https://github.com/formalverification/lean2agda/issues/5
[#6]: https://github.com/formalverification/lean2agda/issues/6
[#7]: https://github.com/formalverification/lean2agda/issues/7
[#8]: https://github.com/formalverification/lean2agda/issues/8
[#9]: https://github.com/formalverification/lean2agda/issues/9
[#10]: https://github.com/formalverification/lean2agda/issues/10
[#11]: https://github.com/formalverification/lean2agda/issues/11
[#12]: https://github.com/formalverification/lean2agda/issues/12
[#17]: https://github.com/formalverification/lean2agda/issues/17
[#18]: https://github.com/formalverification/lean2agda/issues/18
[#19]: https://github.com/formalverification/lean2agda/issues/19
[#20]: https://github.com/formalverification/lean2agda/issues/20
[#21]: https://github.com/formalverification/lean2agda/issues/21
[#22]: https://github.com/formalverification/lean2agda/issues/22
[#23]: https://github.com/formalverification/lean2agda/issues/23
[#24]: https://github.com/formalverification/lean2agda/issues/24
[#26]: https://github.com/formalverification/lean2agda/issues/26
[#27]: https://github.com/formalverification/lean2agda/issues/27
[#28]: https://github.com/formalverification/lean2agda/issues/28
[#29]: https://github.com/formalverification/lean2agda/issues/29
[#30]: https://github.com/formalverification/lean2agda/issues/30
[#31]: https://github.com/formalverification/lean2agda/issues/31
[#32]: https://github.com/formalverification/lean2agda/issues/32
[#33]: https://github.com/formalverification/lean2agda/issues/33
[#34]: https://github.com/formalverification/lean2agda/issues/34
[#36]: https://github.com/formalverification/lean2agda/issues/36
[#37]: https://github.com/formalverification/lean2agda/issues/37
[#38]: https://github.com/formalverification/lean2agda/issues/38
[#39]: https://github.com/formalverification/lean2agda/issues/39
[#40]: https://github.com/formalverification/lean2agda/issues/40
[#43]: https://github.com/formalverification/lean2agda/issues/43
[#44]: https://github.com/formalverification/lean2agda/issues/44
[#52]: https://github.com/formalverification/lean2agda/issues/52
[#53]: https://github.com/formalverification/lean2agda/issues/53
[#55]: https://github.com/formalverification/lean2agda/issues/55
[#66]: https://github.com/formalverification/lean2agda/pull/66
[#69]: https://github.com/formalverification/lean2agda/pull/69
[#70]: https://github.com/formalverification/lean2agda/pull/70
[#75]: https://github.com/formalverification/lean2agda/pull/75
[#76]: https://github.com/formalverification/lean2agda/pull/76
[#77]: https://github.com/formalverification/lean2agda/pull/77

[catalog]: gap-catalog.md
[cat-impredicative-prop]: gap-catalog.md#impredicative-prop
[cat-proof-irrelevance]: gap-catalog.md#proof-irrelevance
[cat-k-and-uip]: gap-catalog.md#k-and-uip
[cat-large-elimination]: gap-catalog.md#large-elimination
[cat-quotients]: gap-catalog.md#quotients
[cat-axioms]: gap-catalog.md#axioms
[cat-universe-levels]: gap-catalog.md#universe-levels
[cat-structure-eta]: gap-catalog.md#structure-eta
[cat-literals]: gap-catalog.md#literals
[cat-trust-escape-hatches]: gap-catalog.md#trust-escape-hatches
[cat-decidable-and-noncomputable]: gap-catalog.md#decidable-and-noncomputable
[cat-nested-and-mutual-inductives]: gap-catalog.md#nested-and-mutual-inductives
[cat-projections-and-let]: gap-catalog.md#projections-and-let
[corpus-readme]: ../../corpus/README.md
[schema]: ../../corpus/SCHEMA.md
[manifest]: ../../corpus/manifest.json
[lean-findings]: ../lean-findings.md
[printing]: ../translator/printing.md
[blowup]: ../reports/printing-blowup-2026-10-12.md
[pinning]: ../pinning.md
[tables-script]: ../../scripts/python/corpus_tables.py
