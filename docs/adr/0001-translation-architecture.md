<!-- File: docs/adr/0001-translation-architecture.md -->

# ADR 0001: translation architecture

File: `lean2agda/docs/adr/0001-translation-architecture.md`

+  **Status**: Proposed.  Written at the close of Milestone 1 for William's
   acceptance; every decision below names the issue that carries what it leaves
   open.
+  **Date**: 2026-10-13 (the day the gap report of [#10] merged; the evidence
   was gathered between 2026-10-04 and 2026-10-13).
+  **Tracking**: [#12] (this record); the open questions it names, [#26] (the
   normalizer), [#27] (the encoding of `Prop`, ADR 0002), [#28] and [#29]
   (universe levels), [#30] (quotients), [#36] and [#37] (the atlas and the
   layer rules, the layering record), [#53] (choice under univalence), [#55]
   (uniqueness of identity proofs on types), [#24] (the comparison with
   lyphyser's tool), [#14] (the predecessors' authors); and [#60], which brings
   the record up to date in Milestone 7.
+  **Ancestry**: [#4], the related-work survey (PR [#65]); [#5], the gap
   catalog (PR [#68]); [#6] to [#10], the corpus and its gap report (PRs [#66],
   [#69], [#70], [#75], [#76], [#78]); [#11], the axiom atlas (PR [#71]); [#3],
   the pins (PR [#64]); [#13], the license (PR [#62]); [#15], [#16] and [#17],
   the translator's loader and the emitter's first two passes (PRs [#73],
   [#74], [#77]); and the register of findings about Lean's internals,
   [`lean-findings.md`] (PRs [#71] and [#72]), cited below by entry number
   (LF-n).

**Terms used throughout**.  The terms the issue asks this record to define, and
the few names it leans on, are as follows; the companion note's Terms section
says the same at more length, and each section below defines its further terms
where it first needs them.

+  A *profile* is a set of Agda flags the output must check under, plus what
   remains a module parameter; the four are U, K, CC and CU (§ 4).
+  A *tier* sorts a declaration by the axioms it depends on, computed exactly,
   the first rule that applies deciding: T3 if any axiom is outside the
   standard three, else T2 if `Classical.choice` is among them, else T1 if
   `propext` or `Quot.sound` is, else T0 (§ 5).
+  A *layer* is one of the two halves of an emitted library, the constructive
   one (tiers T0 and T1) and the classical one (T2); T3 is refused (§ 5).
+  The *atlas* is the per-declaration record, computed over the whole pinned
   environment, from which the layering is read: each constant's axioms and
   tier, its kind and module, and the flags no axiom shows (§ 5).
+  *Lean⁻* is Lean without two of its definitional rules, proof irrelevance and
   K-like reduction, and the *normalizer* is the stage that rewrites a Lean
   environment into a Lean⁻ one by inserting explicit casts where either rule
   was used (§ 2).
+  The *corpus* is the set of twelve declarations translated into Agda by hand
   before the translator existed, the translator's test oracle (§ 8); *the pin*
   is the toolchain every measurement was taken at, Lean v4.33.1 with Mathlib's
   tag v4.33.1 and Agda 2.8.0 (§ 8); *the roadmap* is `docs/GITHUB_PROJECT.md`,
   whose issues this record cites by number.
+  *lyphyser's lean2agda* is a 2024 proof-of-concept exporter from Lean 4 to
   Agda that shares this project's name; Lean4Less, lean2dk, rocq-lean-import,
   Predicativize and hol2dk are the other predecessors the survey covers, each
   introduced where it is first cited.
+  In a Status line, *adopted* means landed on `main` in the pull request
   named, *proposed* means decided here and not yet built, and *open* means not
   decided.

## Executive summary

lean2agda translates Lean 4 libraries, Mathlib first, into Agda libraries that
Agda checks, so that Agda users can consume Lean's mathematics and so that the
project can measure, declaration by declaration, which features of Lean's type
theory its libraries use that Agda's lacks.  This record states the
architecture decided for that translation and the evidence that earned each
decision.  The companion note, [`architecture.md`], explains the pipeline
itself, its stages, what each consumes and produces, and which predecessor's
idea each one uses; nothing here explains a component, and everything here
decides one.

**The design in five minutes**.

+  **A direct translator, written in Lean, over the elaborated environment**.
   The translator is a Lean 4 program that loads the compiled `.olean` modules
   Lake builds and reads the kernel terms from Lean's own data structures; it
   reads no export file, except in the Kernel Arena entry, and goes through no
   intermediate framework (§ 1).
+  **Lean4Less as the normalizer**.  Before Agda sees a term, Deducteam's
   Lean4Less rewrites the Lean environment into one typeable in Lean⁻, Lean
   without definitional proof irrelevance and K-like reduction, by inserting
   explicit casts; the project extends the same device to the computation rule
   of quotients.  The Dedukti route, which exists in pieces and has never been
   run end to end, is the recorded alternative and a future baseline (§ 2).
+  **Universe levels in two steps**.  Specialize each constant by which of its
   universe-level parameters are zero, which decides which of its sorts are
   `Prop` and removes `imax`, then compute predicative level annotations by
   constraint solving in the style of Predicativize (§ 3).
+  **Four target profiles**.  U (`--type-in-type`, scaffolding only), K
   (`--safe` with Agda's K, the faithful target), CC
   (`--safe --cubical-compatible`, the primary deliverable) and CU
   (`--safe --cubical`) (§ 4).
+  **Two layers, computed from the atlas**.  Every constant's exact axiom set
   sorts it into a tier; tiers T0 and T1 form the constructive layer, T2 the
   classical layer, which imports the first, and T3 is refused.  Both layers
   are `--safe`: the classical principles are module parameters (§ 5).
+  **The encoding of `Prop` is open**.  Two candidates, h-propositions in `Set`
   and Agda's `Prop`, go to the experiment of [#27] with the corpus's evidence
   for each (§ 6).
+  **The emitter**.  Milestone 2 has fixed injective names, visibility read
   from kernel types and a sharing pass; the roadmap plans one module per Lean
   module, `data` and `record` declarations, recursors by pattern matching and
   opaque theorems (§ 7).
+  **A hand-translated corpus as the oracle, and one pinned toolchain** (§ 8).

Why it is shaped this way comes down to three findings of Milestone 1.

+  **Every Lean 4 predecessor works from the elaborated environment**
   (lyphyser's tool, Lean4Less and lean2dk all load `.olean` modules), and the
   one that reads export files, rocq-lean-import, could declare Lean 3's
   mathlib into Rocq only with conversion checking off.  A kernel-level
   encoding drops the metadata a readable library needs (binder visibility,
   names, module structure), which a direct translator reads from the
   environment as it goes.
+  **Two rules of Lean's theory have no counterpart Agda can use**:
   definitional proof irrelevance for the propositions Lean eliminates into
   types (`Eq`, `Acc` and the other subsingletons, which must live in `Set` on
   the Agda side, where Agda's own proof-irrelevant `Prop` cannot reach), and
   K-like reduction, which no flag of Agda gives; they are the two rules
   Lean4Less eliminates.  Lean's theory proves uniqueness of identity proofs
   for every type, so a translation into `--cubical-compatible` Agda must
   justify each use with a proof that the type is an h-set; and global choice
   of Lean's form contradicts univalence, so the classical layer cannot be
   cubical.  The gap catalog settled both at the pin with probe files.
+  **Most of Mathlib depends on `Classical.choice`, and the corpus suggests
   that much of the dependence is in proofs rather than statements**.  Of
   Mathlib's 569,189 constants at the pin, 365,216 (64.2 percent) depend on
   `Classical.choice`, 365,190 of them in tier T2; and the corpus proved three
   of its four T2 statements with no classical principle, a sample of four.
   How many statements, as opposed to proofs, are classical is not yet
   measured: the atlas follows a constant's type and its value together, and
   separating the two is the work of [#36] and [#39].  That is why the layering
   is computed per declaration, and why a classical-layer theorem can be
   promoted by a hand-written constructive proof (the overlay of [#40]).

### Where it stands

Milestone 1 is complete but for this record, the last task of the license
question ([#13]) and the outreach ([#14]): the survey, the catalog (thirteen
entries, settled by 34 Agda and 7 Lean probe files), twelve hand translations
(sixteen Agda files, all `--safe`, none with a postulate or a use of K), the
gap report and the atlas (771,129 constants, every axiom set exact) are on
`main`.  Of Milestone 2, the environment loader, the naming scheme and the
expression printer with its sharing pass are merged, so the direct translator
is evidence rather than a plan: it loads Mathlib's environment, orders a
closure, names every constant of the pinned environment injectively, and prints
the twelve corpus closures as Agda that Agda parses and scope-checks.  No
translated module checks whole yet; what Agda refuses is the emitters' work
([#18] to [#21]).

### Where it goes

Milestone 2 finishes the emitter under profile U ([#18] to [#25]).  Milestone 3
integrates the normalizer ([#26]), decides the encoding of `Prop` ([#27]),
elaborates universes ([#28], [#29]), translates quotients, literals and
subsingleton elimination faithfully ([#30] to [#32]), and delivers profile K on
`Init` and `Std` ([#33]) with a first measurement of CC ([#34]).  Milestone 4
turns the atlas into the layers ([#36] to [#42]).  Milestones 5 to 7 scale, go
cubical and verify; [#60] updates this record with their measurements (§ 9).

---

## 1.  A direct translator in Lean over the elaborated environment

(See also [#15], [#16], [#17], [#24], [#56], [`related-work.md`] and
[`architecture.md`].)

**Decision**.  The translator is a Lean 4 program, a Lake package in
`translator/` that requires Mathlib and lean4export at pinned tags; it loads
compiled modules with `importModules`, selects declarations, computes their
dependency closure, and translates from the `Environment` directly.

+  **The environment, not an export file**.  lean4export's NDJSON is read only
   where a kernel checker's interface demands it, in the entry of [#56] to the
   Lean Kernel Arena, the Lean FRO's public benchmark of Lean kernel checkers.
   The translator's own input is the environment, whose `Expr` values carry
   binder names and binder information at every occurrence, over which the
   kernel's `whnf` and `check` are available as pure functions, and whose
   `.olean` files are what Mathlib's cache provides.
+  **Direct, not through Dedukti**.  The chain Lean4Less, lean2dk,
   Predicativize, Agda is the alternative recorded in § 2; it is kept as a
   comparison, not built.
+  **lyphyser's lean2agda is cited and not copied**.  It is the 2024
   proof-of-concept exporter that shares this project's name.  Its pass
   structure and its level clauses are borrowed as ideas, with attribution in
   [`architecture.md`] and the component notes; no code is taken before [#24]
   has run both tools on the same declarations, and a pass taken then follows
   the attribution rule of [`licensing.md`].
+  **A pure core with IO at the edges**.  `Lean2Agda/Core/` holds the closure,
   the names, the printer and the sharing pass as pure functions; `Main.lean`
   loads and writes.

**Evidence**.

+  **The predecessors**.  lyphyser's tool, Lean4Less and lean2dk all load
   `.olean` modules.  rocq-lean-import reads export files, and its Lean 3
   experiments calibrate the cost: the stdlib (10,244 definitions and
   inductives) could not be fully checked because of pathological conversion
   problems, and the mathlib run (66,400 entries, 1 h 13 min, 10 GB) was made
   with conversion checking off, so it declared the terms without checking them
   and skipped 11,867 of them ([`related-work.md`], rocq-lean-import).
+  **What an export loses**.  lean4export keys the subterms it writes by
   alpha-equivalence, so two subterms that differ only in binder names or
   binder information get one record carrying the first's, and a scratch export
   stated `(α : Type) → α → α` as `{α : Type} → α → α` (LF-11).  The printer
   reads binder information from the environment and never from an export; a
   translator over exports would have to repair visibility it cannot see.
+  **What the environment costs**.  The translator is written against Lean's
   internal API at one version, so every pin moves together (§ 8), and a tool
   at another version cannot share its process without a bridge: Lean4Less's
   toolchain is five releases behind the pin (§ 2).  An export is a stable,
   versioned format (3.1.0 at the pinned exporter), which is why the Arena
   entry can read one.
+  **lyphyser's tool**.  3,177 lines of Lean against Lean v4.12.0-rc1,
   twenty-one releases before the pin, so a pass is ported rather than copied;
   its output needs `--prop --type-in-type`, is a single file, and postulates
   quotients, axioms and the `Set`-valued `Acc.rec`, the choices profiles K and
   CC exist to undo; its pass structure and its level clauses are the ideas
   worth taking ([`related-work.md`], lyphyser/lean2agda, and its decision
   section).
+  **What the environment gives**.  A kernel application carries no visibility;
   the printer reads it from the head's type through `Lean.Kernel.whnf` and
   `Lean.Kernel.check`, pure functions of the environment, and with the repair
   that uses them turned off Agda refuses four of one scaffold's types with
   `WrongHidingInLambda` ([`translator/printing.md`], Applications and
   visibility, Binder repair).
+  **As built**.  The loader ([#15], PR [#73]) imports an environment, follows
   types, values, constructors, recursors and their rules, mutual companions
   and the quotient package, orders the closure by strongly connected
   components, and prints `Nat.gcd_self`'s closure of 334 constants in 278
   groups within the acceptance deadline of a minute; the closure's axiom set
   agrees with the atlas's record ([`translator/loading.md`]).  The naming
   scheme ([#16], PR [#74]) is injective by construction and was checked for
   collisions over every name of the atlas, and a probe round-tripped the names
   of all 771,129 imported constants through the decoder
   ([`translator/naming.md`]; LF-9).  The printer ([#17], PR [#77]) prints the
   scaffolds of all twelve corpus entries, each in under 12 seconds, and Agda
   parses and scope-checks every one
   ([`reports/printing-blowup-2026-10-12.md`], Every corpus entry).

**Status**.  Adopted for the loader and the two passes built (PRs [#73], [#74],
[#77]).  Open: the emitters of [#18] to [#21], multi-module emission ([#22]),
the golden tests and the `Init` fragments ([#23]), the comparison with
lyphyser's tool ([#24]), the engineering standards ([#25]), and the Arena's
NDJSON reader ([#56]).

---

## 2.  The normalizer: Lean4Less, with the Dedukti route as the alternative

(See also [#13], [#14], [#26], [#30], [#31], [#36], [`related-work.md`] and
[`pinning.md`].)

**Terms**.  *Lean⁻* is Vaishnav's name for a sub-theory of Lean obtained by
dropping definitional rules; this project's Lean⁻ drops definitional proof
irrelevance (any two proofs of a proposition are definitionally equal) and
K-like reduction (the recursor of a proposition with one field-free
constructor, `Eq.rec` above all, reduces on any proof whose indices match the
constructor's, not only on the constructor itself).  The *normalizer* is the
roadmap's name for the stage that rewrites a Lean environment into a Lean⁻ one
by inserting an explicit cast wherever the kernel used either rule; it computes
no normal forms, and the name is kept because the roadmap uses it.

**Decision**.  The normalizer inserts an explicit cast wherever Lean's kernel
used proof irrelevance or K-like reduction, before any term is printed.
Deducteam's Lean4Less is the instrument, run as an external tool at its own
toolchain and never copied while it is unlicensed; [#26] chooses the bridge
across the toolchain skew among the three named under Evidence, and takes the
repair of its `.olean` output as its first task.  The project extends its cast
mechanism to the computation rule of `Quot.lift`, records its casts per
constant as atlas fields apart from the source's axioms, and leaves its
optional eliminations of structure-like reduction and unit eta switched off.

+  **Why a normalizer at all**.  Agda's `Prop` is proof-irrelevant but
   eliminates into `Set` only by the absurd pattern, so the propositions Lean
   eliminates largely (`Eq`, `Acc`, `And`, `True`, `False` and the other
   subsingletons) live in `Set` on the Agda side, where two proofs are not
   definitionally equal; and Agda's K is a pattern-matching principle, not a
   reduction, so a neutral proof never computes under any flag.  Every Lean
   term whose typing used either rule needs an explicit cast in Agda, under
   profile K as much as under CC, and `Classical.em`, whose proof makes
   essential use of proof irrelevance (Vaishnav's thesis, chapter 5, as the
   survey locates it), is the first term that matters: without the casts no
   classical logic gets through.
+  **Casts carry `propext` in Lean⁻, and the tier stays the source's**.  Since
   Lean4Less's commit `5b66bbc` of 2026-02-11 its proof-irrelevance lemma
   `prfIrrel` is a theorem proved from `propext`, not an axiom as in the paper
   and the thesis, so in the Lean⁻ environment a cast inserted into a tier-T0
   constant brings a `propext` dependency with it.  On the Agda side a cast is
   justified by the encoding's own device, the h-proposition's witness under
   encoding A or an h-set proof under B (§ 6), never by replaying Lean⁻'s proof
   of `prfIrrel`, so no `propext` parameter enters a T0 module through a cast.
   The atlas therefore records casts as a field of their own, apart from the
   source's axioms, and computes the tier from the source ([#26], [#36]).
+  **The Dedukti route is recorded, not taken**.  Lean4Less to Lean⁻, lean2dk
   to Dedukti, Predicativize to a predicative theory and then to Agda: every
   piece exists, the chain has never been run end to end, and whether
   Predicativize accepts lean2dk's encoding (Lean's `imax`, level normalization
   by rewriting, `Nat` and `String` literals, quotients) is open.  The route
   would lose readability, since Predicativize's own Matita case had its
   inductive types and recursive functions rebuilt by hand; robustness, since
   lean2dk's output was two to three orders of magnitude larger than its input
   and its current branch needs a patched Dedukti and value-stubs constants
   that are "trusted, not checked"; and the metadata the emitter needs.  Once
   lean2dk translates and checks, without stubs, a module the direct translator
   also handles, the two checks of one Lean⁻ module, Dedukti's against Agda's,
   are compared; that comparison needs no Predicativize.  What the direct route
   pays in exchange: predicativization is implemented in Lean rather than taken
   from Predicativize (§ 3), the cast insertion is re-implemented if
   Lean4Less's license is refused (the fallback below), and one program carries
   the whole trusted base, which the trust analysis of [#57] takes apart.
+  **The fallback**.  Lean4Less has no license file; running a published tool
   at arm's length needs none, while copying or forking it does, which is why a
   fork waits on the answer [#14] asks its authors for.  If the answer is no,
   or silence, [#26] re-implements the cast insertion from the paper and the
   thesis of Lean4Less's author, Vaishnav, which are published under CC BY 4.0,
   over Lean4Lean, Carneiro's Lean kernel written in Lean, which Lean4Less
   itself modifies and which is Apache-2.0; the survey recommended that [#26]
   record this fallback so that nothing depends on an answer, and its body does
   not yet.

**Evidence**.

+  **The overhead**, measured by Vaishnav at Lean v4.16.0-rc2.  On `Std`
   (29,859 constants) 1,736 constants use proof irrelevance and 134 K-like
   reduction (6.3 percent), the environment grows from 226 MB to 261 MB (15.5
   percent), and checking the output under the Lean⁻ kernel takes 3 m 9 s
   against 2 m 19 s for the input under Lean's (36.0 percent); on
   `Mathlib.Algebra.Order.Field.Rat` (113,899 constants) the figures are 2,965
   and 237 (2.8 percent), 1,485 MB to 1,501 MB (1.1 percent), and 5 m 44 s
   against 5 m 11 s (10.6 percent).  `Mathlib.Data.Real.Basic` translated.  The
   tool "does not currently scale beyond small libraries" or lower Mathlib
   modules, and its `.olean` output is "currently broken" since Lean's module
   system changed ([`related-work.md`], Lean4Less).
+  **The toolchain skew**.  Lean4Less's `main` (`5b66bbc`) names
   `leanprover/lean4:v4.28.0-rc1`; the project pins v4.33.1, five minor
   releases later, and lean4-nix carries no release candidates, so the flake
   cannot fetch Lean4Less's Lean ([`pinning.md`], Lean4Less).  [#26] bridges
   the skew by a Mathlib revision both tools support, by a fork at the pinned
   Lean if a license is granted, or by running the translator inside
   Lean4Less's process, and takes the `.olean` repair as its first task.
+  **What the corpus read**.  Proof irrelevance was read in two kernel terms
   (`Subtype.ext`'s match and `Finset.eq_of_veq`) and measured nowhere, because
   the kernel's diagnostics count reductions, not the conversions proof
   irrelevance decides, and the elaborator's switch `proofIrrelevance := false`
   still identifies proofs in argument position (LF-4); Lean4Less is the
   instrument that will count the rest.  K-like reduction entered ten of the
   twelve closures through `eq_of_heq`, uniqueness of identity proofs on a
   universe (LF-5), and one Mathlib proof, `Lists'.of_toList`, uses it in its
   own right (LF-7) ([`foundations/gap-report-corpus.md`], The gaps).
+  **The computation rule of quotients**.  The kernel reduces `Quot.lift` in 2
   declarations of `multiset-map-map`'s closure, 9 of `finset-card-image`'s, 53
   of `real-sqrt-nonneg`'s and 102 of `subgroup-card-dvd`'s; in the hand
   translations each use became a rewrite by the parameter record's
   propositional rule `lift-β`, which is what the extension to `Quot.lift`
   ([#30]) automates.  Lean's proof of `funext` computes `Quot.lift` under a
   binder and cannot be replayed by pointwise rewrites, so `funext` is a
   parameter of its own, which bears on [#30]'s task of checking `Init.Core`'s
   `funext` under profile K with no postulates
   ([`foundations/gap-report-corpus.md`], `quotients`).
+  **A stale claim corrected**.  Lean4Less's README aborts constants that
   compute large `Nat.gcd`s because, it says, `Nat.gcd`'s defining equation
   holds definitionally only through K-like reduction.  At the pin the equation
   is not definitional at all: since v4.27.0 a definition by well-founded
   recursion on a `Nat` measure compiles through the fuel-based
   `WellFounded.Nat.fix`, and re-checking the 192 theorems and definitions of
   `Nat.gcd_succ`'s closure with the kernel's diagnostics on, only `eq_of_heq`
   reduces a recursor that admits K-like reduction (LF-6).  Whether Lean4Less
   still refuses `Nat.gcd` at the pin needs a run of Lean4Less, which is
   [#26]'s.
+  **Eta stays switched off**.  Lean4Less can eliminate structure-like
   reduction (since 2025-04-10) and unit eta (since 2026-06-13, on its
   `claude-stable` branch).  Agda's records have eta, recursive ones included
   where the positivity checker permits (probe `P10cRecursiveRecord`) and where
   Lean's have none, and the elaborator's test found structure eta used in the
   mathematics of three corpus closures at no cost in Agda
   ([`foundations/gap-catalog.md`], `structure-eta`;
   [`foundations/gap-report-corpus.md`], `structure-eta`).

**Status**.  Proposed; nothing of the normalizer is built.  [#26] integrates it
and measures the cast overhead on the corpus and `Init`; [#30] extends it to
`Quot.lift`; [#36] carries the cast counts; [#14] asks for the license; [#31]
decides what to do about `Nat.gcd`, and its description still says the equation
needs K-like reduction, which LF-6 refutes.

---

## 3.  Universe levels: specialize, then predicativize

(See also [#28], [#29], [`foundations/gap-catalog.md`] and
[`related-work.md`].)

**Terms**.  Lean's levels are `u`, `0`, `S ℓ`, `max` and `imax`, where
`imax u 0 = 0` lets a proposition quantify over any universe and stay a
proposition; `Prop` is impredicative.  Agda's levels have `lzero`, `lsuc` and
`_⊔_` and no `imax`, and both `Set ℓ` and `Prop ℓ` are predicative.

**Decision**.  The universe stage runs in two steps, in the order
rocq-lean-import and lyphyser's tool both chose.  First, specialize each
constant by which of its universe-level parameters are zero (`Sort 0` is
`Prop`, so this decides which of its sorts are propositions; rocq-lean-import
calls the pattern a `Prop` instantiation), generating instances lazily as they
are used, which removes every `imax` ([#28]).  Then compute predicative,
universe-polymorphic level annotations by collecting level constraints and
unifying them in the equational theory of levels, in the style of Felicissimo
and Blanqui's Predicativize, with a hook for constraints added by hand per
constant ([#29]).  A constant whose constraints have no solution is reported as
essentially impredicative, not translated.

**Evidence**.

+  **The predecessors**.  rocq-lean-import duplicates each constant per pattern
   of universe parameters instantiated at `Prop`, that is, at level zero
   (`_instX`) and gives each distinct algebraic universe a surrogate parameter;
   lyphyser's level clauses are the same specialization, needed even under
   `--type-in-type` because Agda's syntax separates `Prop` from `Set`;
   Predicativize's elaboration took Matita's arithmetic library to Agda that
   checks under `--safe`, with level constraints added by hand for some
   constants, and its paper proves that not every solvable level-unification
   problem has a most general unifier (Theorem 6.1) and reports that Agda's own
   unifier fails a constraint theirs solves, `_0 ⊔ _1 = _0 ⊔ _2` (Remark 6.3)
   ([`related-work.md`], the three sections).
+  **Without the first step**.  Printing `Prop` for every sort whose level
   normalizes to zero, under `--prop --type-in-type`, raised Agda's refusals on
   the `nat-gcd-succ` and `nat-gcd-self` scaffolds from 6 to 17 and from 7 to
   20, every new one `UnequalSorts Prop != Set`: a universe-polymorphic
   constant printed with `Set` and instantiated at `Prop`
   ([`translator/printing.md`], Sorts under profile U).  So an encoding that
   puts propositions in Agda's `Prop` needs the specialization first, and
   profile U prints every sort as `Set` instead.
+  **How much impredicativity is essential**.  Seven corpus entries exercise
   `impredicative-prop`, and in five the statement or a definition it names
   quantifies over a type inside a proposition.  In four of the five the use is
   inessential: the statement holds at every level, and the Agda leaves the
   level free or lets Agda compute it.  In the fifth,
   `substructure-closure-le`, Mathlib's infimum of substructures and its
   `closure` have no predicative assignment of levels, since the carrier would
   have to land at the level it ranges over, and the theorem survives in two
   predicative forms, the infimum one universe up and an inductive closure at a
   level that absorbs the others under join, `u ⊔ w ⊔ p`
   ([`foundations/gap-report-corpus.md`], `impredicative-prop`).  The kernel
   term records none of these levels, since the kernel computes
   `imax (u+1) 0 = 0` itself.
+  **Where levels land**.  Every level parameter of the corpus became an Agda
   `Level`, and the records that quantify over levels live in `Setω`, as a
   universe-polymorphic Lean constant must
   ([`foundations/gap-report-corpus.md`], `universe-levels`;
   [`foundations/gap-catalog.md`], `universe-levels`, probe `P09Setω`).

**Status**.  Proposed; nothing of the stage is built.  [#28] measures the
number of instances generated for `Init` against rocq-lean-import's count of
possible instances, and [#29] the fraction of `Init` and `Std` that elaborates,
listing the essentially impredicative constants with the constraint that
failed.

---

## 4.  The target profiles U, K, CC and CU

(See also [#21], [#33], [#34], [#51], [#52], [#53], [#55],
[`foundations/gap-catalog.md`] and [`foundations/gap-report-corpus.md`].)

**Terms**.  A *profile* is the set of Agda flags the output must check under,
plus what remains a module parameter.  `--safe` forbids postulates,
`--type-in-type` and the pragmas that bypass a check; `--cubical-compatible`
implies `--without-K`, so K, the principle that any two proofs of an equality
are equal, is unavailable by pattern matching; `--cubical` adds the interval
and higher inductive types.  An *h-proposition* is a type any two of whose
elements are equal; an *h-set* is a type whose equality types are
h-propositions, so that any two proofs of `a ≡ b` are equal.  In what follows,
K alone names Agda's rule, profile K the target, and K-like reduction Lean's
rule.

**Decision**.  Four profiles, as follows.

| Profile | Agda flags | What stays a parameter | Purpose |
| --- | --- | --- | --- |
| U | `--type-in-type`, postulates allowed | nothing (postulated) | scaffolding for Milestone 2; never a deliverable |
| K | `--safe` (Agda's default, with K) | `propext`, the quotient primitives, `funext`, `Classical.choice` | the faithful target: every rule of Lean's theory has a counterpart |
| CC | `--safe --cubical-compatible` | as K | the primary deliverable; each use of K justified by an h-set proof |
| CU | `--safe --cubical` | `Classical.choice` only, in forms consistent with univalence | the cubical target; quotients, `funext` and `propext` become theorems; constructive layer first |

+  **U prints every sort as `Set` and uses `--type-in-type` alone**, not
   `--prop`, since the specialization of § 3 does not exist yet; it gives up
   definitional proof irrelevance, and its postulates stand in for every value
   the emitters cannot yet express.
+  **Profile K is the stepping stone to CC**, as the roadmap decided on
   2026-10-04: under Agda's default theory every rule of Lean's has a
   counterpart once the normalizer has made the two eliminated rules explicit,
   so a failure under profile K is a translator defect, a constant the
   normalizer aborted, or an essential use of impredicativity, and the report
   of [#35] on what fraction of `Init` and `Std` translates sorts the failures
   into those classes before CC adds the h-set obligations; the foundational
   gaps proper, K on types that are not h-sets and choice under univalence,
   appear only under CC and CU.
+  **CC is the primary deliverable** because the constructive layer is meant
   for users of `--safe --cubical-compatible` Agda, and because every use of K
   it must justify measures where Lean's libraries rely on uniqueness of
   identity proofs.
+  **CU takes the constructive layer first**, and the classical layer only in
   the forms of choice that univalence allows ([#53]).

**Evidence**.

+  **Lean proves uniqueness of identity proofs for every type**.
   `example {α : Sort u} {a b : α} (p q : a = b) : p = q := rfl` is accepted at
   the pin, and so is the same statement for `p q : α = β` with `α β : Type`;
   `Eq.rec` reduces on a variable proof, `(h ▸ x) = x := rfl`.  Agda accepts
   `uip refl refl = refl` under `--safe` (probe `P05KAccepted`) and refuses it
   under `--cubical-compatible` with `[SplitError.UnificationStuck]`
   (`P06KRejected`) and under `--cubical` (`P17CubicalK`).  What remains is
   Hedberg's theorem for types with decidable equality (`P07HedbergNat`)
   ([`foundations/gap-catalog.md`], The profiles and the two facts that shape
   them).
+  **Global choice is inconsistent with univalence**.  The HoTT book's Lemma
   3.8.5 exhibits a 1-type `X` and a family `Y` of sets over it with
   `∏(x:X) ∥Y(x)∥` and no `∏(x:X) Y(x)`, so a function of `Classical.choice`'s
   type cannot exist under univalence even restricted to h-sets.  Agda accepts
   such a parameter under `--safe --cubical` (`P19ChoiceParam`), so the point
   is vacuity, not soundness: nothing in cubical Agda could instantiate it.
   The classical layer is therefore a `--cubical-compatible` library, and which
   weaker principles follow the constructive layer into CU is [#53]'s question
   (ibid.).
+  **The corpus checks under `--safe`, CC and CU**.  All sixteen Agda files of
   the twelve entries check under `--safe`, fourteen under CC and two under CU,
   with no postulate and no use of Agda's K.  The one K-like step in a Mathlib
   proof is replaced by Hedberg's theorem for `Bool`; `eq_of_heq`, which ten
   closures carry, has no proof under CC and is avoided by Agda's own pattern
   matching, as the translator will do in [#19]; and uniqueness of identity
   proofs came due through the quotient record (its field `squash`, which says
   the quotient is an h-set), for `ℕ` (agda-stdlib's `≡-irrelevant`) and for
   the type of propositions (`Ω-uip`, from `propext` and `funext`)
   ([`foundations/gap-report-corpus.md`], Findings, `k-and-uip`).
+  **The parameters are jointly satisfiable**.  The two CU files instantiate
   their entries' CC records (`Quotients`, `PropExt`, `FunExt`) from the
   cubical library's set quotients and `hProp` with no classical principle.
   The quotient record takes `ind`'s motive in h-propositions, since a motive
   in all of `Set` proves a section of every quotient map, which is Mathlib's
   `Quot.out` and needs choice; and `propext` is stated over h-propositions,
   since over all of `Set` it is refutable
   ([`foundations/gap-report-corpus.md`], `quotients`, `axioms`).
+  **A translated library can check under `--safe`**.  Predicativize's Matita
   library does, under Agda 2.6.3's default theory with K; Matita's theory has
   no proof irrelevance, K-like reduction or quotients, so this is evidence for
   the universe step of § 3 and for the `--safe` target, not for the rest of
   profile K, and it says nothing about `--cubical-compatible`
   ([`related-work.md`], Predicativize).
+  **How far UIP reaches**.  Every `noConfusion` of an inductive type with
   parameters or indices uses `eq_of_heq`: 2,412 of 4,494 under
   `import Mathlib` (LF-5).  Two Mathlib lemmas of one closure rely on K-like
   reduction and structure eta in their own proofs (LF-7).  A cast between
   types, as in `subgroup-card-dvd`'s `groupEquivQuotientProdSubgroup`, needs
   uniqueness of identity proofs on a universe, which no h-set proof supplies;
   those uses are [#55]'s study.

**Status**.  Adopted as the roadmap's targets; U is in use (PR [#77]), profile
K is [#33]'s deliverable, CC is first measured by [#34] and delivered by [#51],
and CU by [#52].  Open: the h-set inference and the K-essential list ([#34],
[#51]); the forms of choice CU can keep ([#53]); uniqueness of identity proofs
on types that are not h-sets ([#55]).

---

## 5.  Two layers, computed from the atlas

(See also [#11], [#20], [#36], [#37], [#38], [#39], [#40],
[`reports/atlas-mathlib-v4.33.1-0df444a.md`] and [`atlas/README.md`].)

**Terms**.  The *atlas* is the per-declaration record of what every constant of
the pinned environment depends on: its axioms and tier, its kind and module,
and the flags no axiom shows (`noncomputable`, `unsafe`, `partial`); later
versions add the kernel features its typing used, the normalizer's casts, and
its acceptance under each profile.  A *tier* sorts a constant by its exact
axiom set, the first rule that applies deciding: T3 if any axiom is outside the
standard three, else T2 if `Classical.choice` is among them, else T1 if
`propext` or `Quot.sound` is, else T0; the atlas's `tierOf` tests the rules in
that order.  A *layer* is one of the two halves of the emitted library.

**Decision**.  The emitted library has a constructive layer (tiers T0 and T1)
and a classical layer (T2) that imports it; T3 is refused and reported with the
axiom that put it there.  Both layers are `--safe`: the classical principles
are record-typed module parameters in the style of the TypeTopology library,
threaded so that a module takes only what its declarations need, and a one-line
user module outside the library may postulate them.  The layering is computed
from the atlas, declaration by declaration, as follows.

+  **The tier is computed from the exact axiom set**, by reachability over the
   edges `Lean.collectAxioms` follows (a constant's type and value, an
   inductive type's constructors), never from `#print axioms`.
+  **Any axiom other than the standard three is T3**, rather than a listed few,
   because the population cannot be enumerated: at the pin the environment
   declares 15 axioms, the standard three, `sorryAx`, the deprecated
   native-reduction family (`Lean.ofReduceBool`, `Lean.ofReduceNat`,
   `Lean.trustCompiler`) and eight `unsafe` compiler axioms
   (`lcProof : ∀ {α : Prop}, α` among them), and `native_decide` creates a
   bespoke axiom per invocation (`<theorem>._native.native_decide.ax_1_1`),
   which no list written today can name.
+  **The hatches no axiom shows are atlas fields, not tiers**: `unsafe` and
   `partial` in the atlas's version 0, and `implemented_by` from [#36].  An
   `unsafe` constant is exempt from kernel checking and is refused.  A
   `partial def` is an `opaque` constant whose only trace is a companion
   `<name>._unsafe_rec` of safety `partial`, invisible to `#print axioms` and
   detected by the companion; `implemented_by` replaces a constant in compiled
   code only, which the kernel never sees.  The roadmap's description, the
   README and the survey's Terms ([`related-work.md`], Terms) listed `unsafe`
   and `partial` under T3 until this record, the survey with `implemented_by`
   too, and are corrected with it; this record keeps the tier an axiom-only
   notion and leaves the refusal rule for the hatches to the layer rules of
   [#37], which has to reconcile it with [#20]'s emission of `partial`
   definitions as `opaque` constants.
+  **`propext` and `Quot.sound` are constructive** because univalent type
   theory validates both: in the cubical library `funExt` and `hPropExt` are
   theorems and set quotients are higher inductive types whose `rec` computes
   on points (probe `P16CubicalQuotient`), and the two CU corpus files
   instantiate the parameter records from them with no classical principle.
   The reasoning is written out by [#37].
+  **A theorem whose statement is constructive and whose proof is classical**
   sits in the classical layer until a hand-written constructive proof promotes
   it: the overlay of [#40] is a module of such proofs, each checked against
   the generated statement and preferred by the emitter, so that a
   declaration's layer is a function of the atlas and the overlay together, and
   a promotion can move the tiers of everything downstream of the promoted
   proof, which the blocker analysis of [#41] is for.  The classical
   `Decidable` instances that make statements classical are detected and
   abstracted into hypotheses by [#39].
+  **Casts are recorded apart from the source's axioms** (§ 2), so that the
   normalizer does not move constants from T0 to T1.

**Evidence**.

+  **The tiers at the pin**.  Of Mathlib's 569,189 constants, 83,868 (14.7
   percent) are T0, 120,090 (21.1) T1, 365,190 (64.2) T2 and 41 (under 0.1) T3,
   so the constructive layer would hold 35.8 percent of Mathlib's constants;
   without the 243,956 auto-generated ones, 33,919 (10.4), 52,978 (16.3),
   238,303 (73.3) and 33.  Among Mathlib's 439,939 theorems, 304,219 (69.2
   percent) are T2.  Over the whole environment of 771,129 constants the tiers
   hold 154,356, 179,007, 437,511 and 255
   ([`reports/atlas-mathlib-v4.33.1-0df444a.md`], Tiers, Mathlib by kind).
+  **Mathlib's T3 is 41 constants, every one on the compiler axiom `lcProof`**.
   Mathlib's 41 T3 constants all depend on `lcProof` and all are `unsafe`
   definitions: fourteen `Repr` instances (`Real`, `Complex`, `Finset` among
   them), the floating-point arithmetic of `Mathlib.Data.FP.Basic`,
   `Part.unwrap`, `Quot.unquot`, `Multiset.instToExprOfToLevel` and four
   tactic-side helpers.  Of the environment's 255, 249 are `unsafe` and the
   other 6 are the native-reduction family and `sorryAx`; no theorem is T3, and
   nothing safe rests on an unsafe axiom (LF-2).  `sorryAx` has no dependent
   but itself, and no `native_decide` axiom exists in `import Mathlib` (LF-2;
   [`reports/atlas-mathlib-v4.33.1-0df444a.md`], T3).
+  **Why exact reachability**.  `Lean.collectAxioms`, which `#print axioms`
   calls, caches the axioms of a constant it reaches while one of that
   constant's own dependencies is still being visited, and since Lean v4.30.0
   every `.olean` stores the results so computed, which importing modules
   trust.  At the pin it under-reports 1,837 constants of the environment, 550
   of them Mathlib's, and never over-reports; 532 Mathlib constants would get
   the wrong tier from it (136 from T0 to T1, 129 from T0 to T2, 267 from T1 to
   T2).  The omitted axiom is always one of the standard three here, but the
   same mechanism hides `sorryAx` across modules (LF-1; Lean issue 15226, open,
   whose pull request 15385 would fix inductive types only).  The atlas records
   what Lean leaves out in `lean_omits` and stops if Lean ever names an axiom
   the graph does not reach ([`reports/atlas-mathlib-v4.33.1-0df444a.md`],
   Where `#print axioms` falls short; [`atlas/README.md`]).
+  **The cost**.  `make atlas` imports Mathlib in 6 s, builds the dependency
   graphs and the exact axiom sets in 43 s, and writes the records, Lean's
   `collectAxioms` of each constant among them, in 137 s: 185 s in all by the
   report's own total, its rounded phases summing to 186, at a peak of 7.5 GiB,
   for 221,461,382 bytes of records that two runs reproduced byte for byte
   ([`reports/atlas-mathlib-v4.33.1-0df444a.md`], Reproducing the atlas).
+  **The published counts, reproduced**.  Two counts of Mathlib's dependence on
   choice were published before the atlas: in Mathlib pull request 35685, an
   open draft that reduces the use of `Classical.choice` on a custom Lean, and
   in Mendoza-Smith's 2026 paper on neural proof embeddings, which partitions
   declarations into classical and constructive.  The pull request's 446,045
   choice-dependent constants on master (57.5 percent), entered 2026-08-25 at
   commit `661ab0b`, reproduce as 446,081 of 775,887 with its script run
   verbatim there; the paper's 171,522 classical of 471,260 at `9f0aee2`
   reproduce as 171,523 of 471,261 by its method, which at the pin misses
   121,931 choice-dependent constants because its graph has edges only from the
   values of definitions and theorems, none from types or out of the other
   kinds, and no paths through internal names.  At the pin the exact count over
   the whole environment is 437,606 of 771,129 (56.7 percent): the 437,511 T2
   constants and 95 T3 constants that reach choice as well; of Mathlib's own,
   365,216 depend on choice and 365,190 are T2
   ([`reports/atlas-mathlib-v4.33.1-0df444a.md`], Comparison with the published
   counts, Against this report's denominator).
+  **Classical by the proof, not the statement**.  Three of the corpus's four
   T2 statements are proved with no classical principle: `finset-card-image` by
   Lean's own proof with its classical lemmas proved constructively over the
   given decidable equality, `substructure-closure-le` for two predicative
   closures, and `real-sqrt-nonneg` over a record of the reals; the fourth,
   Lagrange's theorem, has a constructive file for finite groups beside its
   classical one.  `by_cases` with no `Decidable` instance in scope opens
   `Classical`, which is how core's `List.perm_iff_count`, and through it
   `Finset.image` and every statement that mentions it, is T2 (LF-10).  The
   type `ℝ` is T2 only through proofs, the shortest path through one in
   `Rat.instIsStrictOrderedRing`, so every statement about the reals is T2
   whatever its proof does, while `NNReal.sqrt` and `Nat.card` reach choice
   through data.  Of Mathlib's 439,939 theorems, 1,465 cite a classical
   decidability constant in their statement directly
   ([`foundations/gap-report-corpus.md`], Findings,
   `decidable-and-noncomputable`).
+  **The corpus agrees**.  The atlas's axiom sets equal the manifest's, which
   `#print axioms` printed, for all twelve entries, so none is affected by the
   under-report ([`reports/atlas-mathlib-v4.33.1-0df444a.md`], Agreement with
   the corpus).

**Status**.  The atlas v0 is adopted (PR [#71]); the layers are the roadmap's,
and nothing of them is emitted yet.  Open: the atlas v1 schema and producer
([#36]); the layer rules, the module roots and the refusal rule for the hatches
no axiom shows, recorded in the layering record, the ADR that [#37] writes; the
threading of the parameter records ([#33], [#38]); the classical instances
([#39]); the promotion overlay ([#40]); and the count of T1 declarations that
owe their tier to `simp`'s `eq_self` alone, the lemma that rewrites `a = a` to
`True` and is proved from `propext`, which no issue owns.

---

## 6.  The encoding of `Prop`: two candidates, left open

(See also [#27], [#32], [`foundations/gap-catalog.md`] and
[`foundations/gap-report-corpus.md`].)

**Terms**.  *Encoding A* maps each Lean proposition to an h-proposition in
`Set`, a type carrying a witness that any two of its elements are equal (the
corpus writes `Ω p = Σ (Set p) Irrelevant`); it needs a cast wherever Lean used
proof irrelevance and a propositional-truncation parameter for `Or`, `Exists`
and `Nonempty`, and it is the dialect agda-unimath and the cubical library
speak.  *Encoding B* maps each proposition to Agda's `Prop` universe under
`--prop`, which is definitionally proof-irrelevant and eliminates into `Set`
only by the absurd pattern; the propositions Lean eliminates largely (`Eq`,
`HEq`, `Acc`, `And`, `True`, `False` and the other subsingletons) move to
`Set`, and casts are needed only for those.  The gap catalog's
`proof-irrelevance` and `large-elimination` entries use the two letters the
other way round; this record uses [#27]'s, the roadmap's and the corpus's.

**Decision**.  Not taken here.  Both encodings are to be implemented behind a
switch and decided by measurement on the corpus and `Init` in [#27], ADR 0002;
the losing encoding is to stay available for Milestone 6 if it is the
cubical-friendly one.  Under either encoding the subsingleton eliminators live
in `Set` ([#32]), the quotient record's `squash` is needed, and the level costs
of § 3 stand.  What this record fixes is the evidence each candidate starts
from and the order in which [#27] measures.

**Evidence**.

+  **What the corpus wrote**.  Seven entries read Lean's `Prop` as encoding A
   does; the witness is used in a proof in three files, keeps a statement
   consistent or a subset well formed in three, and goes unused in one.  Five
   entries read Lean's propositions as proof-relevant types in `Set` with no
   witness, a third reading that served where a theorem builds a proof and
   never compares two, and that no translator can use throughout, since it
   would make `Nonempty A` the type `A` and `Classical.choice` trivial.  One
   entry, `subtype-coe-eta`, was written both ways
   ([`foundations/gap-report-corpus.md`], The two encodings of `Prop`).
+  **For B**.  The one proof-irrelevance conversion the corpus translates, in
   `Subtype.ext`, is `refl` under B and one explicit use of the witness under
   A, the cast Lean4Less would insert.  Two of A's lemmas hold by definition in
   `Prop`: a function type into a proposition is one (A needed `funext` for it
   in `finset-card-image`), and `Squash` truncates (A took a `Truncation`
   record for `Nonempty` and `∃` in `subgroup-card-dvd`).  Two do not:
   `propext` stays a parameter either way, and a lift of a quotient into
   propositions needs uniqueness of identity proofs for the type of
   propositions, which neither encoding has by definition; A proved it for `Ω`
   twice, from `propext` and `funext`, and under B the same argument should
   need `propext` alone, since a bi-implication between propositions is itself
   in `Prop`, though the corpus did not write that proof (ibid.).
+  **For A**.  A's files check under CC and their records are instantiated
   under CU from the cubical library.  B's one file checks under CC, but Lean's
   match form of `Subtype.ext` draws `UnsupportedIndexedMatch` under
   `--cubical-compatible --prop`, and the catalog's probe `P25bPropEqCC`
   refuses a match on a `Prop`-valued indexed family with a `Prop` motive
   outright, `[CannotGenerateTransportClause]`, as does `P25cPropEqCubical`
   under `--cubical`, while `--prop` alone accepts it.  The probe matches
   `refl` on one equality-shaped family, and the corpus's closures hold matches
   on indexed propositions such as `Nat.le` (in `Nat.le_trans`, which
   `nat-gcd-succ` cites) that were not rendered.  A covers a `Sort u` that may
   be `Prop` with one statement over `Set a`; B needs a copy for the zero
   level, and the measurement of § 3 says it needs the specialization of [#28]
   first.  Some of A's costs are paid once, in a prelude; two recur, a witness
   wherever Lean identifies two proofs and an irrelevance proof or a truncation
   for each inductive proposition ([`foundations/gap-catalog.md`],
   `proof-irrelevance`; [`foundations/gap-report-corpus.md`], The two encodings
   of `Prop`).
+  **What neither changes**.  Agda's `Prop` is predicative too (`Prop₀ : Set₁`,
   probe `P08Impredicativity`), so every level cost stands under both; an
   equation that is transported along stays in `Set` under both and needs the
   same h-set proof under CC, which is why `multiset-map-map` cannot tell the
   encodings apart; `squash` and `Acc` are needed under both (ibid.).
+  **The measurements, in the order that saves work** ([#27], the comment of
   2026-10-13): first whether B can match under CC at all, by rendering the
   closures' matches on indexed propositions, `Nat.le_trans`'s first, under
   `--cubical-compatible --prop` and `--cubical --prop`, since a refusal for
   every indexed family rules B out for CC and CU whatever else is counted;
   then the casts Lean4Less inserts per constant, split by whether the
   proposition eliminates largely, since those stay in `Set` under B and count
   for nothing; then, under B, the equations in positions Lean types as
   propositions, which need a squash and then an h-set proof to transport;
   then, under A, the inductive propositions that need a generated irrelevance
   proof and those that need the truncation.

**Status**.  Open, by design; [#27] decides and writes ADR 0002 once [#26] has
produced the casts to count.  The catalog's swapped letters are its owner's to
correct ([#5], closed).

---

## 7.  The emitter: what Milestone 2 has fixed, and what the roadmap plans

(See also [#16], [#17], [#18], [#19], [#20], [#21], [#22], [#44],
[`translator/naming.md`], [`translator/printing.md`] and
[`reports/printing-blowup-2026-10-12.md`].)

**Terms**.  The *closure* of a declaration is every constant it reaches through
types, values, constructors, recursors and their rules, ordered by strongly
connected components; the *scaffold* is the Agda module the printer writes for
a closure under profile U, every constant with its printed type as a postulate
except `Nat` and `String`, bound to their builtins, the type abbreviations, the
roots' values and the auxiliaries the sharing pass makes.

**Decision**.  The emitter's shape is as follows; the first three items are
built, the rest are the roadmap's plan.

+  **Names are encoded injectively from Lean's structured names**, never from
   their printed strings: components joined by `:`, with `~` escapes for
   underscores, Unicode, numeric and empty components and Agda's keywords, and
   no truncation, hash or collision index, so that a declaration's identifier
   never depends on what else is translated; a reverse-map sidecar beside each
   module maps identifiers back to structured names ([#16]).
+  **Visibility is read from the kernel's types, and lambdas are repaired to
   match**: every argument's visibility comes from the head's type, instance
   arguments are always passed in instance braces, and a definition's leading
   lambdas print as left-hand-side patterns, since Agda inserts the implicit
   ones itself ([#17]).
+  **Repeated closed subterms become auxiliary definitions** before printing,
   those of at least 32 expression nodes, kernel-checked and owned by the
   declaration they came from ([#17]); the threshold is where the measured
   bytes bottom out, since a small shared subterm costs as much in references
   as it saves; sharing across declarations and a blowup factor tracked in CI
   are [#44]'s.
+  **Every sort prints as `Set` under profile U**, with `--type-in-type` alone
   (§ 3, § 4).
+  **One Agda module per Lean module, under a root per profile and layer**,
   importing the images of the Lean module's imports, with an `.agda-lib` file
   and an import graph ([#22]; the roots by [#37]).
+  **Structure-like inductives become records with eta and the rest `data`;
   recursors become pattern-matching definitions whose clauses are the kernel's
   rules; theorems go in `opaque` blocks and definitions stay transparent;
   Lean's `opaque` is Agda's `opaque`; axioms are postulates under U and
   parameters from Milestone 3; the quotient primitives are postulates with a
   `REWRITE` rule under U** ([#18] to [#21]).

**Evidence**.

+  **Names**.  The scheme is injective by construction, was checked for
   collisions over every name of the atlas, and round-tripped the names of all
   771,129 imported constants; printed names with macro scopes fail Lean's own
   name-literal decoder, which is why the sidecars store tagged components
   (LF-9).  lyphyser's `stringifyIdent` does not distinguish a literal dot in a
   component from a separator, and rocq-lean-import asks Rocq for a fresh
   identifier on a clash and warns that collisions remain possible
   ([`translator/naming.md`]).
+  **Visibility and repair**.  In every type and value of `nat-gcd-self`'s
   closure, 29 lambdas are repaired at the top and 198 below; with the repair
   off Agda refuses four of that scaffold's types with `WrongHidingInLambda`.
   `ByteArray`'s field is named `data`, an Agda keyword, which the subscripted
   binder names avoid ([`translator/printing.md`], Binders, Binder repair).
+  **Sharing**.  The three core-Lean corpus terms are barely shared (2.0, 3.6
   and 4.4 printed nodes per distinct subterm, 23.5 in the worst declaration),
   so the pass takes `nat-gcd-self`'s full rendering only from 431,486 to
   417,558 bytes, 0.61 of its export; on a shared term it is what keeps the
   text linear, `Nat.add` doubled ten times printing in 1,288 bytes with the
   pass against 19,498 without, and a tree of 2^20 leaves in 100 nodes against
   2^22 − 3.  The bytes form a U-shaped curve in the threshold: at 32 they are
   lowest for `nat-gcd-succ` and 2.2 percent above the lowest for
   `nat-gcd-self`, with 9 and 15 auxiliaries against 133 and 218 at a threshold
   of 8, each auxiliary repeating its owner's long name and adding a type.  The
   printed text is 15 to 40 bytes per export record with the pass off and at
   most 48 at any threshold, against the export's 63 to 67, so it is smaller
   than the export it came from ([`reports/printing-blowup-2026-10-12.md`],
   Size against the threshold, A shared term).  lean2dk's text output was two
   to three orders of magnitude larger than its `.olean` input because pointer
   sharing is lost ([`related-work.md`], lean2dk).
+  **Why one module per Lean module**.  lyphyser's one output file ran Agda out
   of memory on larger tasks.  Agda's scope check of the scaffolds grows faster
   than the module: 6.0 s for `substructure-closure-le`'s 0.7 MB, 49.8 s for
   1.1 MB, 186.5 s for 3.0 MB and 1,652.4 s for `real-sqrt-nonneg`'s 7.5 MB,
   each a whole closure of 1,879 to 11,036 constants in one module, far more
   than the module that declares the root holds; what the image of one Lean
   module costs is [#22]'s and [#43]'s to measure
   ([`reports/printing-blowup-2026-10-12.md`], Every corpus entry).  hol2dk,
   which took HOL Light's libraries into Rocq (17,500 theorems in its
   Multivariate release), bounds Rocq's memory with one file per theorem and an
   interface file that declares the theorem as an axiom ([`related-work.md`],
   hol2dk).
+  **What Agda refuses today**.  Under profile U Agda checks 17 of 21, 104 of
   201 and 139 of 266 values of the three core-Lean closures, and every refusal
   is an `UnequalTerms` that needs a definition unfolded or a recursor
   computed: `Nat.rec`, instance projections, literals against `OfNat.ofNat`,
   `Quot.lift` in `funext`, K-like reduction in `eq_of_heq`.  All but the
   K-like one are the emitters' work, and that one waits for the normalizer
   (§ 2); none is a wrong visibility, a scope error or a parse error
   ([`translator/printing.md`], What Agda checks).
+  **Records, recursors, opaque**.  Agda's records have eta, recursive ones
   included where the positivity checker permits (probe `P10cRecursiveRecord`),
   and Lean's structure eta is used in the mathematics of three corpus closures
   at no cost in Agda; the hand translations replace every `brecOn` and
   `noConfusion` by pattern matching; and `RealSqrtNonneg.agda` makes `sqrt`
   Agda-`opaque` and proves its lemma in an `unfolding sqrt` block, mirroring
   Lean's `unfold sqrt`, where a control without the clause fails
   ([`foundations/gap-report-corpus.md`], `structure-eta`, `k-and-uip`,
   `projections-and-let`, `trust-escape-hatches`).

**Status**.  Adopted for names, printing and sharing (PRs [#74], [#77]); the
rest is the roadmap's.  Open: [#18] to [#23], [#25] and [#44]; and the erasure
of `autoParam` syntax trees from closures, which the gap report finds in five
of the twelve and which no issue owns.

---

## 8.  The corpus as the oracle, and one pinned toolchain

(See also [#3], [#6], [#13], [#23], [#49], [`corpus/README.md`], [`pinning.md`]
and [`licensing.md`].)

**Terms**.  The *corpus* is the set of Lean declarations translated into Agda
by hand before any translator existed, one directory per entry with the Lean
statement, its exported kernel term, the idiomatic Agda and notes on what the
translation needed; the translator is built to reproduce it.

**Decision**.  Twelve declarations, nine of Mathlib's and three of Lean's core
library, selected so that every entry of the gap catalog but
`trust-escape-hatches`, which no translated entry can exercise, is exercised at
least once, are the translator's test oracle; its golden tests ([#23]) and its
comparison with lyphyser's tool ([#24]) run on them.  Every tool the pipeline
runs today is pinned and moves on purpose: Lean v4.33.1, Mathlib tag v4.33.1,
lean4export v4.33.0, and Agda 2.8.0 with agda-stdlib 2.3 and cubical 0.9, all
from one `nix develop`, and Mathlib is never rebuilt from source; Lean4Less,
which nothing runs yet, is not pinned, and its pin lands with [#26].  The
translator is Apache-2.0, and so is every library generated from Mathlib, as a
derived work of it; a library generated from another Lean library carries that
library's license, and one whose license is incompatible with Apache-2.0 is not
translated until the question is settled with its authors; code adapted from a
predecessor keeps its notice and is listed in `NOTICE`; an unlicensed
predecessor (Lean4Less, Predicativize) is used as an external tool and never
copied.

**Evidence**.

+  **The hand translations came first on purpose**, and found four things the
   plan had assumed wrongly and one it had not asked: `Nat.gcd`'s equation
   needs no K-like reduction at the pin (LF-6); impredicativity is essential
   only in one entry's definitions, not in its theorem; structure eta is not
   what `Subtype.coe_eta`'s kernel term uses; `funext` cannot be a theorem
   under the parameter record and is a parameter of its own; and `propext` over
   all of `Set` is refutable, so it is stated over h-propositions
   ([`foundations/gap-report-corpus.md`], Findings, `impredicative-prop`,
   `structure-eta`, `quotients`, `axioms`; [`corpus/README.md`], Coverage).
+  **The coverage is flat by closure**.  A *carrier* is a shared declaration
   that brings a feature into every closure that reaches it, and a few of them
   (`eq_of_heq`, `funext`, `autoParam`'s syntax trees, `simp`'s `eq_self`)
   account for most of the coverage table's marks: `universe-levels` and
   `projections-and-let` in all twelve entries, `axioms` in eleven, `k-and-uip`
   and `large-elimination` in ten.  A translator meets each carrier once, in
   the declaration that carries it ([`foundations/gap-report-corpus.md`], The
   coverage table).
+  **Sizes**.  Exports run from 29,267 bytes (`set-ext`) to 41,933,263
   (`real-sqrt-nonneg`) and the idiomatic files from 16 to 289 lines of code;
   the ratio between a kernel term and a mechanical rendering Agda accepts is
   not yet measurable, since no rendering of a whole entry checks, and [#23]
   and [#44] take it ([`foundations/gap-report-corpus.md`], Sizes, What M2-9
   will measure).
+  **The pins**.  Lean's `.olean` files are specific to one release, so every
   Lean tool in the pipeline runs at the pin or as a separate program at its
   own; `lake update` without `--keep-toolchain` rewrites `lean-toolchain`
   through the symlink and, when lean4-nix lacks the version Lake wrote, breaks
   every shell; Mathlib's cache at the tag is 8,690 files, 440 MB compressed
   and 7.1 GB unpacked ([`pinning.md`]).  The pin is the newest Lean lean4-nix
   carries, with Mathlib's matching tag.
+  **Licensing**.  Lean, Mathlib, lean4export, lean2dk and lyphyser's tool are
   Apache-2.0; Lean4Less and Predicativize declare no license; a generated
   library is a derived work of Mathlib ([`licensing.md`]).

**Status**.  Adopted (PRs [#62], [#64], [#66], [#69], [#70], [#75], [#76],
[#78]).  Open: the golden tests ([#23]); the upgrade rehearsal that corrects
the pinning procedure ([#49]); the outreach that may change the license answer
([#14]); and three manifest objects that omit `quotients` for a carrier their
closures hold ([`foundations/gap-report-corpus.md`], Corrections).

---

## 9.  Where it goes

+  **Milestone 2** finishes the emitter under profile U: inductive types and
   records ([#18]), recursors ([#19]), definitions, theorems and opaque
   constants ([#20]), quotients with a rewrite rule ([#21]), one module per
   Lean module ([#22]), the golden tests and `Init` fragments with the first
   performance baseline ([#23]), the comparison with lyphyser's tool ([#24])
   and the engineering standards ([#25]).
+  **Milestone 3** makes the translation faithful: the normalizer ([#26]), ADR
   0002 on the encoding of `Prop` ([#27]), the two universe steps ([#28],
   [#29]), quotients ([#30]), literals and `Nat.gcd` ([#31]), subsingleton
   elimination, `Acc` and eta ([#32]), profile K on `Init` and `Std` ([#33]),
   the first measurement of CC ([#34]) and the faithfulness report ([#35]).
+  **Milestone 4** turns the atlas into the layers: the v1 schema ([#36]), the
   layer rules and the layering record ([#37]), the parameters ([#38]),
   classical instances ([#39]), the promotion overlay ([#40]), the reports
   ([#41]) and the first layered fragment ([#42]).
+  **Milestones 5 to 7** scale ([#43] to [#50]), deliver CC and CU ([#51] to
   [#55]), and verify: the Arena entry ([#56]), the trust analysis ([#57]), the
   soundness-bug suite ([#58]), the foundational distance report ([#59]), the
   update of this record ([#60]) and the outreach ([#61]).
+  **Recorded and deliberately not taken**: the Dedukti route as the pipeline
   (§ 2); copying from lyphyser's tool before [#24] (§ 1); Lean4Less's
   eliminations of structure-like reduction and unit eta (§ 2); `--prop` under
   profile U (§ 3); `#print axioms` as the tier's source (§ 5).

---

## 10.  Decision log

| # | Decision | Status | Evidence |
| --- | --- | --- | --- |
| 1 | A direct translator written in Lean over the elaborated environment; export files only for the Arena entry | Adopted for the stages built ([#15], [#16], [#17]; PRs [#73], [#74], [#77]) | Every predecessor at scale loads `.olean`; rocq-lean-import's mathlib run with conversion checking off; LF-11; the twelve scaffolds print and scope-check (§ 1) |
| 2 | lyphyser's tool cited and not copied before [#24] | Adopted ([#4], PR [#65]) | 3,177 lines against Lean v4.12.0-rc1; its choices are the ones K and CC undo (§ 1) |
| 3 | Casts before any term is printed, with Lean4Less as the instrument, external and never copied while unlicensed; casts recorded apart from the axioms; the Dedukti route recorded as the alternative; re-implementation over Lean4Lean as the fallback | Proposed ([#26], [#30], [#36], [#14]) | 6.3 percent of `Std`'s constants, 15.5 percent growth; `prfIrrel` a theorem from `propext`; the chain never run; v4.28.0-rc1 against v4.33.1 (§ 2) |
| 4 | Lean4Less's eliminations of structure-like reduction and unit eta stay off | Proposed ([#26]) | Agda's records have eta; three closures use structure eta at no cost (§ 2) |
| 5 | Universe levels: specialize by which level parameters are zero, then predicativize with a hook for hand constraints; essential impredicativity reported | Proposed ([#28], [#29]) | rocq-lean-import and lyphyser; Predicativize's Theorem 6.1; refusals 6 to 17 and 7 to 20 without the first step; one essential case in twelve (§ 3) |
| 6 | Four profiles U, K, CC and CU; U with `--type-in-type` alone; K the stepping stone; CC the primary deliverable; CU constructive layer first | Adopted as targets (roadmap; U in PR [#77]); K [#33], CC [#34] and [#51], CU [#52] | Probes `P05` to `P07`, `P17`, `P19`; sixteen files `--safe`, fourteen CC, two CU, no postulate, no K; Lemma 3.8.5 (§ 4) |
| 7 | Two layers from the atlas: T0 and T1 constructive, T2 classical, T3 refused; both `--safe` with the principles as parameters | Adopted as the roadmap's shape; the rules [#37], the parameters [#38] | 14.7, 21.1, 64.2 and under 0.1 percent of Mathlib's constants; three of four T2 statements proved constructively (§ 5) |
| 8 | The tier is the exact axiom set's; any other axiom is T3; the hatches no axiom shows are atlas fields (`unsafe` and `partial` today, `implemented_by` from [#36]) whose refusal rule is [#37]'s | Adopted for the atlas (PR [#71]); the rule [#37] | 15 axioms at the pin and `native_decide`'s bespoke axioms; 1,837 under-reports, 532 Mathlib tiers wrong by `#print axioms`; 41 T3, all `lcProof` (§ 5) |
| 9 | `propext` and `Quot.sound` are constructive | Proposed ([#37]) | `funExt`, `hPropExt` and set quotients in the cubical library; two CU files instantiate the records (§ 5) |
| 10 | The encoding of `Prop` is open: A and B behind a switch, decided by [#27] in ADR 0002 in the measured order | Open ([#27]) | Seven entries as A, one both ways; `refl` against a witness; `P25bPropEqCC`; copies by level (§ 6) |
| 11 | Injective names from structured components, with reverse-map sidecars | Adopted ([#16], PR [#74]) | Zero collisions over the atlas; 771,129 names round-tripped; LF-9 (§ 7) |
| 12 | Visibility from the kernel's types, lambdas repaired, leading lambdas as patterns | Adopted ([#17], PR [#77]) | 29 and 198 repairs in one closure; `WrongHidingInLambda` without them (§ 7) |
| 13 | A sharing pass over closed repeated subterms at threshold 32 | Adopted ([#17], PR [#77]) | 431,486 to 417,558 bytes; 19,498 to 1,288 on a shared term; 2^22 − 3 to 100 nodes (§ 7) |
| 14 | One Agda module per Lean module | Proposed ([#22]) | lyphyser's out of memory; 6 s to 1,652 s for 0.7 MB to 7.5 MB in one module (§ 7) |
| 15 | Records with eta, `data`, recursors by pattern matching, opaque theorems, quotient postulates with a rewrite rule under U | Proposed ([#18] to [#21]) | Every refusal Agda makes today but the K-like one needs a definition unfolded or a recursor computed, which these supply; the K-like one waits for the normalizer (§ 7) |
| 16 | Twelve hand-translated entries as the oracle | Adopted ([#6] to [#10]) | Four assumptions corrected and one finding; coverage flat by closure (§ 8) |
| 17 | One pinned toolchain, Mathlib never rebuilt; Lean4Less's pin waits for [#26] | Adopted ([#3], PR [#64]) | `.olean` files per release; the symlink trap (§ 8) |
| 18 | Apache-2.0 for the translator and the libraries generated from Mathlib, the source's own license for other libraries; unlicensed predecessors as external tools | Adopted ([#13], PR [#62]) | The predecessors' licenses (§ 8) |

---

## References

+  **Issues**: the ancestry [#3], [#4], [#5], [#6], [#7], [#8], [#9], [#10],
   [#11], [#13], [#15], [#16], [#17]; this record [#12]; the outreach [#14];
   Milestone 2, [#18], [#19], [#20], [#21], [#22], [#23], [#24], [#25];
   Milestone 3, [#26], [#27], [#28], [#29], [#30], [#31], [#32], [#33], [#34],
   [#35]; Milestone 4, [#36], [#37], [#38], [#39], [#40], [#41], [#42];
   Milestone 5, [#43], [#44], [#49], [#50]; Milestone 6, [#51], [#52], [#53],
   [#55]; Milestone 7, [#56], [#57], [#58], [#59], [#60], [#61].
+  **PRs**: [#62] (the setup, with the license), [#64] ([#3]), [#65] ([#4]),
   [#66] ([#6]), [#68] ([#5]), [#69] ([#8]), [#70] ([#7]), [#71] ([#11]), [#72]
   (the register's index, LF-6 and LF-7), [#73] ([#15]), [#74] ([#16]), [#75]
   and [#76] ([#9]), [#77] ([#17]), [#78] ([#10]).
+  **Docs**: [`architecture.md`], the companion note; [`related-work.md`], the
   predecessors with every figure located in its source;
   [`foundations/gap-catalog.md`], the thirteen gaps and their probes;
   [`foundations/gap-report-corpus.md`], what the hand translations needed;
   [`reports/atlas-mathlib-v4.33.1-0df444a.md`], the tiers at the pin;
   [`reports/printing-blowup-2026-10-12.md`], the printer's measurements;
   [`translator/loading.md`], [`translator/naming.md`] and
   [`translator/printing.md`], the loader and the passes built;
   [`lean-findings.md`], the register (LF-1 to LF-11); [`pinning.md`];
   [`licensing.md`]; [`atlas/README.md`]; [`corpus/README.md`] and
   [`corpus/SCHEMA.md`].
+  **Code map** (`translator/`): `Lean2Agda/Core/Closure.lean`, the dependency
   closure and its order; `Core/Naming.lean` and `Core/ReverseMap.lean`, the
   identifiers and the sidecars; `Core/Print.lean`, `Core/Share.lean` and
   `Core/Scaffold.lean`, the printer, the sharing pass and the scaffold;
   `Main.lean`, the IO shell; `Atlas/`, the atlas producer; `tests/`, the
   golden scaffolds and the semantic checks; `scripts/python/scaffold_check.py`
   and `atlas_report.py` at the repository root's `scripts/python/`.

<!-- One definition per issue or PR cited above; PRs resolve to /pull/,
     issues to /issues/; the URLs are the API's. -->
[#3]: https://github.com/formalverification/lean2agda/issues/3
[#4]: https://github.com/formalverification/lean2agda/issues/4
[#5]: https://github.com/formalverification/lean2agda/issues/5
[#6]: https://github.com/formalverification/lean2agda/issues/6
[#7]: https://github.com/formalverification/lean2agda/issues/7
[#8]: https://github.com/formalverification/lean2agda/issues/8
[#9]: https://github.com/formalverification/lean2agda/issues/9
[#10]: https://github.com/formalverification/lean2agda/issues/10
[#11]: https://github.com/formalverification/lean2agda/issues/11
[#12]: https://github.com/formalverification/lean2agda/issues/12
[#13]: https://github.com/formalverification/lean2agda/issues/13
[#14]: https://github.com/formalverification/lean2agda/issues/14
[#15]: https://github.com/formalverification/lean2agda/issues/15
[#16]: https://github.com/formalverification/lean2agda/issues/16
[#17]: https://github.com/formalverification/lean2agda/issues/17
[#18]: https://github.com/formalverification/lean2agda/issues/18
[#19]: https://github.com/formalverification/lean2agda/issues/19
[#20]: https://github.com/formalverification/lean2agda/issues/20
[#21]: https://github.com/formalverification/lean2agda/issues/21
[#22]: https://github.com/formalverification/lean2agda/issues/22
[#23]: https://github.com/formalverification/lean2agda/issues/23
[#24]: https://github.com/formalverification/lean2agda/issues/24
[#25]: https://github.com/formalverification/lean2agda/issues/25
[#26]: https://github.com/formalverification/lean2agda/issues/26
[#27]: https://github.com/formalverification/lean2agda/issues/27
[#28]: https://github.com/formalverification/lean2agda/issues/28
[#29]: https://github.com/formalverification/lean2agda/issues/29
[#30]: https://github.com/formalverification/lean2agda/issues/30
[#31]: https://github.com/formalverification/lean2agda/issues/31
[#32]: https://github.com/formalverification/lean2agda/issues/32
[#33]: https://github.com/formalverification/lean2agda/issues/33
[#34]: https://github.com/formalverification/lean2agda/issues/34
[#35]: https://github.com/formalverification/lean2agda/issues/35
[#36]: https://github.com/formalverification/lean2agda/issues/36
[#37]: https://github.com/formalverification/lean2agda/issues/37
[#38]: https://github.com/formalverification/lean2agda/issues/38
[#39]: https://github.com/formalverification/lean2agda/issues/39
[#40]: https://github.com/formalverification/lean2agda/issues/40
[#41]: https://github.com/formalverification/lean2agda/issues/41
[#42]: https://github.com/formalverification/lean2agda/issues/42
[#43]: https://github.com/formalverification/lean2agda/issues/43
[#44]: https://github.com/formalverification/lean2agda/issues/44
[#49]: https://github.com/formalverification/lean2agda/issues/49
[#50]: https://github.com/formalverification/lean2agda/issues/50
[#51]: https://github.com/formalverification/lean2agda/issues/51
[#52]: https://github.com/formalverification/lean2agda/issues/52
[#53]: https://github.com/formalverification/lean2agda/issues/53
[#55]: https://github.com/formalverification/lean2agda/issues/55
[#56]: https://github.com/formalverification/lean2agda/issues/56
[#57]: https://github.com/formalverification/lean2agda/issues/57
[#58]: https://github.com/formalverification/lean2agda/issues/58
[#59]: https://github.com/formalverification/lean2agda/issues/59
[#60]: https://github.com/formalverification/lean2agda/issues/60
[#61]: https://github.com/formalverification/lean2agda/issues/61
[#62]: https://github.com/formalverification/lean2agda/pull/62
[#64]: https://github.com/formalverification/lean2agda/pull/64
[#65]: https://github.com/formalverification/lean2agda/pull/65
[#66]: https://github.com/formalverification/lean2agda/pull/66
[#68]: https://github.com/formalverification/lean2agda/pull/68
[#69]: https://github.com/formalverification/lean2agda/pull/69
[#70]: https://github.com/formalverification/lean2agda/pull/70
[#71]: https://github.com/formalverification/lean2agda/pull/71
[#72]: https://github.com/formalverification/lean2agda/pull/72
[#73]: https://github.com/formalverification/lean2agda/pull/73
[#74]: https://github.com/formalverification/lean2agda/pull/74
[#75]: https://github.com/formalverification/lean2agda/pull/75
[#76]: https://github.com/formalverification/lean2agda/pull/76
[#77]: https://github.com/formalverification/lean2agda/pull/77
[#78]: https://github.com/formalverification/lean2agda/pull/78

[`architecture.md`]: ../architecture.md
[`related-work.md`]: ../related-work.md
[`lean-findings.md`]: ../lean-findings.md
[`pinning.md`]: ../pinning.md
[`licensing.md`]: ../licensing.md
[`foundations/gap-catalog.md`]: ../foundations/gap-catalog.md
[`foundations/gap-report-corpus.md`]: ../foundations/gap-report-corpus.md
[`reports/atlas-mathlib-v4.33.1-0df444a.md`]: ../reports/atlas-mathlib-v4.33.1-0df444a.md
[`reports/printing-blowup-2026-10-12.md`]: ../reports/printing-blowup-2026-10-12.md
[`translator/loading.md`]: ../translator/loading.md
[`translator/naming.md`]: ../translator/naming.md
[`translator/printing.md`]: ../translator/printing.md
[`atlas/README.md`]: ../../atlas/README.md
[`corpus/README.md`]: ../../corpus/README.md
[`corpus/SCHEMA.md`]: ../../corpus/SCHEMA.md
