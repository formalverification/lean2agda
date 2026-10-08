<!-- File: docs/related-work.md -->

# Related work

lean2agda translates Lean 4 libraries into Agda libraries.  Most of the hard
parts of that translation have been attacked separately by others, and this
survey (issue [#4]) records what each predecessor did, how far it got, and what
this project takes from it, with every figure checked against its primary
source.  Later design discussions cite a section of this document, which
carries the locators into the sources.  It was checked in full on 2026-10-07;
each section carries the date it was checked and, where a repository is
involved, the revision, so that later issues (the authors' answers under [#14],
the side-by-side comparison with lyphyser's tool under [#24]) can add to one
section without re-checking the rest.

**How to read a figure**.  Every figure is followed by a footnote naming where
it stands in its source: a page or section of a paper, a file and line of a
repository at a named commit, a path in a JSON record, or the body of a pull
request, so that the next reader can check it in a minute.  A figure that could
not be found in its source is marked as unverified, with where it was looked
for.  Anything measured on a Lean toolchain, a Mathlib revision or an Arena
round is given with its version and should not be quoted without it.  Issues of
this repository are cited by number in brackets; the README and the roadmap
also name them by milestone position, so that M2-10 is [#24].

**Terms**.  The roadmap's Description section (`docs/GITHUB_PROJECT.md`)
defines the project's vocabulary; this survey uses it as follows.  A *profile*
is a set of Agda flags the output must check under, plus what remains a module
parameter: U (`--type-in-type`, scaffolding only), K (`--safe` with Agda's K
rule), CC (`--safe --cubical-compatible`) and CU (`--safe --cubical`).  A
*layer* is one of the two halves of the emitted library, constructive and
classical.  A *tier* sorts a declaration by the axioms it depends on and, for
the lowest tier, by the trust escape hatches it uses: T0 none, T1 `propext` or
`Quot.sound`, T2 `Classical.choice`, T3 `sorryAx`, `Lean.ofReduceBool`,
`unsafe` or `partial` definitions and `implemented_by`.  The *atlas* is the
per-declaration record of axioms, computability and kernel features from which
the layering is computed.  The *normalizer* is the roadmap's name for the
pipeline stage that replaces definitional proof irrelevance and K-like
reduction by explicit casts; it computes no normal forms, and the survey keeps
the name only because the roadmap uses it.  *K-like reduction* is a rule of
Lean's kernel: the recursor of a `Prop` inductive whose single constructor has
no fields, `Eq.rec` above all, reduces on any proof whose indices match the
constructor's, not only on the constructor itself; Agda's K is a principle of
pattern matching and gives no such reduction on a neutral proof.
*Structure-like reduction* is the kernel's eta rule for structures, under which
the recursor of a one-constructor type reduces on any major premise by
projecting its fields.  *Lean⁻* is Vaishnav's name for a sub-theory of Lean
obtained by dropping definitional rules; this project's Lean⁻ drops proof
irrelevance and K-like reduction, the two eliminations the Lean4Less paper
benchmarks, and [#26] decides whether the newer eliminations of structure-like
reduction and unit eta stay switched off, as Agda's own eta for records
suggests.

Each predecessor section answers the same questions in the same order, so that
the sections can be compared: what it translates and into what; how (from the
elaborated environment or from an export file, directly or through Dedukti);
how it handles `Prop`, universe levels, proof irrelevance and K, quotients, and
axioms; the scale it reached; its license and activity; and what lean2agda
takes from it, by roadmap issue.  Three sections close the survey: the Dedukti
route, the decision about lyphyser's tool, and the references.

## lyphyser/lean2agda

Checked on 2026-10-07 at commit `fbd86b6` (2024-09-13), the repository's last.

+  **What it translates**.  Lean 4 declarations, read from compiled modules,
   into one Agda file.  Its README calls it "An Agda exporter for Lean 4, that
   produces Agda code from elaborated Lean code, written in Lean" and "a proof
   of concept preliminary version".[^1]
+  **How**.  Directly, from the elaborated environment:
   `lake exe lean2agda <mods> [-- <decls>]` loads the named modules from the
   core library or `LEAN_PATH`, with their transitive dependencies, and
   translates them or the listed declarations.  The repository is a fork of
   lean4export that keeps its command-line interface; the README says the code
   "has been pretty much completely rewritten".  The git history shows the
   fork: the first eleven commits are lean4export's own, by Sebastian Ullrich,
   Siddhartha Gadgil and Mario Carneiro, from 2023-03-01 to 2023-11-30, and
   lyphyser's ten commits run from 2024-09-10 ("Initial commit of lean2agda")
   to 2024-09-13.[^2]  The GitHub repository was created on 2024-09-10 and last
   pushed on 2024-09-13.[^3]  It pins Lean `v4.12.0-rc1` and depends on
   Batteries.[^4]  The translation is a sequence of passes, each described in
   the README: deduplication (a new constant for every closed subexpression
   that occurs more than once within one constant, against the exponential
   blow-up of printing Lean's pointer-shared terms), lambda binder fixing (Agda
   requires a lambda's binder implicitness to match the Pi type's, Lean does
   not), unused-argument erasure, annotation (`mdata` nodes carrying the
   universe levels of projections and the implicitness of applied arguments),
   universe level specialization, and printing.[^5]
+  **`Prop` and universe levels**.  Lean's `Prop` becomes Agda's `Prop`, and
   every output file begins with `{-# OPTIONS --prop --type-in-type #-}`; the
   README explains that universe checking is disabled "since Agda doesn't yet
   have impredicative Prop".[^6]  Universe levels are handled by
   specialization, which is needed even under `--type-in-type`: Agda's syntax
   separates `Prop` from `Set`, and whether `Sort u` is one or the other, and
   whether `imax u v` collapses to zero, depends on whether a level parameter
   is zero, which a universe-polymorphic Lean constant leaves open.  So every
   constant is split into versions in which each `imax` second argument and
   each `Sort` argument is either always zero or always nonzero.  A version is
   described by its "level clauses", disjunctions of level parameters at least
   one of which the version assumes nonzero (a clause `u ∨ v` says that
   `max u v` is nonzero); inside a version, every level expression normalizes
   to a `max` of `lsuc` towers.  The README credits the idea to
   rocq-lean-import, the "Coq is a Lean typechecker" code in its words.[^7]
+  **Proof irrelevance and K**.  Not addressed as such: Agda's `Prop` supplies
   definitional proof irrelevance, `--type-in-type` removes the universe
   checks, and the rest is left to Agda's default theory with K.  That cannot
   cover Lean's large elimination from `Prop`: Agda lets a function from a
   `Prop` datatype into `Set` match only on the absurd pattern, and its
   documentation says of a `Prop`-valued equality type that "the corresponding
   eliminator cannot be defined because of the limitations on pattern
   matching".  The shipped example stays inside that limit: every instance of
   `Eq.rec`, `And.rec` and `False.rec` in it is the specialization with a
   `Prop`-valued motive, which Agda accepts and where its own irrelevance makes
   K-like reduction moot, and the `Set`-valued instance of `Acc.rec` is
   postulated, as the README says, "since Agda doesn't accept it because it
   breaks subject reduction", with `WellFounded.fixFEq` postulated "since it
   depends on unfolding Acc.rec".[^8]  A `Set`-valued `Eq.rec`, or K-like
   reduction on a neutral proof, would have no counterpart in this output, and
   the README does not discuss either.
+  **Quotients and axioms**.  "Quotients are currently postulated"; the README
   adds that higher inductive types "would be nicer if possible".  Axioms
   become postulates, as does every constant without a value.[^9]
+  **Scale**.  The README reports that the tool "works on relatively simple
   tasks like `lean2agda Init.Data.Nat.Gcd -- Nat.gcd_self`, but on larger
   tasks Agda runs out of memory when checking the single output file", and
   that emitting separate modules would help.  The one shipped example,
   `examples/Nat.gcd_self.agda`, is 6,942 lines.[^10]  The tool is 3,177 lines
   of Lean, counted by
   `find . -name '*.lean' -not -path './examples/*' -not -path './.lake/*' | xargs wc -l`
   at the checked commit; the count includes `Main.lean` and the 13-line
   `lakefile.lean`.[^11]  Inductive types become records where possible and
   `data` otherwise; recursors become definitions by pattern matching, "the
   only constants that have multiple definition patterns"; namespaces are
   flattened by turning the dot into a colon and qualifying every name in
   full.[^12]
+  **License and activity**.  Apache-2.0; the `LICENSE` file is lean4export's,
   added on 2023-05-30 and kept.  Dormant since 2024-09-13, with six stars on
   2026-10-07.[^3]
+  **What lean2agda takes**.  The pass structure, pass by pass and with
   citation: deduplication of closed subterms and binder fixing in the
   expression printer ([#17]), records for structure-like inductives ([#18]),
   recursors by pattern matching ([#19]), the namespace mapping ([#16]), and
   postulates for what the scaffolding profile cannot yet express ([#20],
   [#21]).  Its level clauses are the starting point of the
   `Prop`-instantiation specialization ([#28]).  Its out-of-memory finding on
   one file is the first evidence for multi-module emission ([#22]) and term
   size control ([#44]).  Its two postulated recursors are entries in the
   subsingleton-elimination work ([#32]).  The project's relationship to the
   tool is decided at the end of this survey, and [#24] (M2-10) runs both tools
   on the same declarations.

## Lean4Less

Checked on 2026-10-07.  The `main` branch stands at `5b66bbc` (2026-02-11) on
Lean `v4.28.0-rc1`; its `claude-stable` branch is newer, reaching `79cadc7`
(2026-06-17), and lean2dk pins that branch's commit `df479f2`
(2026-06-13).[^13]

+  **What it translates**.  A Lean environment into a Lean⁻ environment: the
   same constants, with every use of definitional proof irrelevance and K-like
   reduction made explicit as a typecast whose equality proof is built from a
   proof-irrelevance lemma and congruence lemmas.  The README describes it as
   "a tool for translating Lean to smaller theories", generically called Lean-,
   and as "a modification of Lean4Lean", Carneiro's Lean kernel written in
   Lean.  The paper's title names the method, an extensional-to-intensional
   translation.[^14]
+  **How**.  Directly, from the elaborated environment (`.olean` files), inside
   a modified Lean4Lean type checker that inserts a cast wherever the original
   checker would have used one of the eliminated rules.  The output is a set of
   `.olean` files, or with `--only` one constant's translation, together with
   `aborted.txt`, the list of constants whose translation was abandoned.  A
   fork of Lean4Lean with the two rules switched off, the Lean⁻ kernel,
   re-checks the output.[^15]
+  **`Prop` and universe levels**.  Unchanged: Lean⁻ keeps Lean's impredicative
   `Prop` and its level algebra.  The translation is about definitional
   equality, not about universes.
+  **Proof irrelevance and K**.  Eliminated, by construction.  The paper and
   the thesis justify the casts with an axiom,
   `axiom prfIrrel {P : Prop} (p q : P) : p = q`, and the paper says that
   assuming it "breaks some theoretical properties of Lean".[^16]  On
   2026-02-11 the repository replaced the axiom by a theorem: `prfIrrel` is now
   proved from `propext` (an inhabited proposition equals `True`, whose proofs
   are identified by elimination), so the translated environment adds no axiom
   to Lean's.[^17]  The consequence for this project is that a cast inserted
   into a tier-T0 constant brings a `propext` dependency with it; the atlas
   must record casts separately from the source's axioms, or the normalizer
   moves constants from T0 to T1 ([#26], [#36]).  Since 2025-04-10 the tool can
   also eliminate structure-like reduction, and since 2026-06-13, on its
   `claude-stable` branch, unit eta; Agda has eta for records, so neither is
   needed here, and [#26] decides what stays switched off.[^13]
+  **Quotients and axioms**.  Untouched: `Quot` and its reduction rule stay in
   Lean⁻, and Lean's axioms pass through.  The roadmap extends the cast
   mechanism to the computation rule of `Quot.lift` for targets without
   definitional quotients ([#30]).
+  **Scale**.  The thesis (section 7.1.1, page 159) and the paper report the
   same table, measured at Lean `v4.16.0-rc2` on an eight-core Xeon at 2.20 GHz
   with 32 GB.[^18]

   | Module | Constants | Using proof irrelevance / K-like reduction | Environment, input to output | Translation | Typechecking, input under the Lean kernel against output under the Lean⁻ kernel |
   | --- | --- | --- | --- | --- | --- |
   | `Std` | 29,859 | 1,736 / 134 (6.3 percent) | 226 MB to 261 MB (15.5 percent) | 18m02s | 2m19s against 3m9s (36.0 percent) |
   | `Mathlib.Algebra.Order.Field.Rat` | 113,899 | 2,965 / 237 (2.8 percent) | 1,485 MB to 1,501 MB (1.1 percent) | 32m16s | 5m11s against 5m44s (10.6 percent) |

   The two typechecking times are the input environment checked by the Lean
   kernel and the translated output checked by the Lean⁻ kernel, so the
   percentage is the cost of checking the casts; it is not a range.  The thesis
   also reports `Mathlib.Data.Real.Basic` translated, "containing several
   thousands of lines of code and thousands of uses of proof irrelevance and
   K-like reduction".[^18]  The limits are stated in the README's caveats and
   in the thesis.  The translation "does not currently scale beyond small
   libraries (e.g. the Lean standard library `Std`) or lower modules in the
   Mathlib import hierarchy", getting stuck or running out of memory on higher
   ones, and single definitions sometimes take more than ten minutes.  An
   expected type that itself needs patching produces "transport hell", output
   that can "explode" in size, which the README calls "inherent to the
   translation".  Casts are sometimes inserted where Lean⁻ did not need them.
   Running the tool to eliminate proof irrelevance but not K-like reduction
   makes its output verification recurse deeply, so the two are always
   eliminated together.  Constants whose typing needs large `Nat.gcd`
   computations are aborted: the README's explanation is that the defining
   equation `Nat.gcd (succ y) x = Nat.gcd (mod x (succ y)) (succ y)` holds
   definitionally in Lean only through K-like reduction, so `Nat.gcd` cannot be
   a kernel primitive in Lean⁻; the survey repeats that explanation without
   re-deriving it.[^19]  The `.olean` output is "currently broken" since Lean's
   module system changed.[^20]
+  **Why the normalizer exists**.  Where chapter 5 of the thesis opens (page
   113), it says that a direct Dedukti translation of Lean⁻ alone "will be
   limited to constructive logic, as Lean's proof of the excluded middle
   property makes essential use of proof irrelevance".[^21]  That sentence is
   about Dedukti; the Agda-side argument is this project's own and runs as
   follows.  Agda's `Prop` is definitionally proof-irrelevant but cannot
   eliminate into `Set` except by the absurd pattern, so Lean's
   large-eliminating propositions (`Eq`, `Acc`, `And`, `True` and the other
   subsingletons) have to live in `Set` on the Agda side, where two proofs are
   not definitionally equal; and K-like reduction on a neutral proof has no
   counterpart in Agda under any flag, since Agda's K is a pattern-matching
   principle and not a reduction.  Every Lean term whose typing used either
   rule therefore needs an explicit cast in Agda, under profile K as much as
   under CC, and `Classical.em` is the first such term that matters.  The casts
   are what let classical logic through; what the step loses is the list above
   (the aborted `Nat.gcd` constants, the modules it cannot finish, the terms it
   inflates), recorded per constant in `aborted.txt` and per run in the
   overhead figures.  How the proposition encoding interacts with this, `Prop`
   with casts or h-propositions in `Set`, is the open question of [#27].
+  **License and activity**.  No license file on 2026-10-07; the README invites
   pull requests.[^13]  The paper appeared at ICTAC 2025 (Marrakech, November
   2025, pages 202 to 219) and is on HAL under CC BY 4.0 ([lean4less-paper];
   the author's site carries the same PDF, [lean4less-paper-pdf]); the thesis
   was defended at ENS Paris-Saclay on 2026-03-10.[^22]
+  **What lean2agda takes**.  The normalizer itself and the name Lean⁻ ([#26]);
   the per-constant counts of proof-irrelevance and K-like uses as atlas fields
   ([#26], [#36]); the overhead figures above as the baseline [#26] measures
   against; the license question (the licensing decision [#13] and the contact
   [#14]); and the broken `.olean` output as the integration risk [#26] must
   resolve, by restoring it or by running the translator inside the Lean4Less
   process.

## lean2dk

Checked on 2026-10-07.  `main` stands at `471208f` (2026-06-13) on Lean
`v4.22.0-rc4`; the `claude-stable` branch, which `main`'s README calls "the
most feature-complete", stands at `29f9856` (2026-06-15) on Lean
`v4.18.0-rc1`.[^23]

+  **What it translates**.  A Lean⁻ environment into Dedukti: one `.dk` file
   per input Lean module, in a pure-type-system encoding of Lean⁻ with a
   rewriting-based encoding of universe levels (the thesis's chapters 2 and 3).
+  **How**.  From the elaborated environment, running Lean4Less first as an
   external dependency (`--no-elim` skips it); the translation is written in
   Lean and uses `MetaM`'s type inference for function types and
   projections.[^24]  Checking the output needs a patched Dedukti.  The
   `claude-stable` README explains that stock Dedukti "cannot check the output
   of realistic Lean modules" because the encodings of well-founded recursion,
   structure eta and universe levels drive its conversion into non-termination
   or exponential work, and it names the three kernel changes of the
   rish987/Dedukti fork it targets: lazy-delta congruence, memoized
   convertibility with reduction sharing, and per-declaration budgets that
   abort a declaration, naming it, instead of exhausting memory.[^25]
+  **`Prop`, universe levels, proof irrelevance, K, quotients, axioms**.
   `Prop` and the level algebra are encoded, not eliminated; the thesis devotes
   a chapter to a normalizing rewrite system for Lean's universe levels with
   `imax`.  Proof irrelevance and K-like reduction are gone before lean2dk
   runs.  Quotient reduction is encoded as rewrite rules for `Quot.ind` and
   `Quot.lift` applied to `Quot.mk`, alongside the other reduction rules;
   axioms are declared.[^26]
+  **Scale**.  The thesis (section 7.1.2, pages 160 to 161) reports "some
   initial success in translating lower-level modules of the standard library
   (like its classical logic library `Init.Classical`)", and that the
   translation "scales quite poorly to higher-level standard library modules,
   resulting in translated output Dedukti files that are 2-3 orders of
   magnitude larger than the original input Lean `.olean` files", which it
   attributes to the loss, in a text format, of the pointer sharing between
   common subterms that `.olean` files have.[^27]  The `claude-stable` branch,
   three months after the defense, "translates and type-checks
   `Init.Data.Nat.Lemmas` end-to-end against a patched Dedukti kernel", with "a
   couple dozen" constants value-stubbed (emitted with their type but no body)
   because, in its README's words, their cost after translation "is inherent to
   the encoding rather than the kernel": bignum `Nat` primitives on a unary
   encoding, the `omega` machinery's exponentially large normal forms, and
   `String` literals.  Lean's own kernel checks the first class with GMP and
   Agda's builtin naturals compute natively too, so that class is a problem of
   the encoding, not of the target ([#31]).  Its README is explicit that a
   stubbed constant is "trusted, not checked".[^28]
+  **License and activity**.  Apache-2.0.  Active through June 2026, when the
   `claude-stable` work landed.[^23]
+  **What lean2agda takes**.  The measured cost of printing shared terms as
   text, which the expression printer ([#17]) and term size control ([#44])
   must avoid; the three stub categories as the checklist for the literal and
   kernel-arithmetic work ([#31]); and the Dedukti route as a baseline,
   discussed below.

## rocq-lean-import

Checked on 2026-10-07 at `2d28bbe` (2026-10-01).

+  **What it translates**.  Lean export files into Rocq, through a plugin
   command `Lean Import`; the author is Gaëtan Gilbert, under the handle
   SkySkimmer.  The README's first line, "Alpha Announcement: Coq is a Lean
   Typechecker", dates from the Lean 3 era; the plugin now takes lean4export's
   output for Lean 4 and names the commits that still take Lean 3's.[^29]
+  **How**.  From an export file, directly into Rocq's kernel, with no
   intermediate framework.
+  **`Prop` and universe levels**.  Lean's `Prop` becomes Rocq's `SProp`.
   Because Rocq's universe-polymorphic constants cannot be instantiated at
   `SProp`, every constant is duplicated per pattern of universe parameters
   instantiated at `Prop`: the all-`Type` version keeps the base name and the
   others get an `_instX` suffix, `X` the bitmask of `Prop` positions, produced
   lazily as they are needed.  Each universe expression (`max`, `imax`,
   successors) is reduced to a Rocq algebraic universe, and since Rocq
   instantiates polymorphic universes only with atomic ones, each distinct
   algebraic universe gets a surrogate parameter, appended to the constant's
   parameters with the constraints that relate them; `imax(a, b)` becomes
   `SProp` when `b` does, and otherwise the maximum.[^30]
+  **Proof irrelevance and K**.  `SProp` supplies definitional proof
   irrelevance.  The translation needs definitional UIP: "Sadly this is not
   enough to make the translation work in Coq without UIP, because such a Coq
   also lacks the special reduction of the eliminator of equality".  Where Lean
   allows large elimination and Rocq's `SProp` does not (the README's example
   is `Acc`), the plugin detects the case and disables universe checking while
   declaring the inductive.[^31]
+  **Quotients and axioms**.  Quotients are emulated with private inductive
   types in a module `Coq.Lean` that must be required first; it also
   predeclares equality, since `Quot.lift` mentions it.  Axioms are declared as
   axioms.[^32]
+  **Scale**.  The README's "Experimental results", measured on the author's
   laptop with Lean 3 exports, are as follows.[^33]  `core.lean`, 584
   definitions and inductives, "passes without issue in about 2s".  The whole
   Lean 3 stdlib, 10,244 definitions and inductives (10,245 entries, 24,081
   possible instances), "cannot be checked as some conversion problems are
   pathological", `two_pos` being the typical example; with a 10 s per-entry
   timeout the import takes 451 s and 720 MB and skips 89 entries, 32 of them
   timeouts and the rest missing dependencies.  Lean 3 mathlib, 66,400 entries,
   with the timeout and with `Unset Conversion Checking` takes 1h13min and 10
   GB, produces 1.4 GB of `.vo`, and skips 11,867 entries.  The qualifier
   matters: with conversion checking off, Rocq declares the terms without
   checking them, so the mathlib run measured parsing and declaration, not
   verification; the entries it skipped are those that still hit the 10 s
   timeout and everything depending on them (the first is
   `real.linear_order._proof_5`).  What the figures calibrate is the scale of a
   kernel-level import of a Mathlib-sized library: an hour and ten gigabytes to
   declare it, and no complete check within any timeout the author tried.
+  **License and activity**.  LGPL-2.1.  Active: the last commits, from
   September and October 2026, update the Lean 4 core test and the universe
   handling.[^34]
+  **What lean2agda takes**.  The duplication per `Prop`-instantiation pattern,
   which lyphyser's level clauses also implement, as the model for [#28]; the
   surrogate-parameter treatment of algebraic universes as one of the options
   for [#29]; `Acc` as the known hard case of subsingleton elimination ([#32]);
   and the pathological-conversion finding as the reason the Agda performance
   study ([#43]) and term size control ([#44]) come before any Mathlib-scale
   run.

## Predicativize

Checked on 2026-10-07 at `3aeccde` (2026-06-17, continuous integration added);
the last substantive commit is `55894a2` of 2022-11-01.[^35]

+  **What it translates**.  Dedukti developments written in an impredicative
   pure type system (Matita's Calculus of Inductive Constructions as its
   Dedukti exporter encodes it, and a fragment of Isabelle's HOL library) into
   Dedukti developments in a predicative universe-polymorphic theory, the
   paper's UPP, and from there into Agda files (`-a`, or `-at` to typecheck
   them too).[^36]
+  **How**.  Dedukti to Dedukti, by universe-polymorphic elaboration: each
   entry is rewritten with level metavariables, the typing constraints between
   levels are collected, a unification algorithm solves them, and the solved
   entry is generalized over its remaining level variables.  The paper's
   section 6 proves that not every solvable level-unification problem has a
   most general unifier (Theorem 6.1) and characterizes the single equations
   that do; the algorithm is partial, and extra constraints can be supplied by
   hand (`--cstr`).[^37]
+  **`Prop`, universe levels, proof irrelevance, K, quotients, axioms**.
   Impredicative `Prop` is what the tool removes: a proof survives if its uses
   of impredicativity are inessential, that is, if its level constraints have a
   solution.  Matita's theory has none of definitional proof irrelevance, K or
   quotients, so the tool says nothing about them.
+  **Scale**.  The LMCS paper (section 8, pages 23:34 to 23:35) reports
   Matita's arithmetic library translated to Agda that "typechecks with the
   --safe flag", containing, "as far as we know", "the very first proofs in
   Agda of Bertrand's Postulate and Fermat's Little Theorem", and also "the
   Binomial Law, the Chinese Remainder Theorem, and the Pigeonhole Principle".
   Human intervention was needed twice.  Level constraints were added by hand
   for some constants, listed in `extra_cstrs/matita.dk`, to make the library
   predicative; and "because the rewrite rules in the Dedukti files cannot be
   translated to Agda", the authors "had to define the inductive types and
   recursive functions manually in Agda", assembling type formers and
   constructors that had been translated as postulates into inductive
   declarations and adapting the rewrite rules, emitted as comments, into
   function definitions.  The total translation time "from Dedukti (CIC) to
   Dedukti (UPP) and then to Agda, is about 32 minutes on a machine with an i7
   processor"; the repository README gives about 37 minutes with two theorems
   (`lt_4_to_fact` and `le_fact_10`) and about 7 minutes without them.[^38]
   Compressed sizes (Table 1): Matita 67, Dedukti (CIC) 640, Dedukti (UPP) 570,
   Agda 190 KB.  The result is on Zenodo ([predicativize-zenodo], DOI
   10.5281/zenodo.10686897; published 2024-02-21, CC BY 4.0, a 266,130-byte
   archive, typechecked with Agda 2.6.3).[^39]  Remark 6.3 and the conclusion
   report that Agda answers "Failed to solve the following constraints" for an
   entry whose level constraint (`_0 ⊔ _1 = _0 ⊔ _2`) their algorithm solves
   (Example 6.12), and the authors suggest that "our work could also be used to
   improve Agda's unification algorithm"; such a constraint has more than one
   solution, and whether Agda should pick one is a design question the paper
   does not take up.[^40]
+  **License and activity**.  No license file.  Dormant since November 2022
   apart from the 2026 CI commit.[^35]  The preliminary version is the CSL 2023
   paper, with Ashish Kumar Barnawal as third author; the journal version is
   LMCS 20(3), 2024, article 23, published 2024-09-10.[^41]
+  **What lean2agda takes**.  The elaboration algorithm and the
   most-general-unifier characterization, which the predicativization stage
   ([#29]) implements over Lean's levels after [#28] has removed `imax`; the
   two interventions as warnings, since a direct translator emits `data` and
   pattern-matching definitions natively ([#18], [#19]) but must expect some
   constants to need level constraints the solver cannot find; and the `--safe`
   Agda library, checked with Agda 2.6.3 under its default theory with K, as
   the existence proof that a translated library can check under `--safe`,
   which is profile K's goal; it says nothing about `--cubical-compatible`,
   which is profile CC's.

## lean4export and the Lean Kernel Arena

lean4export checked on 2026-10-07 at `05d43a2` (2026-10-06, Lean
`v4.35.0-rc4`); Arena figures from `results.json`, whose `meta.timestamp` is
`2026-10-03 13:31:24 UTC` at revision `b1d6e91d`.[^42]

+  **lean4export**.  The Lean FRO's declaration exporter, writing the NDJSON
   export format, version 3.1.0 in `format_ndjson.md`: an initial `meta` object
   with the exporter, Lean and format versions; names, levels and expressions
   as tagged primitives, binders carrying `default`, `implicit`,
   `strictImplicit` or `instImplicit`; then declarations (axiom, definition,
   theorem, opaque, quot, inductive, constructor, recursor), the pieces of an
   inductive or mutual package grouped, recursors with their rules and a `k`
   flag.  The format carries data a checker would ignore, such as recursor
   types, "for the benefit of other tools that want all constants with their
   types".  Options `--export-unsafe` and `--export-mdata` include what is
   normally left out.  Apache-2.0; created 2023-03-01; bumped with every Lean
   release.[^43]
+  **The Arena** ([arena]).  A public benchmark of Lean kernel implementations:
   each checker is built and run on every test, a test being an export file
   with an expected outcome.  Exit codes are 0 for accept, 1 for reject and 2
   for decline; anything else is an error, and timeouts, derived from the
   official checker's wall times, count as declines.  Tests are grouped as
   real-world corpora, `bugs/` (soundness bugs found in a checker),
   `corner-cases/` (outcome `either`), `perf/`, `tutorial/` and `other/`.  The
   round in progress is rebuilt whenever a checker or test changes, so every
   figure below carries the JSON's timestamp.[^44]  On 2026-10-03 the JSON held
   25 checkers and 223 tests (134 accept, 71 reject, 18 either).  The `mathlib`
   test is an export of Mathlib at `d13f23b` under Lean 4.34.1 with lean4export
   3.1.0: 6,184,415,052 bytes ("5.8 GB" on the page, which labels GiB as GB)
   and 109,790,519 lines.  The official checker, v4.34.1, accepted it in 37.9
   minutes of wall time at 10.7 GB of resident memory; the page's time column
   is a virtual CPU time computed from instruction counts at 6.0 Ginstr/s,
   which gives 32.3 minutes for the same run.  The fastest accepting checker,
   sokonanoda, took 0.96 minutes of wall time, multi-threaded, about 40 times
   less than the official checker by wall time and about 15 times less by the
   page's virtual CPU time; Lean4Lean's entry took 39.0 minutes.[^45]
+  **What lean2agda takes**.  The export format as the translator's second
   input: the translator reads the elaborated environment, but the Arena entry
   ([#56]) must take NDJSON, and the format carries what a translator needs
   beyond the bare terms: binder implicitness, for readable Agda, and the
   recursor's `k` flag, which marks the recursors whose K-like reduction the
   normalizer eliminates.  The `bugs/` and `reject` tests seed the
   soundness-bug suite ([#58]).  The official checker's Mathlib time is the
   yardstick against which a translation-plus-Agda checker will be slow, and
   the reason [#56] is a completeness entry, not a performance one.

## hol2dk

Checked on 2026-10-07 at `986fe97` (2026-07-24).

+  **What it translates**.  HOL Light proofs into Dedukti, Lambdapi and Rocq;
   the Rocq output is published as the opam packages `coq-hol-light` (the
   Multivariate library) and `rocq-hollight-logic` (the Logic library).[^46]
+  **How**.  HOL Light is patched to record proof steps; a library is dumped,
   simplified by rewrite rules on proof steps and purged of unused theorems
   (for `hol.ml`, "60% of proof steps are useless after simplication" [sic]);
   the proofs are split one file per theorem, translated to Lambdapi, then to
   Rocq; HOL Light types and functions are mapped to the Rocq standard
   library's, so that a theorem about HOL Light reals becomes a theorem about
   Rocq reals.  To keep Rocq's memory bounded, each theorem also gets a `_spec`
   file declaring it as an axiom, which other proofs require instead of the
   proof.[^47]
+  **The theory**.  Simple type theory into the Calculus of Inductive
   Constructions: no impredicative `Prop` question, no universes, no K.  The
   Rocq library assumes classical logic, indefinite description, functional and
   propositional extensionality and proof irrelevance as axioms.[^48]
+  **Scale**.  The hol2dk README says the Multivariate library "contains more
   than 20,000 theorems"; the `coq-hol-light` 3.0.0 release note of 2025-01-21
   says "the whole Multivariate library (17,500 theorems)", and the 2.0.0
   release of 2024-12-17 covered the base library `hol_lib.ml` with "~3000
   theorems".  The README's performance table counts 40,728 theorems for
   `Multivariate/make_complex.ml` and 5,687 for `hol.ml`, a count that includes
   unnamed theorems; the three figures count different things.[^49]  The same
   table gives the cost on a 32-processor i9-13950HX with 128 GB: dumping
   Multivariate takes 2h30m and 135 GB, the Lambdapi translation 45 minutes,
   the Rocq translation 24 minutes, and checking the 91 GB of Rocq files
   21h14m.  The published library therefore ships its theorems as axioms, with
   a script that regenerates and checks the proofs in about 25 hours.[^50]
+  **License and activity**.  CeCILL 2.1.  Active through July 2026; the LPAR
   2024 paper describes the method.[^46]
+  **What lean2agda takes**.  The precedent that a library of this size can be
   translated between proof assistants and published, and the engineering
   shape: one file per theorem with interface files to bound memory ([#22],
   [#45]), proof simplification before output ([#44]), alignment of types to
   the target's standard library ([#50]), and provenance that lets a reader
   regenerate what was shipped as an axiom ([#47]).

## Foundations

Checked on 2026-10-07.

+  **Carneiro, *The Type Theory of Lean*** (MSc thesis, dated 2019-04-16).[^51]
   Presents Lean's theory in full (inductive types, a universe hierarchy with
   an impredicative `Prop`, proof irrelevance, subsingleton elimination, and
   the axioms of propositional extensionality, quotients and choice), proves
   unique typing, builds the set-theoretic model, and derives consistency
   relative to ZFC with n inaccessible cardinals for every finite n, which it
   shows is optimal.  It also proves that type checking is undecidable (section
   3.1, undecidability of definitional equality), that Lean's implementation is
   "a decidable non-transitive underapproximation of the typing judgment", and
   that subject reduction fails.  The gap catalog ([#5]) cites it for each
   rule.
+  **Abel and Coquand, *Failure of Normalization in Impredicative Type Theory
   with Proof-Irrelevant Propositional Equality*** (LMCS 16(2), 2020, article
   14).[^52]  Normalization fails in a type theory with an impredicative
   universe of propositions and a proof-irrelevant propositional equality; the
   counterexample adapts Girard's against System F with a type-equality
   decider, and refutes Werner's conjecture.  Lean has both ingredients, which
   is one reason its kernel's conversion is an underapproximation and a
   translation cannot rely on normal forms.
+  **Lean4Lean** (Carneiro, arXiv 2403.14064; repository
   `digama0/lean4lean`).[^53]  A Lean 4 kernel written in Lean, derived from
   the C++ implementation; the paper's abstract puts it 20 to 50 percent slower
   on Mathlib, and in the Arena round above it is about 3 percent slower, a
   newer build on a different machine; the repository also holds a formal
   statement of Lean's typing rules (`Lean4Lean.Theory`) and a proof that the
   implementation meets it (`Lean4Lean.Verify`).  Lean4Less is a modification
   of it, and its Arena entry is the figure above.  The arXiv record's latest
   comment reads "14 pages, submitted to CPP 2026"; the PDF's front matter
   carries a template placeholder and no venue, so none is cited here.
   Apache-2.0, pushed 2026-08-29, on Lean `v4.33.0-rc2`.  A companion
   repository, `lean4lean-model` (created 2026-08-02, no license), states the
   consistency theorem over the formal theory with Mathlib available and leaves
   its proof open.[^54]  For this project the repository matters in three ways:
   as the code the normalizer modifies, as the formal reference for what each
   kernel rule is ([#5]), and as the reference checker the Arena entry ([#56])
   is compared with.
+  **The HoTT book, Lemma 3.8.5**.[^55]  "There exists a type X and a family Y
   : X → U such that each Y(x) is a set, but such that (3.8.3) is false", where
   (3.8.3) is the axiom of choice in the form (∏(x:X) ∥Y(x)∥) → ∥∏(x:X) Y(x)∥
   and the sentence before the lemma says "we cannot relax the requirement that
   X be a set".  The proof takes X :≡ Σ(A:U) ∥2 = A∥, the type of types merely
   equal to the two-element type, which is a 1-type and not a set, and Y(x) :≡
   (x₀ = x), a family of sets; the two-element type is what makes X fail to be
   a set.  Lean's `Classical.choice` chooses an element of every nonempty type,
   hence of each Y(x) here, so under univalence it is contradictory even though
   every type it is applied to in the counterexample is a set.  That is what
   the README means by "even when restricted to h-sets".  A module parameter
   cannot make `--safe` code inconsistent, so the point is not soundness but
   vacuity: the classical layer checks under profile CC and can be imported
   from cubical code, but nothing in cubical Agda could ever instantiate its
   choice parameter, and which weaker principles can (choice for set-indexed
   families of sets, excluded middle for propositions) is what [#53], the
   choice-under-univalence study, settles.

## Mathlib measurements

Checked on 2026-10-07.

+  **Mathlib pull request 35685, "feat: reduce the use of Classical.choice"**
   ([mathlib-pr-35685]; R. Brasca, opened 2026-02-23).[^56]  An open draft, not
   merged, last updated 2026-09-15, whose branch runs on a custom Lean
   toolchain built from the author's fork (Lean core itself depends on choice
   through `grind`) and a custom Batteries.  Its body reports, from a script
   that walks every constant of the environment: "Currently, we have 430049
   declaration that depend on choice, over 775824 in total (55.4%).  For
   comparison, `master` has 446045 use of choice (57.5%)."  The total of
   775,824 is the branch's; the body gives master's count and percentage but no
   total for it.  The master figure is a measurement of Mathlib as it was when
   the body was written (the pull request was opened in February 2026 and its
   body last edited in September 2026, comparing its fork against Lean
   v4.34.0); the branch figure is the experiment's.  The project's first README
   draft read this as a reduction Mathlib had made; the README and issue [#11]
   have been corrected.
+  **Mendoza-Smith, *Geometric Measurements of the Axiom of Choice in Neural
   Proof Embeddings*** (arXiv 2606.28572, 2026-06-26).[^57]  "The full kernel
   dependency graph contains 471,260 Mathlib declarations, of which 171,522 are
   classical and 299,738 are constructive."  Classical here means reached from
   `Classical.choice` in the kernel dependency graph, the appendix's
   "Classical.choice-reached".  The paper does not state the Mathlib revision;
   its repository's README pins Mathlib `v4.29.0-rc8` (`9f0aee2`) for the
   compiled library and LeanDojo traces at Mathlib `1bc7728a`.[^58]
+  **Why the denominators differ**.  The pull request's script iterates over
   `env.constants` of an environment that imports all of Mathlib: Lean core,
   Batteries and Mathlib together, every auxiliary and compiler-generated
   constant included (equation lemmas, `match` auxiliaries, `_proof_n` terms,
   instances), at the master of the body's writing.  The paper's population is
   "Mathlib declarations" of a kernel dependency graph built by its own script,
   at the revision its repository pins, with a selection the paper leaves to
   the repository.  The two are counts of different sets at different
   revisions, 57.5 against 36.4 percent classical, and cannot be reconciled
   from what is published; the atlas ([#11]) computes both kinds of count
   itself, states its denominator, reports with and without auto-generated
   declarations, and explains its distance from each.
+  **Mathlib's statistics page**, read 2026-10-07: 137,930 definitions, 290,195
   theorems, 772 contributors.  The page has no history, so the day is part of
   the figure.[^59]

## The Dedukti route

The chain exists in pieces: Lean4Less takes Lean to Lean⁻; lean2dk takes Lean⁻
to Dedukti; Predicativize takes an impredicative Dedukti development to a
predicative one and prints Agda.  The survey found no report of the chain run
end to end (the thesis's lean2dk results stop at Dedukti, and Predicativize's
inputs were Matita and HOL), and whether Predicativize accepts lean2dk's
encoding is open: Predicativize elaborates terms in its own pure-type-system
theory (`theory/pts.dk`), reached from a source encoding through a
meta-rewriting file, and lean2dk's encoding carries Lean's `imax`, its level
normalization by rewriting, `Nat` and `String` literals, and quotients, none of
which Predicativize's Matita input had.  Someone would have to write that meta
file and find out what the solver does with Lean's level constraints.

What the route would give: an independent baseline for the direct translator,
built from tools that exist; a check of the Lean⁻ step by a kernel in a
different framework; and a collaboration with Deducteam, whose tools these are.
What it would lose: readability, since Predicativize's own case needed
inductive types and recursive functions rebuilt by hand in Agda; robustness,
since the thesis reports output two to three orders of magnitude larger than
its input, and the current lean2dk needs a patched Dedukti and value-stubs the
constants its README says no term-based kernel can check after translation;
and, less decisively, the metadata the emitter needs (binder implicitness,
names, module structure, docstrings), which a kernel-level encoding drops and a
side table keyed by constant name would have to re-attach.  The roadmap
therefore builds the direct translator and keeps the route as a comparison:
[#24] compares against lyphyser's tool, the nearer baseline, at the end of M2;
the Dedukti route is compared once lean2dk translates and checks, without
stubs, a module the direct translator also handles; that comparison is of the
two checks of one Lean⁻ module, Dedukti's against Agda's, and needs no
Predicativize.

## lyphyser/lean2agda: the decision

Decision: cite lyphyser's tool, borrow its ideas with attribution in the design
notes, and reuse none of its code before [#24] (M2-10) has run both tools on
the same declarations.  If that comparison shows a pass worth taking, the rule
in `docs/licensing.md` applies: the file carries the attribution the rule
requires (the source's copyright notice where one exists, and lyphyser's
repository has none beyond the Apache license text inherited from lean4export,
so the repository, author and commit), and it is listed in `NOTICE`; Apache-2.0
on both sides makes that straightforward.  The reasons are as follows.

+  The code is 3,177 lines against Lean `v4.12.0-rc1`; this project pins
   `v4.33.1` (`docs/pinning.md`), twenty-one releases later, so a pass is not
   taken by copying a file but by porting it, and [#24] decides pass by pass
   whether porting beats re-deriving the idea against the current API.
+  Its design choices are the ones the profiles K and CC exist to undo:
   `--type-in-type` in place of level elaboration, `--prop` with a postulated
   `Acc.rec`, one output file, postulated quotients and axioms.  The
   scaffolding profile U shares them, which is why [#24] can compare the two
   tools there, but nothing past M2 can keep them.
+  What is valuable is the pass structure and the level-clause idea, and those
   are ideas, cited per section above and in the architecture note that [#12]
   writes.
+  The author's answer to the outreach under [#14] may change the decision,
   which is why the draft asks whether they would like to be involved rather
   than whether the code may be copied.

The same tests, applied to Lean4Less, come out worse: it has no license file,
its `main` is pinned to Lean `v4.28.0-rc1` against this project's `v4.33.1`,
and its `.olean` output is broken.  It is adopted anyway, and the asymmetry is
deliberate.  Lean4Less is not copied: [#13] decided that an unlicensed
predecessor is used as an external tool at its own toolchain and never copied,
and [#26] bridges the version gap by pinning Mathlib to a revision both tools
support, or by running the translator inside the Lean4Less process, and takes
the `.olean` repair as its first task.  The license question goes to its
authors under [#14].  If the answer is no, or silence, the fallback this survey
recommends is to re-implement the cast insertion from the paper and the thesis,
which are published under CC BY 4.0, over Lean4Lean, which is Apache-2.0; that
is a rewrite of a kernel modification, and [#26] should record it as the
fallback so that the project does not depend on an answer.

The message for the project's author to send is drafted in
`docs/outreach/lyphyser.md`; the answer, or silence after a month, is recorded
here under [#14].

## References

Each entry names the label the footnotes use, what the source is, and the
version checked; the link definitions follow the list.  An issue cited by
number is at github.com/formalverification/lean2agda/issues/ followed by the
number.

+  `[lyphyser-lean2agda]`: lyphyser, lean2agda, GitHub repository, Apache-2.0,
   checked at `fbd86b6` (2024-09-13):
   [github.com/lyphyser/lean2agda][lyphyser-lean2agda].
+  `[lean4less]`: Deducteam, Lean4Less, GitHub repository, no license file,
   `main` at `5b66bbc` (2026-02-11) and `claude-stable` at `79cadc7`
   (2026-06-17): [github.com/Deducteam/Lean4Less][lean4less].
+  `[lean4less-paper]`: R. Vaishnav, "Lean4Less: Eliminating Definitional
   Equalities from Lean via an Extensional-to-Intensional Translation", ICTAC
   2025; the HAL record hal-05310102 (CC BY 4.0) is the version read:
   [inria.hal.science/hal-05310102][lean4less-paper].
+  `[lean4less-paper-pdf]`: the same paper on the author's site:
   [rish987.github.io/files/lean4less.pdf][lean4less-paper-pdf].
+  `[vaishnav-thesis]`: R. Vaishnav, "Translating Proofs from Lean to Dedukti",
   PhD thesis, Université Paris-Saclay, defended 2026-03-10; the PDF on the
   author's site, 176 pages:
   [rish987.github.io/files/thesis.pdf][vaishnav-thesis].
+  `[lean2dk]`: Deducteam, lean2dk, GitHub repository, Apache-2.0, `main` at
   `471208f` (2026-06-13) and `claude-stable` at `29f9856` (2026-06-15):
   [github.com/Deducteam/lean2dk][lean2dk].
+  `[rocq-lean-import]`: G. Gilbert, rocq-lean-import, GitHub repository,
   LGPL-2.1, at `2d28bbe` (2026-10-01):
   [github.com/rocq-community/rocq-lean-import][rocq-lean-import].
+  `[predicativize]`: T. Felicissimo, Predicativize, GitHub repository, no
   license file, at `3aeccde` (2026-06-17):
   [github.com/Deducteam/predicativize][predicativize].
+  `[predicativize-paper]`: T. Felicissimo and F. Blanqui, "Sharing proofs with
   predicative theories through universe-polymorphic elaboration", LMCS 20(3),
   2024, article 23; the arXiv version 2308.15465 is the one read, and the CSL
   2023 version with A. K. Barnawal is cited in the text:
   [arxiv.org/abs/2308.15465][predicativize-paper].
+  `[predicativize-zenodo]`: T. Felicissimo, "Matita's arithmetic library in
   Agda", Zenodo, 2024-02-21:
   [doi.org/10.5281/zenodo.10686897][predicativize-zenodo].
+  `[lean4export]`: Lean FRO, lean4export, GitHub repository, Apache-2.0, at
   `05d43a2` (2026-10-06): [github.com/leanprover/lean4export][lean4export].
+  `[arena]`: the Lean Kernel Arena site, round in progress, page generated
   2026-10-03 13:31:24 UTC: [arena.lean-lang.org][arena].
+  `[arena-results]`: the site's `results.json`, same stamp:
   [arena.lean-lang.org/results.json][arena-results].
+  `[arena-repo]`: Lean FRO, lean-kernel-arena, GitHub repository, Apache-2.0,
   at `b1d6e91d`: [github.com/leanprover/lean-kernel-arena][arena-repo].
+  `[hol2dk]`: F. Blanqui, hol2dk, GitHub repository, CeCILL 2.1, at `986fe97`
   (2026-07-24): [github.com/Deducteam/hol2dk][hol2dk].
+  `[coq-hol-light]`: Deducteam, coq-hol-light, GitHub repository and its
   releases, read 2026-10-07:
   [github.com/Deducteam/coq-hol-light][coq-hol-light].
+  `[carneiro-thesis]`: M. Carneiro, "The Type Theory of Lean", MSc thesis,
   2019; `main.pdf` of release v1.0 of the digama0/lean-type-theory repository:
   [github.com/digama0/lean-type-theory/releases/tag/v1.0][carneiro-thesis].
+  `[abel-coquand]`: A. Abel and T. Coquand, "Failure of Normalization in
   Impredicative Type Theory with Proof-Irrelevant Propositional Equality",
   LMCS 16(2), 2020, article 14; arXiv 1911.08174:
   [arxiv.org/abs/1911.08174][abel-coquand].
+  `[lean4lean-paper]`: M. Carneiro, "Lean4Lean: Verifying a Typechecker for
   Lean, in Lean", arXiv 2403.14064, version 3 (2025-09-14), venue unconfirmed:
   [arxiv.org/abs/2403.14064][lean4lean-paper].
+  `[lean4lean]`: M. Carneiro, lean4lean, GitHub repository, Apache-2.0, read
   2026-10-07: [github.com/digama0/lean4lean][lean4lean].
+  `[lean4lean-model]`: M. Carneiro, lean4lean-model, GitHub repository, no
   license file, read 2026-10-07:
   [github.com/digama0/lean4lean-model][lean4lean-model].
+  `[hott-book]`: The Univalent Foundations Program, "Homotopy Type Theory:
   Univalent Foundations of Mathematics", 2013; the online PDF, version
   first-edition-82-g578b85c: [hott.github.io/book/hott-online.pdf][hott-book].
+  `[agda-prop]`: Agda documentation, "Prop", latest version, read 2026-10-07:
   [agda.readthedocs.io/en/latest/language/prop.html][agda-prop].
+  `[mathlib-pr-35685]`: R. Brasca, "feat: reduce the use of Classical.choice",
   Mathlib pull request 35685, open draft, read 2026-10-07:
   [github.com/leanprover-community/mathlib4/pull/35685][mathlib-pr-35685].
+  `[mendoza-smith]`: R. Mendoza-Smith, "Geometric Measurements of the Axiom of
   Choice in Neural Proof Embeddings", arXiv 2606.28572 (2026-06-26):
   [arxiv.org/abs/2606.28572][mendoza-smith].
+  `[mendoza-smith-repo]`: its repository, README read 2026-10-07:
   [github.com/rodrgo/geometric-axiom-of-choice][mendoza-smith-repo].
+  `[mathlib-stats]`: Mathlib statistics, read 2026-10-07:
   [leanprover-community.github.io/mathlib_stats.html][mathlib-stats].

[#4]: https://github.com/formalverification/lean2agda/issues/4
[#5]: https://github.com/formalverification/lean2agda/issues/5
[#11]: https://github.com/formalverification/lean2agda/issues/11
[#12]: https://github.com/formalverification/lean2agda/issues/12
[#13]: https://github.com/formalverification/lean2agda/issues/13
[#14]: https://github.com/formalverification/lean2agda/issues/14
[#16]: https://github.com/formalverification/lean2agda/issues/16
[#17]: https://github.com/formalverification/lean2agda/issues/17
[#18]: https://github.com/formalverification/lean2agda/issues/18
[#19]: https://github.com/formalverification/lean2agda/issues/19
[#20]: https://github.com/formalverification/lean2agda/issues/20
[#21]: https://github.com/formalverification/lean2agda/issues/21
[#22]: https://github.com/formalverification/lean2agda/issues/22
[#24]: https://github.com/formalverification/lean2agda/issues/24
[#26]: https://github.com/formalverification/lean2agda/issues/26
[#27]: https://github.com/formalverification/lean2agda/issues/27
[#28]: https://github.com/formalverification/lean2agda/issues/28
[#29]: https://github.com/formalverification/lean2agda/issues/29
[#30]: https://github.com/formalverification/lean2agda/issues/30
[#31]: https://github.com/formalverification/lean2agda/issues/31
[#32]: https://github.com/formalverification/lean2agda/issues/32
[#36]: https://github.com/formalverification/lean2agda/issues/36
[#43]: https://github.com/formalverification/lean2agda/issues/43
[#44]: https://github.com/formalverification/lean2agda/issues/44
[#45]: https://github.com/formalverification/lean2agda/issues/45
[#47]: https://github.com/formalverification/lean2agda/issues/47
[#50]: https://github.com/formalverification/lean2agda/issues/50
[#53]: https://github.com/formalverification/lean2agda/issues/53
[#56]: https://github.com/formalverification/lean2agda/issues/56
[#58]: https://github.com/formalverification/lean2agda/issues/58

[lyphyser-lean2agda]: https://github.com/lyphyser/lean2agda
[lean4less]: https://github.com/Deducteam/Lean4Less
[lean4less-paper]: https://inria.hal.science/hal-05310102
[lean4less-paper-pdf]: https://rish987.github.io/files/lean4less.pdf
[vaishnav-thesis]: https://rish987.github.io/files/thesis.pdf
[lean2dk]: https://github.com/Deducteam/lean2dk
[rocq-lean-import]: https://github.com/rocq-community/rocq-lean-import
[predicativize]: https://github.com/Deducteam/predicativize
[predicativize-paper]: https://arxiv.org/abs/2308.15465
[predicativize-zenodo]: https://doi.org/10.5281/zenodo.10686897
[lean4export]: https://github.com/leanprover/lean4export
[arena]: https://arena.lean-lang.org/
[arena-results]: https://arena.lean-lang.org/results.json
[arena-repo]: https://github.com/leanprover/lean-kernel-arena
[hol2dk]: https://github.com/Deducteam/hol2dk
[coq-hol-light]: https://github.com/Deducteam/coq-hol-light
[carneiro-thesis]: https://github.com/digama0/lean-type-theory/releases/tag/v1.0
[abel-coquand]: https://arxiv.org/abs/1911.08174
[lean4lean-paper]: https://arxiv.org/abs/2403.14064
[lean4lean]: https://github.com/digama0/lean4lean
[lean4lean-model]: https://github.com/digama0/lean4lean-model
[hott-book]: https://hott.github.io/book/hott-online.pdf
[agda-prop]: https://agda.readthedocs.io/en/latest/language/prop.html
[mathlib-pr-35685]: https://github.com/leanprover-community/mathlib4/pull/35685
[mendoza-smith]: https://arxiv.org/abs/2606.28572
[mendoza-smith-repo]: https://github.com/rodrgo/geometric-axiom-of-choice
[mathlib-stats]: https://leanprover-community.github.io/mathlib_stats.html

[^1]: [lyphyser-lean2agda], `README.md` at `fbd86b6`: the first line and the
    section "Current status".
[^2]: `git log --reverse --format='%h %ad %an %s' --date=short` in a clone of
    [lyphyser-lean2agda] at `fbd86b6`: `a4e9e21` 2023-03-01 Sebastian Ullrich
    "basic version" through `3e38d03` 2023-11-30 Mario Carneiro "update lean"
    (eleven commits), then `fd73502` 2024-09-10 lyphyser "Initial commit of
    lean2agda" through `fbd86b6` 2024-09-13 (ten commits).  The README's
    sentence on lean4export is in the section "How to Run".
[^3]: GitHub API, `repos/lyphyser/lean2agda`, read 2026-10-07: `created_at`
    2024-09-10T12:25:20Z, `pushed_at` 2024-09-13T21:57:31Z, `license.spdx_id`
    Apache-2.0, `stargazers_count` 6.  The LICENSE commit is `f1d507f` of
    2023-05-30 in the same log.
[^4]: [lyphyser-lean2agda] at `fbd86b6`: `lean-toolchain`
    (`leanprover/lean4:v4.12.0-rc1`) and `lakefile.lean` (`require batteries`).
[^5]: [lyphyser-lean2agda], `README.md` at `fbd86b6`, section "How does it
    work": "Lambda binder fixing", "Deduplication", "Unused argument erasure",
    "Expression annotation", "Universe level specialization".
[^6]: [lyphyser-lean2agda] at `fbd86b6`: `Lean2Agda/Aux/ModuleState.lean`, line
    48, prints the pragma; the quotation is from the README's section
    "Limitations".
[^7]: [lyphyser-lean2agda], `README.md` at `fbd86b6`, section "Universe level
    specialization".
[^8]: [lyphyser-lean2agda], `README.md` at `fbd86b6`, section "Limitations"; the
    postulates are at `Lean2Agda/Main/Translate.lean`, lines 246 to 247 and 297
    to 298.  In `examples/Nat.gcd_self.agda`, `grep -o '^[A-Za-z:]*:rec#[a-z]*'
    | sort | uniq -c` lists `Eq:rec#zn`, `Eq:rec#zz`, `And:rec#z` and
    `False:rec#z` and no other instance of those recursors (the suffix's first
    letter is the motive's level, `z` for zero, so `Prop`), and the `postulate`
    blocks hold `Acc:rec#zn`, `Acc:rec#nn` and `WellFounded:fixFEq#nn`.  Agda's
    rule and the sentence quoted are in [agda-prop], sections "Usage" and
    "Limitations".
[^9]: [lyphyser-lean2agda], `README.md` at `fbd86b6`, section "Quotients"; in
    `Lean2Agda/Main/Translate.lean`, axioms (lines 335 to 336) and `quot`
    declarations (line 344) are translated with no value, and the no-value
    branch (line 311) prints `postulate`.
[^10]: [lyphyser-lean2agda], `README.md` at `fbd86b6`, section "Current status";
    `wc -l examples/Nat.gcd_self.agda` gives 6942.
[^11]: The command, run on 2026-10-07 in a clone at `fbd86b6`, prints 3177 as
    its total; the largest files are `Lean2Agda/Main/Translate.lean` (406 lines)
    and `Lean2Agda/Main/FormatExpr.lean` (393).
[^12]: [lyphyser-lean2agda], `README.md` at `fbd86b6`, sections "Inductive
    types", "Recursors" and "Namespaces".
[^13]: GitHub API, `repos/Deducteam/Lean4Less`, read 2026-10-07: `license` null,
    `pushed_at` 2026-06-17T17:30:19Z.  `git log --all --date=short` in a clone:
    `5b66bbc` 2026-02-11 "feat: proof irrelevance is no longer an axiom" (the
    head of `main`); `7490d95` 2025-04-10 "feat: struct-like reduction
    elimination"; `df479f2` 2026-06-13 "feat: eliminate unit-eta (alongside
    proof irrelevance / K-like reduction)"; `79cadc7` 2026-06-17 "deps: use
    lean4lean claude-stable; add --unit-eta/--stub flags".  `lean-toolchain` on
    `main` reads `leanprover/lean4:v4.28.0-rc1`.  The README's last line invites
    pull requests.
[^14]: [lean4less], `README.md` at `5b66bbc`, first two paragraphs and the paper
    link; the paper's title is in [lean4less-paper].
[^15]: [lean4less], `README.md` at `5b66bbc`, sections "Running" (the `--only`,
    `out/` and `aborted.txt` descriptions) and "Verification".
[^16]: [lean4less-paper], HAL version: the code block "axiom prfIrrel {P : Prop}
    (p q : P) : p = q" in section 2 ("Theoretical Background") and the sentence
    "Assuming such an axiom breaks some theoretical properties of Lean" in
    section 4.1 ("Congruence Lemmas"); [vaishnav-thesis], Figure 7.1 (page 160)
    lists `axiom prfIrrel` in `PatchTheorems.lean`.
[^17]: [lean4less], commit `5b66bbc` (2026-02-11), which changes `README.md` and
    `patch/PatchTheorems.lean`; in the file at that commit, `propEqTrue` applies
    `propext` (lines 10 to 14) and `prfIrrel` is proved by `subst` and two
    `cases` (lines 16 to 22).
[^18]: [vaishnav-thesis], section 7.1.1, page 159: the sentence "with the
    versions of both libraries using Lean toolchain v4.16.0-rc2", the machine
    ("Intel Xeon 8-core CPU @ 2.20GHz and 32 GB RAM"), the table, and its
    footnote 1 ("When run with the Lean and Lean− kernels, respectively").  The
    `Mathlib.Data.Real.Basic` sentence is on the same page.  The same table is
    in [lean4less-paper] (pdftotext lines 727 to 742 of the HAL PDF).
[^19]: [lean4less], `README.md` at `5b66bbc`, section "Caveats/Limitations", all
    five bullets; [vaishnav-thesis], section 7.1.1, page 160 (ten minutes,
    memory) and section 7.1.3 ("Transport Hell", page 161 onward; the `Nat.gcd`
    paragraph near its end).
[^20]: [lean4less], `README.md` at `5b66bbc`, the NOTE in section "Running";
    commit `4db0b93` of 2025-06-25 is titled "chore: toolchain update (.olean
    output broken)".
[^21]: [vaishnav-thesis], chapter 5, opening paragraphs, page 113, the page
    before the first one headed "CHAPTER 5" in the running head.
[^22]: HAL record `hal-05310102`, read through the HAL API on 2026-10-07:
    conference "ICTAC 2025 - International Colloquium on Theoretical Aspects of
    Computing", produced 2025-11-24; the PDF's citation block gives Marrakech,
    pages 202 to 219, DOI 10.1007/978-3-032-11176-0_13, and CC BY 4.0.
    [vaishnav-thesis], title page: "Thèse soutenue à ENS Paris-Saclay, le 10
    Mars 2026", NNT 2026UPASG009, directed by Frédéric Blanqui.
[^23]: GitHub API, `repos/Deducteam/lean2dk`, read 2026-10-07: `license.spdx_id`
    Apache-2.0, `pushed_at` 2026-06-15T15:35:07Z.  In a clone: `git log main`
    head `471208f` 2026-06-13, `git log origin/claude-stable` head `29f9856`
    2026-06-15 "fix(deps): pin lean4less to df479f2"; `lean-toolchain` on `main`
    reads `v4.22.0-rc4` and on `claude-stable` `v4.18.0-rc1`.  The quotation is
    the note at the top of `main`'s `README.md`.
[^24]: [vaishnav-thesis], section 7.1.2, page 160; [lean2dk], `README.md` on
    `main`, section "Running" (`--no-elim`).
[^25]: [lean2dk], `README.md` on `claude-stable` at `29f9856`, section "Checking
    the translated output (requires a patched Dedukti)".
[^26]: [vaishnav-thesis], chapter 3 ("Universe Encoding"), and section 4.2
    ("Deriving Reduction Rule Encodings"), whose subsection "Quotient Reduction"
    gives the rewrite rules for `Quot.ind` and `Quot.lift`.
[^27]: [vaishnav-thesis], section 7.1.2, pages 160 to 161.
[^28]: [lean2dk], `README.md` on `main` at `471208f`, the note at the top;
    `README.md` on `claude-stable` at `29f9856`, section "Stubbing infeasible
    constants", including its "Caveat" paragraph.
[^29]: [rocq-lean-import], `README.md` at `2d28bbe`, sections "Introduction" and
    "How do I use this?".
[^30]: [rocq-lean-import], `README.md` at `2d28bbe`, sections "Prop
    instantiations" and "Algebraic universes".
[^31]: [rocq-lean-import], `README.md` at `2d28bbe`, section "Subsingletons".
[^32]: [rocq-lean-import], `README.md` at `2d28bbe`, section "Primitive
    quotients".
[^33]: [rocq-lean-import], `README.md` at `2d28bbe`, section "Experimental
    results" and its "Some stats" list.
[^34]: [rocq-lean-import] at `2d28bbe`: `LICENSE` (GNU Lesser General Public
    License, version 2.1); `git log --format='%an' | sort | uniq -c` gives
    Gaëtan Gilbert 200 commits, Jason Gross 46 and Pierre-Marie Pédrot 10;
    GitHub API `license.spdx_id` LGPL-2.1, `pushed_at` 2026-10-01T15:36:09Z;
    `git log` heads `2d28bbe` 2026-10-01 "Merge pull request #81 from
    SkySkimmer/upcore" and `7912d03` 2026-09-30 "uconv remember added
    constraints instead of using constraints_for".
[^35]: `git log --date=short` in a clone of [predicativize]: `3aeccde`
    2026-06-17 Frédéric Blanqui "add ci (#1)", `5d4ce55` 2022-11-01 "updates
    readme2", `55894a2` 2022-11-01 "corrects small mistake when printing
    idents", first commit `2a08ebb` 2022-02-26.  GitHub API: `license` null,
    `pushed_at` 2026-07-01T09:27:46Z.
[^36]: [predicativize], `README.md` at `3aeccde`, sections "Installation" and
    "Modes"; [predicativize-paper], section 8 (the Matita and Isabelle
    experiments) and Figure 7.
[^37]: [predicativize-paper], sections 5 and 6: Theorem 6.1 ("Not all solvable
    problems of universe level unification have a most general unifier"), the
    characterization that follows it, and the algorithm of section 6; the
    `--cstr` option is in the README's "Modes".
[^38]: [predicativize-paper], section 8, pages 23:34 to 23:35 (the paragraphs on
    `extra_cstrs/matita.dk`, the manual definition of inductive types and
    recursive functions, the Zenodo link, the `--safe` sentence, and "about 32
    minutes on a machine with an i7 processor"); [predicativize], `README.md` at
    `3aeccde`, section "Times".
[^39]: [predicativize-paper], Table 1, page 23:35; Zenodo record 10686897 read
    through the Zenodo API on 2026-10-07: `publication_date` 2024-02-21, license
    `cc-by-4.0`, one file `thiagofelicissimo/matita_lib_in_agda-v1.zip` of
    266,130 bytes, description "The files have been typechecked using Agda
    2.6.3".
[^40]: [predicativize-paper], Remark 6.3 (after Theorem 6.1) and the
    conclusion's paragraph on Agda (section 9).
[^41]: [predicativize-paper], the LMCS header on page 23:1 ("Volume 20, Issue 3,
    2024, pp. 23:1–23:38", "Published Sep. 10, 2024") and the "Related version"
    paragraph of section 1; its bibliography entry [FBB23] is T. Felicissimo, F.
    Blanqui and A. K. Barnawal, "Translating proofs from an impredicative type
    system to a predicative one", CSL 2023, LIPIcs 252, pages 19:1 to 19:19, DOI
    10.4230/LIPIcs.CSL.2023.19.
[^42]: `git log` in a clone of [lean4export]: head `05d43a2` 2026-10-06 "chore:
    bump toolchain to v4.35.0-rc4 (#55)"; [arena-results], `meta.timestamp`,
    `meta.git_revision_short` and `meta.github_run_id` (37120292644), fetched
    2026-10-07.
[^43]: [lean4export] at `05d43a2`: `format_ndjson.md`, title line "Lean 4 export
    format: version 3.1.0", the `meta` object, the `binderInfo` alternatives,
    the sections "Quotients" and the recursor object with `"k": boolean`;
    `README.md`, section "Options"; `LICENSE`.  GitHub API: `created_at`
    2023-03-01T12:42:13Z.
[^44]: [arena-repo], `README.md` at the clone's head of 2026-10-06: "Exit
    codes", the timeout paragraph, and "Contributing Tests" (the test groups);
    the page's "Scoring" and "Performance" paragraphs ("The ⏱️ column shows
    virtual CPU time, calculated from instruction counts using a fixed rate of
    6.0 Ginstr/s"), read 2026-10-07 on a page stamped "Generated on 2026-10-03
    13:31:24 UTC".
[^45]: [arena-results] of 2026-10-03: `checkers` has 25 entries and `tests` 223,
    with `outcome` accept 134, reject 71, either 18; the `mathlib` entry of
    `tests` has `size` 6184415052, `size_str` "5.8 GB", `lines` 109790519,
    `lean_version` 4.34.1, `lean4export_version` 3.1.0 and a `source_url` at
    Mathlib `d13f23b`; in `results`, the rows with `test` mathlib give
    `official` `wall_time` 2275.7 s, `max_rss` 10.7 GB and `instructions`
    11,614,030,827,219 (which divided by 6.0 Ginstr/s is 1,935.7 s),
    `sokonanoda` `wall_time` 57.5 s, `cpu_time` 194.4 s and `instructions`
    759,498,093,019 (126.6 s at 6.0 Ginstr/s, so the official checker's 1,935.7
    s is 15.3 times it), and `lean4lean` `wall_time` 2342.6 s.  The page's
    checker table of the same day shows `official v4.34.1 ... 32.3 m 9.9 GB`.
[^46]: [hol2dk], `README.md` at `986fe97`: the opening paragraphs, "Examples"
    and "Bibliography" ("Translating HOL-Light proofs to Coq", LPAR 2024, DOI
    10.29007/6k4x); `LICENSE.txt` ("CeCILL FREE SOFTWARE LICENSE AGREEMENT",
    "Version 2.1 dated 2013-06-21"); GitHub API `pushed_at`
    2026-07-24T17:23:19Z.
[^47]: [hol2dk], `README.md` at `986fe97`, sections "Patching HOL-Light
    sources", "Dumping HOL-Light proofs" (the "60%" sentence, under "Purging
    dumped proofs") and "Translating HOL-Light proofs to Lambdapi and Rocq" (its
    "Remark").
[^48]: [coq-hol-light], `README.md`, read through the GitHub API on 2026-10-07,
    section "Axioms used".
[^49]: [hol2dk], `README.md` at `986fe97`, section "Examples" ("more than 20,000
    theorems") and the table under "Performances" (columns "thms": 40728 and
    5687); [coq-hol-light] releases through the GitHub API on 2026-10-07: 3.0.0,
    published 2025-01-21T17:52:36Z, body beginning "Include a translation of the
    whole Multivariate library (17,500 theorems)"; 2.0.0, published
    2024-12-17T16:39:22Z, body "translation of all the HOL-Light base library
    hol_lib.ml with alignment of real numbers (~3000 theorems)".
[^50]: [hol2dk], `README.md` at `986fe97`, the table under "Performances" and
    its preamble; [coq-hol-light], `README.md`, third paragraph ("provided as
    axioms", "91 Gb", "about 25 hours with 32 processors").
[^51]: [carneiro-thesis], `main.pdf` of release v1.0 (published 2019-04-17):
    title page ("April 16, 2019"), abstract, and the table of contents entry
    "3.1 Undecidability of definitional equality".
[^52]: [abel-coquand], LMCS header ("Volume 16, Issue 2, 2020, pp. 14:1–14:5",
    published 2020-06-30) and abstract.
[^53]: [lean4lean-paper], the arXiv abstract page read 2026-10-07 (v3 of
    2025-09-14; comments "14 pages, submitted to CPP 2026") and the PDF's first
    page (abstract: "running between 20% and 50% slower"; running head
    "Conference'17, Washington, DC, USA"); [lean4lean], GitHub API read
    2026-10-07 (`license.spdx_id` Apache-2.0, `pushed_at` 2026-08-29T18:50:24Z,
    255 stars), `README.md` ("Building": `Lean4Lean.Theory`, `Lean4Lean.Verify`)
    and `lean-toolchain`.
[^54]: [lean4lean-model], GitHub API read 2026-10-07 (`created_at` 2026-08-02,
    `pushed_at` 2026-09-23, `license` null) and `README.md`, section "Target".
[^55]: [hott-book], version "first-edition-82-g578b85c" (the file the site's
    `hott-online.pdf` redirects to, fetched 2026-10-07), page 120: Lemma 3.8.2
    states (3.8.3), the sentence "However, observe that we cannot relax the
    requirement that X be a set" precedes Lemma 3.8.5, and the proof follows the
    lemma.
[^56]: GitHub API, `repos/leanprover-community/mathlib4/pulls/35685`, read
    2026-10-07: `state` open, `draft` true, `merged` false, `created_at`
    2026-02-23T17:51:21Z, `updated_at` 2026-09-15T22:55:31Z, `head.label`
    riccardobrasca:less_choice; the body's opening paragraphs (the custom
    toolchain and Batteries) and its section "Does it work?" (the script and the
    two figures).
[^57]: [mendoza-smith], section 1 (the paragraph beginning "The full kernel
    dependency graph") and the appendix table whose first row is "Declarations
    in Lean Environment 471,260"; the abstract says "we partition 471,260
    declarations".
[^58]: [mendoza-smith-repo], `README.md` read through the GitHub API on
    2026-10-07: the row for the compiled Mathlib, which "pins v4.29.0-rc8 @
    `9f0aee2`", and the row for the LeanDojo traces, "traced @ Mathlib4
    `1bc7728a`".  The paper's appendix A says only that the repository "records
    the exact Lean, Mathlib, and LeanDojo revisions used in all experiments".
[^59]: [mathlib-stats], section "Counts", read 2026-10-07.
