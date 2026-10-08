<!-- File: README.md -->

# lean2agda

A Lean 4 to Agda translator, and the Agda libraries it produces.

**Status**: planning, October 2026.  Nothing translates yet.  The
roadmap, with milestones, labels, issues and dependency graphs, is
[`docs/GITHUB_PROJECT.md`](docs/GITHUB_PROJECT.md).

## Why

Lean's Mathlib holds roughly 138,000 definitions and 290,000 theorems
and grows daily; no Agda library is within an order of magnitude of
that.  The project's aim is to let Agda users consume Lean developments
as Agda libraries, and to learn something about both systems on the
way.  Three goals, in priority order:

+  **Libraries**.  Translate Lean libraries, Mathlib first, into Agda
   libraries with readable statements and machine-checked proofs.  The
   output is split into a *constructive* layer, which never mentions a
   classical axiom and checks under `--safe --cubical-compatible`, and
   a *classical* layer that takes the classical principles as module
   parameters, so that the whole library stays `--safe` and each user
   decides what to assume.
+  **Foundations**.  Lean is an impredicative, proof-irrelevant
   Calculus of Inductive Constructions with primitive quotients and
   three axioms; Agda is predicative Martin-Löf type theory, with or
   without the K rule, optionally cubical.  The differences are known
   in principle and unmeasured in practice.  Every translation that
   fails or needs repair is a data point about which features of Lean's
   theory its libraries use essentially; the project publishes the
   measurements.
+  **Confirmation**.  A proof that Agda accepts after translation has
   been checked by a second kernel implementing a different theory.  A
   proof that cannot be translated is a translator limitation, a
   genuine foundational gap, or a problem in the Lean development, and
   the pipeline tells those outcomes apart.  Independent re-checking of
   Lean's kernel is already done well by other checkers (see the Lean
   Kernel Arena below); what a translation into Agda adds is a check
   against a *different theory*, and a library at the end of it.

## What the translation has to bridge

The two theories differ in ways that each force a design decision.
The project keeps a catalog of these gaps (`docs/foundations/`, once
M1 lands); the main entries are as follows.

| Feature | Lean 4 | Agda | Consequence |
| --- | --- | --- | --- |
| Universe of propositions | `Prop` is impredicative: a proposition may quantify over any universe and stay in `Prop` | `Set ℓ` and `Prop ℓ` are predicative | universe-polymorphic level elaboration; essentially impredicative uses cannot be translated |
| Proof irrelevance | definitional: any two proofs of a proposition are equal | only in the `Prop` universe (`--prop`), which cannot eliminate into `Set` except by absurd patterns | either use Agda's `Prop` plus explicit casts for the propositions Lean eliminates largely, or h-propositions in `Set` plus casts everywhere |
| K and UIP | every type has unique identity proofs; `Eq.rec` reduces by K-like reduction | available with K (Agda's default); rejected under `--cubical-compatible` | each use of K must be justified by an `isSet` proof, or reported as K-essential |
| Large elimination from `Prop` | `Eq`, `HEq`, `Acc`, `And`, `True`, `False` and other subsingletons eliminate into `Type` | not from `Prop` | those propositions live in `Set` on the Agda side |
| Quotients | primitive `Quot` with a definitional computation rule and the axiom `Quot.sound` | none in plain Agda; set quotients as higher inductive types under `--cubical` | a module-parameter record with a propositional computation rule (casts inserted), or cubical set quotients |
| Axioms | `propext`, `Quot.sound`, `Classical.choice` | none; postulates are forbidden by `--safe` | module parameters; `Classical.choice` is inconsistent with univalence, so the classical layer cannot live under `--cubical` unchanged |
| Universe levels | `max`, `imax`, and `Sort 0 = Prop` as a special case | `⊔`, `lsuc`, no `imax` | specialize each constant by which level parameters are zero |
| Eta | definitional eta for structures and unit-like types | eta for records | structure-like inductives become records |
| Literals | `Nat` literals with GMP-accelerated kernel arithmetic; `String` literals | builtin naturals and strings with different definitional edges | an operation table; `Nat.gcd` needs special care |
| Trust escape hatches | `Lean.ofReduceBool` (`native_decide`), `implemented_by`, `partial`, `unsafe`, `sorryAx` | none | refused and reported |

Two consequences shape the whole design.  First, Lean's theory proves
uniqueness of identity proofs for every type, so a translation into
`--cubical-compatible` Agda must prove, for each type on which K is
used, that the type is an h-set; where it cannot (equalities between
types, typically), the declaration is reported rather than translated.
Second, Lean's `Classical.choice` chooses an element of every nonempty
type, and a function of that type contradicts univalence even when
restricted to h-sets (HoTT book, Lemma 3.8.5); the classical layer is
therefore a `--cubical-compatible` library and not a `--cubical` one,
and only weakened forms of choice can follow the constructive layer
into cubical Agda.

## Approach

The translator is a Lean 4 program over the elaborated Lean environment
(the `.olean` files Lake builds), which is how every serious
predecessor works.  It runs in five stages, as follows:

1. **Profile**.  For every constant, record the axioms it depends on,
   its computability, and the kernel features its typing used.  This
   per-declaration record is the *atlas*; the layering is computed
   from it.
2. **Normalize**.  Run Lean4Less (Deducteam) to replace definitional
   proof irrelevance and K-like reduction with explicit casts, giving
   terms typeable in the smaller theory Lean⁻; extend the mechanism to
   the computation rule of `Quot.lift` where the target has no
   definitional quotients.
3. **Elaborate universes**.  Specialize each constant by which of its
   universe parameters are `Prop`, then compute predicative,
   universe-polymorphic level annotations by constraint solving, in the
   style of Felicissimo and Blanqui's Predicativize.
4. **Emit**.  One Agda module per Lean module and layer: `data` and
   `record` types, recursors as pattern-matching definitions, theorems
   in `opaque` blocks, axioms as module parameters, `.agda-lib` files
   and an import graph.
5. **Check**.  Run Agda under the profile's flags; every failure goes
   back into the atlas with its category.

### Target profiles

A *profile* is the set of Agda flags the output must check under, plus
what remains a module parameter.

| Profile | Agda flags | Parameters | Purpose |
| --- | --- | --- | --- |
| U | `--type-in-type`, postulates allowed | none (postulated) | scaffolding for building the mechanical parts; never a deliverable |
| K | `--safe` (Agda's default, with K) | `propext`, quotients, `funext`, `Classical.choice` | the faithful target: every rule of Lean's theory has a counterpart |
| CC | `--safe --cubical-compatible` | as K | the primary deliverable; K must be justified by `isSet` proofs |
| CU | `--safe --cubical` | `Classical.choice` only, in forms consistent with univalence | quotients, `funext` and `propext` become theorems; constructive layer first |

### Layers

Lean's `#print axioms` sorts declarations into tiers: T0 (no axioms),
T1 (`propext` or `Quot.sound`, both validated by univalent type
theory), T2 (`Classical.choice`), T3 (`Lean.ofReduceBool`, `sorryAx`,
`unsafe`, `partial`).  The emitted library has a **constructive**
layer (T0 and T1) and a **classical** layer (T2) importing it; T3 is
refused.  Both layers are `--safe`: the classical principles are
record-typed module parameters, as in TypeTopology, and a one-line user
module may postulate them for anyone who prefers that.  A theorem whose
statement is constructive but whose Mathlib proof is classical sits in
the classical layer until a hand-written constructive proof promotes
it.

## Prior work this builds on

The survey [`docs/related-work.md`](docs/related-work.md) has a section
on each of the following, with every figure checked against its primary
source on 2026-10-07 and the source location footnoted; this list is
the summary.

+  **lyphyser/lean2agda** (September 2024, Apache-2.0).  A
   proof-of-concept Agda exporter for Lean 4: a fork of lean4export,
   written in Lean over the elaborated environment, rewritten in ten
   commits over four days.  It specializes constants by universe-level
   zero-ness, deduplicates repeated closed subterms, fixes binder
   implicitness, emits records and pattern-matching recursors, and
   postulates quotients, axioms, `Acc.rec` and `WellFounded.fixFEq`;
   its output needs `--prop --type-in-type`, is a single file, and ran
   Agda out of memory on larger tasks.  Our M2 ends roughly where it
   stopped; we cite its ideas and reuse no code before M2-10 (issue 24)
   compares the two tools.
+  **Lean4Less and lean2dk** (Deducteam; Vaishnav's 2026 thesis
   *Translating Proofs from Lean to Dedukti*).  Lean4Less eliminates
   definitional proof irrelevance and K-like reduction by inserting
   casts justified by a proof-irrelevance lemma (an axiom in the paper,
   a theorem from `propext` in the repository since February 2026),
   yielding terms typed in the smaller theory Lean⁻.  On Lean's `Std`
   at v4.16.0-rc2, 6.3 percent of constants used those rules and the
   environment grew 15.5 percent; it translated
   `Mathlib.Data.Real.Basic` but does not yet scale to higher Mathlib
   modules, and its `.olean` output is currently broken.  Without this
   step a translation keeps no classical logic: Lean's proof of excluded
   middle uses proof irrelevance, and Agda's `Prop` cannot eliminate
   into `Set`, so the proofs Lean identifies definitionally need
   explicit casts on the Agda side; this step is the normalizer of our
   pipeline.  lean2dk then exports to Dedukti; its best branch checks
   `Init.Data.Nat.Lemmas` against a patched Dedukti with a couple dozen
   constants stubbed.  Lean4Less has no license file.
+  **rocq-lean-import** (Gaëtan Gilbert, LGPL-2.1).  Imports Lean export
   files into Rocq: `Prop` as `SProp`, duplication of constants per
   `Prop`-instantiation pattern, algebraic universes with surrogate
   parameters for `imax`, quotients as private inductives, and
   definitional UIP required.  Its Lean 3 experiments calibrate our
   expectations: the stdlib could not be fully checked because of
   pathological conversion problems, and the mathlib run (66,400
   entries, 11,867 skipped, 73 minutes, 10 GB) was made with conversion
   checking off, so it declared the terms without checking them.
+  **Predicativize** (Felicissimo and Blanqui, LMCS 2024; with Barnawal
   at CSL 2023).
   Universe-polymorphic elaboration with level unification, used to
   translate Matita's arithmetic library, through Dedukti, into Agda
   that checks under `--safe` (as far as its authors know, the first
   Agda proofs of Fermat's little theorem and Bertrand's postulate), in
   about 32 minutes, with hand-added level constraints and with the
   inductive types and recursive functions rebuilt by hand.  Our
   universe stage follows its algorithm.
+  **lean4export and the Lean Kernel Arena** (Lean FRO).  The NDJSON
   export format (version 3.1.0) and a public benchmark of Lean
   checkers, including invalid exports a checker must reject: 25
   checkers and 223 tests in the round of 2026-10-03, in which the
   official checker took 38 minutes of wall time on a 6.2 GB Mathlib
   export.  The round is rebuilt on every change.  M7 enters
   translation-plus-Agda as a checker.
+  **hol2dk** (Blanqui, CeCILL-2.1).  HOL Light's base and Multivariate
   libraries, more than 20,000 theorems by its README (17,500 by the
   release note), translated through Dedukti and Lambdapi into Rocq and
   released in December 2024 and January 2025, the theorems shipped as
   axioms with a script that regenerates and checks the proofs in about
   a day: the precedent that library-scale translation between proof
   assistants is feasible.
+  **Foundations**.  Carneiro's thesis on Lean's type theory; Abel and
   Coquand's proof that normalization fails with impredicative `Prop`
   and proof-irrelevant propositional equality; Lean4Lean, the Lean
   kernel in Lean with a formal statement of Lean's typing rules, which
   Lean4Less modifies; and the HoTT book's Lemma 3.8.5, the reason
   choice cannot follow the constructive layer into cubical Agda.
+  **Mathlib measurements**.  An open Mathlib pull request (35685,
   opened February 2026, on a custom Lean fork) counted 446,045
   declarations depending on `Classical.choice` on master (57.5 percent
   of the environment) against 430,049 of 775,824 on its branch (55.4
   percent); an
   independent 2026 study counts 171,522 classical against 299,738
   constructive among 471,260 declarations.  The counts have different
   denominators and dates; the project's atlas will state its own.

## Where the results live

+  **This repository**: the translator (a Lean 4 package under
   `translator/`), the hand-translated corpus that is its test oracle
   (`corpus/`), the atlas tooling (`atlas/`, `scripts/python/`), and the
   documentation, including the design records under `docs/adr/`.
+  **Generated libraries**: one repository per translated Lean
   library, created when the first regenerable subtree exists (end of
   M5), with provenance (Lean version, Mathlib revision, translator
   version, profile), its own CI, and Mathlib's Apache-2.0 license and
   notices.  `docs/libraries.md` will list them.

Until the first generated library exists, the corpus will be the main
Agda output under version control: twelve Mathlib declarations,
selected in issue M1-6 and translated by hand in issues M1-7 through
M1-9, each with the Lean statement, its exported kernel term, the
idiomatic Agda version, and notes on what the translation needed.  The
hand translations come first on purpose; the translator is built to
reproduce them.

## Development setup

The toolchain is a Nix flake; one `nix develop` provides it.  The
`.#agda` shell leaves out Lean and the `.#lean` shell leaves out Agda;
both keep make, git and Python 3, and only the default shell carries
the roadmap tools (gh, jq, and the github-project engine).

```sh
nix develop         # Lean (from lean-toolchain), Agda 2.8.0, agda-stdlib 2.3,
                    # cubical 0.9, Python 3, gh, make
make doctor         # print versions; fail, naming any missing tool or library
make corpus-check   # type-check every translated corpus entry (corpus/README.md)
make test           # the Python tests (scripts/python/tests/)
make atlas          # placeholder until M1-11: axiom profile of pinned Mathlib
make lint           # structural check of docs/GITHUB_PROJECT.md
```

The translator is a Lake package in `translator/` that requires Mathlib
at the release tag matching `lean-toolchain`.  Mathlib's prebuilt
`.olean` files come from `lake exe cache get` inside `translator/`;
nothing in the project rebuilds Mathlib from source.  A fresh checkout
fetches them once, as follows (several gigabytes, under
`translator/.lake/`, which is gitignored):

```sh
cd translator && lake update --keep-toolchain && cd ..   # clone Mathlib; its hook fetches the cache
make lean-cache     # lake exe cache get: fetch whatever is still missing
make lean-build     # lake build in translator/
make lean-smoke     # check that no Mathlib module is stale, then load Mathlib
```

`docs/pinning.md` names every pin (Lean, Mathlib, lean4export,
Lean4Less, Agda, agda-stdlib, cubical, and the flake's inputs), where
each lives, the command that changes it, and the procedure for moving
them.

## Roadmap

Seven milestones; the full plan with issues and dependency graphs is
[`docs/GITHUB_PROJECT.md`](docs/GITHUB_PROJECT.md).

1. **Foundations, corpus, and gap catalog**: repository setup, Nix,
   pins, related-work survey, the gap catalog, twelve hand
   translations, the axiom atlas over Mathlib, ADR 0001.
2. **Translator core on the scaffolding profile**: names, expressions,
   inductive types, recursors, definitions, quotients, multi-module
   emission, on profile U, proven on the corpus and `Init` fragments.
3. **Faithful translation**: Lean4Less, the `Prop` encoding decision,
   universe-level elaboration, quotients, literals, subsingleton
   elimination; profile K on `Init` and `Std`, and a first measurement
   of profile CC.
4. **Constructive and classical layering**: the atlas as the shape of
   the output, axioms as module parameters, classical `Decidable`
   instances, the promotion overlay, a first layered Mathlib fragment.
5. **Scaling and the first generated library**: Agda performance, term
   size control, incremental regeneration, readable statements, the
   library repository template, a Mathlib upgrade rehearsal, bridges to
   agda-stdlib and agda-algebras.
6. **Cubical-compatible and cubical targets**: profile CC on the
   generated library, profile CU with cubical quotients, choice under
   univalence, interop with agda/cubical and agda-unimath.
7. **Verification and the foundational study**: a Lean Kernel Arena
   entry, trust analysis, a soundness-bug suite, the report on the
   practical distance between the two foundations, outreach.

## Conventions

Python follows the functional house style: total functions, `Result`
values instead of exceptions, frozen dataclasses, a `File:` header in
every file, a test for every pure function.  Lean code keeps a pure
translation core with IO at the edges.  Agda output targets Agda 2.8.0
with agda-stdlib 2.3 and the cubical library 0.9.  Design decisions are
recorded as ADRs under `docs/adr/`, each with a companion note beside
the component it describes.  Repository Markdown wraps at about 80
columns; GitHub issue and PR bodies do not wrap.

## License

Apache License, Version 2.0 (`LICENSE`, `NOTICE`), matching Lean,
Mathlib, lean4export and the predecessors whose code might be reused.
Every generated library is a derived work of Mathlib and carries
Apache-2.0 with Mathlib's notices and its own provenance record; the
rules are in [`docs/licensing.md`](docs/licensing.md).

## References

+  lyphyser/lean2agda: <https://github.com/lyphyser/lean2agda>
+  Lean4Less: <https://github.com/Deducteam/Lean4Less>; R. Vaishnav,
   *Lean4Less: Eliminating Definitional Equalities from Lean via an
   Extensional-to-Intensional Translation*, ICTAC 2025:
   <https://inria.hal.science/hal-05310102>
+  lean2dk: <https://github.com/Deducteam/lean2dk>
+  R. Vaishnav, *Translating Proofs from Lean to Dedukti*, PhD thesis,
   Université Paris-Saclay, 2026: <https://rish987.github.io/files/thesis.pdf>
+  rocq-lean-import: <https://github.com/rocq-community/rocq-lean-import>
+  Predicativize: <https://github.com/Deducteam/predicativize>;
   T. Felicissimo and F. Blanqui, *Sharing proofs with predicative
   theories through universe-polymorphic elaboration*, LMCS 20(3),
   2024: <https://arxiv.org/abs/2308.15465>; the CSL 2023 version, with
   A. K. Barnawal: <https://doi.org/10.4230/LIPIcs.CSL.2023.19>; the
   translated library: <https://doi.org/10.5281/zenodo.10686897>
+  lean4export: <https://github.com/leanprover/lean4export>; Lean
   Kernel Arena: <https://arena.lean-lang.org/> and
   <https://github.com/leanprover/lean-kernel-arena>
+  hol2dk: <https://github.com/Deducteam/hol2dk>; its Rocq library:
   <https://github.com/Deducteam/coq-hol-light>
+  M. Carneiro, *The Type Theory of Lean*, MSc thesis, 2019:
   <https://github.com/digama0/lean-type-theory/releases/tag/v1.0>;
   M. Carneiro, *Lean4Lean: Verifying a Typechecker for Lean, in Lean*,
   arXiv 2403.14064, venue unconfirmed:
   <https://arxiv.org/abs/2403.14064>; the repository:
   <https://github.com/digama0/lean4lean>
+  A. Abel and T. Coquand, *Failure of Normalization in Impredicative
   Type Theory with Proof-Irrelevant Propositional Equality*, LMCS 16(2),
   2020: <https://arxiv.org/abs/1911.08174>
+  The Univalent Foundations Program, *Homotopy Type Theory*, 2013:
   <https://hott.github.io/book/hott-online.pdf>
+  Mathlib PR 35685, *reduce the use of Classical.choice*:
   <https://github.com/leanprover-community/mathlib4/pull/35685>
+  R. Mendoza-Smith, *Geometric Measurements of the Axiom of Choice in
   Neural Proof Embeddings*, 2026: <https://arxiv.org/abs/2606.28572>
+  Mathlib statistics: <https://leanprover-community.github.io/mathlib_stats.html>
+  Agda documentation: `Prop`
  (<https://agda.readthedocs.io/en/latest/language/prop.html>) and
  command-line options
  (<https://agda.readthedocs.io/en/latest/tools/command-line-options.html>)
