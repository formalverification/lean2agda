<!-- File: docs/foundations/gap-catalog.md -->

# The foundational gap catalog

One entry per feature of Lean's kernel theory that Agda's lacks, has in a
different form, or has only under some flags, with the Lean rule, Agda's status
under each of the project's four target profiles, the translation strategy, the
predecessors' treatment, and the references (issue [#5]).  The catalog is the
checklist the translator is built against and the vocabulary of everything that
classifies: the corpus manifest's `features` field uses the entry slugs below
([`../../corpus/SCHEMA.md`][corpus-schema], section Features), the gap report
of [#10] counts corpus entries per entry, and ADR 0001 ([#12]), once written,
is to cite it.  It supersedes the table "What the translation has to bridge" in
the [README][readme].

Everything here was checked on 2026-10-07 at the project's pins
([`../pinning.md`][pinning]): Lean v4.33.1 (commit `819816b`) with Mathlib
v4.33.1, read through the Lake package in `translator/`, and Agda 2.8.0 with
agda-stdlib 2.3 and the cubical library 0.9, the shell's `agda`.  Three kinds
of evidence are used, as follows.

+  **Lean's rules** are quoted from Carneiro's thesis ([carneiro-thesis]),
   which presents Lean 3's kernel theory; from Vaishnav's thesis
   ([vaishnav-thesis]), whose section 1.2 states Lean 4's typing, definitional
   equality and reduction rules, including the ones Lean 4 added; from the
   kernel's source at tag `v4.33.1` ([kernel-type-checker], [kernel-inductive],
   [kernel-quot]), with line numbers; and from the Lean language reference at
   version 4.33.1 ([lean-manual]).  Each rule was also exercised in a scratch
   file elaborated at the pin (`probes/lean/`, below).
+  **Agda's status** is settled by probe files run with the shell's `agda`
   (`probes/agda/`, below): one file per claim, accepted or rejected, with the
   error Agda prints quoted where the point is a rejection.  The Agda
   documentation for 2.8.0 is cited for the rule behind each probe
   ([agda-prop], [agda-safe], [agda-cubical-compatible], [agda-without-k],
   [agda-options], [agda-records], [agda-builtins], [agda-levels], [agda-let],
   [agda-data], [agda-mutual], [agda-irrelevance], [agda-sorts]).
+  **What exists at the pin** was measured by a scan of every constant in the
   environment of `import Mathlib` (`probes/lean/Scan.lean` and
   `ScanByRoot.lean`): 771,136 constants, of which 569,189 are declared in
   `Mathlib.*` modules.  The scan took 2 min 29 s of wall time and 6.97 GB of
   memory on a machine with a load average of 1.19; the per-root rerun took 2
   min 18 s.  Its results are in the table of the next section and in the
   entries that use them.

**Terms**.  The roadmap ([`../GITHUB_PROJECT.md`][roadmap], Description)
defines *profile* (a set of Agda flags plus what stays a module parameter: U is
`--type-in-type` with postulates, K is `--safe` with Agda's default K rule, CC
is `--safe --cubical-compatible`, CU is `--safe --cubical`), *layer*
(constructive or classical), *tier* (T0 no axioms, T1 `propext` or
`Quot.sound`, T2 `Classical.choice`, T3 anything else), *atlas* and
*normalizer*.  The related-work survey ([`../related-work.md`][related-work],
Terms) defines *K-like reduction*, *structure-like reduction* and *Lean⁻*, and
this catalog uses them as it does.  Two more are needed here.  A type is an
*h-proposition* (`isProp`) when any two of its elements are equal, and an
*h-set* (`isSet`) when any two proofs of an equality between its elements are
equal; *univalence* is the cubical library's `ua`, under which equalities
between types are equivalences, so that types are not h-sets in general.

**How to read an entry**.  Each entry is headed by its slug, which is its
anchor and its name in the manifest, and has the following five fields: the
**Lean rule**, with where the kernel implements it; **Agda's status**, one line
per profile; the **translation strategy**, by roadmap issue; the
**predecessors' treatment**, citing the survey's sections rather than
re-deriving them; and **references**, with the probes that settled the Agda
claims.  An entry that has nothing to say under a profile says why in a line.

## The profiles and the two facts that shape them

| Profile | Agda flags | What stays a parameter | Deliverable |
| --- | --- | --- | --- |
| U | `--type-in-type`, postulates allowed | nothing (postulated) | no: scaffolding for M2 |
| K | `--safe` (Agda's default, with K) | `propext`, quotients, `funext`, `Classical.choice` | the faithful target |
| CC | `--safe --cubical-compatible` | as K | the primary deliverable |
| CU | `--safe --cubical` | `Classical.choice` only, in forms consistent with univalence | the cubical target |

Two facts about Lean's theory, both checked at the pin, decide the shape of the
profiles.

**Lean proves uniqueness of identity proofs for every type**.  Because `a = b`
is a proposition and Lean's definitional equality identifies any two proofs of
a proposition, `example {α : Sort u} {a b : α} (p q : a = b) : p = q := rfl` is
accepted, and so is the same statement for `p q : α = β` with `α β : Type`
(`probes/lean/DefEq.lean`, `Recursors.lean`).  The recursor of `Eq` also
carries K-like reduction: with `a : α` and `C : α → Sort v`,
`example (x : C a) (h : a = a) : (h ▸ x) = x := rfl` is accepted on a variable
proof `h`.  Agda's default theory has K as a principle of pattern matching, and
`uip refl refl = refl` is accepted under `--safe` (probe `P05KAccepted`).
Under `--cubical-compatible`, which "implies" `--without-K`
([agda-cubical-compatible]), the same definition is rejected (probe
`P06KRejected`), as follows:

```text
error: [SplitError.UnificationStuck]
I'm not sure if there should be a case for the constructor refl,
because I get stuck when trying to solve the following unification
problems (inferred index ≟ expected index):
  x ≟ x
Possible reason why unification failed:
  Cannot eliminate reflexive equation x = x of type A because K has
  been disabled.
```

The same error appears under `--cubical` (probe `P17CubicalK`).  What remains
available is Hedberg's theorem: a type with decidable equality is an h-set, and
agda-stdlib's `Data.Nat.Properties.≡-irrelevant` proves uniqueness of identity
proofs for `ℕ` under `--safe --cubical-compatible` (probe `P07HedbergNat`).  A
translation into profile CC must therefore produce, for each type on which a
Lean proof used K, a proof that the type is an h-set, and report the
declaration where it cannot (equalities between types, typically); that is the
work of [#34], [#51] and [#55], and the entry [`k-and-uip`](#k-and-uip) below.

**Global choice is inconsistent with univalence**.  Lean's
`Classical.choice : {α : Sort u} → Nonempty α → α` chooses an element of every
nonempty type.  The HoTT book's Lemma 3.8.5 ([hott-book], page 120, as the
survey's Foundations section locates it) exhibits a type `X :≡ Σ(A:U) ∥2 = A∥`,
which is a 1-type and not a set, and a family `Y : X → U` of sets with
`∏(x:X) ∥Y(x)∥` but no `∏(x:X) Y(x)`; a function of `Classical.choice`'s type
applied to each `Y(x)` would give the second from the first, so under
univalence no such function exists, even though every type it is applied to is
an h-set.  The lemma is the book's reason that choice must be stated for
set-indexed families ("we cannot relax the requirement that X be a set").  A
module parameter cannot make a `--safe` module inconsistent, and Agda accepts a
module parameterized by `choice : (A : Type) → ∥ A ∥₁ → A` under
`--safe --cubical` (probe `P19ChoiceParam`); the point is vacuity, not
soundness: nothing in cubical Agda could ever instantiate the parameter.  The
classical layer is therefore a `--cubical-compatible` library, and which weaker
principles follow the constructive layer into profile CU is the study of [#53]:
the book's excluded middle for h-propositions,
`LEM :≡ ∏(A:U) isProp(A) → (A + ¬A)` (its (3.4.1)), is consistent with
univalence, while its untruncated form is refuted by Theorem 3.2.2
([hott-book]).

## What exists at the pin

The scan of the environment of `import Mathlib` (`probes/lean/Scan.lean`,
`ScanByRoot.lean`) gives the following counts; the Mathlib column counts
constants declared in `Mathlib.*` modules, the environment column everything
Lean, Std, Batteries, Aesop, Qq, ProofWidgets, Plausible and Mathlib declare.

| Measure | Environment | `Mathlib.*` |
| --- | --- | --- |
| Constants | 771,136 | 569,189 |
| Inductive types | 6,790 | |
| Inductive types in `Prop` | 2,253 | |
| Of which with large elimination (a recursor into `Sort u`) | 1,980 | |
| Recursors | 6,913 | |
| Of which with K-like reduction (`k = true`) | 15 | 5 |
| Nested or mutual inductive declarations | 86 | 11 (4 outside tactic code) |
| Axioms declared | 15 (7 safe, 8 `unsafe`) | 0 |
| Constants depending on an axiom other than `propext`, `Quot.sound`, `Classical.choice` | 255 | 41 |
| `unsafe` constants | 714 | 68 |
| `partial` definitions (an `opaque` with an `_unsafe_rec` companion) | 1,509 | 266 |
| Constants with `implemented_by` | 341 | 28 |
| `noncomputable` constants | 16,021 | 15,734 |
| Opaque constants | 3,062 | |

How each was measured: inductive types and recursors by `ConstantInfo`; a
`Prop` inductive by the sort at the end of its type; large elimination by the
recursor having one universe parameter more than its inductive type (the
motive's level); K-like reduction by `RecursorVal.k`; nested or mutual by
`InductiveVal.numNested > 0` or `all.length > 1`; axioms as `AxiomVal`, with
`isUnsafe`; dependents by `Lean.collectAxioms` on every constant; `partial` by
the `_unsafe_rec` companion, since a `partial def` becomes an `opaque` that
`#print axioms` reports as depending on no axiom and that
`Compiler.getImplementedBy?` does not see (`probes/lean/Hatches.lean`);
`implemented_by` by `Compiler.getImplementedBy?`; `noncomputable` by
`Lean.isNoncomputable`.  The axiom tiers themselves are the atlas's to compute
([#11]) and are not repeated here.

## Entries

### `impredicative-prop`

**Impredicative `Prop`, and `imax`**.

+  **Lean rule**.  `Prop` is `Sort 0`, and a function type `(x : A) → B` with
   `A : Sort u` and `B : Sort v` lives in `Sort (imax u v)`, where
   `imax u 0 = 0` and `imax u v = max u v` otherwise, so that a proposition may
   quantify over a type of any universe and stay a proposition
   (`∀ (α : Type u), Nonempty α : Prop`).  Carneiro states the level grammar
   `ℓ ::= u | 0 | Sℓ | max(ℓ, ℓ) | imax(ℓ, ℓ)`, the typing rule for `∀` at
   `U_imax(ℓ₁, ℓ₂)`, and the semantics of `imax` (section 2.1, page 6).[^1]
   The reference manual says the same: "Propositions may quantify over types
   from any universe whatsoever", and "`imax` is used to implement
   impredicative quantification for `Prop`".[^2]  A consequence that shapes the
   whole translation: Abel and Coquand prove that normalization fails in a type
   theory with an impredicative universe of propositions and a proof-irrelevant
   propositional equality, and their counterexample "can be directly replayed
   in Lean 3.4.2 with the standard prelude", a term "closed with respect the
   standard axioms of Lean" ([abel-coquand]);[^3] Lean has both ingredients, so
   its kernel's conversion is "a decidable non-transitive underapproximation of
   the typing judgment" (Carneiro, section 3.1) and no translation may rely on
   normal forms.
+  **Agda's status**.  Agda's `Prop` is a predicative hierarchy
   `Prop₀ : Set₁, Prop₁ : Set₂, …` ([agda-prop], "The predicative hierarchy of
   Prop"), and a quantification over `Set` lands one level up:
   `(A : Set) → Squash A` has type `Prop₁`, and asking for `Prop` fails with
   `Prop₁ != Prop` (probe `P08Impredicativity`; `P08bPredicativeLevels` accepts
   it at `Prop₁`).  By profile, as follows.
   +  U: `--type-in-type` makes every `Set ℓ` equal to `Set`, so the universe
      side of impredicativity type-checks (this is why lyphyser's output needs
      the flag); the `Prop` against `Set` distinction stays syntactic, so a
      constant still has to be specialized by which of its level parameters are
      zero.
   +  K: no impredicativity; a constant translates only if its uses of
      impredicativity are inessential, that is, if its level constraints have a
      predicative solution.
   +  CC: as K; `--cubical-compatible` changes nothing about universes.
   +  CU: as K.
+  **Translation strategy**.  Specialize each constant by which of its universe
   parameters are instantiated at `Prop`, which removes every `imax` ([#28],
   from lyphyser's level clauses and rocq-lean-import's instantiation
   patterns); then compute predicative, universe-polymorphic level annotations
   by constraint solving in the style of Predicativize ([#29]); report the
   constants whose constraints have no solution as essentially impredicative.
   The corpus expects `order-hom-map-lfp` and `substructure-closure-le` to
   exercise this, each taking an infimum over all subsets or all substructures
   ([`../../corpus/README.md`][corpus-readme], Coverage).
+  **Predecessors**.  lyphyser emits `--prop --type-in-type` and specializes by
   level clauses ([related-work], lyphyser/lean2agda); rocq-lean-import
   duplicates each constant per pattern of `Prop`-instantiated universe
   parameters and turns `imax(a, b)` into `SProp` when `b` is, with surrogate
   parameters for algebraic universes (rocq-lean-import); Predicativize removes
   impredicativity by universe-polymorphic elaboration, proves that not every
   level-unification problem has a most general unifier (Theorem 6.1) and takes
   extra constraints by hand (Predicativize); Lean4Less leaves `Prop` and the
   level algebra unchanged, and lean2dk encodes them with a rewrite system
   (Lean4Less, lean2dk).
+  **References**.  [carneiro-thesis] section 2.1 and section 3.1;
   [abel-coquand]; [lean-manual-universes] and [lean-manual-propositions];
   [agda-prop], [agda-sorts], [agda-levels]; probes `P08Impredicativity`,
   `P08bPredicativeLevels`, `P09Setω`.

### `proof-irrelevance`

**Definitional proof irrelevance**.

+  **Lean rule**.  Any two proofs of a proposition are definitionally equal:
   Carneiro's rule `Γ ⊢ p : P, Γ ⊢ h : p, Γ ⊢ h' : p ⟹ Γ ⊢ h ≡ h'`, "called
   proof irrelevance" (section 2.2, pages 6 to 7);[^4] the kernel's
   `is_def_eq_proof_irrel`, which returns true when the type of one side is a
   proposition and the two types are definitionally equal
   ([kernel-type-checker], lines 932 to 939).  At the pin
   `example (p : Prop) (h1 h2 : p) : h1 = h2 := rfl` is accepted
   (`probes/lean/DefEq.lean`).  Vaishnav's rule [PI] (section 1.2.2, page 18)
   is justified propositionally from `propext`: an inhabited proposition equals
   `True`, whose proofs are identified by elimination, which is how Lean4Less's
   `prfIrrel` became a theorem in February 2026.[^5]  Consequences recorded by
   Carneiro: definitional equality is undecidable (section 3.1, through `acc`),
   algorithmic equality is not transitive (3.1.1), and subject reduction fails
   (3.1.2).
+  **Agda's status**.  Agda has three partial counterparts, none of them Lean's
   rule.  The `Prop` universe (option `--prop`, off by default: "Default:
   `--no-prop`" [agda-options]) is definitionally proof-irrelevant: with
   `P : Prop` and `f : P → Bool`, `irr : (p q : P) → f p ≡ f q` holds by `refl`
   (probe `P01bPropAbsurd`), but a `Prop` eliminates into `Set` only by the
   absurd pattern (next entry).  Irrelevant arguments `.(x : A)` are ignored by
   conversion ([agda-irrelevance]): `f : (n : ℕ) → .(0 < n) → ℕ` gives
   `f n p ≡ f n q` by `refl` (probe `P20Irrelevance`).  In `Set`, two proofs of
   a proposition are not definitionally equal, and an h-proposition carries an
   explicit `isProp` proof.  By profile, as follows.
   +  U: `--prop` and `--type-in-type` combine, as lyphyser's output shows.
   +  K: `--prop` is compatible with `--safe` (probe `P01bPropAbsurd` runs
      under both); proofs that Lean identifies definitionally need a cast
      wherever they are compared in a `Set`.
   +  CC: `--prop` combines with `--cubical-compatible` for absurd patterns and
      for the squash eliminator (probe `P25PropCC`), but not for pattern
      matching on a `Prop`-valued indexed family even with a `Prop` motive:
      `substP P refl px = px` on `_≐_ : A → A → Prop`, accepted under `--prop`
      alone (probe `P01bPropAbsurd`), is rejected under
      `--cubical-compatible --prop` with `[CannotGenerateTransportClause]`:
      "Could not generate a transport clause for substP because a term of type
      … lives in the sort Prop and thus can not be transported" (probe
      `P25bPropEqCC`).  This bears on the encoding decision of [#27].
   +  CU: `--prop` is accepted with `--cubical` (probe `P18PropCubical`), with
      the same transport restriction (probe `P25cPropEqCubical`).
+  **Translation strategy**.  The normalizer (Lean4Less, [#26]) makes every use
   of the rule explicit as a cast justified by `prfIrrel`; since that lemma is
   proved from `propext`, a cast inserted into a T0 constant brings a `propext`
   dependency, and the atlas records casts separately from the source's axioms
   ([#26], [#36]).  Which encoding of Lean's `Prop` the Agda side uses, Agda's
   `Prop` with casts where Lean eliminates largely (encoding A) or
   h-propositions in `Set` with casts everywhere (encoding B), is decided by
   experiment in [#27] (ADR 0002); the corpus expects `finset-card-image` and
   `subtype-coe-eta` to supply evidence.
+  **Predecessors**.  lyphyser maps Lean's `Prop` to Agda's `Prop` and leaves
   the rest to `--type-in-type`; Lean4Less eliminates the rule by casts, always
   together with K-like reduction, with the overhead figures the survey
   tabulates (6.3 percent of `Std`'s constants use one of the two rules);
   rocq-lean-import uses Rocq's `SProp`; Predicativize's source theory has no
   proof irrelevance; hol2dk's Rocq library assumes proof irrelevance as an
   axiom ([related-work], the respective sections).
+  **References**.  [carneiro-thesis] sections 2.2 and 3.1; [vaishnav-thesis]
   sections 1.2.2 and 4.1.2; [kernel-type-checker] lines 932 to 939;
   [lean-manual-propositions]; [agda-prop], [agda-irrelevance], [agda-options];
   probes `P01bPropAbsurd`, `P18PropCubical`, `P20Irrelevance`, `P25PropCC`,
   `P25bPropEqCC`, `P25cPropEqCubical`.

### `k-and-uip`

**K-like reduction, and uniqueness of identity proofs**.

+  **Lean rule**.  Uniqueness of identity proofs is a special case of proof
   irrelevance (the first fact above).  K-like reduction is a second rule: the
   recursor of a `Prop` inductive type with one constructor and no fields
   reduces on any major premise whose type matches the constructor's, not only
   on the constructor.  Carneiro calls it "a second reduction rule called
   'K-like reduction' used for subsingleton eliminators", "a combination of
   proof irrelevance to change the major premise into a constructor followed by
   the iota rule", with the equality recursor's instance `rec_= C x a h ≡ x` as
   the foremost example (section 2.6.4, page 12);[^6] Vaishnav's rule [KLR]
   (section 1.2.3, pages 22 to 23) states it for any such type with its
   parameters and indices.[^7]  The kernel marks a declaration as a K target
   when it is not mutual, lives in `Prop` and has one constructor with no
   fields after the parameters (`init_K_target`, [kernel-inductive], lines 594
   to 613), and lean4export carries the flag as the recursor's `k` field.  At
   the pin, 15 recursors have `k = true`: `Eq.rec`, `HEq.rec`, `True.rec`,
   `Std.LeftIdentity.rec`, `Std.RightIdentity.rec` and
   `Lean.Meta.CheckTactic.CheckGoalType.rec` in `Init`;
   `AddCircle.EndpointIdent.rec`, `CategoryTheory.Cat.FreeReflRel.rec`,
   `CategoryTheory.Presieve.singleton.rec`,
   `CategoryTheory.Subgroupoid.Discrete.Arrows.rec` and
   `SimpleGraph.Walk.Nil.rec` in Mathlib; two in Batteries and two in Qq.
   `Acc.rec` and `And.rec` are not K targets (their constructors have fields)
   and `False.rec` is not (no constructor).  The rule on a variable proof is
   what `(h ▸ x) = x := rfl` exercises (`probes/lean/DefEq.lean`).
+  **Agda's status**.  Agda's K is a pattern-matching principle, not a
   reduction: a neutral proof `h : x ≡ x` never computes, under any flag.  By
   profile, as follows.
   +  U: K available by pattern matching (Agda's default).
   +  K: available by pattern matching (probe `P05KAccepted`); every K-like
      *reduction* in a Lean term still needs an explicit cast, since Agda will
      not reduce `subst P h x` on a variable `h`.
   +  CC: `--cubical-compatible` implies `--without-K`, which "Disables
      reasoning principles incompatible with univalent type theory, most
      importantly Streicher's K axiom" ([agda-options]); the pattern match is
      rejected with the error quoted above (probe `P06KRejected`), and a
      `--with-K` module such as agda-stdlib's
      `Relation.Binary.HeterogeneousEquality` cannot be imported,
      `[CoInfectiveImport]`: "Importing module
      Relation.Binary.HeterogeneousEquality not using the --cubical-compatible
      flag from a module which does" (probe `P22HEq`); `--safe` forbids
      combining `--cubical-compatible` with `--with-K` ([agda-safe]).
      Hedberg's theorem supplies UIP for types with decidable equality (probe
      `P07HedbergNat`).
   +  CU: `--cubical` "Turns on `--cubical-compatible` and `--without-K`"
      ([agda-options]); same rejection (probe `P17CubicalK`); the cubical
      library's `isSet` and `Discrete→isSet` play Hedberg's role.
+  **Translation strategy**.  The normalizer eliminates K-like reduction
   together with proof irrelevance ([#26]); each remaining use of K in a
   translated term is justified under CC by an `isSet` proof inferred per type
   ([#34]), extended to the generated library's types in [#51]; the
   declarations that need UIP on types that are not h-sets (equalities between
   types, `cast`, `HEq`) are enumerated and studied in [#55].  The corpus
   expects `nat-gcd-succ` to exercise this entry; see the
   [`literals`](#literals) entry for what the pin's definition of `Nat.gcd`
   changes about that expectation.
+  **Predecessors**.  lyphyser's shipped example uses `Eq.rec`, `And.rec` and
   `False.rec` only at `Prop` motives and postulates the `Set`-valued
   `Acc.rec`; Lean4Less eliminates the rule, and cannot eliminate proof
   irrelevance without it ([related-work], Lean4Less); rocq-lean-import needs
   definitional UIP: "such a Coq also lacks the special reduction of the
   eliminator of equality" (rocq-lean-import); Predicativize's Agda output was
   checked with K (Agda 2.6.3's default) and says nothing about
   `--cubical-compatible` (Predicativize).
+  **References**.  [carneiro-thesis] section 2.6.4; [vaishnav-thesis] section
   1.2.3; [kernel-inductive] lines 594 to 613; [agda-without-k],
   [agda-cubical-compatible], [agda-safe], [agda-options]; probes
   `P05KAccepted`, `P06KRejected`, `P07HedbergNat`, `P17CubicalK`, `P22HEq`.

### `large-elimination`

**Large elimination from `Prop` for subsingletons: `Eq`, `HEq`, `Acc`, `And`,
`True`, `False`**.

+  **Lean rule**.  An inductive proposition eliminates into `Sort u` when it is
   a syntactic subsingleton: Carneiro's second reason for large elimination,
   "The type family has at most one constructor, and all the non-recursive
   arguments to the constructor are either propositions or directly appear in
   the output type", with `eq` and `acc` as the examples (section 2.6.2, pages
   10 to 11);[^8] the manual's two requirements, "There is at most one
   constructor" and "Each of the constructor's parameter types is either a
   `Prop`, a parameter, or an index".[^9]  The kernel's
   `elim_only_at_universe_zero` ([kernel-inductive], lines 522 to 575) adds
   that a mutual block of propositions eliminates only into `Prop` and that a
   proposition with no constructors eliminates anywhere.  At the pin, 1,980 of
   the 2,253 inductive propositions in the environment eliminate largely, 152
   of them in `Init`: `Acc`, `And`, `Eq`, `False`, `HEq`, `Iff`, `Equivalence`,
   `NeZero`, `LawfulBEq`, and the `Std.*` and `Lawful*` classes, most of them
   `class … : Prop` structures whose fields are all propositions; `Exists`,
   `Nonempty` and `Or` do not (`probes/lean/Recursors.lean`).  `Acc` is the
   hard case: `Acc.rec` eliminates into `Sort u`, `WellFounded.fix` is built on
   it, and Carneiro's undecidability argument (section 3.1) unfolds a proof of
   `acc` forever.
+  **Agda's status**.  A `Prop` data type eliminates into `Set` only by the
   absurd pattern: "When defining a function from a data type in Prop to a type
   in Set, pattern matching is restricted to the absurd pattern ()", and of a
   `Prop`-valued equality, "the corresponding eliminator cannot be defined
   because of the limitations on pattern matching" ([agda-prop]).  Probes:
   `unsq (sq b) = b` on `Squash Bool : Prop` is rejected with
   `[SplitInProp] Cannot split on datatype in Prop unless target is in Prop`
   (`P01PropElim`), and so are `subst` on a `Prop`-valued `_≐_`
   (`P02PropEqElim`) and well-founded recursion on a `Prop`-valued `AccP`
   (`P02bAccProp`); `⊥-elim ()` is accepted (`P01bPropAbsurd`).  By profile, as
   follows.
   +  U: the restriction is one of pattern matching, not of universes, so
      `--type-in-type` does not lift it: `P26AccPropU` fails with the same
      `[SplitInProp]` error, which is why lyphyser postulated the `Set`-valued
      `Acc.rec`.
   +  K: `Eq`, `HEq`, `Acc`, `And`, `True`, `False` and `Iff` live in `Set` on
      the Agda side (agda-stdlib's `_≡_`, `Acc`, `_×_`, `⊤`, `⊥`), where large
      elimination is ordinary pattern matching; `Acc` in `Set` computes on
      closed terms (`gcd 1000000007 998244353 ≡ 1` by `refl`, probe
      `P11Literals`).
   +  CC: as K; nothing here depends on K.
   +  CU: as K, with the cubical library's types.
+  **Translation strategy**.  [#32]: the subsingleton eliminators become
   `Set`-valued types in profiles K, CC and CU, under either `Prop` encoding;
   under encoding A the propositions Lean eliminates largely are the ones that
   leave Agda's `Prop`, and the casts the normalizer inserts relate the two
   sides.  Well-founded recursion goes through `Acc` in `Set`, or through the
   fuel-based fixpoint the pin now uses for `Nat` measures
   ([`literals`](#literals)).  The corpus expects `nat-gcd-succ` and
   `lists-subset-refl` to exercise this entry.
+  **Predecessors**.  lyphyser accepts the `Prop`-motive instances and
   postulates `Acc.rec` into `Set` and `WellFounded.fixFEq` ([related-work],
   lyphyser/lean2agda); rocq-lean-import detects the case, `Acc` being its
   example, and disables universe checking while declaring the inductive
   (rocq-lean-import); Lean4Less leaves it alone and lean2dk encodes it
   (Lean4Less, lean2dk).
+  **References**.  [carneiro-thesis] sections 2.6.2 and 3.1;
   [kernel-inductive] lines 522 to 575; [lean-manual-inductive] (Subsingleton
   Elimination) and [lean-manual-propositions] (Restricted Elimination);
   [agda-prop]; probes `P01PropElim`, `P01bPropAbsurd`, `P02PropEqElim`,
   `P02bAccProp`, `P11Literals`, `P26AccPropU`.

### `quotients`

**Primitive quotients and their computation rule**.

+  **Lean rule**.  `Quot`, `Quot.mk`, `Quot.lift` and `Quot.ind` are kernel
   primitives, added by `environment::add_quot` after it checks that `Eq` has
   the expected shape ([kernel-quot]), with the reduction
   `Quot.lift f h (Quot.mk r a) ⇝ f a` (and the corresponding rule for
   `Quot.ind`) applied in `whnf_core` ([kernel-type-checker], line 395);
   `Quot.sound : r a b → Quot.mk r a = Quot.mk r b` is an axiom in `Init.Core`.
   Carneiro: a "semi-builtin" axiom, since "Lean does not support adding
   computational rules to the kernel", and only `sound` counts as an axiom,
   because the other three constants and the rule would be satisfied by taking
   `α/R` to be `α`, `mk` to be the identity and `lift f h` to be `f` (section
   2.7.1, page 13);[^10] the manual: "quotient types are a built-in feature of
   Lean's type system".[^11]  `funext` is proved from quotients (Carneiro,
   section 2.8, item 8; Vaishnav, page 19), which is why `Quot.sound` appears
   in the axioms of so many T1 declarations (ten of the twelve corpus entries).
   At the pin `Quot.lift f h (Quot.mk r a) = f a := rfl` is accepted and
   `#print Quot` answers "Quotient primitive" (`probes/lean/DefEq.lean`).
+  **Agda's status**.  Plain Agda has no quotients.  By profile, as follows.
   +  U: postulated, as lyphyser's output does; a postulated `lift` does not
      compute.
   +  K: a record of the primitives as a module parameter, `Quot`, `mk`,
      `lift`, `ind`, `sound` and a propositional computation rule `lift-β`,
      type-checks under `--safe`; the rule has to be a field, since
      `lift f h (mk R a) ≡ f a` by `refl` is rejected with
      `lift f h (mk R a) != f a of type A` (probe `P24QuotParam`).  Every
      definitional use of the computation rule in a Lean term becomes a rewrite
      by `lift-β`.
   +  CC: as K (`P24QuotParam` runs under `--cubical-compatible`).
   +  CU: the cubical library's set quotients `_/_` with `[_]`, `eq/` and
      `squash/` ([cubical-setquot]): `SQ.rec` computes definitionally on
      points, so `liftQ [ a ] ≡ f a` holds by `refl` (probe
      `P16CubicalQuotient`); `eq/` is `Quot.sound` and `SQ.elimProp` is
      `Quot.ind`.  The quotient is set-truncated and `SQ.rec` asks for
      `isSet B`, a hypothesis Lean's `Quot.lift` does not have because every
      Lean type is an h-set; a lift into a type not known to be an h-set needs
      that proof too.  `funExt` and `hPropExt` are theorems ([cubical-prelude],
      [cubical-univalence]; probe `P16CubicalQuotient`).
+  **Translation strategy**.  Postulates under profile U ([#21]); the parameter
   record with the propositional rule, and the extension of the normalizer's
   cast mechanism to `Quot.lift`'s computation rule ([#30]); parameters
   threaded per module in both layers ([#38]); cubical set quotients and the
   parameter-free constructive layer under CU ([#52]).  The corpus expects
   `multiset-map-map` and `set-ext`, in both a CC and a CU file, and the three
   T2 entries to exercise this entry.
+  **Predecessors**.  lyphyser: "Quotients are currently postulated"
   ([related-work], lyphyser/lean2agda); rocq-lean-import emulates them with
   private inductive types in a module `Coq.Lean` (rocq-lean-import); Lean4Less
   leaves `Quot` and its rule in Lean⁻, and lean2dk encodes the rule as rewrite
   rules for `Quot.ind` and `Quot.lift` on `Quot.mk` (Lean4Less, lean2dk);
   Carneiro's section 3.1.1 notes that `lift` on a quotient of a proposition is
   a second source of non-transitivity.
+  **References**.  [carneiro-thesis] sections 2.7.1, 2.8 and 3.1.1;
   [vaishnav-thesis] sections 1.2.2 and 1.2.3; [kernel-quot];
   [kernel-type-checker] line 395; [lean-manual-quotients]; [cubical-setquot],
   [cubical-prelude], [cubical-univalence]; probes `P16CubicalQuotient`,
   `P24QuotParam`.

### `axioms`

**The axioms `propext`, `Quot.sound` and `Classical.choice`**.

+  **Lean rule**.  Three axioms are declared for all of Lean's mathematics:
   `propext : (a ↔ b) → a = b` and `Quot.sound` in `Init.Core`, and
   `Classical.choice : {α : Sort u} → Nonempty α → α` in `Init.Prelude`, "a
   global choice function" from which "the law of excluded middle is derived
   (it is not stated as a separate axiom)" (Carneiro, section 2.7.3, page
   13);[^12] `Classical.em` depends on all three (`probes/lean/DefEq.lean`).
   Carneiro's comparison with Coq's axioms (section 2.8, item 8) lists what
   they imply: functional extensionality, every form of excluded middle,
   indefinite description.  The environment at the pin declares 15 axioms (the
   scan): these three; `sorryAx`; `Lean.ofReduceBool`, `Lean.ofReduceNat` and
   `Lean.trustCompiler`; and eight `unsafe` compiler axioms in `Init.Prelude`
   (`lcProof`, `lcCast`, `lcAny`, `lcErased`, `lcUnreachable`, `lcVoid`,
   `isScalarObj`, `Quot.lcInv`).  Everything past the first three is a trust
   escape hatch (that entry).  The tier of a declaration bounds the axioms its
   *proof* uses, not what the mathematics needs: `List.reverse_reverse` is T1
   only because `simp` closes a goal with `eq_self`, proved from `propext`, and
   the Agda proof needs no axiom
   ([`../../corpus/list-reverse-reverse/notes.md`][corpus-seed-notes]);
   `Nat.gcd_self` is T1 through `eq_self` and `Nat.mod_self` as well.  The
   atlas ([#11]) can count how many T1 declarations owe their tier to `eq_self`
   alone.
+  **Agda's status**.  `--safe` forbids postulates: `postulate funext : …` is
   rejected with `[SafeFlagPostulate] Cannot postulate funext with safe flag`
   (probe `P03SafePostulate`; the rule is the first item of [agda-safe]'s
   list).  By profile, as follows.
   +  U: postulates allowed, so each axiom is a postulate; the result is never
      a deliverable.
   +  K: `propext`, the quotient primitives, `funext` and `Classical.choice`
      are record-typed module parameters in the style of TypeTopology, threaded
      so that a module takes only what its declarations need; a one-line user
      module may postulate them outside the `--safe` library.
   +  CC: as K.
   +  CU: `funExt` and `hPropExt` are theorems and quotients are higher
      inductive types (probe `P16CubicalQuotient`), so only `Classical.choice`
      remains, and only in forms consistent with univalence (the second fact
      above); a parameter of Lean's form is accepted but can never be
      instantiated (probe `P19ChoiceParam`).
+  **Translation strategy**.  Axioms under U ([#20]); the parameter records on
   `Init` and `Std` ([#33]) and the two-layer generalization ([#38]); the layer
   rules, with the reasoning for treating `propext` and `Quot.sound` as
   constructive ([#37]); the classical `Decidable` instances ([#39]) and the
   promotion overlay ([#40]); choice under univalence ([#53]).  The
   normalizer's casts carry `propext` (the previous entries), so the atlas
   records casts apart from the source's axioms ([#26], [#36]).
+  **Predecessors**.  lyphyser postulates the axioms, as it does every constant
   without a value; rocq-lean-import declares them as axioms; Lean4Less passes
   them through and, since February 2026, adds none of its own; hol2dk's Rocq
   library assumes classical logic, indefinite description, functional and
   propositional extensionality and proof irrelevance as axioms;
   Predicativize's Agda output checks under `--safe` with none ([related-work],
   the respective sections).  Mathlib's dependence on choice is measured in the
   survey's Mathlib measurements section, with the caveats about denominators
   that the atlas resolves.
+  **References**.  [carneiro-thesis] sections 2.7 and 2.8;
   [lean-manual-axioms]; [agda-safe], [agda-postulates]; [corpus-seed-notes];
   probes `P03SafePostulate`, `P16CubicalQuotient`, `P19ChoiceParam`.

### `universe-levels`

**Universe polymorphism and level arithmetic**.

+  **Lean rule**.  Levels are `u | 0 | Sℓ | max(ℓ, ℓ) | imax(ℓ, ℓ)`; every
   constant has a list of universe variables instantiated at each use; level
   equality is decided by an inequality judgment whose semantics is the
   pointwise order on `ℕ` under all substitutions (Carneiro, section 2.1, pages
   6 to 7).[^1]  `Prop = Sort 0`, `Type u = Sort (u+1)`; there is no
   quantification over levels inside a term, only at the head of a constant.
   Carneiro's remark on Coq, "universe polymorphism is a luxury": a theorem at
   fixed levels can be reproduced by duplicating constants per instantiation
   (section 2.8, item 3).
+  **Agda's status**.  Universe levels are first-class values of type `Level`
   with `lzero`, `lsuc` and `_⊔_` and nothing else ([agda-levels]); there is no
   `imax`.  The definitional laws are idempotence, associativity,
   commutativity, distributivity of `lsuc` over `⊔`, neutrality of `lzero` and
   subsumption (`a ⊔ lsuc a` is `lsuc a`) ([agda-levels]); probe
   `P08bPredicativeLevels` checks `Set (a ⊔ a) → Set a`,
   `Set (lsuc a ⊔ a) → Set (lsuc a)` and `Set (a ⊔ b) → Set (b ⊔ a)` by
   conversion.  A type that quantifies over a level lives in `Setω`:
   `(ℓ : Level) → Set ℓ → Set ℓ : Setω`, and asking for `Set₁` fails with
   `Setω != Set₁` (probe `P09Setω`), so a universe-polymorphic Lean constant
   becomes an Agda declaration with explicit `Level` arguments whose type lives
   in `Setω`, which Agda allows for a top-level declaration.  By profile, as
   follows.
   +  U: `--type-in-type` ignores levels; `--safe` rejects the flag with
      `[SafeFlagPragma]`: "The --safe mode does not allow OPTIONS pragma
      --type-in-type" (probe `P04SafeTypeInType`).
   +  K: full level elaboration; `Prop ℓ` is predicative (previous entries).
   +  CC: as K.
   +  CU: as K; the cubical library writes `Type ℓ` and `ℓ-max`, `ℓ-suc` for
      the same levels.
+  **Translation strategy**.  `Prop`-instantiation specialization first
   ([#28]), which removes `imax`; then predicativization by level unification
   ([#29]), expecting some constants to need constraints the solver cannot find
   (Predicativize's Theorem 6.1) and some to be essentially impredicative.  The
   corpus lists six entries under this feature, `list-reverse-reverse` among
   them (one level parameter, no `imax`, no instantiation at `Prop`).
+  **Predecessors**.  lyphyser's level clauses and rocq-lean-import's `_instX`
   duplication with surrogate parameters for algebraic universes
   ([related-work], the two sections); Predicativize's elaboration algorithm,
   the most-general-unifier characterization, and Agda's "Failed to solve the
   following constraints" on `_0 ⊔ _1 = _0 ⊔ _2`, a constraint with more than
   one solution (Predicativize, Remark 6.3); lean2dk's rewrite system for
   levels with `imax` (Vaishnav, chapter 3).
+  **References**.  [carneiro-thesis] sections 2.1 and 2.8;
   [lean-manual-universes]; [agda-levels], [agda-sorts]; probes
   `P04SafeTypeInType`, `P08bPredicativeLevels`, `P09Setω`.

### `structure-eta`

**Structure eta and unit eta**.

+  **Lean rule**.  A term `t` of a structure-like type `S` (one constructor, no
   indices, not recursive) is definitionally equal to `S.mk p t.1 … t.m`; the
   kernel's `try_eta_struct_core` checks that one side is a constructor
   application of a non-recursive structure and compares each field with the
   projection of the other side ([kernel-type-checker], lines 889 to 907;
   `is_non_rec_structure`, [kernel-inductive], lines 28 to 34).  Any two terms
   of a unit-like type (structure-like with no fields) are definitionally equal
   (`is_def_eq_unit_like`, [kernel-type-checker], lines 1159 to 1170).
   Vaishnav states both as [ETA-S] (section 1.2.2, pages 19 to 20) and [UNIT]
   (page 21);[^13] the manual: "Definitional equality includes η-equivalence of
   functions and single-constructor inductive types".[^14]  These are Lean 4
   additions and absent from Carneiro's rules, which have only η for functions
   (section 2.2).  At the pin `p = (p.1, p.2) := rfl` and
   `u = PUnit.unit := rfl` are accepted, and for a recursive
   `structure Tree where children : List Tree` the eta equation
   `t = ⟨t.children⟩ := rfl` is rejected with a type mismatch
   (`probes/lean/DefEq.lean`).  Structure-like reduction, the recursor of a
   structure-like type reducing on any major premise by projection, is the
   related rule Lean4Less can eliminate ([related-work], Terms).
+  **Agda's status**.  Records have η by default, data types do not:
   `p ≡ (proj₁ p , proj₂ p)` and `u ≡ tt` hold by `refl` (probe
   `P10RecordEta`), while for `data Wrap` the equation `w ≡ wrap (unwrap w)` is
   rejected with `w != wrap (unwrap w) of type Wrap A` (probe `P10bDataNoEta`).
   "Inductive record types have η-equality enabled by default if this does not
   lead to potential infinite η-expansion (as determined by the positivity
   checker)" ([agda-records], Recursive records): a recursive record `Tree`
   with a field `children : List Tree` has η in Agda (probe
   `P10cRecursiveRecord`), where Lean has none.  That is a gap in the other
   direction: Agda identifies more terms, which can only make a translated term
   easier to check.  `no-eta-equality` turns η off per record; the `ETA` pragma
   that forces it for unguarded recursive records is forbidden under `--safe`
   ([agda-safe]).  By profile, as follows.
   +  U: as K.
   +  K: structure-like inductives become `record`s and keep both rules;
      unit-like types become records with no fields.
   +  CC: as K; η for records is unaffected by `--cubical-compatible` (probe
      `P10RecordEta` runs under it).
   +  CU: as K.
+  **Translation strategy**.  Records for structure-like inductives ([#18]);
   the eta cases in [#32]; and the decision in [#26] about Lean4Less's optional
   eliminations of structure-like reduction and unit eta, which Agda's own η
   for records suggests leaving switched off.  Recursive structures need
   nothing: Agda grants what Lean withholds.  The corpus expects
   `subtype-coe-eta` to exercise this entry.
+  **Predecessors**.  lyphyser emits records "where possible" ([related-work],
   lyphyser/lean2agda); Lean4Less eliminates structure-like reduction since
   2025-04-10 and unit eta since 2026-06-13 on its `claude-stable` branch
   (Lean4Less); lean2dk's encoding of structure eta is one of the three that
   drive stock Dedukti's conversion "into non-termination or exponential work"
   (lean2dk).
+  **References**.  [vaishnav-thesis] section 1.2.2; [kernel-type-checker]
   lines 889 to 907 and 1159 to 1170; [kernel-inductive] lines 28 to 34;
   [lean-manual-type-system]; [agda-records]; probes `P10RecordEta`,
   `P10bDataNoEta`, `P10cRecursiveRecord`.

### `literals`

**`Nat` literals with the kernel's accelerated arithmetic, and `String`
literals**.

+  **Lean rule**.  A natural number literal is a kernel term (`Expr.lit`),
   interchangeable with `Nat.zero` and `Nat.succ` during conversion
   (`is_nat_zero`, `is_nat_succ`, [kernel-type-checker], lines 1058 to 1086),
   and fifteen operations on literals are computed by the arbitrary-precision
   library rather than by unfolding: the unary `Nat.succ`, and the fourteen
   binary `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.pow`, `Nat.gcd`, `Nat.mod`,
   `Nat.div`, `Nat.beq`, `Nat.ble`, `Nat.land`, `Nat.lor`, `Nat.xor`,
   `Nat.shiftLeft` and `Nat.shiftRight` (`reduce_nat`, lines 702 to 733), with
   a size limit on results (`LEAN_NAT_MAX_SIZE`) and a refusal for `Nat.pow`
   beyond it.  The manual: "In the kernel, there are special `Nat` literal
   values that use a widely-trusted, efficient arbitrary-precision integer
   library (usually GMP)".[^15]  A string literal is also a kernel term,
   expanded on demand to `String.ofList [c₁, …, cₙ]`
   (`try_string_lit_expansion`, lines 1145 to 1156, and `whnf_core`, line 421;
   the constant the kernel expands to is `String.ofList`, line 1342).  At the
   pin `String` is a structure
   `String.ofByteArray (toByteArray : ByteArray) (isValidUTF8 : …)`, "a logical
   model that specifies their behavior in terms of `ByteArray`s that contain
   UTF-8 scalar values",[^16] and `String.mk : List Char → String` is a
   deprecated definition in favor of `String.ofList`; `Char` is a structure
   over `UInt32` with a validity proof (`probes/lean/Strings.lean`).  Accepted
   at the pin: `18446744073709551616 + 1 = 18446744073709551617 := rfl`,
   `2 ^ 64 = 18446744073709551616` and `Nat.gcd 1000000007 998244353 = 1` by
   `decide`, `Nat.gcd 12 18 = 6 := rfl`, `"a" = String.mk ['a'] := rfl`,
   `"ab" ++ "c" = "abc"` by `decide` (`probes/lean/DefEq.lean`).
   `Nat.gcd` deserves its own paragraph.  At the pin it is defined by
   well-founded recursion ([lean-gcd-source], lines 34 to 41), as follows:

   ```lean
   @[extern "lean_nat_gcd"]
   def gcd (m n : @& Nat) : Nat :=
     if m = 0 then n else gcd (n % m) m
     termination_by m
   ```

   It is compiled to `Nat.gcd._unary` through `WellFounded.Nat.fix`, which at
   this version is fuel-based structural recursion,
   `fix h F x = fix.go h F (eager (h x + 1)) x _` with `go` defined by
   `Nat.rec` on the fuel and the proof `h x < fuel` eliminated only in the
   unreachable zero case; it depends on no axiom (`probes/lean/Gcd.lean`).  The
   defining equation does not hold by conversion on variables:
   `Nat.gcd (x+1) y = Nat.gcd (y % (x+1)) (x+1)` fails
   `with_unfolding_all rfl`, since the two sides unfold with different fuel,
   and `Nat.gcd_succ` is a theorem through the equation lemma `Nat.gcd.eq_1`,
   which depends on `Quot.sound`; closed instances hold by the kernel's `gcd`.
   Lean4Less's README says the equation
   `Nat.gcd (succ y) x = Nat.gcd (mod x (succ y)) (succ y)` holds
   definitionally only through K-like reduction, so `Nat.gcd` cannot be a
   kernel primitive in Lean⁻ and constants computing large gcds are aborted;
   Vaishnav attributes it to the well-founded definition "invoking a use of
   K-like reduction at some point during reduction" (section 7.1.3, page
   163).[^17]  That README predates the fuel-based `WellFounded.Nat.fix`;
   whether Lean⁻ at this pin still needs K-like reduction to compute a closed
   `Nat.gcd` by unfolding is for the corpus entry `nat-gcd-succ` ([#7]) to
   settle by running Lean4Less.
+  **Agda's status**.  `{-# BUILTIN NATURAL ℕ #-}` gives literals, and the
   builtin operations on closed naturals compute with the host's integers
   ([agda-builtins]): `18446744073709551616 + 1 ≡ 18446744073709551617` and
   `2 ^ 64 ≡ 18446744073709551616` by `refl`, the latter by 64 builtin
   multiplications since `_^_` is a library function; agda-stdlib's `gcd` is
   defined by well-founded recursion through `Acc` ([stdlib-gcd], lines 46
   to 51) and computes on closed terms, `gcd 1000000007 998244353 ≡ 1` by
   `refl`; the whole probe checks in 3.6 s (probe `P11Literals`).  `String`
   is a primitive type, not a structure: `primStringAppend`,
   `primStringToList` and `primStringFromList` with their injectivity
   primitives ([agda-builtins]); `"ab" ++ "c" ≡ "abc"` and
   `primStringFromList ('a' ∷ 'b' ∷ []) ≡ "ab"` hold by `refl`.  The
   accelerated sets differ: Agda has builtin `+`, `-`, `*`, `div`, `mod`,
   `≡ᵇ` and `<ᵇ` and no builtin `gcd`, `pow`, shifts or bitwise operations.
   By profile, as follows.
   +  U: as K.
   +  K: as described.
   +  CC: as described (probe `P11Literals` runs under it).
   +  CU: the same builtins through `Agda.Builtin.Nat` and
      `Agda.Builtin.String` (probe `P28CubicalLiterals`).
+  **Translation strategy**.  Literals through `BUILTIN NATURAL` and the
   builtin string type in the printer ([#17]); the operation table ([#31]): for
   each accelerated Lean operation, its Agda counterpart, what a closed
   computation costs after translation, and the treatment of `Nat.gcd` and of
   `String.ofList` against the primitive string.  The corpus expects
   `nat-gcd-self` and `nat-gcd-succ` to exercise this entry.
+  **Predecessors**.  lean2dk value-stubs three classes of constants whose cost
   "is inherent to the encoding rather than the kernel", bignum `Nat`
   primitives on a unary encoding, the `omega` machinery's normal forms and
   `String` literals, and its README says a stub is "trusted, not checked"
   ([related-work], lean2dk); Lean4Less keeps every kernel primitive but
   `Nat.gcd` (Lean4Less); lyphyser's one shipped example is `Nat.gcd_self`
   (lyphyser/lean2agda).
+  **References**.  [kernel-type-checker] lines 421, 702 to 733, 1058 to 1086,
   1145 to 1156 and 1342; [lean-gcd-source]; [lean-manual-nat],
   [lean-manual-strings], [lean-manual-recursion]; [vaishnav-thesis] section
   7.1.3; [agda-builtins]; [stdlib-gcd]; probes `P11Literals`,
   `P28CubicalLiterals`, `probes/lean/Gcd.lean`, `probes/lean/Strings.lean`.

### `trust-escape-hatches`

**The trust escape hatches: `sorryAx`, `native_decide`, `Lean.ofReduceBool`,
`implemented_by`, `partial`, `unsafe`**.

+  **Lean rule**.  A declaration uses a hatch when something other than Lean's
   kernel is trusted for it.  The corpus defines the tier T3, which the
   translator refuses, as any axiom other than `propext`, `Quot.sound` and
   `Classical.choice` ([corpus-schema], Tiers from axioms); the catalog defines
   the hatch the same way and adds the two that `#print axioms` cannot see.
   What exists at the pin, from the scan and `probes/lean/Hatches.lean`, is as
   follows.
   +  `sorryAx : (α : Sort u) → Bool → α` (`Init.Prelude`), behind `sorry`; its
      only dependent in the environment is itself.
   +  `Lean.ofReduceBool : ∀ (a b : Bool), Lean.reduceBool a = b → a = b`,
      `Lean.ofReduceNat` and `Lean.trustCompiler : True` (`Init.Core`): the
      kernel evaluates `Lean.reduceBool c` and `Lean.reduceNat c` by running
      the compiled code of `c` (`reduce_native`, [kernel-type-checker], lines
      614 to 635).  At the pin all three are deprecated, with the message
      "in-kernel native reduction is deprecated; assert native evaluations with
      axioms instead", and their only dependents are the five constants of
      their own family.
   +  `native_decide` no longer goes through `Lean.ofReduceBool`: a theorem it
      proves depends on a generated axiom named
      `<theorem>._native.native_decide.ax_1_1`, one per invocation (the manual:
      "the `native_decide` tactic creates a bespoke axiom for each invocation",
      and such a proof "depends on the correctness of the Lean compiler and all
      definitions with an `@[implemented_by]` attribute").[^18]  No such axiom
      exists in the environment of `import Mathlib`.
   +  Eight `unsafe` axioms of the compiler in `Init.Prelude`:
      `lcProof : ∀ {α : Prop}, α`, `lcCast`, `lcAny`, `lcErased`,
      `lcUnreachable`, `lcVoid`, `isScalarObj`, `Quot.lcInv`.  242 constants
      depend on `lcProof`, 41 of them in Mathlib: the `Repr` instances of
      `Real`, `Complex`, `NNReal`, `ENNReal`, `Finset`, `Multiset`, `Finsupp`,
      `DFinsupp`, `Sym2`, `Cycle`, `Equiv.Perm`, `PrimeMultiset`,
      `TensorProduct` and `CauSeq.Completion`, the floating-point arithmetic of
      `Mathlib.Data.FP.Basic`, `Part.unwrap`, `Quot.unquot`,
      `Multiset.instToExprOfToLevel`, and four tactic-side helpers.  The
      roadmap's T3 list does not name `lcProof`; the atlas should.
   +  `unsafe` definitions (714 in the environment, 68 in Mathlib) are exempt
      from kernel checking ("The `unsafe` marker exempts a definition from
      kernel checking").[^19]
   +  `partial` definitions (1,509 and 266): "treated as opaque constants by
      the kernel and are neither unfolded nor reduced";[^20] a `partial def f`
      becomes an `opaque f` with an `unsafe` companion `f._unsafe_rec`, depends
      on no axiom, and carries no `implemented_by` attribute, so it is
      invisible to `#print axioms` and detected by the companion.
   +  `implemented_by` (341 and 28) and `@[extern]` (as on `Nat.gcd`) replace a
      constant in compiled code; the kernel ignores them, so they matter
      logically only through `native_decide` and the `reduceBool` family.
   `opaque` constants (3,062) and `noncomputable` definitions are not hatches:
   an `opaque` must have an inhabited type, and `noncomputable` concerns the
   compiler (next entry).
+  **Agda's status**.  `--safe` is the hatch-free mode, and it rejects, with
   the error quoted, the following: postulates (`[SafeFlagPostulate]`, probe
   `P03SafePostulate`); the `TERMINATING` and `NON_TERMINATING` pragmas
   (`[SafeFlagTerminating] Cannot use TERMINATING pragma with safe flag.`,
   probe `P04bSafeTerminating`; `[SafeFlagNonTerminating]`, probe
   `P12SafeNonTerminating`); `--type-in-type` (`[SafeFlagPragma]`, probe
   `P04SafeTypeInType`).  Its full list adds `--allow-unsolved-metas`,
   `NON_COVERING`, `NO_POSITIVITY_CHECK`, `POLARITY`, `NO_UNIVERSE_CHECK`,
   `INJECTIVE`, `ETA`, `--rewriting`, `COMPILE` pragmas, `primEraseEquality`
   with `--without-K`, `--allow-exec`, and the flag combinations known to be
   inconsistent ([agda-safe]); `--safe` is coinfective, so every imported
   module must be safe too.  By profile, as follows.
   +  U: no `--safe`, so postulates stand in for everything the scaffold cannot
      yet express; this is why U is never a deliverable.
   +  K: `--safe`; nothing translated may need a hatch.
   +  CC: as K.
   +  CU: as K; `--guardedness` is required by the cubical library and is safe
      without `--sized-types` ([agda-options]).
+  **Translation strategy**.  T3 is refused and reported with the hatch each
   refused declaration uses ([#37]); the atlas detects `partial` and
   `implemented_by` apart from the axiom set and classifies the `lcProof`
   family ([#11], [#36]); the soundness-bug suite confirms that translation
   plus Agda rejects what must be rejected ([#58]); the trust analysis names
   every component a user trusts instead ([#57]).  The corpus has no T3 entry,
   by design.
+  **Predecessors**.  lean2dk's value-stubbed constants are "trusted, not
   checked"; hol2dk ships its theorems as axioms with a script that regenerates
   the proofs; rocq-lean-import's mathlib run declared terms with conversion
   checking off; lyphyser's postulates are profile U's ([related-work], the
   respective sections).
+  **References**.  [lean-manual-axioms], [lean-manual-modifiers],
   [lean-manual-recursion], [lean-manual-tactics]; [kernel-type-checker] lines
   614 to 635; [agda-safe], [agda-options]; [corpus-schema]; probes
   `P03SafePostulate`, `P04SafeTypeInType`, `P04bSafeTerminating`,
   `P12SafeNonTerminating`, `probes/lean/Hatches.lean`,
   `probes/lean/Scan.lean`, `probes/lean/ScanByRoot.lean`.

### `decidable-and-noncomputable`

**`Decidable` and `noncomputable`**.

+  **Lean rule**.  `Decidable : Prop → Type` with constructors `isFalse` and
   `isTrue`, `decide : (p : Prop) → [Decidable p] → Bool`, and
   `if … then … else` elaborated to `ite` or `dite` on an instance.
   `Classical.propDecidable : (a : Prop) → Decidable a`, whose value is
   `Classical.choice` applied to a proof, is `noncomputable` and depends on all
   three axioms, as does `Classical.decEq` (`probes/lean/DefEq.lean`,
   `Strings.lean`).  `noncomputable` is a compiler-facing modifier: "Functions
   marked `noncomputable` are not compiled and cannot be executed";[^19] the
   kernel is indifferent to it, a `noncomputable def` unfolds like any other,
   and what stops computation is the axiom, which has no reduction rule.  At
   the pin 16,021 constants are `noncomputable`, 15,734 of them in Mathlib (the
   scan).  Mathlib statements carry classical `Decidable` instances
   (`Finset.filter`, `Finset.image`); the corpus entry `finset-card-image` is
   T2 for that reason.
+  **Agda's status**.  agda-stdlib's `Dec P` is a record with `does : Bool` and
   `proof : Reflects P does`, and `if_then_else_` branches on a `Bool`; there
   is no `noncomputable` modifier and no need for one.  With excluded middle as
   a module parameter `lem : (P : Set) → Dec P`, the definition
   `f = if does (lem ⊤) then 1 else 0` type-checks and `f ≡ 1` by `refl` is
   rejected with `if does (lem ⊤) then 1 else 0 != 1 of type ℕ` (probe
   `P13DecStuck`): the decision is stuck on the parameter, which is what
   `noncomputable` meant in Lean.  By profile, as follows.
   +  U: a postulated `lem` is stuck the same way.
   +  K: the classical layer takes `Choice` or excluded middle as a parameter
      and its decisions are stuck; a statement whose only classical content is
      such an instance can be restated with the instance as a hypothesis.
   +  CC: as K.
   +  CU: excluded middle for h-propositions is consistent with univalence (the
      second fact above) and can be a parameter; a classical `Dec P` for an
      arbitrary `Set P` cannot be instantiated.
+  **Translation strategy**.  Detect classical instance terms in statements and
   proofs as atlas fields; abstract the instance into a hypothesis so that the
   statement becomes constructive even when the proof stays classical, and
   count how many T2 statements this recovers ([#39]); promote a theorem by a
   hand-written constructive proof ([#40]); thread the parameters ([#38]).  The
   corpus expects `finset-card-image`, `real-sqrt-nonneg`, `subgroup-card-dvd`
   and `nat-gcd-succ` (whose `if m = 0` decides through `Nat.decEq`, which
   computes) to exercise this entry.
+  **Predecessors**.  None treats it separately: lyphyser and rocq-lean-import
   postulate or declare `Classical.choice`, Lean4Less passes it through, and
   hol2dk assumes classical logic as an axiom ([related-work], the respective
   sections).  Mathlib's own effort to reduce the use of choice is the open
   pull request 35685 (Mathlib measurements).
+  **References**.  [lean-manual-modifiers], [lean-manual-classes]; [hott-book]
   section 3.4; probes `P13DecStuck`, `probes/lean/DefEq.lean`,
   `probes/lean/Strings.lean`.

### `nested-and-mutual-inductives`

**Nested and mutual inductive types**.

+  **Lean rule**.  The kernel accepts mutual blocks, whose types "must live in
   the same universe" ([kernel-inductive], line 294), and nested inductive
   types, in which the type being defined occurs as a parameter of a previously
   declared inductive type (`List Tree`); it eliminates a nested declaration
   into an auxiliary mutual one and restores the original afterwards
   (`elim_nested_inductive_fn`, lines 978 to 1050; the manual: "Internally, the
   kernel performs this translation; if it succeeds, then the original nested
   inductive type is accepted").[^21]  A mutual block of propositions
   eliminates only into `Prop` (previous entries).  `InductiveVal.numNested`
   and `all` record the two.  Carneiro's Lean 3 kernel had neither: "Coq also
   supports mutual inductives, nested inductive types, and coinductive types.
   These can all be encoded using regular inductives" (section 2.8, item 5).
   At the pin the environment holds 86 nested or mutual inductive declarations:
   64 in Lean's own code, 6 in Aesop, 2 in Std, 1 each in Batteries and
   ProofWidgets, `Lean.Syntax` in `Init` (nested through `Array Syntax` and
   `List Syntax.Preresolved`), and 11 in Mathlib, of which 4 are outside tactic
   code: the mutual propositions `Lists'.Subset` and `Lists.Equiv` of
   `Mathlib.SetTheory.Lists` and their compiler-generated `.below` companions;
   the other 7 are tactic code such as `Mathlib.Tactic.Translate.ArgReorder`.
   Nested and mutual inductive types are therefore almost absent from Mathlib's
   mathematics, and the corpus takes the one mutual block there is
   (`lists-subset-refl`).
+  **Agda's status**.  Agda has `mutual` blocks, interleaved mutual blocks and
   forward declarations ([agda-mutual]); nested occurrences through `List` pass
   the positivity checker, which requires strict positivity ([agda-data]); and
   it has induction-recursion, which Lean's kernel does not.  Probe
   `P14NestedMutual` defines a rose tree, a `Lists'`-style pair of mutual
   types, mutual `Even` and `Odd` predicates and an inductive-recursive
   universe under `--safe --cubical-compatible`, and `P27CubicalInductives` the
   same under `--safe --cubical`.  By profile, as follows.
   +  U: as K.
   +  K: both forms are native; a mutual family of propositions is a mutual
      family of `Set`s in Agda and eliminates anywhere.
   +  CC: as K (probe `P14NestedMutual`).
   +  CU: as K (probe `P27CubicalInductives`).
+  **Translation strategy**.  Emit mutual blocks and nested types directly
   ([#18]); the recursors of a nested type have one motive per nested
   occurrence, which the pattern-matching translation ([#19]) must fold back
   into one definition; `Lean.Syntax` is the `Init` test case and
   `lists-subset-refl` the corpus one.
+  **Predecessors**.  lyphyser's README does not discuss them;
   rocq-lean-import's Lean 3 exports had them already encoded; Predicativize
   rebuilt every inductive type by hand in Agda ([related-work], the respective
   sections).
+  **References**.  [carneiro-thesis] section 2.8; [kernel-inductive] lines 294
   and 978 to 1050; [lean-manual-inductive] (Nested Inductive Types);
   [agda-mutual], [agda-data]; probes `P14NestedMutual`,
   `P27CubicalInductives`, `probes/lean/Scan.lean`.

### `projections-and-let`

**Projections and `let`**.

+  **Lean rule**.  `Expr.proj S i t` is a kernel primitive distinct from the
   projection functions `S.i` (definitions that unfold to it); it reduces when
   `t` reduces to a constructor application (`whnf_core`,
   [kernel-type-checker], line 450, and `lazy_delta_proj_reduction`, line
   1123), and is typed by Vaishnav's rule [PROJ] "applied to terms of
   structure-like types" (section 1.2.1, page 14).  `let x : α := v; e` is a
   kernel term with ζ-reduction: Carneiro defines it to be equivalent to
   `e[v/x]`, notes that the body is checked with the definitional equality
   `x ≡ v` available, and that "we don't have any congruence rules for let.  We
   simply unfold it whenever we need to" (section 2.4, page 8);[^22] the manual
   lists ζ among the reductions of definitional equality.[^14]  `.olean` terms
   are pointer-shared, and `let` is the one explicit device for sharing in a
   term; the survey records lean2dk's output two to three orders of magnitude
   larger than its input because a text format loses that sharing.  The corpus
   seed entry's kernel term has two projections, each the first field of a
   `PProd` in the course-of-values recursion `List.brecOn` compiles
   `reverseAux` into, and no `let` ([corpus-seed-notes]).
+  **Agda's status**.  Record projections are ordinary functions that compute
   on constructors (`proj₁ p ≡ 1` by `refl`, probe `P15ProjLet`) and interact
   with record η (the `structure-eta` entry).  `let` is sugar: it "substitutes
   away let-bindings", bindings are not recursive and "cannot be used to
   introduce sharing"; a record pattern is allowed on the left ([agda-let]);
   `(let x = 1 in x + x) ≡ 2` and `(let (a , b) = p in a + b) ≡ 3` hold by
   `refl` (probe `P15ProjLet`).  By profile, as follows.
   +  U: as K.
   +  K: projections become applications of the record's projection functions;
      `let` becomes Agda's `let` or, where sharing matters for checking time,
      an auxiliary definition.
   +  CC: as K (probe `P15ProjLet` runs under it).
   +  CU: as K.
+  **Translation strategy**.  The expression printer handles `Expr.proj` and
   `let` ([#17]), with a sharing pass that introduces a new constant for every
   closed subterm that occurs more than once, since Agda's `let` gives the
   checker no sharing; term size control measures the result ([#44]).  The
   corpus lists five entries under this feature.
+  **Predecessors**.  lyphyser deduplicates repeated closed subexpressions into
   new constants and annotates projections with their universe levels through
   `mdata` nodes ([related-work], lyphyser/lean2agda); lean2dk measured the
   cost of printing shared terms as text (lean2dk); hol2dk simplifies proofs
   before output (hol2dk).
+  **References**.  [carneiro-thesis] section 2.4; [vaishnav-thesis] section
   1.2.1; [kernel-type-checker] lines 450 and 1123; [lean-manual-type-system];
   [agda-let], [agda-records]; [corpus-seed-notes]; probe `P15ProjLet`.

## The probes

Every Agda claim above was settled by a file under `probes/agda/`, run with the
shell's `agda` from any directory
(`agda docs/foundations/probes/agda/P06KRejected.agda`); every Lean claim by a
file under `probes/lean/`, run from `translator/` as
`lake env lean ../docs/foundations/probes/lean/DefEq.lean` (the two scans
import all of Mathlib and need its cache, about 7 GB of memory and two and a
half minutes).  The outcomes, first measured on 2026-10-07, are as follows; a
rejected probe's first error line is the evidence quoted in the entries, and an
accepted one checked with no output beyond Agda's `Checking` line.

| Probe | Flags | Shows | Outcome |
| --- | --- | --- | --- |
| `P01PropElim` | `--safe --prop` | a `Prop` data type eliminated into `Set` | rejected, `[SplitInProp]` |
| `P01bPropAbsurd` | `--safe --prop` | absurd pattern, `Prop` motive, definitional irrelevance | accepted |
| `P02PropEqElim` | `--safe --prop` | `subst` on a `Prop`-valued equality | rejected, `[SplitInProp]` |
| `P02bAccProp` | `--safe --prop` | well-founded recursion on a `Prop`-valued `Acc` | rejected, `[SplitInProp]` |
| `P03SafePostulate` | `--safe` | a postulate | rejected, `[SafeFlagPostulate]` |
| `P04SafeTypeInType` | `--safe --type-in-type` | the flag combination | rejected, `[SafeFlagPragma]` |
| `P04bSafeTerminating` | `--safe` | the `TERMINATING` pragma | rejected, `[SafeFlagTerminating]` |
| `P05KAccepted` | `--safe` | K and UIP by pattern matching | accepted |
| `P06KRejected` | `--safe --cubical-compatible` | the same UIP | rejected, `[SplitError.UnificationStuck]` |
| `P07HedbergNat` | `--safe --cubical-compatible` | UIP for `ℕ` from agda-stdlib | accepted, 1.7 s |
| `P08Impredicativity` | `--safe --prop` | `(A : Set) → Squash A : Prop` | rejected, `Prop₁ != Prop` |
| `P08bPredicativeLevels` | `--safe --prop` | the same at `Prop₁`; level laws by conversion | accepted |
| `P09Setω` | `--safe` | `(ℓ : Level) → Set ℓ → Set ℓ : Set₁` | rejected, `Setω != Set₁` |
| `P10RecordEta` | `--safe --cubical-compatible` | η for `_×_` and `⊤` | accepted |
| `P10bDataNoEta` | `--safe --cubical-compatible` | η for a one-constructor `data` | rejected, `w != wrap (unwrap w)` |
| `P10cRecursiveRecord` | `--safe --cubical-compatible` | η for a recursive record | accepted |
| `P11Literals` | `--safe --cubical-compatible` | literal arithmetic, `gcd`, strings by `refl` | accepted, 3.6 s |
| `P12SafeNonTerminating` | `--safe` | the `NON_TERMINATING` pragma | rejected, `[SafeFlagNonTerminating]` |
| `P13DecStuck` | `--safe --cubical-compatible` | a decision on a parameter `lem` | rejected, stuck term |
| `P14NestedMutual` | `--safe --cubical-compatible` | nested, mutual, induction-recursion | accepted |
| `P15ProjLet` | `--safe --cubical-compatible` | projections and `let` by `refl` | accepted |
| `P16CubicalQuotient` | `--safe --cubical --guardedness` | set quotients, `funExt`, `hPropExt` | accepted |
| `P17CubicalK` | `--safe --cubical --guardedness` | UIP by pattern matching | rejected, `[SplitError.UnificationStuck]` |
| `P18PropCubical` | `--safe --cubical --guardedness --prop` | `Prop` irrelevance under `--cubical` | accepted |
| `P19ChoiceParam` | `--safe --cubical --guardedness` | `Classical.choice` as a parameter | accepted |
| `P20Irrelevance` | `--safe --cubical-compatible` | an irrelevant argument | accepted |
| `P22HEq` | `--safe --cubical-compatible` | importing a `--with-K` module | rejected, `[CoInfectiveImport]` |
| `P24QuotParam` | `--safe --cubical-compatible` | the quotient record; `lift-β` by `refl` | rejected, `lift f h (mk R a) != f a` |
| `P25PropCC` | `--safe --cubical-compatible --prop` | absurd pattern, squash eliminator, irrelevance | accepted |
| `P25bPropEqCC` | `--safe --cubical-compatible --prop` | a `Prop` motive on a `Prop` equality | rejected, `[CannotGenerateTransportClause]` |
| `P25cPropEqCubical` | `--safe --cubical --guardedness --prop` | the same | rejected, `[CannotGenerateTransportClause]` |
| `P26AccPropU` | `--type-in-type --prop` | `P02bAccProp` under profile U's flags | rejected, `[SplitInProp]` |
| `P27CubicalInductives` | `--safe --cubical --guardedness` | nested, mutual, induction-recursion | accepted |
| `P28CubicalLiterals` | `--safe --cubical --guardedness` | builtin naturals and strings | accepted |

The Lean files are `DefEq.lean` (the definitional equalities, the recursor
flags, `Classical.propDecidable`, `Nat.gcd`), `Hatches.lean` (`sorryAx`, the
native-reduction family and its deprecation, `lcProof`, a `native_decide`
theorem, a `partial` and an `unsafe` definition), `Strings.lean` (`String` and
`Char` at the pin, `Lists'.Subset` and `Lists.Equiv`, `Nat.gcd_succ`),
`Gcd.lean` (`WellFounded.Nat.fix`, the failed `rfl` tests, `String.mk`),
`Recursors.lean` (`WellFounded.Nat.fix.go`, large elimination of `Iff`,
`Nonempty`, `Exists` and `Acc`, UIP on types, `HEq`), and `Scan.lean` and
`ScanByRoot.lean` (the table of the section "What exists at the pin").  Each
file carries, in a comment at its end, the output it produced on 2026-10-08
when run by that command from its committed path, the scan's 1,765-name list of
Mathlib's large-eliminating propositions excepted.

## References

+  `[carneiro-thesis]`: M. Carneiro, "The Type Theory of Lean", MSc thesis,
   2019; `main.pdf` of release v1.0, 46 pages, printed page numbers:
   [github.com/digama0/lean-type-theory/releases/tag/v1.0][carneiro-thesis].
+  `[abel-coquand]`: A. Abel and T. Coquand, "Failure of Normalization in
   Impredicative Type Theory with Proof-Irrelevant Propositional Equality",
   LMCS 16(2), 2020, article 14; arXiv 1911.08174 is the version read:
   [arxiv.org/abs/1911.08174][abel-coquand].
+  `[vaishnav-thesis]`: R. Vaishnav, "Translating Proofs from Lean to Dedukti",
   PhD thesis, Université Paris-Saclay, 2026; the PDF on the author's site,
   cited by its printed page numbers:
   [rish987.github.io/files/thesis.pdf][vaishnav-thesis].
+  `[hott-book]`: The Univalent Foundations Program, "Homotopy Type Theory:
   Univalent Foundations of Mathematics", 2013; the online PDF, version
   first-edition-82-g578b85c: [hott.github.io/book/hott-online.pdf][hott-book].
+  `[kernel-type-checker]`, `[kernel-inductive]`, `[kernel-quot]`: Lean 4's
   kernel at tag `v4.33.1`, `src/kernel/type_checker.cpp`, `inductive.cpp` and
   `quot.cpp`, cited by line.
+  `[lean-gcd-source]`: `src/Init/Data/Nat/Gcd.lean` at tag `v4.33.1`.
+  `[lean-manual]`: The Lean Language Reference, version 4.33.1, read
   2026-10-07; the pages cited are [lean-manual-type-system],
   [lean-manual-propositions], [lean-manual-universes],
   [lean-manual-inductive], [lean-manual-quotients], [lean-manual-nat],
   [lean-manual-strings], [lean-manual-modifiers], [lean-manual-recursion],
   [lean-manual-axioms], [lean-manual-tactics] and [lean-manual-classes].
+  `[agda-*]`: the Agda documentation for version 2.8.0, read 2026-10-07:
   [agda-prop], [agda-safe], [agda-cubical-compatible], [agda-without-k],
   [agda-options], [agda-records], [agda-builtins], [agda-levels], [agda-let],
   [agda-data], [agda-mutual], [agda-irrelevance], [agda-sorts],
   [agda-postulates].
+  `[stdlib-gcd]`: agda-stdlib 2.3, `src/Data/Nat/GCD.agda`, as installed by
   the flake.
+  `[cubical-setquot]`, `[cubical-prelude]`, `[cubical-univalence]`: the
   cubical library 0.9, `Cubical/HITs/SetQuotients/Base.agda` and
   `Properties.agda`, `Cubical/Foundations/Prelude.agda`,
   `Cubical/Foundations/Univalence.agda`, as installed by the flake.
+  `[related-work]`, `[roadmap]`, `[readme]`, `[pinning]`, `[corpus-schema]`,
   `[corpus-readme]`, `[corpus-seed-notes]`: this repository's documents.

[#5]: https://github.com/formalverification/lean2agda/issues/5
[#7]: https://github.com/formalverification/lean2agda/issues/7
[#10]: https://github.com/formalverification/lean2agda/issues/10
[#11]: https://github.com/formalverification/lean2agda/issues/11
[#12]: https://github.com/formalverification/lean2agda/issues/12
[#17]: https://github.com/formalverification/lean2agda/issues/17
[#18]: https://github.com/formalverification/lean2agda/issues/18
[#19]: https://github.com/formalverification/lean2agda/issues/19
[#20]: https://github.com/formalverification/lean2agda/issues/20
[#21]: https://github.com/formalverification/lean2agda/issues/21
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
[#44]: https://github.com/formalverification/lean2agda/issues/44
[#51]: https://github.com/formalverification/lean2agda/issues/51
[#52]: https://github.com/formalverification/lean2agda/issues/52
[#53]: https://github.com/formalverification/lean2agda/issues/53
[#55]: https://github.com/formalverification/lean2agda/issues/55
[#57]: https://github.com/formalverification/lean2agda/issues/57
[#58]: https://github.com/formalverification/lean2agda/issues/58

[carneiro-thesis]: https://github.com/digama0/lean-type-theory/releases/tag/v1.0
[abel-coquand]: https://arxiv.org/abs/1911.08174
[vaishnav-thesis]: https://rish987.github.io/files/thesis.pdf
[hott-book]: https://hott.github.io/book/hott-online.pdf
[kernel-type-checker]: https://github.com/leanprover/lean4/blob/v4.33.1/src/kernel/type_checker.cpp
[kernel-inductive]: https://github.com/leanprover/lean4/blob/v4.33.1/src/kernel/inductive.cpp
[kernel-quot]: https://github.com/leanprover/lean4/blob/v4.33.1/src/kernel/quot.cpp
[lean-gcd-source]: https://github.com/leanprover/lean4/blob/v4.33.1/src/Init/Data/Nat/Gcd.lean
[lean-manual]: https://lean-lang.org/doc/reference/4.33.1/
[lean-manual-type-system]: https://lean-lang.org/doc/reference/4.33.1/The-Type-System/
[lean-manual-propositions]: https://lean-lang.org/doc/reference/4.33.1/The-Type-System/Propositions/
[lean-manual-universes]: https://lean-lang.org/doc/reference/4.33.1/The-Type-System/Universes/
[lean-manual-inductive]: https://lean-lang.org/doc/reference/4.33.1/The-Type-System/Inductive-Types/
[lean-manual-quotients]: https://lean-lang.org/doc/reference/4.33.1/The-Type-System/Quotients/
[lean-manual-nat]: https://lean-lang.org/doc/reference/4.33.1/Basic-Types/Natural-Numbers/
[lean-manual-strings]: https://lean-lang.org/doc/reference/4.33.1/Basic-Types/Strings/
[lean-manual-modifiers]: https://lean-lang.org/doc/reference/4.33.1/Definitions/Modifiers/
[lean-manual-recursion]: https://lean-lang.org/doc/reference/4.33.1/Definitions/Recursive-Definitions/
[lean-manual-axioms]: https://lean-lang.org/doc/reference/4.33.1/Axioms/
[lean-manual-tactics]: https://lean-lang.org/doc/reference/4.33.1/Tactic-Proofs/Tactic-Reference/
[lean-manual-classes]: https://lean-lang.org/doc/reference/4.33.1/Type-Classes/
[agda-prop]: https://agda.readthedocs.io/en/v2.8.0/language/prop.html
[agda-safe]: https://agda.readthedocs.io/en/v2.8.0/language/safe-agda.html
[agda-cubical-compatible]: https://agda.readthedocs.io/en/v2.8.0/language/cubical-compatible.html
[agda-without-k]: https://agda.readthedocs.io/en/v2.8.0/language/without-k.html
[agda-options]: https://agda.readthedocs.io/en/v2.8.0/tools/command-line-options.html
[agda-records]: https://agda.readthedocs.io/en/v2.8.0/language/record-types.html
[agda-builtins]: https://agda.readthedocs.io/en/v2.8.0/language/built-ins.html
[agda-levels]: https://agda.readthedocs.io/en/v2.8.0/language/universe-levels.html
[agda-let]: https://agda.readthedocs.io/en/v2.8.0/language/let-and-where.html
[agda-data]: https://agda.readthedocs.io/en/v2.8.0/language/data-types.html
[agda-mutual]: https://agda.readthedocs.io/en/v2.8.0/language/mutual-recursion.html
[agda-irrelevance]: https://agda.readthedocs.io/en/v2.8.0/language/irrelevance.html
[agda-sorts]: https://agda.readthedocs.io/en/v2.8.0/language/sort-system.html
[agda-postulates]: https://agda.readthedocs.io/en/v2.8.0/language/postulates.html
[stdlib-gcd]: https://github.com/agda/agda-stdlib/blob/v2.3/src/Data/Nat/GCD.agda
[cubical-setquot]: https://github.com/agda/cubical/blob/v0.9/Cubical/HITs/SetQuotients/Properties.agda
[cubical-prelude]: https://github.com/agda/cubical/blob/v0.9/Cubical/Foundations/Prelude.agda
[cubical-univalence]: https://github.com/agda/cubical/blob/v0.9/Cubical/Foundations/Univalence.agda
[related-work]: ../related-work.md
[roadmap]: ../GITHUB_PROJECT.md
[readme]: ../../README.md
[pinning]: ../pinning.md
[corpus-schema]: ../../corpus/SCHEMA.md
[corpus-readme]: ../../corpus/README.md
[corpus-seed-notes]: ../../corpus/list-reverse-reverse/notes.md

[^1]: [carneiro-thesis], section 2.1, page 6: the grammar of levels (`u`, `0`,
    `S`, `max`, `imax`), the typing rule whose conclusion puts `∀x : α. β` in
    the universe `imax(ℓ₁, ℓ₂)`, and on page 7 the semantics "imax(m, n + 1) =
    max(m, n + 1) and imax(m, 0) = 0".
[^2]: [lean-manual-propositions], the list under "Propositions have the
    following properties" (the items "Definitional proof irrelevance",
    "Impredicativity", "Restricted Elimination", "Extensionality");
    [lean-manual-universes], section 4.3.1 "Predicativity" and the paragraph on
    `imax` under the `Level` datatype.
[^3]: [abel-coquand], abstract and introduction, and the paragraphs on Lean on
    pages 14:2 to 14:4, which say the definitions "can be directly replayed in
    Lean 3.4.2 with the standard prelude, yielding a non-normalizing term Omega"
    and that "term Omega is closed with respect the standard axioms of Lean"
    (sic).
[^4]: [carneiro-thesis], section 2.2, the last rule of the definitional-equality
    figure on page 6 and the sentence "The last rule is called proof
    irrelevance, which states that any two proofs of a proposition (a type in P
    := U₀) are equal" on page 7.
[^5]: [vaishnav-thesis], section 1.2.2, page 18, the rule [PI] and the theorems
    `propEqTrue` and `prfIrrel`; the repository change is footnoted in
    [related-work], Lean4Less.
[^6]: [carneiro-thesis], section 2.6.4, page 12, the paragraph beginning "This
    rule suffices for the theoretical presentation, but there is a second
    reduction rule called 'K-like reduction'", ending with the displayed
    instance for the equality recursor (`rec_= C x a h ≡ x` in this catalog's
    notation).
[^7]: [vaishnav-thesis], section 1.2.3, pages 22 to 23, the subsection "K-Like
    Reduction" and the rule [KLR].
[^8]: [carneiro-thesis], section 2.6.2, pages 10 to 11, the two numbered reasons
    and the sentence "This is called subsingleton (SS) elimination".
[^9]: [lean-manual-inductive], section 4.4.3.1.1.1 "Subsingleton Elimination",
    the sentence "Propositions that fulfill both of the following requirements
    are considered to be subsingletons" and its two items.
[^10]: [carneiro-thesis], section 2.7.1, page 13, the displayed constants and
    the paragraph beginning "Because the last rule is a computational rule".
[^11]: [lean-manual-quotients], the closing paragraph beginning "Like functions
    and universes, quotient types are a built-in feature of Lean's type system".
[^12]: [carneiro-thesis], section 2.7.3, page 13: "The axiom of choice in Lean
    is expressed as a global choice function" and "From the axiom of choice, the
    law of excluded middle is derived (it is not stated as a separate axiom)".
[^13]: [vaishnav-thesis], section 1.2.2, the subsection "Struct-η" on pages 19
    to 20 with the rules [ETA-S'] and [ETA-S], and the subsection "Unit-η" on
    page 21 with the rule [UNIT].
[^14]: [lean-manual-type-system], the paragraph "Definitional equality includes
    the following forms of reduction" (β, δ, ι, ζ, quotient reduction) and the
    one beginning "Definitional equality includes η-equivalence of functions and
    single-constructor inductive types".
[^15]: [lean-manual-nat], the paragraph beginning "In the kernel, there are
    special Nat literal values".
[^16]: [lean-manual-strings], the opening list ("They have a logical model that
    specifies their behavior in terms of ByteArrays that contain UTF-8 scalar
    values") and the structure `String.ofByteArray` with fields `toByteArray`
    and `isValidUTF8`.
[^17]: [vaishnav-thesis], section 7.1.3, page 163, the paragraph "GCD as a
    Primitive Operation"; the README's claim is quoted in [related-work],
    Lean4Less, with its footnote.
[^18]: [lean-manual-axioms], the paragraphs "Creating and Tracking Proofs That
    Trust the Compiler" and "Axioms and the native_decide Tactic";
    [lean-manual-tactics], the entry for `native_decide`.
[^19]: [lean-manual-modifiers], the paragraphs beginning "Functions marked
    noncomputable are not compiled and cannot be executed" and "The unsafe
    marker exempts a definition from kernel checking".
[^20]: [lean-manual-recursion], the item "Partial functions with nonempty
    codomains": "Functions marked partial are treated as opaque constants by the
    kernel and are neither unfolded nor reduced."
[^21]: [lean-manual-inductive], section 4.4.5.4 "Nested Inductive Types".
[^22]: [carneiro-thesis], section 2.4, page 8, the paragraph beginning "The
    first and simplest extension to this language is to add support for a let
    binder" and the sentence "Note that we don't have any congruence rules for
    let."
