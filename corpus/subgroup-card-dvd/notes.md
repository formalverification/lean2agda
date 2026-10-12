<!-- File: corpus/subgroup-card-dvd/notes.md -->

# Subgroup.card_subgroup_dvd_card

The entry for Lagrange's theorem, translated by issue M1-9 ([#9]).
Mathlib declares `Subgroup.card_subgroup_dvd_card` in
`Mathlib.GroupTheory.Coset.Card`: the cardinality of a subgroup divides
that of the group, where cardinality is `Nat.card`, the number of
elements of a finite type and 0 for an infinite one.  Two Agda files
translate it, both under profile CC (`--safe --cubical-compatible`):
`agda/SubgroupCardDvd.agda` states and proves Lean's theorem with Lean's
proof, taking the classical principles the proof uses and `Nat.card` as
module parameters; `agda/SubgroupCardDvdFinite.agda` proves the theorem
for finite groups, with no parameters.

## Statement

Lean's statement, as `#check` prints it:

    @Subgroup.card_subgroup_dvd_card : ∀ {α : Type u_1} [inst : Group α] (s : Subgroup α), Nat.card ↥s ∣ Nat.card α

The Agda statement of `SubgroupCardDvd.agda`, inside the module
`Lagrange`, which takes the parameter records:

    card-subgroup-dvd-card : {a p : Level} {A : Set a} ⦃ G : Group A ⦄ (H : Subgroup p) → card ⟨ H ⟩ ∣ card A

It matches Lean's up to notation and up to the following:

+  `Nat.card` is the field `card` of the parameter record `Card`;
+  Lean's class `Group` is the record `Group A`, taken as an instance
   argument, and `Subgroup` is a record whose carrier is a subset of `A`
   in the reading of the entry `set-ext` (`ℙ A p = A → Ω p`, with `Ω p`
   the propositions of `Set p`);
+  `↥s`, the subtype of the elements of `s`, is `⟨ H ⟩ = Σ A (_∈ carrier H)`;
+  Lean's `∣` on `ℕ` (`a ∣ b ↔ ∃ c, b = a * c`) is agda-stdlib's `_∣_`,
   the record of a quotient `q` and a proof that `n ≡ q * m`.

The statement of `SubgroupCardDvdFinite.agda` is another statement:

    card-subgroup-dvd-card-fin : m ∣ n

in a module that takes `⦃ G : Group A ⦄`, `H : Subgroup p`,
`eA : A ↔ Fin n` and `eH : ⟨ H ⟩ ↔ Fin m`.  Enumerations replace
`Nat.card`, so the statement speaks of finite groups only.  For a finite
group it is Lean's: `SubgroupCardDvd.agda` derives it from the
classical theorem through the field `card-fin`
(`card-subgroup-dvd-card-fin` there).  For an infinite group Lean's
statement holds trivially, since `Nat.card α = 0` and every number
divides 0; so the finite statement carries all of the theorem's content.

## Tier

`#print axioms` prints `[propext, Classical.choice, Quot.sound]`, so the
entry is T2.  `Classical.choice` comes from two places, along shortest
paths in the dependency graph (from the probe of
[`../real-sqrt-nonneg/notes.md`][sqrt-notes], Remarks), as follows:

+  **the statement**: `Nat.card α` is `Cardinal.toNat (Cardinal.mk α)`,
   and the path runs through `Cardinal.toENat`, `Cardinal.toENatAux` and
   `Function.extend`, which decides with `Classical.propDecidable`
   whether a cardinal is the cast of a natural number, that is, whether
   it is finite.  The rest of Mathlib's cardinal
   arithmetic is classical too: `Cardinal.linearOrder` takes its
   `Decidable` instances from `Classical.decRel`, and the order rests on
   Schröder and Bernstein's theorem and on well-orders.
+  **the proof**: `card_eq_card_quotient_mul_card_subgroup` applies
   `Nat.card_congr` to `Subgroup.groupEquivQuotientProdSubgroup`, an
   equivalence `α ≃ (α ⧸ s) × s`, which picks a representative of each
   coset with `Quotient.out`, that is, `Quot.out`, `Classical.choose`,
   `Classical.indefiniteDescription` and `Classical.choice`.

Both reach it through data, not only through proofs: a walk of the
dependency graph that never enters a constant whose type is a
proposition still reaches `Classical.choice` from `Nat.card`, by
`Function.extend`'s decision, and `Quotient.out` is data by definition.
`propext` and `Quot.sound` come with the quotients, `α ⧸ s` and the type
of cardinals (a quotient of types by equivalence), and with `funext`.
The export's axiom declarations are the same three (Lean issue
[lean4#15226] does not affect the set).

**De-classicalization**.  The statement does not survive as written:
`Nat.card` has no constructive counterpart.  The file proves why
(`card-wlem`): any function `card` with `card-congr` and `card-fin`
decides, for each proposition `P`, between `¬ P` and `¬ ¬ P`, by
comparing `card (P ⊎ ⊤)` with 2, and that weak excluded middle is not
provable in Agda without postulates.  Abstracting `Nat.card` into a
parameter therefore abstracts a classical principle.  The statement for
finite groups survives, and has a constructive proof, as it does on
paper: `SubgroupCardDvdFinite.agda` proves it with no parameter.  What
the proof costs here is the following:

+  decidable equality on the group, from its enumeration, and with it
   uniqueness of identity proofs for the carrier (Hedberg's theorem, as
   agda-stdlib's `Decidable⇒UIP`), which Lean has for every type;
+  decidable membership in the subgroup, by searching its enumeration;
+  a representative for each coset, the first element of the
   enumeration that lies in it, which replaces `Quotient.out`; the
   search and its lemmas take 50 lines of code;
+  the count of the representatives, a decidable subset of `Fin n`;
   agda-stdlib has no lemma counting a decidable subset of `Fin n`, so
   the file proves one (`count`, 48 lines of code);
+  agda-stdlib's `*↔×` and `↔⇒≡` (`Fin` is injective) for the
   arithmetic.

In all, 279 lines of code against 288 for the classical file, which
spends most of its own on the parameters and on what they need (UIP for
`Ω`, the exactness of quotients).  The constructive proof computes: the
file's last section takes the Klein four-group with a subgroup of order
2, and the quotient of the divisibility the theorem returns, the number
of cosets, reduces to 2, which `refl` checks (a control claiming 1
fails with `2 != 1`).  Lean's `Nat.card` is `noncomputable`, so Lean's
proof computes nothing.

## What the kernel term needed

The export holds 6,248 declarations: 306 inductive types, the 4 quotient
primitives, 2,255 definitions, 3,678 theorems, 2 opaque constants
(`String.Internal.append`, `Lean.opaqueId`) and the 3 axioms.  By module
(counting constructors and recursors): 3,750 constants from Lean's core
library, 922 from `Mathlib.Order`, 867 from `Mathlib.Algebra`, 588 from
`Mathlib.Data`, 286 from `Mathlib.Logic`, 196 from `Mathlib.SetTheory`,
44 from `Mathlib.GroupTheory`, and 31 elsewhere.  Cardinals, which the
statement reaches through `Nat.card`, account for much of it; the group
theory is 44 constants.

Re-checked in Lean's kernel with its diagnostics on, the check of
`card_subgroup_dvd_card` itself unfolds only the instances of `ℕ` that
connect the statement's `∣` and `*` with `dvd_mul_left`'s
(`Nat.instDvd`, `semigroupDvd`, `Nat.instCommSemigroup`, `instMulNat`,
...), and reduces no recursor and no quotient.  The 5,933 theorems and
definitions of the closure re-checked in 3.5 seconds, and the kernel
rejected none.  By feature, each named by its entry in the gap catalog
([catalog]), the closure uses the following:

+  [`quotients`][cat-quotients]: `α ⧸ s` is `Quotient (leftRel s)`, and
   cardinals are a quotient of types.  The kernel reduces `Quot.lift` 429
   times, in 102 declarations, nearly all of them in the arithmetic and
   order of cardinals (the proofs of `Cardinal.commSemiring`, the lemmas
   of `Cardinal.lift`), and in `funext`.  The classical file takes
   `α ⧸ s` from the `Quotients` record of the entry `multiset-map-map`,
   whose computation rule `lift-β` is a propositional equation; the
   finite file has no quotient.
+  [`axioms`][cat-axioms]: the three, as under Tier.
+  [`decidable-and-noncomputable`][cat-decidable-and-noncomputable]: the
   case split of `Nat.card`, `Cardinal.linearOrder`, `Fintype.equivFin`
   (`Classical.decEq`); 86 constants are `noncomputable`, among them
   `Quot.out` and `Function.invFun`, and 64 cite a classical `Decidable`
   instance.  The finite file's decisions are real: equality of `Fin n`
   and agda-stdlib's `any?`.
+  [`universe-levels`][cat-universe-levels]: the statement has one
   universe parameter, `u_1`; the closure has 4,520 universe-polymorphic
   constants (`Cardinal.lift` among them).  The next section gives the
   Agda levels.
+  [`impredicative-prop`][cat-impredicative-prop]: Lean's `Set α`, the
   type of a subgroup's carrier, is `α → Prop` in the universe of `α`,
   while Agda's `ℙ A p` lives one universe above `p`; the mechanical
   count finds 83 uses of a constant at universe arguments that make an
   `imax` in its type zero.
+  [`k-and-uip`][cat-k-and-uip]: the kernel reduces `Eq.rec` 28 times in
   17 declarations.  The count includes ordinary reductions on
   `Eq.refl`; one of the 17 is `eq_of_heq` (K-like reduction on a
   universe, LF-5 of [`lean-findings.md`][lean-findings]), and the
   others (the proofs of `Equiv.piUnique`, `PSigma.eta`, lemmas about
   `Multiset.pmap` and `Multiset.attach`, equation lemmas of
   `Lean.Grind`'s matchers) are for Lean4Less (M3-1, [#26]) to classify.
   Neither Agda file uses K.
+  [`large-elimination`][cat-large-elimination]: 19 uses of a recursor
   of a proposition at a motive of any universe (`Eq.rec` in `cast` and
   `Eq.mpr`, `HEq.rec`, `False.rec`).  One `Eq.mpr` is in the data of
   `groupEquivQuotientProdSubgroup`: Mathlib identifies each fiber of the
   quotient map with a coset by `rw` and `simp` inside the definition of
   an equivalence, so its term casts an `Equiv.refl` along an equation
   between types.  The Agda proof uses the exactness of the quotient
   instead, and casts no type.
+  [`structure-eta`][cat-structure-eta]: 19 of the closure's 5,933
   theorems and definitions need it by the elaborator's test (the method
   of [`../real-sqrt-nonneg/notes.md`][sqrt-notes], Remarks), among them
   the proofs of `Equiv.sigmaEquivProd` and two of
   `Equiv.sigmaCongrRight`, both of which
   `groupEquivQuotientProdSubgroup` composes, the proofs of
   `Equiv.prodComm`, `ULift.up_down`, `MulOpposite.op_unop`, and the two
   `Nat.Internal.Linear` lemmas that `finset-card-image` found.  Another
   31 are rejected with eta on as well and cannot be judged.  Agda's `Σ`
   and `_×_` are records with eta, so neither Agda file needs anything
   for it.
+  [`literals`][cat-literals]: 2,668 `Nat` literals and 354 `String`
   literals in 1,379 constants.
+  [`nested-and-mutual-inductives`][cat-nested-and-mutual-inductives]:
   `Lean.Syntax`, along the path `Nat.card`, `Cardinal.commSemiring`,
   `Semiring.mk`, `autoParam`: a field of `Semiring` with a default
   tactic stores the tactic's syntax tree in the constructor's type, as
   in the other two entries of this part, and a tactic default of a
   function's argument stores it in a constant `_auto_<n>`
   (`Std.IsLinearOrder.of_le._auto_1` is on another path).  Cutting both
   forms removes `Lean.Syntax` and leaves 6,618 of the 6,684 constants,
   `eq_of_heq`, `Quot.lift` and `funext` among them.
+  [`projections-and-let`][cat-projections-and-let]: 927 projections in
   748 constants and 594 `let` expressions in 274; the statement reaches
   the carrier through `SetLike.instMembership`.

The closure has no `partial` and no `unsafe` constant, and five with
`implemented_by`.  Definitional proof irrelevance is not counted by the
kernel's diagnostics ([#26] will settle it).  Of the features the
manifest listed, `quotients`, `decidable-and-noncomputable`,
`universe-levels` and `axioms`, the term uses all four; the other seven
are added under the schema's closure rule.

### Levels

Lean's group lives in `Type u_1`, its subgroups in `Type u_1`, and
`α ⧸ s` in `Type u_1`, since a quotient stays in the universe of its
type.  In Agda the carrier lives in `Set a` and a subgroup's membership
in `Set p`, so `Subgroup p : Set (a ⊔ suc p)`, `⟨ H ⟩ : Set (a ⊔ p)`, and
`A⧸H : Set (a ⊔ p)`, which is `Set a` when `p ≤ a`.  The `Card` record
lives in `Setω`, with `card` at every level and `card-congr` between
two, as Lean's `Nat.card_congr` relates `Type u` and `Type v`.  The
finite file's transversal lives in `Set a`, with the carrier.

## Instance arguments

The statement carries 7 instance arguments.  It binds one instance,
`[inst : Group α]`, which it passes to `Subgroup` and to the
`SetLike` instance of subgroups; the others are `Nat.instDvd` for `∣`,
and `SetLike.instMembership` with `Subgroup.instSetLike` for the
coercion `↥s`.  The proof carries 62: the statement's again, in the
types of `of_eq_true` and `Eq.trans`, `instHMul` and `instMulNat` for
`*`, `QuotientGroup.instHasQuotientSubgroup` for `⧸`, and the chain from
`Nat.instCommSemigroup` that `dvd_mul_left` needs (`semigroupDvd`,
`CommSemigroup.toSemigroup`, `CommMagma.toMul`, ...), which the proof
names explicitly as `@dvd_mul_left ℕ`.  The closure carries 451,949.
The count is of arguments at instance-implicit positions of applications
with a constant head.

In Agda, `[Group α]` is an instance argument, `⦃ G : Group A ⦄`, in both
files: `Subgroup` takes it from its module, and the Klein example
declares an `instance` that Agda's search supplies to the theorem.  The
`SetLike` and `Membership` instances become the projection `carrier` and
`_∈_` on `ℙ`; `HasQuotient` becomes the definition `A⧸H`; and the
instances on `ℕ` become agda-stdlib's `_*_` and `_∣_`, which take none.
The classical principles are module parameters, never instances.

## The Agda version

**`agda/SubgroupCardDvd.agda`**, profile CC, in five parts, as follows:

+  `Ω`, `ℙ` and `_∈_` as in the entry `set-ext`; the record `Group`, with
   Lean's operations and laws (`mul_assoc`, `one_mul`, `mul_one`,
   `inv_mul_cancel`) and without the data fields `npow`, `zpow` and
   `div` that Lean's structure carries with default values; five
   consequences of the laws; the record `Subgroup`, Lean's `Subgroup`,
   `Submonoid` and `Subsemigroup` flattened; `⟨_⟩` and `⟨⟩-≡`, equality
   in the subtype by the irrelevance that `Ω` carries; and `leftRel`, the
   relation `x⁻¹ * y ∈ H`, with its laws.
+  Six parameter records, each standing for a Lean primitive, axiom or
   definition: `PropExt` and `FunExt` as in `set-ext` (`propext`, and
   `funext`, which Lean proves from `Quot.sound`); `Quotients` as in
   `multiset-map-map` (`Quot` and `Quot.sound`); `Truncation`, Lean's
   inductive proposition `Nonempty`, which also serves `∃`; `Choice T`,
   Lean's `Classical.choice : Nonempty α → α`; and `Card`, `Nat.card`.
+  What `PropExt` and `FunExt` give: `Ω-is-set`, uniqueness of identity
   proofs for `Ω`, by Hedberg's argument as agda-stdlib packages it
   (`Constant⇒UIP`), and `exact`, Lean's `Quotient.exact`, proved as Lean
   proves it, by lifting the proposition `R x _` to the quotient.  The
   entry `multiset-map-map` left the first open ("`UIP (Ω p)` should
   follow from `PropExt` and `FunExt` by Hedberg's argument, which this
   entry neither needs nor proves"); this entry needs it, for the lift
   into `Ω`, and proves it, as `finset-card-image` does (`Ω-uip`, in part
   1 of [#9], [#75]), the two written in parallel.
+  The module `Lagrange`: `Quot.exists_rep` by `ind` (its motive is a
   proposition because the truncation is one), `Quot.out` and its
   specification from `choice`, the quotient `A⧸H`, the equivalence
   `A ↔ (A⧸H × ⟨ H ⟩)`, the cardinality equation and the theorem, Lean's
   proof step for step; then the finite statement, by `card-fin`.
+  `card-wlem`, the weak excluded middle that `Card` implies.

Three decisions shape it, as follows:

+  **`Nat.card` as a parameter, and the finite statement as well**.  The
   kickoff offered a choice between an abstract cardinality and a
   statement for finite groups; the entry takes both, since the first
   is the translation of Lean's statement and the second the
   de-classicalized one, and the classical file derives the second from
   the first.  `Card` holds the two laws the proof uses
   (`Nat.card_congr`, `Nat.card_prod`) and `card-fin`, Mathlib's
   `Nat.card_eq_fintype_card` at `Fin n`, which the proof does not use:
   without it the constant function 0 satisfies the record and the
   theorem says nothing.  With it the record implies weak excluded
   middle.  It leaves out the infinite case.
+  **Lean's quotient and `Quotient.out`, not a transversal**.  Lean's
   equivalence goes through `α ⧸ s` and a representative of each coset,
   so the classical file does too, with the corpus's `Quotients` record
   and `out` from `Choice`.  Lean identifies each fiber with a coset by
   an equation of sets (`propext`, `funext`); the Agda proof uses
   exactness, whose lift into `Ω` needs `Ω-is-set`, hence `FunExt`.  The
   principles match Lean's, though the steps differ.
+  **A truncation for `Nonempty`**.  `Classical.choice` takes a
   `Nonempty α`, a proposition.  Read in `Set` without truncation,
   `Nonempty A` would be `A` itself and `choice` trivial, while
   `∃ x, mk x ≡ q` would not be a proposition, so `ind` could not prove
   it.  The `Truncation` record is not classical (the cubical library
   proves it); profile CC lacks it only because it has no higher
   inductive types.  `Choice` is a record parameterized by it.

**`agda/SubgroupCardDvdFinite.agda`**, profile CC, no parameters.  It
imports `Group`, `Subgroup`, `⟨_⟩`, `⟨⟩-≡` and the relation `_~_` from
the classical file, and adds the following:

+  decisions through `does` and agda-stdlib's `dec-true`, `dec-false` and
   `toWitness`, and cases on `Fin` through agda-stdlib's `∀-cons`, so that
   no clause matches on a constructor of `Fin` or `Dec`, whose indices
   would make `--cubical-compatible` warn `[UnsupportedIndexedMatch]`;
   the file checks with no warning;
+  `first`, the first index at which a Boolean function holds, and
   `first-or`, with a default, with the lemmas that it holds there, that
   it respects pointwise equality, and that the default does not matter
   where the function holds somewhere;
+  `count`, which returns the number `k` of elements of a decidable family
   of propositions over `Fin n` together with the isomorphism to `Fin k`,
   so that no goal has to unfold a separate counting function;
+  the proof: decidable equality on `A`, `A-is-set`, decidable membership
   in `H`, `rep` (the representative of a coset) with `rep-mem`,
   `rep-cong` and `rep-idem`, the transversal `Σ A (λ x → rep x ≡ x)` in
   the place of `α ⧸ s`, the equivalence `A ↔ (Transversal × ⟨ H ⟩)`,
   which is Lean's with the transversal for the quotient, the count of
   the transversal, and the composite `Fin n ↔ Fin (k * m)`;
+  the Klein four-group example.

## Sizes

| Measure | Value |
| --- | --- |
| Export, bytes | 24,928,106 (over 1 MB, so `lean/term.sidecar.json` stands in for it) |
| Export, records | 470,166 |
| Export, expression records | 424,797 |
| Export, declarations | 6,248: 306 inductive, 4 quot, 2,255 def, 3,678 thm, 2 opaque, 3 axiom |
| Agda, lines per file | `SubgroupCardDvd.agda` 495, of which 288 are code; `SubgroupCardDvdFinite.agda` 421, of which 279 are code |
| Agda, check time | 6.9 seconds for the two files (Agda 2.8.0, no `.agdai` files of the corpus) |

The check time is `make corpus-check`'s for the entry: the classical
file first, then the finite file, which loads its interface.

## Remarks

The export was made on 2026-10-11 with lean4export v4.33.0 (format
3.1.0) under Lean v4.33.1 (commit `819816b`), the pins of
[`docs/pinning.md`](../../docs/pinning.md).  Two runs gave the same
bytes, with the SHA-256 the sidecar records.  The kernel measurements and
feature counts come from the probe described in
[`../real-sqrt-nonneg/notes.md`][sqrt-notes], Remarks.

The finite file takes the enumerations themselves, where Lean's
`Finite α` is `Nonempty (α ≃ Fin n)`, a proposition.  From truncated
enumerations the proof should still go through, by eliminating into
`m ∣ n`, which is a proposition because `m ≥ 1` (the subgroup contains
1); the file does not do it, since it would need the `Truncation`
record, a parameter.

[#9]: https://github.com/formalverification/lean2agda/issues/9
[#26]: https://github.com/formalverification/lean2agda/issues/26
[#75]: https://github.com/formalverification/lean2agda/pull/75
[catalog]: ../../docs/foundations/gap-catalog.md
[cat-axioms]: ../../docs/foundations/gap-catalog.md#axioms
[cat-decidable-and-noncomputable]: ../../docs/foundations/gap-catalog.md#decidable-and-noncomputable
[cat-impredicative-prop]: ../../docs/foundations/gap-catalog.md#impredicative-prop
[cat-k-and-uip]: ../../docs/foundations/gap-catalog.md#k-and-uip
[cat-large-elimination]: ../../docs/foundations/gap-catalog.md#large-elimination
[cat-literals]: ../../docs/foundations/gap-catalog.md#literals
[cat-nested-and-mutual-inductives]: ../../docs/foundations/gap-catalog.md#nested-and-mutual-inductives
[cat-projections-and-let]: ../../docs/foundations/gap-catalog.md#projections-and-let
[cat-quotients]: ../../docs/foundations/gap-catalog.md#quotients
[cat-structure-eta]: ../../docs/foundations/gap-catalog.md#structure-eta
[cat-universe-levels]: ../../docs/foundations/gap-catalog.md#universe-levels
[lean-findings]: ../../docs/lean-findings.md
[lean4#15226]: https://github.com/leanprover/lean4/issues/15226
[sqrt-notes]: ../real-sqrt-nonneg/notes.md
