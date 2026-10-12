<!-- File: corpus/real-sqrt-nonneg/notes.md -->

# Real.sqrt_nonneg

The entry for the real numbers, translated by issue M1-9 ([#9]).
Mathlib declares `Real.sqrt_nonneg` in `Mathlib.Analysis.Real.Sqrt`
(`Mathlib.Data.Real.Sqrt` is a deprecated module that re-exports it at
the pin).  One Agda file, `agda/RealSqrtNonneg.agda`, checks under
profile CC (`--safe --cubical-compatible`), with the real numbers as a
module parameter.

## Statement

Lean's statement, as `#check` prints it:

    Real.sqrt_nonneg : ∀ (x : ℝ), 0 ≤ √x

The Agda statement, inside a module that takes `R : Reals r ℓ`:

    sqrt-nonneg : (x : ℝ) → 0ℝ ≤ sqrt x

They match up to notation and up to what `ℝ`, `0`, `≤` and `√` are,
which is as follows:

+  Lean: `ℝ` is the structure `Real` with the one field
   `cauchy : CauSeq.Completion.Cauchy abs`, a quotient of the Cauchy
   sequences of rationals; `0`, `*`, `≤` and `max` are the instances
   `Real.instZero`, `Real.instMul`, `Real.instLE` and `Real.instMax`,
   whose operations Mathlib defines with `private irreducible_def`;
   `√x` is `Real.sqrt x`, defined as `NNReal.sqrt (Real.toNNReal x)`
   with the coercion from `ℝ≥0`.
+  Agda: `ℝ`, `0ℝ`, `_*_`, `_≤_` and `max` are fields of the parameter
   record `Reals`; `ℝ≥0`, `toNNReal` and `sqrt` are defined in the file
   as Mathlib defines them, from the record's fields and its field
   `nnsqrt`, which stands for `NNReal.sqrt`.

So the Agda statement is Lean's with the construction of the reals
abstracted, and the definitions between the statement and that
construction kept.

## Tier

`#print axioms` prints `[propext, Classical.choice, Quot.sound]`, so the
entry is T2.  The proof brings in no axiom: its term is
`fun x => id (NNReal.coe_nonneg (NNReal.sqrt x.toNNReal))`, and
`NNReal.coe_nonneg r` is `r.property`.  The axioms come with the
constants the statement mentions.  A breadth-first search of the
dependency graph from the statement's type alone (the probe under
Remarks) reaches `Classical.choice` along three paths, as follows:

+  through the type `Real` itself: `Real.ofCauchy` mentions
   `CauSeq.Completion.Cauchy abs`, whose instances need
   `Rat.instIsStrictOrderedRing`, whose proof that `ℚ` has no zero
   divisors goes through `IsDomain.to_noZeroDivisors`,
   `IsRightCancelMulZero.to_noZeroDivisors` and
   `Classical.or_iff_not_imp_right`, which uses
   `Classical.propDecidable`.  So `#print axioms Real` prints all three
   axioms, and every theorem whose statement mentions `ℝ` is T2, by a
   proof inside an instance about the rationals;
+  through `Real.toNNReal`, whose proof `0 ≤ max r 0` is `le_max_right`
   at the linear order `Real.linearOrder`, which takes its `Decidable`
   instances from `Classical.propDecidable`;
+  through `NNReal.sqrt`, defined as the inverse of the order
   isomorphism `NNReal.powOrderIso 2` of `x ↦ x ^ 2`, which
   `StrictMono.orderIsoOfSurjective` builds from a proof of surjectivity
   (by continuity, in a conditionally complete order); its inverse is
   `Function.invFun` (through `Equiv.ofInjective`), which picks a
   preimage with `Exists.choose`, that is, by choice.  The shortest path
   runs through `NNReal.instConditionallyCompleteLinearOrderBot`.

`propext` and `Quot.sound` come along the same paths.  The first two
paths run through proofs only, and the third through data: a walk of the
dependency graph that never enters a constant whose type is a
proposition (a theorem or a proof's auxiliary definition) does not reach
`Classical.choice` from `Real`, `Real.instLE`, `Real.instZero` or
`Real.toNNReal` (611 to 652 constants visited), and does reach it from
`NNReal.sqrt`, through `NNReal.powOrderIso`, the linear order on `ℝ≥0`
and `Real.linearOrder`, whose `Decidable` instances are data.  So the
statement's square root is classical in its definition, not only in its
proofs.  The export's
axiom declarations are the same three, so the set is not affected by
the way `#print axioms` can leave axioms out (Lean issue
[lean4#15226]).

The statement survives de-classicalization.  The Agda file states it
over a record whose fields are all constructive notions (constructive
reals have an order, a maximum and a square root of a nonnegative
number), the proof uses no field but `nnsqrt`, and the proof is Lean's,
so a constructive proof is known: it is this one, once any constructive
reals instantiate the record.  None of the three classical uses above is
essential to the statement: the first is a proof about `ℚ`, the second
a proof of a fact that holds constructively for `max`, and the third,
the one in data, the construction of a function that constructive
analysis builds without choice.  The record has an instance in the file
with no classical principle (`one-point`), which shows that the
parameter adds no logical strength, though not that it describes ℝ; the
libraries the corpus may import have no real numbers.

## What the kernel term needed

The export holds 10,169 declarations: 399 inductive types, the 4
quotient primitives, 3,061 definitions, 6,689 theorems, 13 opaque
constants and the 3 axioms.  By the module of each constant (counting
constructors and recursors), the closure is 4,533 constants from Lean's
core library, 2,613 from `Mathlib.Algebra`, 1,648 from `Mathlib.Order`,
1,110 from `Mathlib.Data`, 608 from `Mathlib.Topology`, 152 from
`Mathlib.Logic`, and a few dozen elsewhere.  That is the construction of
ℝ, its order and field structure, the theory of conditionally complete
orders and the topology that proves `NNReal.sqrt` exists, all of which
the Agda version abstracts into the record.

The check of `Real.sqrt_nonneg` itself is small.  Re-checked in Lean's
kernel with its diagnostics on (the probe under Remarks), it unfolds
`Real.sqrt` once (the step that `unfold sqrt` relies on, which the
kernel takes although `Real.sqrt` is `@[irreducible]`, an attribute the
kernel ignores), `Real.instLE` once, `LE.le` twice, `FunLike` once and
`outParam` twice, and reduces no recursor and no quotient.  Everything
else below is in the closure, which the schema counts (`SCHEMA.md`,
Features).  The same probe re-checked all 9,750 theorems and definitions
of the closure in 6.4 seconds and the kernel rejected none.  By feature,
each named by its entry in the gap catalog ([catalog]), the closure uses
the following:

+  [`quotients`][cat-quotients]: `CauSeq.Completion.Cauchy` is a
   quotient, and the kernel reduces `Quot.lift` 136 times, in 53 of the
   closure's theorems and definitions (the operations on Cauchy
   sequences and `funext`).  The Agda version has no quotient.
+  [`axioms`][cat-axioms]: the three, as under Tier.  The Agda version
   takes none; the record holds the reals, not a principle.
+  [`decidable-and-noncomputable`][cat-decidable-and-noncomputable]:
   `Real.sqrt` and `NNReal.sqrt` are `noncomputable`, 99 constants of the
   closure are, and 78 cite a classical `Decidable` instance
   (`Classical.propDecidable`, `Classical.decEq`, ...), among them
   `Real.linearOrder` and the inverse on Cauchy sequences.  Agda needs
   no `noncomputable`; the record has no `Decidable` field.
+  [`impredicative-prop`][cat-impredicative-prop]: 131 uses of a constant
   at universe arguments that make an `imax` in its type zero, such as
   `implies_congr.{0, 0}`, in lemmas about sets and filters.  None in the
   statement, whose only sort is that of `ℝ`.
+  [`k-and-uip`][cat-k-and-uip]: the kernel reduces `Eq.rec`, a recursor
   with K-like reduction, 29 times in 17 declarations.  The count
   includes ordinary reductions on `Eq.refl`, so only a zero would be
   conclusive; one of the 17 is `eq_of_heq`, which is K-like reduction
   on a universe (LF-5 of [`lean-findings.md`][lean-findings]), and the
   others (`PSigma.eta`, `Multiset.pmap`'s well-definedness, equation
   lemmas of `Lean.Grind`'s matchers) are for Lean4Less (M3-1, [#26]) to
   classify.  The Agda version needs no K.
+  [`large-elimination`][cat-large-elimination]: recursors of
   propositions used at a motive of any universe, such as `Eq.rec` in
   `cast` and `Eq.mpr`, and `False.rec` in `False.elim`, 23 such uses.
+  [`universe-levels`][cat-universe-levels]: 7,372 universe-polymorphic
   constants; the statement has no universe parameter.  The Agda record
   is polymorphic in the levels `r` of `ℝ` and `ℓ` of `≤`, and `ℝ≥0`
   lives in `Set (r ⊔ ℓ)`, where Lean's subtype stays in `Type`.
+  [`literals`][cat-literals]: 5,988 `Nat` literals and 616 `String`
   literals, in 2,951 constants.  The `String` literals are mostly tactic
   syntax (next item).
+  [`nested-and-mutual-inductives`][cat-nested-and-mutual-inductives]:
   `Lean.Syntax`, a nested inductive type, is in the closure because a
   structure field with a default tactic has the type `autoParam T stx`,
   where `stx : Lean.Syntax` is the tactic's syntax tree.  The shortest
   path here is `NNReal.instPartialOrder`, `Preorder.mk`, `autoParam`:
   `Preorder`'s field `lt_iff_le_not_ge` defaults to
   `by intros; rfl`.  A tactic default of a function's argument does the
   same through a constant `f._auto_<n>`, such as `Rat.normalize._auto_1`,
   which the type `Real` reaches.  `autoParam` is a reducible definition
   equal to `T`, so a translator can erase it, and with it `Lean.Syntax`.
   Cutting both forms from the closure (the probe of part 1's
   `order-hom-map-lfp` notes, on [#75], extended to `_auto_<n>`) removes
   `Lean.Syntax` and leaves 10,628 of the 10,721 constants, with
   `eq_of_heq`, `cast`, `String`, `Decidable`, `Quot.lift` and `funext`
   still in it: for this entry the machinery of tactics is not what
   makes the closure large.
+  [`projections-and-let`][cat-projections-and-let]: 1,424 projections in
   1,151 constants and 1,098 `let` expressions in 499.  The proof itself
   uses `Subtype.property`, a projection, which the Agda version renders
   as `proj₂`.

Three facts outside the catalog's features matter here, as follows:

+  **Mathlib's real operations are opaque to the kernel**.  Ten of the 13
   opaque constants are `Real.wrapped…`: `private irreducible_def`
   defines `Real.zero`, `one`, `add`, `neg`, `mul`, `inv'`, `lt`, `le`,
   `sup` and `inf` through an `opaque` constant holding the definition,
   and the kernel never unfolds an `opaque`.  Lean itself reasons about
   them only through their equation lemmas, so a record of operations is
   how Lean's kernel sees them too; a translation of the closure would
   emit Agda `opaque` definitions for them.  The eleventh is
   `wrapped` in `Mathlib.Topology.Defs.Filter`, and the last two are
   `String.Internal.append` and `Lean.opaqueId`, from core.
+  **No escape hatch**: the closure has no `partial` and no `unsafe`
   constant, and five with `implemented_by` (`List.attachWith`,
   `Nat.repr`, and three constructors of `Lean.Name`), which only
   compiled code sees.
+  **`@[irreducible]` is not Agda's `opaque`**.  The attribute stops
   Lean's elaborator, not its kernel; Agda's `opaque` stops the type
   checker outside an `unfolding` clause.  The Agda file makes `sqrt`
   opaque and its proof an `unfolding sqrt` block, which mirrors Lean's
   `unfold sqrt`; a control with the clause removed fails with
   `[UnequalTerms] proj₁ (nnsqrt (toNNReal x)) != sqrt x`.

Reading the closure finds no structure eta and no definitional proof
irrelevance that a mechanical count can see; neither rule is counted by
the kernel's diagnostics, and Lean4Less ([#26]) will settle both.  Of
the features the manifest listed, `quotients`,
`decidable-and-noncomputable` and `axioms`, the term uses all three; the
other seven are added under the schema's closure rule, as entries of M1-7
([#7]) did.

## Instance arguments

The statement carries 3 instance arguments: `Real.instLE` for `≤`, and
`Zero.toOfNat0` with `Real.instZero` for the literal `0`.  The proof
carries 16: the 3 again, in the type of `id`, and 13 more in
`NNReal.sqrt`'s application as a function, which goes through
`DFunLike.coe` with `instFunLikeOrderIso` and the order on `ℝ≥0`
(`NNReal.instPartialOrder`, through `PartialOrder.toPreorder` and
`Preorder.toLE`, several times over).  The whole closure carries
1,357,155.  The count is of arguments at instance-implicit positions of
applications with a constant head, in the declaration's type and value.

In Agda there is no instance argument.  The instances of `ℝ` become
fields of the module parameter `R : Reals r ℓ`, opened in the module, so
`0ℝ`, `_≤_`, `_*_` and `max` are names in scope; `NNReal.sqrt` becomes
the field `nnsqrt`, a plain function on `ℝ≥0`, so `DFunLike.coe` and the
order isomorphism disappear.

## The Agda version

One file, `agda/RealSqrtNonneg.agda`, profile CC.  Its parameter record
`Reals r ℓ` has nine fields: `ℝ`, `0ℝ`, `_*_`, `_≤_`, `≤-irrelevant`,
`max`, `≤-max-right`, `nnsqrt` and `nnsqrt-mul-self`.  Each stands for a
Mathlib constant, and Mathlib defines or proves every one of them, which
is what the parameter assumes that Lean proves, as follows:

+  `ℝ`, `0ℝ`, `_*_`, `_≤_`, `max`: the type and four of its operations,
   which Mathlib builds on Cauchy sequences (the operations through the
   opaque wrappers above).
+  `≤-irrelevant`: that `x ≤ y` is a proposition, which Lean has by
   definitional proof irrelevance; it makes `ℝ≥0 = Σ ℝ (0ℝ ≤_)` a
   subtype in Lean's sense.  The proof does not use it.
+  `≤-max-right`: `le_max_right` at ℝ, which Lean proves through the
   classical `Real.linearOrder`.
+  `nnsqrt` and `nnsqrt-mul-self`: `NNReal.sqrt` as a function on `ℝ≥0`,
   and `NNReal.mul_self_sqrt`, which says it is a square root; Lean
   proves that the function exists by real analysis and picks it by
   choice.  The proof uses only that `nnsqrt` lands in `ℝ≥0`.

The design follows the kickoff's suggestion with one change: the record
is not an ordered field.  The statement's definitions reach only `0`,
`≤` and `max` of ℝ and `NNReal.sqrt`, so the record holds those and the
one law that makes `nnsqrt` a square root; an ordered field's axioms
would assume much that the theorem never touches.  Nothing in it needs
to be classical, against the kickoff's "classical where it must be":
Lean's `max` on ℝ is `Real.sup`, computed pointwise, and only the proof
of `le_max_right` uses the classical order.

Given the record, `ℝ≥0`, `toNNReal` (`max x 0ℝ , ≤-max-right x 0ℝ`),
`coe-nonneg` (`proj₂`) and `sqrt` are Mathlib's definitions, and
`sqrt-nonneg x = coe-nonneg (nnsqrt (toNNReal x))` is Lean's term
without the `id`: the nonnegativity is the property that the subtype
carries.

A translator would not produce this file: it would emit the 10,169
declarations of the closure, the construction of ℝ included, with the
classical principles as parameters.  The file is the oracle for the
statement, and a measure of the distance: one subtype, two definitions
and a projection on the Agda side, against the export's 42 megabytes.

## Sizes

| Measure | Value |
| --- | --- |
| Export, bytes | 41,933,263 (over 1 MB, so `lean/term.sidecar.json` stands in for it) |
| Export, records | 788,405 |
| Export, expression records | 718,206 |
| Export, declarations | 10,169: 399 inductive, 4 quot, 3,061 def, 6,689 thm, 13 opaque, 3 axiom |
| Agda, lines per file | 124, of which 49 are code |
| Agda, check time | 0.2 seconds (Agda 2.8.0, no `.agdai` files of the corpus) |

## Remarks

The export was made on 2026-10-11 with lean4export v4.33.0 (format
3.1.0) under Lean v4.33.1 (commit `819816b`), the pins of
[`docs/pinning.md`](../../docs/pinning.md).  Two runs gave the same
bytes, with the SHA-256 the sidecar records.

The kernel measurements come from a scratch probe run from `translator/`
on 2026-10-11, the same method as the entries of M1-7 and M1-8 (the
probe printed in [`../multiset-map-map/notes.md`][multiset-notes]): the
closure walk that lean4export performs, and a re-check of every theorem
and definition under a fresh name with `Kernel.Environment.enableDiag`,
reading the counters of `Quot.lift`, `Quot.ind` and the recursors with
`k = true`.  The feature counts walk every type and value of the closure
once (with `Expr.forEach`, so shared subterms count once), counting
projections, `let` expressions and literals, recursors of propositions
applied at a non-zero motive level, constant uses that make an `imax`
zero, `noncomputable` constants and citations of classical `Decidable`
instances.  The paths to `Classical.choice` are shortest paths by
breadth-first search over the same edges; the search from the type alone
starts from the constants the statement mentions.  The scan of the
three entries of this part took 65 seconds, the kernel re-checks 33.

[#7]: https://github.com/formalverification/lean2agda/issues/7
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
[cat-universe-levels]: ../../docs/foundations/gap-catalog.md#universe-levels
[lean-findings]: ../../docs/lean-findings.md
[lean4#15226]: https://github.com/leanprover/lean4/issues/15226
[multiset-notes]: ../multiset-map-map/notes.md
