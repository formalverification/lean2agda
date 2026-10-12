/-
File: corpus/subgroup-card-dvd/lean/Statement.lean

The statement of `Subgroup.card_subgroup_dvd_card`, Lagrange's theorem,
quoted from Mathlib v4.33.1, `Mathlib/GroupTheory/Coset/Card.lean`,
lines 66 to 70:

    /-- **Lagrange's Theorem**: The order of a subgroup divides the order of its ambient group. -/
    @[to_additive (attr := wikidata Q505798) /-- **Lagrange's Theorem**: The order of an additive
    subgroup divides the order of its ambient additive group. -/]
    theorem card_subgroup_dvd_card (s : Subgroup α) : Nat.card s ∣ Nat.card α := by
      simp [card_eq_card_quotient_mul_card_subgroup s, @dvd_mul_left ℕ]

with the lemma its proof cites, from lines 53 to 55 of the same file:

    theorem card_eq_card_quotient_mul_card_subgroup (s : Subgroup α) :
        Nat.card α = Nat.card (α ⧸ s) * Nat.card s := by
      rw [← Nat.card_prod]; exact Nat.card_congr Subgroup.groupEquivQuotientProdSubgroup

and `Nat.card`, from `Mathlib/SetTheory/Cardinal/Finite.lean`, lines 41
and 42:

    protected def card (α : Type*) : ℕ :=
      toNat (mk α)

Run from `translator/` as

    lake env lean ../corpus/subgroup-card-dvd/lean/Statement.lean

it prints the following:

    @Subgroup.card_subgroup_dvd_card : ∀ {α : Type u_1} [inst : Group α] (s : Subgroup α), Nat.card ↥s ∣ Nat.card α
    'Subgroup.card_subgroup_dvd_card' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Nat.card' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Subgroup.groupEquivQuotientProdSubgroup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
import Mathlib.GroupTheory.Coset.Card

#check @Subgroup.card_subgroup_dvd_card
#print axioms Subgroup.card_subgroup_dvd_card
#print axioms Nat.card
#print axioms Subgroup.groupEquivQuotientProdSubgroup
