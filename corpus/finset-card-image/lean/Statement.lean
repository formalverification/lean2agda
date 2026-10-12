/-
File: corpus/finset-card-image/lean/Statement.lean

The statement of `Finset.card_image_of_injective`, quoted from Mathlib
v4.33.1, `Mathlib/Data/Finset/Card.lean`, lines 254 to 256, under the
variables of lines 38 and 224:

    variable {α β R : Type*}
    variable {s t u : Finset α} {f : α → β} {n : ℕ}

    theorem card_image_of_injective [DecidableEq β] (s : Finset α) (H : Injective f) :
        #(s.image f) = #s :=
      card_image_of_injOn fun _ _ _ _ h => H h

with the lemma it cites, from lines 236 and 237:

    theorem card_image_of_injOn [DecidableEq β] (H : Set.InjOn f s) : #(s.image f) = #s := by
      simp only [card, image_val_of_injOn H, card_map]

and the definitions the statement unfolds: `Finset` and `card`, from
`Mathlib/Data/Finset/Defs.lean`, lines 75 to 79, and `Card.lean`,
lines 47 and 48; and `image`, from `Mathlib/Data/Finset/Image.lean`,
lines 280 and 281, under `variable [DecidableEq β]`:

    structure Finset (α : Type*) where
      val : Multiset α
      nodup : Nodup val

    def card (s : Finset α) : ℕ :=
      Multiset.card s.1

    def image (f : α → β) (s : Finset α) : Finset β :=
      (s.1.map f).toFinset

The `DecidableEq β` instance is a hypothesis of the statement already;
`Classical.choice` enters through proofs (../notes.md, Tier).

Run from `translator/` as

    lake env lean ../corpus/finset-card-image/lean/Statement.lean

it prints the following:

    @Finset.card_image_of_injective : ∀ {α : Type u_1} {β : Type u_2} {f : α → β} [inst : DecidableEq β] (s : Finset α),
      Function.Injective f → (Finset.image f s).card = s.card
    'Finset.card_image_of_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Finset.image' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Finset.card' depends on axioms: [propext, Quot.sound]
    'Multiset.Nodup' depends on axioms: [propext, Quot.sound]
-/
import Mathlib.Data.Finset.Card

#check @Finset.card_image_of_injective
#print axioms Finset.card_image_of_injective
#print axioms Finset.image
#print axioms Finset.card
#print axioms Multiset.Nodup
