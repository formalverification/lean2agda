/-
File: corpus/multiset-map-map/lean/Statement.lean

The statement of `Multiset.map_map`, quoted from Mathlib v4.33.1,
`Mathlib/Data/Multiset/MapFold.lean`, lines 150 to 152:

    @[simp]
    theorem map_map (g : β → γ) (f : α → β) (s : Multiset α) : map g (map f s) = map (g ∘ f) s :=
      Quot.inductionOn s fun _l => congr_arg _ List.map_map

with the definition it is about, `Multiset.map`, from lines 47 and 48
of the same file:

    def map (f : α → β) (s : Multiset α) : Multiset β :=
      Quot.liftOn s (fun l : List α => (l.map f : Multiset β)) fun _l₁ _l₂ p => Quot.sound (p.map f)

and `Multiset` itself, from `Mathlib/Data/Multiset/Defs.lean`, lines 70
and 71:

    def Multiset.{u} (α : Type u) : Type u :=
      Quotient (List.isSetoid α)

Run from `translator/` as

    lake env lean ../corpus/multiset-map-map/lean/Statement.lean

it prints the following:

    @Multiset.map_map : ∀ {α : Type u_2} {β : Type u_1} {γ : Type u_3} (g : β → γ) (f : α → β) (s : Multiset α),
      Multiset.map g (Multiset.map f s) = Multiset.map (g ∘ f) s
    'Multiset.map_map' depends on axioms: [propext, Quot.sound]
    'Multiset.map' depends on axioms: [propext, Quot.sound]
-/
import Mathlib.Data.Multiset.MapFold

#check @Multiset.map_map
#print axioms Multiset.map_map
#print axioms Multiset.map
