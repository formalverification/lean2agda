/-
File: corpus/set-ext/lean/Statement.lean

The statement of `Set.ext`, quoted from Mathlib v4.33.1,
`Mathlib/Data/Set/Defs.lean`, lines 82 to 84:

    @[ext, grind ext]
    theorem ext {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b :=
      funext (fun x ↦ propext (h x))

with the definitions it unfolds, from lines 51, 76, 77, 79 and 80 of
the same file:

    def Set (α : Type u) := α → Prop

    protected def Mem (s : Set α) (a : α) : Prop :=
      s a

    instance : Membership α (Set α) :=
      ⟨Set.Mem⟩

Run from `translator/` as

    lake env lean ../corpus/set-ext/lean/Statement.lean

it prints the following:

    @Set.ext : ∀ {α : Type u_1} {a b : Set α}, (∀ (x : α), x ∈ a ↔ x ∈ b) → a = b
    'Set.ext' depends on axioms: [propext, Quot.sound]
    'funext' depends on axioms: [Quot.sound]
-/
import Mathlib.Data.Set.Defs

#check @Set.ext
#print axioms Set.ext
#print axioms funext
