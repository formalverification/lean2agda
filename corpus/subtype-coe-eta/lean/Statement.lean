/-
File: corpus/subtype-coe-eta/lean/Statement.lean

The statement of `Subtype.coe_eta`, quoted from Mathlib v4.33.1,
`Mathlib/Data/Subtype.lean`, lines 65 to 67, under the section variables
of line 34:

    variable {α β γ : Sort*} {p q : α → Prop}

    @[simp]
    theorem coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a :=
      Subtype.ext rfl

with the structure it is about, from Lean v4.33.1,
`src/Init/Prelude.lean`, lines 664 to 673 (doc comments left out):

    structure Subtype {α : Sort u} (p : α → Prop) where
      val : α
      property : p val

and the lemma its proof cites, from `src/Init/Core.lean`, lines 1364
and 1365, under `variable {α : Sort u} {p : α → Prop}`:

    protected theorem ext : ∀ {a1 a2 : {x // p x}}, val a1 = val a2 → a1 = a2
      | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

Run from `translator/` as

    lake env lean ../corpus/subtype-coe-eta/lean/Statement.lean

it prints the following:

    @Subtype.coe_eta : ∀ {α : Sort u_1} {p : α → Prop} (a : { a // p a }) (h : p ↑a), ⟨↑a, h⟩ = a
    'Subtype.coe_eta' does not depend on any axioms
    @Subtype.ext : ∀ {α : Sort u_1} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 = ↑a2 → a1 = a2
    'Subtype.ext' does not depend on any axioms
-/
import Mathlib.Data.Subtype

#check @Subtype.coe_eta
#print axioms Subtype.coe_eta
#check @Subtype.ext
#print axioms Subtype.ext
