/-
File: corpus/order-hom-map-lfp/lean/Statement.lean

The statement of `OrderHom.map_lfp`, quoted from Mathlib v4.33.1,
`Mathlib/Order/FixedPoints.lean`, lines 70 to 73, under the variables
of lines 38 and 46:

    variable {α : Type u} {β : Type v} {γ : Type w}
    variable [CompleteLattice α] (f : α →o α)

    @[simp]
    theorem map_lfp : f f.lfp = f.lfp :=
      have h : f f.lfp ≤ f.lfp := f.map_le_lfp le_rfl
      h.antisymm <| f.lfp_le <| f.mono h

with the definition and the lemmas it cites, from lines 48 to 51, 58
and 59, and 64 to 69 of the same file:

    /-- Least fixed point of a monotone function -/
    def lfp : (α →o α) →o α where
      toFun f := sInf { a | f a ≤ a }
      monotone' _ _ hle := sInf_le_sInf fun a ha => (hle a).trans ha

    theorem lfp_le {a : α} (h : f a ≤ a) : f.lfp ≤ a :=
      sInf_le h

    theorem le_lfp {a : α} (h : ∀ b, f b ≤ b → a ≤ b) : a ≤ f.lfp :=
      le_sInf h

    theorem map_le_lfp {a : α} (ha : a ≤ f.lfp) : f a ≤ f.lfp :=
      f.le_lfp fun _ hb => (f.mono <| le_sInf_iff.1 ha _ hb).trans hb

Run from `translator/` as

    lake env lean ../corpus/order-hom-map-lfp/lean/Statement.lean

it prints the following:

    @OrderHom.map_lfp : ∀ {α : Type u_1} [inst : CompleteLattice α] (f : α →o α), f (OrderHom.lfp f) = OrderHom.lfp f
    'OrderHom.map_lfp' depends on axioms: [propext, Quot.sound]
    'OrderHom.lfp' depends on axioms: [propext]
    'le_sInf_iff' depends on axioms: [propext, Quot.sound]
-/
import Mathlib.Order.FixedPoints

#check @OrderHom.map_lfp
#print axioms OrderHom.map_lfp
#print axioms OrderHom.lfp
#print axioms le_sInf_iff
