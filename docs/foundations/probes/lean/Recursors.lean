-- File: docs/foundations/probes/lean/Recursors.lean
-- WellFounded.Nat.fix.go, large elimination of Iff, Nonempty, Exists, Acc, UIP on types, HEq.
-- Run from translator/ as: lake env lean ../docs/foundations/probes/lean/Recursors.lean
import Lean
#print WellFounded.Nat.fix.go
#print WellFounded.Nat.eager
#print axioms WellFounded.Nat.fix.go
-- closed instances of the gcd equation hold by kernel arithmetic
example : Nat.gcd 7 4 = Nat.gcd (4 % 7) 7 := rfl
-- large-elimination check for Iff, Nonempty, Exists, Subsingleton
#check @Iff.rec
#check @Nonempty.rec
#check @Exists.rec
#check @Acc.rec
-- Subsingleton.elim and UIP on types
example (α β : Type) (p q : α = β) : p = q := rfl
-- HEq
#print HEq
example {α : Sort u} (a : α) (h : HEq a a) : (HEq.rec (motive := fun _ _ => Nat) 0 h : Nat) = 0 := rfl

/- Output on 2026-10-07 (Lean v4.33.1, Mathlib v4.33.1):
@[implicit_reducible] def WellFounded.Nat.fix.go.{u, v} : {α : Sort u} →
  {motive : α → Sort v} →
    (h : α → Nat) →
      ((x : α) → ((y : α) → InvImage (fun x1 x2 => x1 < x2) h y x → motive y) → motive x) →
        (fuel : Nat) → (x : α) → h x < fuel → motive x :=
fun {α} {motive} h F fuel =>
  Nat.rec (motive := fun x => (x_1 : α) → h x_1 < x → motive x_1) (fun x hfuel => ⋯.elim)
    (fun x ih x_1 hfuel => F x_1 fun y hy => ih y ⋯) fuel
@[implicit_reducible] def WellFounded.Nat.eager : Nat → Nat :=
fun n => if n.beq n = true then n else n
'WellFounded.Nat.fix.go' does not depend on any axioms
@Iff.rec : {a b : Prop} →
  {motive : (a ↔ b) → Sort u_1} → ((mp : a → b) → (mpr : b → a) → motive ⋯) → (t : a ↔ b) → motive t
@Nonempty.rec : ∀ {α : Sort u_1} {motive : Nonempty α → Prop}, (∀ (val : α), motive ⋯) → ∀ (t : Nonempty α), motive t
@Exists.rec : ∀ {α : Sort u_1} {p : α → Prop} {motive : Exists p → Prop},
  (∀ (w : α) (h : p w), motive ⋯) → ∀ (t : Exists p), motive t
@Acc.rec : {α : Sort u_2} →
  {r : α → α → Prop} →
    {motive : (a : α) → Acc r a → Sort u_1} →
      ((x : α) → (h : ∀ (y : α), r y x → Acc r y) → ((y : α) → (a : r y x) → motive y ⋯) → motive x ⋯) →
        {a : α} → (t : Acc r a) → motive a t
inductive HEq.{u} : {α : Sort u} → α → {β : Sort u} → β → Prop
number of parameters: 2
constructors:
HEq.refl : ∀ {α : Sort u} (a : α), a ≍ a
-/
