-- Outcome on 2026-10-13 with Agda 2.8.0: accepted
{-# OPTIONS --type-in-type #-}
module I04Promotion where

-- Eq with Lean's promotion undone: a an index, bound explicitly by the
-- constructor as Lean's Eq.refl binds it; the printer's application
-- Eq:refl {α₀} a₁ checks, and so does the postulated recursor's type.
data Eq {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl : (a₁ : α₀) → Eq {α₀} a₁ a₁

postulate Eq:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → Eq {α₀} a₁ a₂ → Set} → motive₂ a₁ (Eq:refl {α₀} a₁) → {a₃ : α₀} → (t₄ : Eq {α₀} a₁ a₃) → motive₂ a₃ t₄

rfl : {α₀ : Set} → {a₁ : α₀} → Eq {α₀} a₁ a₁
rfl {α₀} {a₁} = Eq:refl {α₀} a₁

-- HEq: α a parameter, a an index bound explicitly, β and b indices; the
-- type's own signature has an implicit binder among the indices.
data HEq {α₀ : Set} : α₀ → {β₂ : Set} → β₂ → Set where
  HEq:refl : (a₁ : α₀) → HEq {α₀} a₁ {α₀} a₁

postulate HEq:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : {β₂ : Set} → (a₃ : β₂) → HEq {α₀} a₁ {β₂} a₃ → Set} → motive₂ {α₀} a₁ (HEq:refl {α₀} a₁) → {β₃ : Set} → {a₄ : β₃} → (t₅ : HEq {α₀} a₁ {β₃} a₄) → motive₂ {β₃} a₄ t₅

-- The generic data form of Nat with its builtin.
data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

-- Nat.le: a parameter kept, an index, implicit constructor binders.
data Nat:le (n₀ : Nat) : Nat → Set where
  Nat:le:refl : Nat:le n₀ n₀
  Nat:le:step : {m₁ : Nat} → Nat:le n₀ m₁ → Nat:le n₀ (Nat:succ m₁)

le-test : Nat:le 2 4
le-test = Nat:le:step {2} {3} (Nat:le:step {2} {2} (Nat:le:refl {2}))

-- A structure with a dependent field, its Lean projection functions as
-- definitions over Agda's projections, and Lean's eta.
postulate Fin : Nat → Set

record Dependent : Set where
  constructor Dependent:mk
  field
    size₀ : Nat
    value₁ : Fin size₀

Dependent:size : Dependent → Nat
Dependent:size self₀ = Dependent.size₀ self₀

Dependent:value : (self₀ : Dependent) → Fin (Dependent:size self₀)
Dependent:value self₀ = Dependent.value₁ self₀

eta : (d : Dependent) → Eq {Dependent} d (Dependent:mk (Dependent:size d) (Dependent:value d))
eta d = Eq:refl {Dependent} d
