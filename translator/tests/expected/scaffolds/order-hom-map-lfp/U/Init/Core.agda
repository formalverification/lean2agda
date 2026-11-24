{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of OrderHom:map~ulfp
-- Lean module Init.Core
module U.Init.Core where
import U.Init.Prelude

Ne : {α₀ : Set} → α₀ → α₀ → Set
Ne {α₀} a₁ b₂ = U.Init.Prelude.Not (U.Init.Prelude.Eq {α₀} a₁ b₂)

record Exists {α₀ : Set} (p₁ : α₀ → Set) : Set where
  constructor Exists:intro
  field
    w₂ : α₀
    h₃ : p₁ w₂

-- recursor
Exists:rec : {α₀ : Set} → {p₁ : α₀ → Set} → {motive₂ : Exists {α₀} p₁ → Set} → ((w₃ : α₀) → (h₄ : p₁ w₃) → motive₂ (Exists:intro {α₀} {p₁} w₃ h₄)) → (t₃ : Exists {α₀} p₁) → motive₂ t₃
Exists:rec {α₀} {p₁} {motive₂} intro₃ (Exists:intro w₄ h₅) = intro₃ w₄ h₅

record Iff (a₀ : Set) (b₁ : Set) : Set where
  constructor Iff:intro
  field
    mp₂ : a₀ → b₁
    mpr₃ : b₁ → a₀

-- recursor
Iff:rec : {a₀ : Set} → {b₁ : Set} → {motive₂ : Iff a₀ b₁ → Set} → ((mp₃ : a₀ → b₁) → (mpr₄ : b₁ → a₀) → motive₂ (Iff:intro {a₀} {b₁} mp₃ mpr₄)) → (t₃ : Iff a₀ b₁) → motive₂ t₃
Iff:rec {a₀} {b₁} {motive₂} intro₃ (Iff:intro mp₄ mpr₅) = intro₃ mp₄ mpr₅

Eq:mpr : {α₀ : Set} → {β₁ : Set} → U.Init.Prelude.Eq {Set} α₀ β₁ → β₁ → α₀
Eq:mpr {α₀} {β₁} h₂ b₃ = U.Init.Prelude.Eq:rec {Set} {β₁} {λ (x₄ : Set) → λ (h₅ : U.Init.Prelude.Eq {Set} β₁ x₄) → x₄} b₃ {α₀} (U.Init.Prelude.Eq:symm {Set} {α₀} {β₁} h₂)

-- theorem
opaque
  Iff:refl : (a₀ : Set) → Iff a₀ a₀
  Iff:refl a₀ = Iff:intro {a₀} {a₀} (λ (h₁ : a₀) → h₁) (λ (h₁ : a₀) → h₁)

-- theorem
opaque
  Iff:rfl : {a₀ : Set} → Iff a₀ a₀
  Iff:rfl {a₀} = Iff:refl a₀

postulate propext : {a₀ : Set} → {b₁ : Set} → Iff a₀ b₁ → U.Init.Prelude.Eq {Set} a₀ b₁

-- theorem
opaque
  Iff:mp : {a₀ : Set} → {b₁ : Set} → Iff a₀ b₁ → a₀ → b₁
  Iff:mp {a₀} {b₁} self₂ = Iff.mp₂ {a₀} {b₁} self₂

-- theorem
opaque
  Iff:mpr : {a₀ : Set} → {b₁ : Set} → Iff a₀ b₁ → b₁ → a₀
  Iff:mpr {a₀} {b₁} self₂ = Iff.mpr₃ {a₀} {b₁} self₂

Quot:liftOn : {α₀ : Set} → {β₁ : Set} → {r₂ : α₀ → α₀ → Set} → U.Init.Prelude.Quot {α₀} r₂ → (f₃ : α₀ → β₁) → ((a₄ : α₀) → (b₅ : α₀) → r₂ a₄ b₅ → U.Init.Prelude.Eq {β₁} (f₃ a₄) (f₃ b₅)) → β₁
Quot:liftOn {α₀} {β₁} {r₂} q₃ f₄ c₅ = U.Init.Prelude.Quot:lift {α₀} {r₂} {β₁} f₄ c₅ q₃

postulate Quot:sound : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {a₂ : α₀} → {b₃ : α₀} → r₁ a₂ b₃ → U.Init.Prelude.Eq {U.Init.Prelude.Quot {α₀} r₁} (U.Init.Prelude.Quot:mk {α₀} r₁ a₂) (U.Init.Prelude.Quot:mk {α₀} r₁ b₃)

-- theorem
opaque
  funext : {α₀ : Set} → {β₁ : α₀ → Set} → {f₂ : (x₂ : α₀) → β₁ x₂} → {g₃ : (x₃ : α₀) → β₁ x₃} → ((x₄ : α₀) → U.Init.Prelude.Eq {β₁ x₄} (f₂ x₄) (g₃ x₄)) → U.Init.Prelude.Eq {(x₄ : α₀) → β₁ x₄} f₂ g₃
  funext {α₀} {β₁} {f₂} {g₃} h₄ = let eqv₅ : ((x₅ : α₀) → β₁ x₅) → ((x₅ : α₀) → β₁ x₅) → Set; eqv₅ = λ (f₅ : (x₅ : α₀) → β₁ x₅) → λ (g₆ : (x₆ : α₀) → β₁ x₆) → (x₇ : α₀) → U.Init.Prelude.Eq {β₁ x₇} (f₅ x₇) (g₆ x₇) in let extfunApp₆ : U.Init.Prelude.Quot {(x₆ : α₀) → β₁ x₆} eqv₅ → (x₆ : α₀) → β₁ x₆; extfunApp₆ = λ (f₆ : U.Init.Prelude.Quot {(x₆ : α₀) → β₁ x₆} eqv₅) → λ (x₇ : α₀) → Quot:liftOn {(x₈ : α₀) → β₁ x₈} {β₁ x₇} {eqv₅} f₆ (λ (f₈ : (x₈ : α₀) → β₁ x₈) → f₈ x₇) (λ (x₈ : (x₈ : α₀) → β₁ x₈) → λ (x₉ : (x₉ : α₀) → β₁ x₉) → λ (h₁₀ : eqv₅ x₈ x₉) → h₁₀ x₇) in U.Init.Prelude.id {U.Init.Prelude.Eq {(x₇ : α₀) → β₁ x₇} f₂ g₃} (U.Init.Prelude.congrArg {U.Init.Prelude.Quot {(x₇ : α₀) → β₁ x₇} eqv₅} {(x₇ : α₀) → β₁ x₇} {U.Init.Prelude.Quot:mk {(x₇ : α₀) → β₁ x₇} eqv₅ f₂} {U.Init.Prelude.Quot:mk {(x₇ : α₀) → β₁ x₇} eqv₅ g₃} extfunApp₆ (Quot:sound {(x₇ : α₀) → β₁ x₇} {eqv₅} {f₂} {g₃} h₄))

flip : {α₀ : Set} → {β₁ : Set} → {φ₂ : Set} → (α₀ → β₁ → φ₂) → β₁ → α₀ → φ₂
flip {α₀} {β₁} {φ₂} f₃ b₄ a₅ = f₃ a₅ b₄
