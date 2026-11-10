{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of Nat:gcd~usucc
-- Lean module Init.Core
module U.Init.Core where
import U.Init.Prelude

Eq:mpr : {α₀ : Set} → {β₁ : Set} → U.Init.Prelude.Eq {Set} α₀ β₁ → β₁ → α₀
Eq:mpr {α₀} {β₁} h₂ b₃ = U.Init.Prelude.Eq:rec {Set} {β₁} {λ (x₄ : Set) → λ (h₅ : U.Init.Prelude.Eq {Set} β₁ x₄) → x₄} b₃ {α₀} (U.Init.Prelude.Eq:symm {Set} {α₀} {β₁} h₂)

InvImage : {α₀ : Set} → {β₁ : Set} → (β₁ → β₁ → Set) → (α₀ → β₁) → α₀ → α₀ → Set
InvImage {α₀} {β₁} r₂ f₃ a₄ a₅ = r₂ (f₃ a₄) (f₃ a₅)

record PSigma {α₀ : Set} (β₁ : α₀ → Set) : Set where
  constructor PSigma:mk
  field
    fst₂ : α₀
    snd₃ : β₁ fst₂

postulate PSigma:rec : {α₀ : Set} → {β₁ : α₀ → Set} → {motive₂ : PSigma {α₀} β₁ → Set} → ((fst₃ : α₀) → (snd₄ : β₁ fst₃) → motive₂ (PSigma:mk {α₀} {β₁} fst₃ snd₄)) → (t₃ : PSigma {α₀} β₁) → motive₂ t₃

PSigma:casesOn : {α₀ : Set} → {β₁ : α₀ → Set} → {motive₂ : PSigma {α₀} β₁ → Set} → (t₃ : PSigma {α₀} β₁) → ((fst₄ : α₀) → (snd₅ : β₁ fst₄) → motive₂ (PSigma:mk {α₀} {β₁} fst₄ snd₅)) → motive₂ t₃
PSigma:casesOn {α₀} {β₁} {motive₂} t₃ mk₄ = PSigma:rec {α₀} {β₁} {motive₂} (λ (fst₅ : α₀) → λ (snd₆ : β₁ fst₅) → mk₄ fst₅ snd₆) t₃

Ne : {α₀ : Set} → α₀ → α₀ → Set
Ne {α₀} a₁ b₂ = U.Init.Prelude.Not (U.Init.Prelude.Eq {α₀} a₁ b₂)

Quot:liftOn : {α₀ : Set} → {β₁ : Set} → {r₂ : α₀ → α₀ → Set} → U.Init.Prelude.Quot {α₀} r₂ → (f₃ : α₀ → β₁) → ((a₄ : α₀) → (b₅ : α₀) → r₂ a₄ b₅ → U.Init.Prelude.Eq {β₁} (f₃ a₄) (f₃ b₅)) → β₁
Quot:liftOn {α₀} {β₁} {r₂} q₃ f₄ c₅ = U.Init.Prelude.Quot:lift {α₀} {r₂} {β₁} f₄ c₅ q₃

postulate Quot:sound : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {a₂ : α₀} → {b₃ : α₀} → r₁ a₂ b₃ → U.Init.Prelude.Eq {U.Init.Prelude.Quot {α₀} r₁} (U.Init.Prelude.Quot:mk {α₀} r₁ a₂) (U.Init.Prelude.Quot:mk {α₀} r₁ b₃)

-- theorem
opaque
  funext : {α₀ : Set} → {β₁ : α₀ → Set} → {f₂ : (x₂ : α₀) → β₁ x₂} → {g₃ : (x₃ : α₀) → β₁ x₃} → ((x₄ : α₀) → U.Init.Prelude.Eq {β₁ x₄} (f₂ x₄) (g₃ x₄)) → U.Init.Prelude.Eq {(x₄ : α₀) → β₁ x₄} f₂ g₃
  funext {α₀} {β₁} {f₂} {g₃} h₄ = let eqv₅ : ((x₅ : α₀) → β₁ x₅) → ((x₅ : α₀) → β₁ x₅) → Set; eqv₅ = λ (f₅ : (x₅ : α₀) → β₁ x₅) → λ (g₆ : (x₆ : α₀) → β₁ x₆) → (x₇ : α₀) → U.Init.Prelude.Eq {β₁ x₇} (f₅ x₇) (g₆ x₇) in let extfunApp₆ : U.Init.Prelude.Quot {(x₆ : α₀) → β₁ x₆} eqv₅ → (x₆ : α₀) → β₁ x₆; extfunApp₆ = λ (f₆ : U.Init.Prelude.Quot {(x₆ : α₀) → β₁ x₆} eqv₅) → λ (x₇ : α₀) → Quot:liftOn {(x₈ : α₀) → β₁ x₈} {β₁ x₇} {eqv₅} f₆ (λ (f₈ : (x₈ : α₀) → β₁ x₈) → f₈ x₇) (λ (x₈ : (x₈ : α₀) → β₁ x₈) → λ (x₉ : (x₉ : α₀) → β₁ x₉) → λ (h₁₀ : eqv₅ x₈ x₉) → h₁₀ x₇) in U.Init.Prelude.id {U.Init.Prelude.Eq {(x₇ : α₀) → β₁ x₇} f₂ g₃} (U.Init.Prelude.congrArg {U.Init.Prelude.Quot {(x₇ : α₀) → β₁ x₇} eqv₅} {(x₇ : α₀) → β₁ x₇} {U.Init.Prelude.Quot:mk {(x₇ : α₀) → β₁ x₇} eqv₅ f₂} {U.Init.Prelude.Quot:mk {(x₇ : α₀) → β₁ x₇} eqv₅ g₃} extfunApp₆ (Quot:sound {(x₇ : α₀) → β₁ x₇} {eqv₅} {f₂} {g₃} h₄))
