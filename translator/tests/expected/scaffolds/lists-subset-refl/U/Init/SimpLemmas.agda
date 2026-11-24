{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of Lists~x27~:Subset:refl
-- Lean module Init.SimpLemmas
module U.Init.SimpLemmas where
import U.Init.Core
import U.Init.Prelude

-- theorem
opaque
  eq~utrue : {p₀ : Set} → p₀ → U.Init.Prelude.Eq {Set} p₀ U.Init.Prelude.True
  eq~utrue {p₀} h₁ = U.Init.Core.propext {p₀} {U.Init.Prelude.True} (U.Init.Core.Iff:intro {p₀} {U.Init.Prelude.True} (λ (x₂ : p₀) → U.Init.Core.trivial) (λ (x₂ : U.Init.Prelude.True) → h₁))

-- theorem
opaque
  eq~uself : {α₀ : Set} → (a₁ : α₀) → U.Init.Prelude.Eq {Set} (U.Init.Prelude.Eq {α₀} a₁ a₁) U.Init.Prelude.True
  eq~uself {α₀} a₁ = eq~utrue {U.Init.Prelude.Eq {α₀} a₁ a₁} (U.Init.Prelude.rfl {α₀} {a₁})

-- theorem
opaque
  of~ueq~utrue : {p₀ : Set} → U.Init.Prelude.Eq {Set} p₀ U.Init.Prelude.True → p₀
  of~ueq~utrue {p₀} h₁ = U.Init.Prelude.Eq:rec {Set} {U.Init.Prelude.True} {λ (x₂ : Set) → λ (h₃ : U.Init.Prelude.Eq {Set} U.Init.Prelude.True x₂) → x₂} U.Init.Core.trivial {p₀} (U.Init.Prelude.Eq:symm {Set} {p₀} {U.Init.Prelude.True} h₁)

-- theorem
opaque
  or~utrue : (p₀ : Set) → U.Init.Prelude.Eq {Set} (U.Init.Prelude.Or p₀ U.Init.Prelude.True) U.Init.Prelude.True
  or~utrue p₀ = eq~utrue {U.Init.Prelude.Or p₀ U.Init.Prelude.True} (U.Init.Prelude.Or:inr {p₀} {U.Init.Prelude.True} U.Init.Core.trivial)

-- theorem
opaque
  true~uor : (p₀ : Set) → U.Init.Prelude.Eq {Set} (U.Init.Prelude.Or U.Init.Prelude.True p₀) U.Init.Prelude.True
  true~uor p₀ = eq~utrue {U.Init.Prelude.Or U.Init.Prelude.True p₀} (U.Init.Prelude.Or:inl {U.Init.Prelude.True} {p₀} U.Init.Core.trivial)

-- theorem
opaque
  forall~ucongr : {α₀ : Set} → {p₁ : α₀ → Set} → {q₂ : α₀ → Set} → ((a₃ : α₀) → U.Init.Prelude.Eq {Set} (p₁ a₃) (q₂ a₃)) → U.Init.Prelude.Eq {Set} ((a₃ : α₀) → p₁ a₃) ((a₃ : α₀) → q₂ a₃)
  forall~ucongr {α₀} {p₁} {q₂} h₃ = U.Init.Prelude.Eq:rec {α₀ → Set} {p₁} {λ (x₄ : α₀ → Set) → λ (h₅ : U.Init.Prelude.Eq {α₀ → Set} p₁ x₄) → U.Init.Prelude.Eq {Set} ((a₆ : α₀) → p₁ a₆) ((a₆ : α₀) → x₄ a₆)} (U.Init.Prelude.rfl {Set} {(a₄ : α₀) → p₁ a₄}) {q₂} (U.Init.Core.funext {α₀} {λ (x₄ : α₀) → Set} {p₁} {q₂} h₃)

-- theorem
opaque
  iff~uself : (p₀ : Set) → U.Init.Prelude.Eq {Set} (U.Init.Core.Iff p₀ p₀) U.Init.Prelude.True
  iff~uself p₀ = eq~utrue {U.Init.Core.Iff p₀ p₀} (U.Init.Core.Iff:rfl {p₀})

-- theorem
opaque
  implies~ucongr : {p₀ : Set} → {p₁ : Set} → {q₂ : Set} → {q₃ : Set} → U.Init.Prelude.Eq {Set} p₀ p₁ → U.Init.Prelude.Eq {Set} q₂ q₃ → U.Init.Prelude.Eq {Set} (p₀ → q₂) (p₁ → q₃)
  implies~ucongr {p₀} {p₁} {q₂} {q₃} h₄ h₅ = U.Init.Prelude.Eq:rec {Set} {p₀} {λ (x₆ : Set) → λ (h₇ : U.Init.Prelude.Eq {Set} p₀ x₆) → U.Init.Prelude.Eq {Set} (p₀ → q₂) (x₆ → q₃)} (U.Init.Prelude.Eq:rec {Set} {q₂} {λ (x₆ : Set) → λ (h₇ : U.Init.Prelude.Eq {Set} q₂ x₆) → U.Init.Prelude.Eq {Set} (p₀ → q₂) (p₀ → x₆)} (U.Init.Prelude.rfl {Set} {p₀ → q₂}) {q₃} h₅) {p₁} h₄

-- theorem
opaque
  heq~ueq~ueq : {α₀ : Set} → (a₁ : α₀) → (b₂ : α₀) → U.Init.Prelude.Eq {Set} (U.Init.Prelude.HEq {α₀} a₁ {α₀} b₂) (U.Init.Prelude.Eq {α₀} a₁ b₂)
  heq~ueq~ueq {α₀} a₁ b₂ = U.Init.Core.propext {U.Init.Prelude.HEq {α₀} a₁ {α₀} b₂} {U.Init.Prelude.Eq {α₀} a₁ b₂} (U.Init.Core.Iff:intro {U.Init.Prelude.HEq {α₀} a₁ {α₀} b₂} {U.Init.Prelude.Eq {α₀} a₁ b₂} (U.Init.Prelude.eq~uof~uheq {α₀} {a₁} {b₂}) (U.Init.Prelude.heq~uof~ueq {α₀} {a₁} {b₂}))

-- theorem
opaque
  true~uand : (p₀ : Set) → U.Init.Prelude.Eq {Set} (U.Init.Prelude.And U.Init.Prelude.True p₀) p₀
  true~uand p₀ = U.Init.Core.propext {U.Init.Prelude.And U.Init.Prelude.True p₀} {p₀} (U.Init.Core.Iff:intro {U.Init.Prelude.And U.Init.Prelude.True p₀} {p₀} (λ (x₁ : U.Init.Prelude.And U.Init.Prelude.True p₀) → U.Init.Prelude.And:right {U.Init.Prelude.True} {p₀} x₁) (λ (x₁ : p₀) → U.Init.Prelude.And:intro {U.Init.Prelude.True} {p₀} U.Init.Core.trivial x₁))
