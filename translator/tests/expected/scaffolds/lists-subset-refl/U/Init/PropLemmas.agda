{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of Lists~x27~:Subset:refl
-- Lean module Init.PropLemmas
module U.Init.PropLemmas where
import U.Init.Core
import U.Init.Prelude

~uprivate:Init:PropLemmas:~n0:or~uimp:match~u1~u1 : {a₀ : Set} → {b₁ : Set} → {c₂ : Set} → (motive₃ : U.Init.Prelude.And (a₀ → c₂) (b₁ → c₂) → Set) → (x₄ : U.Init.Prelude.And (a₀ → c₂) (b₁ → c₂)) → ((ha₅ : a₀ → c₂) → (hb₆ : b₁ → c₂) → motive₃ (U.Init.Prelude.And:intro {a₀ → c₂} {b₁ → c₂} ha₅ hb₆)) → motive₃ x₄
~uprivate:Init:PropLemmas:~n0:or~uimp:match~u1~u1 {a₀} {b₁} {c₂} motive₃ x₄ h1₅ = U.Init.Prelude.And:casesOn {a₀ → c₂} {b₁ → c₂} {λ (x₆ : U.Init.Prelude.And (a₀ → c₂) (b₁ → c₂)) → motive₃ x₆} x₄ (λ (left₆ : a₀ → c₂) → λ (right₇ : b₁ → c₂) → h1₅ left₆ right₇)

-- theorem
opaque
  or~uimp : {a₀ : Set} → {b₁ : Set} → {c₂ : Set} → U.Init.Core.Iff (U.Init.Prelude.Or a₀ b₁ → c₂) (U.Init.Prelude.And (a₀ → c₂) (b₁ → c₂))
  or~uimp {a₀} {b₁} {c₂} = U.Init.Core.Iff:intro {U.Init.Prelude.Or a₀ b₁ → c₂} {U.Init.Prelude.And (a₀ → c₂) (b₁ → c₂)} (λ (h₃ : U.Init.Prelude.Or a₀ b₁ → c₂) → U.Init.Prelude.And:intro {a₀ → c₂} {b₁ → c₂} (U.Init.Prelude.Function:comp {a₀} {U.Init.Prelude.Or a₀ b₁} {c₂} h₃ (U.Init.Prelude.Or:inl {a₀} {b₁})) (U.Init.Prelude.Function:comp {b₁} {U.Init.Prelude.Or a₀ b₁} {c₂} h₃ (U.Init.Prelude.Or:inr {a₀} {b₁}))) (λ (x₃ : U.Init.Prelude.And (a₀ → c₂) (b₁ → c₂)) → ~uprivate:Init:PropLemmas:~n0:or~uimp:match~u1~u1 {a₀} {b₁} {c₂} (λ (x₄ : U.Init.Prelude.And (a₀ → c₂) (b₁ → c₂)) → U.Init.Prelude.Or a₀ b₁ → c₂) x₃ (λ (ha₄ : a₀ → c₂) → λ (hb₅ : b₁ → c₂) → λ (t₆ : U.Init.Prelude.Or a₀ b₁) → U.Init.Prelude.Or:rec {a₀} {b₁} {λ (x₇ : U.Init.Prelude.Or a₀ b₁) → c₂} ha₄ hb₅ t₆))

~uprivate:Init:PropLemmas:~n0:forall~uand:match~u1~u1 : {α₀ : Set} → {p₁ : α₀ → Set} → {q₂ : α₀ → Set} → (motive₃ : U.Init.Prelude.And ((x₃ : α₀) → p₁ x₃) ((x₃ : α₀) → q₂ x₃) → Set) → (x₄ : U.Init.Prelude.And ((x₄ : α₀) → p₁ x₄) ((x₄ : α₀) → q₂ x₄)) → ((h₅ : (x₅ : α₀) → p₁ x₅) → (h₆ : (x₆ : α₀) → q₂ x₆) → motive₃ (U.Init.Prelude.And:intro {(x₇ : α₀) → p₁ x₇} {(x₇ : α₀) → q₂ x₇} h₅ h₆)) → motive₃ x₄
~uprivate:Init:PropLemmas:~n0:forall~uand:match~u1~u1 {α₀} {p₁} {q₂} motive₃ x₄ h1₅ = U.Init.Prelude.And:casesOn {(x₆ : α₀) → p₁ x₆} {(x₆ : α₀) → q₂ x₆} {λ (x₆ : U.Init.Prelude.And ((x₆ : α₀) → p₁ x₆) ((x₆ : α₀) → q₂ x₆)) → motive₃ x₆} x₄ (λ (left₆ : (x₆ : α₀) → p₁ x₆) → λ (right₇ : (x₇ : α₀) → q₂ x₇) → h1₅ left₆ right₇)

-- theorem
opaque
  forall~uand : {α₀ : Set} → {p₁ : α₀ → Set} → {q₂ : α₀ → Set} → U.Init.Core.Iff ((x₃ : α₀) → U.Init.Prelude.And (p₁ x₃) (q₂ x₃)) (U.Init.Prelude.And ((x₃ : α₀) → p₁ x₃) ((x₃ : α₀) → q₂ x₃))
  forall~uand {α₀} {p₁} {q₂} = U.Init.Core.Iff:intro {(x₃ : α₀) → U.Init.Prelude.And (p₁ x₃) (q₂ x₃)} {U.Init.Prelude.And ((x₃ : α₀) → p₁ x₃) ((x₃ : α₀) → q₂ x₃)} (λ (h₃ : (x₃ : α₀) → U.Init.Prelude.And (p₁ x₃) (q₂ x₃)) → U.Init.Prelude.And:intro {(x₄ : α₀) → p₁ x₄} {(x₄ : α₀) → q₂ x₄} (λ (x₄ : α₀) → U.Init.Prelude.And:left {p₁ x₄} {q₂ x₄} (h₃ x₄)) (λ (x₄ : α₀) → U.Init.Prelude.And:right {p₁ x₄} {q₂ x₄} (h₃ x₄))) (λ (x₃ : U.Init.Prelude.And ((x₃ : α₀) → p₁ x₃) ((x₃ : α₀) → q₂ x₃)) → λ (x₄ : α₀) → ~uprivate:Init:PropLemmas:~n0:forall~uand:match~u1~u1 {α₀} {p₁} {q₂} (λ (x₅ : U.Init.Prelude.And ((x₅ : α₀) → p₁ x₅) ((x₅ : α₀) → q₂ x₅)) → U.Init.Prelude.And (p₁ x₄) (q₂ x₄)) x₃ (λ (h₅ : (x₅ : α₀) → p₁ x₅) → λ (h₆ : (x₆ : α₀) → q₂ x₆) → U.Init.Prelude.And:intro {p₁ x₄} {q₂ x₄} (h₅ x₄) (h₆ x₄)))

-- theorem
opaque
  forall~ueq : {α₀ : Set} → {p₁ : α₀ → Set} → {a₂ : α₀} → U.Init.Core.Iff ((a₃ : α₀) → U.Init.Prelude.Eq {α₀} a₃ a₂ → p₁ a₃) (p₁ a₂)
  forall~ueq {α₀} {p₁} {a₂} = U.Init.Core.Iff:intro {(a₃ : α₀) → U.Init.Prelude.Eq {α₀} a₃ a₂ → p₁ a₃} {p₁ a₂} (λ (h₃ : (a₃ : α₀) → U.Init.Prelude.Eq {α₀} a₃ a₂ → p₁ a₃) → h₃ a₂ (U.Init.Prelude.rfl {α₀} {a₂})) (λ (h₃ : p₁ a₂) → λ (x₄ : α₀) → λ (e₅ : U.Init.Prelude.Eq {α₀} x₄ a₂) → U.Init.Prelude.Eq:rec {α₀} {a₂} {λ (x₆ : α₀) → λ (h₇ : U.Init.Prelude.Eq {α₀} a₂ x₆) → p₁ x₆} h₃ {x₄} (U.Init.Prelude.Eq:symm {α₀} {x₄} {a₂} e₅))
