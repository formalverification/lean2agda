{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of ArithmeticFixtures:add~uone ArithmeticFixtures:add~usucc ArithmeticFixtures:add~uzero ArithmeticFixtures:beq~usucc~usucc ArithmeticFixtures:beq~usucc~uzero and 49 more
-- Lean module Init.SimpLemmas
module U.Init.SimpLemmas where
import U.Init.Core
import U.Init.Prelude

-- theorem
opaque
  ite~uself : {α₀ : Set} → {c₁ : Set} → {d₂ : U.Init.Prelude.Decidable c₁} → (a₃ : α₀) → U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} c₁ ⦃ d₂ ⦄ a₃ a₃) a₃
  ite~uself {α₀} {c₁} {d₂} a₃ = U.Init.Prelude.Decidable:casesOn {c₁} {λ (t₄ : U.Init.Prelude.Decidable c₁) → U.Init.Prelude.Eq {U.Init.Prelude.Decidable c₁} d₂ t₄ → U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} c₁ ⦃ d₂ ⦄ a₃ a₃) a₃} d₂ (λ (h₄ : U.Init.Prelude.Not c₁) → λ (h₅ : U.Init.Prelude.Eq {U.Init.Prelude.Decidable c₁} d₂ (U.Init.Prelude.Decidable:isFalse {c₁} h₄)) → U.Init.Prelude.Eq:ndrec {U.Init.Prelude.Decidable c₁} {U.Init.Prelude.Decidable:isFalse {c₁} h₄} {λ (d₆ : U.Init.Prelude.Decidable c₁) → U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} c₁ ⦃ d₆ ⦄ a₃ a₃) a₃} (U.Init.Prelude.Eq:refl {α₀} (U.Init.Prelude.ite {α₀} c₁ ⦃ U.Init.Prelude.Decidable:isFalse {c₁} h₄ ⦄ a₃ a₃)) {d₂} (U.Init.Prelude.Eq:symm {U.Init.Prelude.Decidable c₁} {d₂} {U.Init.Prelude.Decidable:isFalse {c₁} h₄} h₅)) (λ (h₄ : c₁) → λ (h₅ : U.Init.Prelude.Eq {U.Init.Prelude.Decidable c₁} d₂ (U.Init.Prelude.Decidable:isTrue {c₁} h₄)) → U.Init.Prelude.Eq:ndrec {U.Init.Prelude.Decidable c₁} {U.Init.Prelude.Decidable:isTrue {c₁} h₄} {λ (d₆ : U.Init.Prelude.Decidable c₁) → U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} c₁ ⦃ d₆ ⦄ a₃ a₃) a₃} (U.Init.Prelude.Eq:refl {α₀} (U.Init.Prelude.ite {α₀} c₁ ⦃ U.Init.Prelude.Decidable:isTrue {c₁} h₄ ⦄ a₃ a₃)) {d₂} (U.Init.Prelude.Eq:symm {U.Init.Prelude.Decidable c₁} {d₂} {U.Init.Prelude.Decidable:isTrue {c₁} h₄} h₅)) (U.Init.Prelude.Eq:refl {U.Init.Prelude.Decidable c₁} d₂)

-- theorem
opaque
  eq~ufalse : {p₀ : Set} → U.Init.Prelude.Not p₀ → U.Init.Prelude.Eq {Set} p₀ U.Init.Prelude.False
  eq~ufalse {p₀} h₁ = U.Init.Core.propext {p₀} {U.Init.Prelude.False} (U.Init.Core.Iff:intro {p₀} {U.Init.Prelude.False} (λ (h₂ : p₀) → U.Init.Prelude.absurd {p₀} {U.Init.Prelude.False} h₂ h₁) (λ (h₂ : U.Init.Prelude.False) → U.Init.Prelude.False:elim {p₀} h₂))

-- theorem
opaque
  eq~ufalse~x27~ : {p₀ : Set} → (p₀ → U.Init.Prelude.False) → U.Init.Prelude.Eq {Set} p₀ U.Init.Prelude.False
  eq~ufalse~x27~ {p₀} h₁ = eq~ufalse {p₀} h₁

-- theorem
opaque
  eq~utrue : {p₀ : Set} → p₀ → U.Init.Prelude.Eq {Set} p₀ U.Init.Prelude.True
  eq~utrue {p₀} h₁ = U.Init.Core.propext {p₀} {U.Init.Prelude.True} (U.Init.Core.Iff:intro {p₀} {U.Init.Prelude.True} (λ (x₂ : p₀) → U.Init.Core.trivial) (λ (x₂ : U.Init.Prelude.True) → h₁))

-- theorem
opaque
  not~ufalse~ueq~utrue : U.Init.Prelude.Eq {Set} (U.Init.Prelude.Not U.Init.Prelude.False) U.Init.Prelude.True
  not~ufalse~ueq~utrue = eq~utrue {U.Init.Prelude.Not U.Init.Prelude.False} (U.Init.Prelude.False:elim {U.Init.Prelude.False})

-- theorem
opaque
  of~ueq~utrue : {p₀ : Set} → U.Init.Prelude.Eq {Set} p₀ U.Init.Prelude.True → p₀
  of~ueq~utrue {p₀} h₁ = U.Init.Prelude.Eq:rec {Set} {U.Init.Prelude.True} {λ (x₂ : Set) → λ (h₃ : U.Init.Prelude.Eq {Set} U.Init.Prelude.True x₂) → x₂} U.Init.Core.trivial {p₀} (U.Init.Prelude.Eq:symm {Set} {p₀} {U.Init.Prelude.True} h₁)

-- theorem
opaque
  eq~uself : {α₀ : Set} → (a₁ : α₀) → U.Init.Prelude.Eq {Set} (U.Init.Prelude.Eq {α₀} a₁ a₁) U.Init.Prelude.True
  eq~uself {α₀} a₁ = eq~utrue {U.Init.Prelude.Eq {α₀} a₁ a₁} (U.Init.Prelude.rfl {α₀} {a₁})

-- theorem
opaque
  and~ufalse : (p₀ : Set) → U.Init.Prelude.Eq {Set} (U.Init.Prelude.And p₀ U.Init.Prelude.False) U.Init.Prelude.False
  and~ufalse p₀ = eq~ufalse {U.Init.Prelude.And p₀ U.Init.Prelude.False} (λ (x₁ : U.Init.Prelude.And p₀ U.Init.Prelude.False) → U.Init.Prelude.And:right {p₀} {U.Init.Prelude.False} x₁)

-- theorem
opaque
  and~uself : (p₀ : Set) → U.Init.Prelude.Eq {Set} (U.Init.Prelude.And p₀ p₀) p₀
  and~uself p₀ = U.Init.Core.propext {U.Init.Prelude.And p₀ p₀} {p₀} (U.Init.Core.Iff:intro {U.Init.Prelude.And p₀ p₀} {p₀} (λ (x₁ : U.Init.Prelude.And p₀ p₀) → U.Init.Prelude.And:left {p₀} {p₀} x₁) (λ (h₁ : p₀) → U.Init.Prelude.And:intro {p₀} {p₀} h₁ h₁))

-- theorem
opaque
  false~uand : (p₀ : Set) → U.Init.Prelude.Eq {Set} (U.Init.Prelude.And U.Init.Prelude.False p₀) U.Init.Prelude.False
  false~uand p₀ = eq~ufalse {U.Init.Prelude.And U.Init.Prelude.False p₀} (λ (x₁ : U.Init.Prelude.And U.Init.Prelude.False p₀) → U.Init.Prelude.And:left {U.Init.Prelude.False} {p₀} x₁)

-- theorem
opaque
  ite~ucongr : {α₀ : Set} → {b₁ : Set} → {c₂ : Set} → {x₃ : α₀} → {y₄ : α₀} → {u₅ : α₀} → {v₆ : α₀} → {s₇ : U.Init.Prelude.Decidable b₁} → ⦃ inst₈ : U.Init.Prelude.Decidable c₂ ⦄ → U.Init.Prelude.Eq {Set} b₁ c₂ → (c₂ → U.Init.Prelude.Eq {α₀} x₃ u₅) → (U.Init.Prelude.Not c₂ → U.Init.Prelude.Eq {α₀} y₄ v₆) → U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} b₁ ⦃ s₇ ⦄ x₃ y₄) (U.Init.Prelude.ite {α₀} c₂ ⦃ inst₈ ⦄ u₅ v₆)
  ite~ucongr {α₀} {b₁} {c₂} {x₃} {y₄} {u₅} {v₆} {s₇} ⦃ inst₈ ⦄ h₉ h₁₀ h₁₁ = U.Init.Prelude.Or:casesOn {c₂} {U.Init.Prelude.Not c₂} {λ (t₁₂ : U.Init.Prelude.Or c₂ (U.Init.Prelude.Not c₂)) → U.Init.Prelude.Eq {U.Init.Prelude.Or c₂ (U.Init.Prelude.Not c₂)} (U.Init.Core.Decidable:em c₂ ⦃ inst₈ ⦄) t₁₂ → U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} b₁ ⦃ s₇ ⦄ x₃ y₄) (U.Init.Prelude.ite {α₀} c₂ ⦃ inst₈ ⦄ u₅ v₆)} (U.Init.Core.Decidable:em c₂ ⦃ inst₈ ⦄) (λ (h₁₂ : c₂) → λ (h₁₃ : U.Init.Prelude.Eq {U.Init.Prelude.Or c₂ (U.Init.Prelude.Not c₂)} (U.Init.Core.Decidable:em c₂ ⦃ inst₈ ⦄) (U.Init.Prelude.Or:inl {c₂} {U.Init.Prelude.Not c₂} h₁₂)) → U.Init.Core.Eq:mpr {U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} b₁ ⦃ s₇ ⦄ x₃ y₄) (U.Init.Prelude.ite {α₀} c₂ ⦃ inst₈ ⦄ u₅ v₆)} {U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} b₁ ⦃ s₇ ⦄ x₃ y₄) u₅} (U.Init.Prelude.id {U.Init.Prelude.Eq {Set} (U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} b₁ ⦃ s₇ ⦄ x₃ y₄) (U.Init.Prelude.ite {α₀} c₂ ⦃ inst₈ ⦄ u₅ v₆)) (U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} b₁ ⦃ s₇ ⦄ x₃ y₄) u₅)} (U.Init.Prelude.congrArg {α₀} {Set} {U.Init.Prelude.ite {α₀} c₂ ⦃ inst₈ ⦄ u₅ v₆} {u₅} (λ (a₁₄ : α₀) → U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} b₁ ⦃ s₇ ⦄ x₃ y₄) a₁₄) (U.Init.Core.if~upos {c₂} {inst₈} h₁₂ {α₀} {u₅} {v₆}))) (U.Init.Prelude.Eq:ndrec {Set} {c₂} {λ (b₁₄ : Set) → {s₁₅ : U.Init.Prelude.Decidable b₁₄} → U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} b₁₄ ⦃ s₁₅ ⦄ x₃ y₄) u₅} (λ {s₁₄ : U.Init.Prelude.Decidable c₂} → U.Init.Core.Eq:mpr {U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} c₂ ⦃ s₁₄ ⦄ x₃ y₄) u₅} {U.Init.Prelude.Eq {α₀} x₃ u₅} (U.Init.Prelude.id {U.Init.Prelude.Eq {Set} (U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} c₂ ⦃ s₁₄ ⦄ x₃ y₄) u₅) (U.Init.Prelude.Eq {α₀} x₃ u₅)} (U.Init.Prelude.congrArg {α₀} {Set} {U.Init.Prelude.ite {α₀} c₂ ⦃ s₁₄ ⦄ x₃ y₄} {x₃} (λ (a₁₅ : α₀) → U.Init.Prelude.Eq {α₀} a₁₅ u₅) (U.Init.Core.if~upos {c₂} {s₁₄} h₁₂ {α₀} {x₃} {y₄}))) (h₁₀ h₁₂)) {b₁} (U.Init.Prelude.Eq:symm {Set} {b₁} {c₂} h₉) {s₇})) (λ (h₁₂ : U.Init.Prelude.Not c₂) → λ (h₁₃ : U.Init.Prelude.Eq {U.Init.Prelude.Or c₂ (U.Init.Prelude.Not c₂)} (U.Init.Core.Decidable:em c₂ ⦃ inst₈ ⦄) (U.Init.Prelude.Or:inr {c₂} {U.Init.Prelude.Not c₂} h₁₂)) → U.Init.Core.Eq:mpr {U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} b₁ ⦃ s₇ ⦄ x₃ y₄) (U.Init.Prelude.ite {α₀} c₂ ⦃ inst₈ ⦄ u₅ v₆)} {U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} b₁ ⦃ s₇ ⦄ x₃ y₄) v₆} (U.Init.Prelude.id {U.Init.Prelude.Eq {Set} (U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} b₁ ⦃ s₇ ⦄ x₃ y₄) (U.Init.Prelude.ite {α₀} c₂ ⦃ inst₈ ⦄ u₅ v₆)) (U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} b₁ ⦃ s₇ ⦄ x₃ y₄) v₆)} (U.Init.Prelude.congrArg {α₀} {Set} {U.Init.Prelude.ite {α₀} c₂ ⦃ inst₈ ⦄ u₅ v₆} {v₆} (λ (a₁₄ : α₀) → U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} b₁ ⦃ s₇ ⦄ x₃ y₄) a₁₄) (U.Init.Core.if~uneg {c₂} {inst₈} h₁₂ {α₀} {u₅} {v₆}))) (U.Init.Prelude.Eq:ndrec {Set} {c₂} {λ (b₁₄ : Set) → {s₁₅ : U.Init.Prelude.Decidable b₁₄} → U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} b₁₄ ⦃ s₁₅ ⦄ x₃ y₄) v₆} (λ {s₁₄ : U.Init.Prelude.Decidable c₂} → U.Init.Core.Eq:mpr {U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} c₂ ⦃ s₁₄ ⦄ x₃ y₄) v₆} {U.Init.Prelude.Eq {α₀} y₄ v₆} (U.Init.Prelude.id {U.Init.Prelude.Eq {Set} (U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} c₂ ⦃ s₁₄ ⦄ x₃ y₄) v₆) (U.Init.Prelude.Eq {α₀} y₄ v₆)} (U.Init.Prelude.congrArg {α₀} {Set} {U.Init.Prelude.ite {α₀} c₂ ⦃ s₁₄ ⦄ x₃ y₄} {y₄} (λ (a₁₅ : α₀) → U.Init.Prelude.Eq {α₀} a₁₅ v₆) (U.Init.Core.if~uneg {c₂} {s₁₄} h₁₂ {α₀} {x₃} {y₄}))) (h₁₁ h₁₂)) {b₁} (U.Init.Prelude.Eq:symm {Set} {b₁} {c₂} h₉) {s₇})) (U.Init.Prelude.Eq:refl {U.Init.Prelude.Or c₂ (U.Init.Prelude.Not c₂)} (U.Init.Core.Decidable:em c₂ ⦃ inst₈ ⦄))

-- theorem
opaque
  ite~ucond~ueq~ufalse : {α₀ : Set} → {c₁ : Set} → {x₂ : U.Init.Prelude.Decidable c₁} → (a₃ : α₀) → (b₄ : α₀) → U.Init.Prelude.Eq {Set} c₁ U.Init.Prelude.False → U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} c₁ ⦃ x₂ ⦄ a₃ b₄) b₄
  ite~ucond~ueq~ufalse {α₀} {c₁} {x₂} a₃ b₄ h₅ = of~ueq~utrue {U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} c₁ ⦃ x₂ ⦄ a₃ b₄) b₄} (U.Init.Prelude.Eq:trans {Set} {U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} c₁ ⦃ x₂ ⦄ a₃ b₄) b₄} {U.Init.Prelude.Eq {α₀} b₄ b₄} {U.Init.Prelude.True} (U.Init.Prelude.congrFun~x27~ {α₀} {Set} {U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} c₁ ⦃ x₂ ⦄ a₃ b₄)} {U.Init.Prelude.Eq {α₀} b₄} (U.Init.Prelude.congrArg {α₀} {α₀ → Set} {U.Init.Prelude.ite {α₀} c₁ ⦃ x₂ ⦄ a₃ b₄} {b₄} (U.Init.Prelude.Eq {α₀}) (ite~ucongr {α₀} {c₁} {U.Init.Prelude.False} {a₃} {b₄} {a₃} {b₄} {x₂} ⦃ U.Init.Core.instDecidableFalse ⦄ h₅ (λ (a₆ : U.Init.Prelude.False) → U.Init.Prelude.Eq:refl {α₀} a₃) (λ (a₆ : U.Init.Prelude.Not U.Init.Prelude.False) → U.Init.Prelude.Eq:refl {α₀} b₄))) b₄) (eq~uself {α₀} b₄))

-- theorem
opaque
  ite~ucond~ueq~utrue : {α₀ : Set} → {c₁ : Set} → {x₂ : U.Init.Prelude.Decidable c₁} → (a₃ : α₀) → (b₄ : α₀) → U.Init.Prelude.Eq {Set} c₁ U.Init.Prelude.True → U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} c₁ ⦃ x₂ ⦄ a₃ b₄) a₃
  ite~ucond~ueq~utrue {α₀} {c₁} {x₂} a₃ b₄ h₅ = of~ueq~utrue {U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} c₁ ⦃ x₂ ⦄ a₃ b₄) a₃} (U.Init.Prelude.Eq:trans {Set} {U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} c₁ ⦃ x₂ ⦄ a₃ b₄) a₃} {U.Init.Prelude.Eq {α₀} a₃ a₃} {U.Init.Prelude.True} (U.Init.Prelude.congrFun~x27~ {α₀} {Set} {U.Init.Prelude.Eq {α₀} (U.Init.Prelude.ite {α₀} c₁ ⦃ x₂ ⦄ a₃ b₄)} {U.Init.Prelude.Eq {α₀} a₃} (U.Init.Prelude.congrArg {α₀} {α₀ → Set} {U.Init.Prelude.ite {α₀} c₁ ⦃ x₂ ⦄ a₃ b₄} {a₃} (U.Init.Prelude.Eq {α₀}) (ite~ucongr {α₀} {c₁} {U.Init.Prelude.True} {a₃} {b₄} {a₃} {b₄} {x₂} ⦃ U.Init.Core.instDecidableTrue ⦄ h₅ (λ (a₆ : U.Init.Prelude.True) → U.Init.Prelude.Eq:refl {α₀} a₃) (λ (a₆ : U.Init.Prelude.Not U.Init.Prelude.True) → U.Init.Prelude.Eq:refl {α₀} b₄))) a₃) (eq~uself {α₀} a₃))
