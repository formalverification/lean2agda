{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of KindFixtures:Marker KindFixtures:Marker:casesOn KindFixtures:Marker:ctorIdx KindFixtures:Marker:mark KindFixtures:Marker:mk and 22 more
-- Lean module TranslatorTests.Input.Kinds
-- refused 5 declarations; refusals.txt names each with its reason
module U.TranslatorTests.Input.Kinds where
import U.Init.Prelude

record KindFixtures:Marker (α₀ : Set) : Set where
  constructor KindFixtures:Marker:mk
  field
    mark₁ : α₀

postulate KindFixtures:Marker:rec : {α₀ : Set} → {motive₁ : KindFixtures:Marker α₀ → Set} → ((mark₂ : α₀) → motive₁ (KindFixtures:Marker:mk {α₀} mark₂)) → (t₂ : KindFixtures:Marker α₀) → motive₁ t₂

KindFixtures:Marker:casesOn : {α₀ : Set} → {motive₁ : KindFixtures:Marker α₀ → Set} → (t₂ : KindFixtures:Marker α₀) → ((mark₃ : α₀) → motive₁ (KindFixtures:Marker:mk {α₀} mark₃)) → motive₁ t₂
KindFixtures:Marker:casesOn {α₀} {motive₁} t₂ mk₃ = KindFixtures:Marker:rec {α₀} {motive₁} (λ (mark₄ : α₀) → mk₃ mark₄) t₂

KindFixtures:Marker:ctorIdx : {α₀ : Set} → KindFixtures:Marker α₀ → U.Init.Prelude.Nat
KindFixtures:Marker:ctorIdx {α₀} x₁ = 0

KindFixtures:Marker:mark : {α₀ : Set} → ⦃ _ : KindFixtures:Marker α₀ ⦄ → α₀
KindFixtures:Marker:mark {α₀} ⦃ self₁ ⦄ = KindFixtures:Marker.mark₁ {α₀} self₁

KindFixtures:Marker:mk:~uflat~uctor : {α₀ : Set} → α₀ → KindFixtures:Marker α₀
KindFixtures:Marker:mk:~uflat~uctor {α₀} mark₁ = KindFixtures:Marker:mk {α₀} mark₁

KindFixtures:Marker:noConfusionType : Set → {α₀ : Set} → KindFixtures:Marker α₀ → {α₁ : Set} → KindFixtures:Marker α₁ → Set
KindFixtures:Marker:noConfusionType P₀ {α₁} t₂ {α₃} t₄ = KindFixtures:Marker:casesOn {α₁} {λ (t₅ : KindFixtures:Marker α₁) → Set} t₂ (λ (mark₅ : α₁) → KindFixtures:Marker:casesOn {α₃} {λ (t₆ : KindFixtures:Marker α₃) → Set} t₄ (λ (mark₆ : α₃) → (U.Init.Prelude.HEq {α₁} mark₅ {α₃} mark₆ → P₀) → P₀))

KindFixtures:Marker:noConfusion : {P₀ : Set} → {α₁ : Set} → {t₂ : KindFixtures:Marker α₁} → {α₃ : Set} → {t₄ : KindFixtures:Marker α₃} → U.Init.Prelude.Eq {Set} α₁ α₃ → U.Init.Prelude.HEq {KindFixtures:Marker α₁} t₂ {KindFixtures:Marker α₃} t₄ → KindFixtures:Marker:noConfusionType P₀ {α₁} t₂ {α₃} t₄
KindFixtures:Marker:noConfusion {P₀} {α₁} {t₂} {α₃} {t₄} eq1₅ eq2₆ = U.Init.Prelude.Eq:ndrec {Set} {α₁} {λ (α₇ : Set) → {t₈ : KindFixtures:Marker α₇} → U.Init.Prelude.HEq {KindFixtures:Marker α₁} t₂ {KindFixtures:Marker α₇} t₈ → KindFixtures:Marker:noConfusionType P₀ {α₁} t₂ {α₇} t₈} (λ {t₇ : KindFixtures:Marker α₁} → λ (eq2₈ : U.Init.Prelude.HEq {KindFixtures:Marker α₁} t₂ {KindFixtures:Marker α₁} t₇) → U.Init.Prelude.Eq:ndrec {KindFixtures:Marker α₁} {t₂} {λ (t₉ : KindFixtures:Marker α₁) → KindFixtures:Marker:noConfusionType P₀ {α₁} t₂ {α₁} t₉} (KindFixtures:Marker:casesOn {α₁} {λ (t₉ : KindFixtures:Marker α₁) → KindFixtures:Marker:noConfusionType P₀ {α₁} t₉ {α₁} t₉} t₂ (λ (mark₉ : α₁) → λ (k₁₀ : U.Init.Prelude.HEq {α₁} mark₉ {α₁} mark₉ → P₀) → k₁₀ (U.Init.Prelude.HEq:refl {α₁} mark₉))) {t₇} (U.Init.Prelude.eq~uof~uheq {KindFixtures:Marker α₁} {t₂} {t₇} eq2₈)) {α₃} eq1₅ {t₄} eq2₆

KindFixtures:Marker:mk:noConfusion : {α₀ : Set} → {P₁ : Set} → {mark₂ : α₀} → {mark₃ : α₀} → U.Init.Prelude.Eq {KindFixtures:Marker α₀} (KindFixtures:Marker:mk {α₀} mark₂) (KindFixtures:Marker:mk {α₀} mark₃) → (U.Init.Prelude.HEq {α₀} mark₂ {α₀} mark₃ → P₁) → P₁
KindFixtures:Marker:mk:noConfusion {α₀} {P₁} {mark₂} {mark₃} eq₄ k₅ = U.Init.Prelude.id {P₁} (KindFixtures:Marker:noConfusion {P₁} {α₀} {KindFixtures:Marker:mk {α₀} mark₂} {α₀} {KindFixtures:Marker:mk {α₀} mark₃} (U.Init.Prelude.Eq:refl {Set} α₀) (U.Init.Prelude.heq~uof~ueq {KindFixtures:Marker α₀} {KindFixtures:Marker:mk {α₀} mark₂} {KindFixtures:Marker:mk {α₀} mark₃} eq₄) k₅)

KindFixtures:Marker:recOn : {α₀ : Set} → {motive₁ : KindFixtures:Marker α₀ → Set} → (t₂ : KindFixtures:Marker α₀) → ((mark₃ : α₀) → motive₁ (KindFixtures:Marker:mk {α₀} mark₃)) → motive₁ t₂
KindFixtures:Marker:recOn {α₀} {motive₁} t₂ mk₃ = KindFixtures:Marker:rec {α₀} {motive₁} mk₃ t₂

postulate KindFixtures:Q : U.Init.Prelude.Eq {U.Init.Prelude.Nat} U.Init.Prelude.Nat:zero U.Init.Prelude.Nat:zero → Set

-- theorem
opaque
  KindFixtures:base : U.Init.Prelude.Eq {U.Init.Prelude.Nat} U.Init.Prelude.Nat:zero U.Init.Prelude.Nat:zero
  KindFixtures:base = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {U.Init.Prelude.Nat:zero}

-- theorem
opaque
  KindFixtures:alias : U.Init.Prelude.Eq {U.Init.Prelude.Nat} U.Init.Prelude.Nat:zero U.Init.Prelude.Nat:zero
  KindFixtures:alias = KindFixtures:base

-- opaque constant
opaque
  KindFixtures:hidden : U.Init.Prelude.Nat
  KindFixtures:hidden = U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 5 ⦃ U.Init.Prelude.instOfNatNat 5 ⦄

KindFixtures:instMarkerNat : KindFixtures:Marker U.Init.Prelude.Nat
KindFixtures:instMarkerNat = KindFixtures:Marker:mk {U.Init.Prelude.Nat} (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄)

-- opaque constant
opaque
  KindFixtures:loop : U.Init.Prelude.Nat → U.Init.Prelude.Nat
  KindFixtures:loop n₀ = let inst₁ : U.Init.Prelude.Inhabited U.Init.Prelude.Nat; inst₁ = U.Init.Prelude.Inhabited:mk {U.Init.Prelude.Nat} n₀ in U.Init.Prelude.Inhabited:default {U.Init.Prelude.Nat} ⦃ inst₁ ⦄

-- cyclic definition, postulated
postulate KindFixtures:loop:~uunsafe~urec : U.Init.Prelude.Nat → U.Init.Prelude.Nat

KindFixtures:plain : U.Init.Prelude.Nat → U.Init.Prelude.Nat
KindFixtures:plain n₀ = U.Init.Prelude.Nat:add n₀ KindFixtures:hidden

KindFixtures:useBase : KindFixtures:Q KindFixtures:base → U.Init.Prelude.Nat
KindFixtures:useBase x₀ = U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄

KindFixtures:useAlias : KindFixtures:Q KindFixtures:alias → U.Init.Prelude.Nat
KindFixtures:useAlias q₀ = KindFixtures:useBase q₀

KindFixtures:useMark : U.Init.Prelude.Nat
KindFixtures:useMark = KindFixtures:Marker:mark {U.Init.Prelude.Nat} ⦃ KindFixtures:instMarkerNat ⦄
