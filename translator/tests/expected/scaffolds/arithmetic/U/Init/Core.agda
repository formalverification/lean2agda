{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of ArithmeticFixtures:add~uone ArithmeticFixtures:add~usucc ArithmeticFixtures:add~uzero ArithmeticFixtures:beq~usucc~usucc ArithmeticFixtures:beq~usucc~uzero and 49 more
-- Lean module Init.Core
module U.Init.Core where
import U.Init.Prelude

InvImage : {α₀ : Set} → {β₁ : Set} → (β₁ → β₁ → Set) → (α₀ → β₁) → α₀ → α₀ → Set
InvImage {α₀} {β₁} r₂ f₃ a₄ a₅ = r₂ (f₃ a₄) (f₃ a₅)

record PSigma {α₀ : Set} (β₁ : α₀ → Set) : Set where
  constructor PSigma:mk
  field
    fst₂ : α₀
    snd₃ : β₁ fst₂

-- recursor
PSigma:rec : {α₀ : Set} → {β₁ : α₀ → Set} → {motive₂ : PSigma {α₀} β₁ → Set} → ((fst₃ : α₀) → (snd₄ : β₁ fst₃) → motive₂ (PSigma:mk {α₀} {β₁} fst₃ snd₄)) → (t₃ : PSigma {α₀} β₁) → motive₂ t₃
PSigma:rec {α₀} {β₁} {motive₂} mk₃ (PSigma:mk fst₄ snd₅) = mk₃ fst₄ snd₅

PSigma:casesOn : {α₀ : Set} → {β₁ : α₀ → Set} → {motive₂ : PSigma {α₀} β₁ → Set} → (t₃ : PSigma {α₀} β₁) → ((fst₄ : α₀) → (snd₅ : β₁ fst₄) → motive₂ (PSigma:mk {α₀} {β₁} fst₄ snd₅)) → motive₂ t₃
PSigma:casesOn {α₀} {β₁} {motive₂} t₃ mk₄ = PSigma:rec {α₀} {β₁} {motive₂} (λ (fst₅ : α₀) → λ (snd₆ : β₁ fst₅) → mk₄ fst₅ snd₆) t₃

Eq:mpr : {α₀ : Set} → {β₁ : Set} → U.Init.Prelude.Eq {Set} α₀ β₁ → β₁ → α₀
Eq:mpr {α₀} {β₁} h₂ b₃ = U.Init.Prelude.Eq:rec {Set} {β₁} {λ (x₄ : Set) → λ (h₅ : U.Init.Prelude.Eq {Set} β₁ x₄) → x₄} b₃ {α₀} (U.Init.Prelude.Eq:symm {Set} {α₀} {β₁} h₂)

record Exists {α₀ : Set} (p₁ : α₀ → Set) : Set where
  constructor Exists:intro
  field
    w₂ : α₀
    h₃ : p₁ w₂

-- recursor
Exists:rec : {α₀ : Set} → {p₁ : α₀ → Set} → {motive₂ : Exists {α₀} p₁ → Set} → ((w₃ : α₀) → (h₄ : p₁ w₃) → motive₂ (Exists:intro {α₀} {p₁} w₃ h₄)) → (t₃ : Exists {α₀} p₁) → motive₂ t₃
Exists:rec {α₀} {p₁} {motive₂} intro₃ (Exists:intro w₄ h₅) = intro₃ w₄ h₅

Ne : {α₀ : Set} → α₀ → α₀ → Set
Ne {α₀} a₁ b₂ = U.Init.Prelude.Not (U.Init.Prelude.Eq {α₀} a₁ b₂)

record Iff (a₀ : Set) (b₁ : Set) : Set where
  constructor Iff:intro
  field
    mp₂ : a₀ → b₁
    mpr₃ : b₁ → a₀

-- recursor
Iff:rec : {a₀ : Set} → {b₁ : Set} → {motive₂ : Iff a₀ b₁ → Set} → ((mp₃ : a₀ → b₁) → (mpr₄ : b₁ → a₀) → motive₂ (Iff:intro {a₀} {b₁} mp₃ mpr₄)) → (t₃ : Iff a₀ b₁) → motive₂ t₃
Iff:rec {a₀} {b₁} {motive₂} intro₃ (Iff:intro mp₄ mpr₅) = intro₃ mp₄ mpr₅

postulate propext : {a₀ : Set} → {b₁ : Set} → Iff a₀ b₁ → U.Init.Prelude.Eq {Set} a₀ b₁

-- theorem
opaque
  trivial : U.Init.Prelude.True
  trivial = U.Init.Prelude.True:intro

Exists:casesOn : {α₀ : Set} → {p₁ : α₀ → Set} → {motive₂ : Exists {α₀} p₁ → Set} → (t₃ : Exists {α₀} p₁) → ((w₄ : α₀) → (h₅ : p₁ w₄) → motive₂ (Exists:intro {α₀} {p₁} w₄ h₅)) → motive₂ t₃
Exists:casesOn {α₀} {p₁} {motive₂} t₃ intro₄ = Exists:rec {α₀} {p₁} {motive₂} (λ (w₅ : α₀) → λ (h₆ : p₁ w₅) → intro₄ w₅ h₆) t₃

~uprivate:Init:Core:~n0:dif~uneg:match~u1~u1 : {c₀ : Set} → (motive₁ : U.Init.Prelude.Decidable c₀ → Set) → (h₂ : U.Init.Prelude.Decidable c₀) → ((hc₃ : c₀) → motive₁ (U.Init.Prelude.Decidable:isTrue {c₀} hc₃)) → ((h₃ : U.Init.Prelude.Not c₀) → motive₁ (U.Init.Prelude.Decidable:isFalse {c₀} h₃)) → motive₁ h₂
~uprivate:Init:Core:~n0:dif~uneg:match~u1~u1 {c₀} motive₁ h₂ h1₃ h2₄ = U.Init.Prelude.Decidable:casesOn {c₀} {λ (x₅ : U.Init.Prelude.Decidable c₀) → motive₁ x₅} h₂ (λ (h₅ : U.Init.Prelude.Not c₀) → h2₄ h₅) (λ (h₅ : c₀) → h1₃ h₅)

-- theorem
opaque
  dif~uneg : {c₀ : Set} → {h₁ : U.Init.Prelude.Decidable c₀} → (hnc₂ : U.Init.Prelude.Not c₀) → {α₃ : Set} → {t₄ : c₀ → α₃} → {e₅ : U.Init.Prelude.Not c₀ → α₃} → U.Init.Prelude.Eq {α₃} (U.Init.Prelude.dite {α₃} c₀ ⦃ h₁ ⦄ t₄ e₅) (e₅ hnc₂)
  dif~uneg {c₀} {h₁} hnc₂ {α₃} {t₄} {e₅} = ~uprivate:Init:Core:~n0:dif~uneg:match~u1~u1 {c₀} (λ (h₆ : U.Init.Prelude.Decidable c₀) → U.Init.Prelude.Eq {α₃} (U.Init.Prelude.dite {α₃} c₀ ⦃ h₆ ⦄ t₄ e₅) (e₅ hnc₂)) h₁ (λ (hc₆ : c₀) → U.Init.Prelude.absurd {c₀} {U.Init.Prelude.Eq {α₃} (U.Init.Prelude.dite {α₃} c₀ ⦃ U.Init.Prelude.Decidable:isTrue {c₀} hc₆ ⦄ t₄ e₅) (e₅ hnc₂)} hc₆ hnc₂) (λ (h₆ : U.Init.Prelude.Not c₀) → U.Init.Prelude.rfl {α₃} {U.Init.Prelude.dite {α₃} c₀ ⦃ U.Init.Prelude.Decidable:isFalse {c₀} h₆ ⦄ t₄ e₅})

~uprivate:Init:Core:~n0:dif~upos:match~u1~u1 : {c₀ : Set} → (motive₁ : U.Init.Prelude.Decidable c₀ → Set) → (h₂ : U.Init.Prelude.Decidable c₀) → ((h₃ : c₀) → motive₁ (U.Init.Prelude.Decidable:isTrue {c₀} h₃)) → ((hnc₃ : U.Init.Prelude.Not c₀) → motive₁ (U.Init.Prelude.Decidable:isFalse {c₀} hnc₃)) → motive₁ h₂
~uprivate:Init:Core:~n0:dif~upos:match~u1~u1 {c₀} motive₁ h₂ h1₃ h2₄ = U.Init.Prelude.Decidable:casesOn {c₀} {λ (x₅ : U.Init.Prelude.Decidable c₀) → motive₁ x₅} h₂ (λ (h₅ : U.Init.Prelude.Not c₀) → h2₄ h₅) (λ (h₅ : c₀) → h1₃ h₅)

-- theorem
opaque
  dif~upos : {c₀ : Set} → {h₁ : U.Init.Prelude.Decidable c₀} → (hc₂ : c₀) → {α₃ : Set} → {t₄ : c₀ → α₃} → {e₅ : U.Init.Prelude.Not c₀ → α₃} → U.Init.Prelude.Eq {α₃} (U.Init.Prelude.dite {α₃} c₀ ⦃ h₁ ⦄ t₄ e₅) (t₄ hc₂)
  dif~upos {c₀} {h₁} hc₂ {α₃} {t₄} {e₅} = ~uprivate:Init:Core:~n0:dif~upos:match~u1~u1 {c₀} (λ (h₆ : U.Init.Prelude.Decidable c₀) → U.Init.Prelude.Eq {α₃} (U.Init.Prelude.dite {α₃} c₀ ⦃ h₆ ⦄ t₄ e₅) (t₄ hc₂)) h₁ (λ (h₆ : c₀) → U.Init.Prelude.rfl {α₃} {U.Init.Prelude.dite {α₃} c₀ ⦃ U.Init.Prelude.Decidable:isTrue {c₀} h₆ ⦄ t₄ e₅}) (λ (hnc₆ : U.Init.Prelude.Not c₀) → U.Init.Prelude.absurd {c₀} {U.Init.Prelude.Eq {α₃} (U.Init.Prelude.dite {α₃} c₀ ⦃ U.Init.Prelude.Decidable:isFalse {c₀} hnc₆ ⦄ t₄ e₅) (t₄ hc₂)} hc₂ hnc₆)

-- theorem
opaque
  not~ufalse : U.Init.Prelude.Not U.Init.Prelude.False
  not~ufalse = U.Init.Prelude.id {U.Init.Prelude.False}

instDecidableFalse : U.Init.Prelude.Decidable U.Init.Prelude.False
instDecidableFalse = U.Init.Prelude.Decidable:isFalse {U.Init.Prelude.False} not~ufalse

Decidable:byCases:match~u1 : {p₀ : Set} → (motive₁ : U.Init.Prelude.Decidable p₀ → Set) → (dec₂ : U.Init.Prelude.Decidable p₀) → ((h₃ : p₀) → motive₁ (U.Init.Prelude.Decidable:isTrue {p₀} h₃)) → ((h₃ : U.Init.Prelude.Not p₀) → motive₁ (U.Init.Prelude.Decidable:isFalse {p₀} h₃)) → motive₁ dec₂
Decidable:byCases:match~u1 {p₀} motive₁ dec₂ h1₃ h2₄ = U.Init.Prelude.Decidable:casesOn {p₀} {λ (x₅ : U.Init.Prelude.Decidable p₀) → motive₁ x₅} dec₂ (λ (h₅ : U.Init.Prelude.Not p₀) → h2₄ h₅) (λ (h₅ : p₀) → h1₃ h₅)

Decidable:byCases : {p₀ : Set} → {q₁ : Set} → ⦃ _ : U.Init.Prelude.Decidable p₀ ⦄ → (p₀ → q₁) → (U.Init.Prelude.Not p₀ → q₁) → q₁
Decidable:byCases {p₀} {q₁} ⦃ dec₂ ⦄ h1₃ h2₄ = Decidable:byCases:match~u1 {p₀} (λ (dec₅ : U.Init.Prelude.Decidable p₀) → q₁) dec₂ (λ (h₅ : p₀) → h1₃ h₅) (λ (h₅ : U.Init.Prelude.Not p₀) → h2₄ h₅)

-- theorem
opaque
  Decidable:em : (p₀ : Set) → ⦃ _ : U.Init.Prelude.Decidable p₀ ⦄ → U.Init.Prelude.Or p₀ (U.Init.Prelude.Not p₀)
  Decidable:em p₀ ⦃ inst₁ ⦄ = Decidable:byCases {p₀} {U.Init.Prelude.Or p₀ (U.Init.Prelude.Not p₀)} ⦃ inst₁ ⦄ (U.Init.Prelude.Or:inl {p₀} {U.Init.Prelude.Not p₀}) (U.Init.Prelude.Or:inr {p₀} {U.Init.Prelude.Not p₀})

~uprivate:Init:Core:~n0:if~uneg:match~u1~u1 : {c₀ : Set} → (motive₁ : U.Init.Prelude.Decidable c₀ → Set) → (h₂ : U.Init.Prelude.Decidable c₀) → ((hc₃ : c₀) → motive₁ (U.Init.Prelude.Decidable:isTrue {c₀} hc₃)) → ((h₃ : U.Init.Prelude.Not c₀) → motive₁ (U.Init.Prelude.Decidable:isFalse {c₀} h₃)) → motive₁ h₂
~uprivate:Init:Core:~n0:if~uneg:match~u1~u1 {c₀} motive₁ h₂ h1₃ h2₄ = U.Init.Prelude.Decidable:casesOn {c₀} {λ (x₅ : U.Init.Prelude.Decidable c₀) → motive₁ x₅} h₂ (λ (h₅ : U.Init.Prelude.Not c₀) → h2₄ h₅) (λ (h₅ : c₀) → h1₃ h₅)

-- theorem
opaque
  if~uneg : {c₀ : Set} → {h₁ : U.Init.Prelude.Decidable c₀} → U.Init.Prelude.Not c₀ → {α₂ : Set} → {t₃ : α₂} → {e₄ : α₂} → U.Init.Prelude.Eq {α₂} (U.Init.Prelude.ite {α₂} c₀ ⦃ h₁ ⦄ t₃ e₄) e₄
  if~uneg {c₀} {h₁} hnc₂ {α₃} {t₄} {e₅} = ~uprivate:Init:Core:~n0:if~uneg:match~u1~u1 {c₀} (λ (h₆ : U.Init.Prelude.Decidable c₀) → U.Init.Prelude.Eq {α₃} (U.Init.Prelude.ite {α₃} c₀ ⦃ h₆ ⦄ t₄ e₅) e₅) h₁ (λ (hc₆ : c₀) → U.Init.Prelude.absurd {c₀} {U.Init.Prelude.Eq {α₃} (U.Init.Prelude.ite {α₃} c₀ ⦃ U.Init.Prelude.Decidable:isTrue {c₀} hc₆ ⦄ t₄ e₅) e₅} hc₆ hnc₂) (λ (h₆ : U.Init.Prelude.Not c₀) → U.Init.Prelude.rfl {α₃} {U.Init.Prelude.ite {α₃} c₀ ⦃ U.Init.Prelude.Decidable:isFalse {c₀} h₆ ⦄ t₄ e₅})

~uprivate:Init:Core:~n0:if~upos:match~u1~u1 : {c₀ : Set} → (motive₁ : U.Init.Prelude.Decidable c₀ → Set) → (h₂ : U.Init.Prelude.Decidable c₀) → ((h₃ : c₀) → motive₁ (U.Init.Prelude.Decidable:isTrue {c₀} h₃)) → ((hnc₃ : U.Init.Prelude.Not c₀) → motive₁ (U.Init.Prelude.Decidable:isFalse {c₀} hnc₃)) → motive₁ h₂
~uprivate:Init:Core:~n0:if~upos:match~u1~u1 {c₀} motive₁ h₂ h1₃ h2₄ = U.Init.Prelude.Decidable:casesOn {c₀} {λ (x₅ : U.Init.Prelude.Decidable c₀) → motive₁ x₅} h₂ (λ (h₅ : U.Init.Prelude.Not c₀) → h2₄ h₅) (λ (h₅ : c₀) → h1₃ h₅)

-- theorem
opaque
  if~upos : {c₀ : Set} → {h₁ : U.Init.Prelude.Decidable c₀} → c₀ → {α₂ : Set} → {t₃ : α₂} → {e₄ : α₂} → U.Init.Prelude.Eq {α₂} (U.Init.Prelude.ite {α₂} c₀ ⦃ h₁ ⦄ t₃ e₄) t₃
  if~upos {c₀} {h₁} hc₂ {α₃} {t₄} {e₅} = ~uprivate:Init:Core:~n0:if~upos:match~u1~u1 {c₀} (λ (h₆ : U.Init.Prelude.Decidable c₀) → U.Init.Prelude.Eq {α₃} (U.Init.Prelude.ite {α₃} c₀ ⦃ h₆ ⦄ t₄ e₅) t₄) h₁ (λ (h₆ : c₀) → U.Init.Prelude.rfl {α₃} {U.Init.Prelude.ite {α₃} c₀ ⦃ U.Init.Prelude.Decidable:isTrue {c₀} h₆ ⦄ t₄ e₅}) (λ (hnc₆ : U.Init.Prelude.Not c₀) → U.Init.Prelude.absurd {c₀} {U.Init.Prelude.Eq {α₃} (U.Init.Prelude.ite {α₃} c₀ ⦃ U.Init.Prelude.Decidable:isFalse {c₀} hnc₆ ⦄ t₄ e₅) t₄} hc₂ hnc₆)

instDecidableTrue : U.Init.Prelude.Decidable U.Init.Prelude.True
instDecidableTrue = U.Init.Prelude.Decidable:isTrue {U.Init.Prelude.True} trivial

bne : {α₀ : Set} → ⦃ _ : U.Init.Prelude.BEq α₀ ⦄ → α₀ → α₀ → U.Init.Prelude.Bool
bne {α₀} ⦃ inst₁ ⦄ a₂ b₃ = U.Init.Prelude.Bool:not (U.Init.Prelude.BEq:beq {α₀} ⦃ inst₁ ⦄ a₂ b₃)
