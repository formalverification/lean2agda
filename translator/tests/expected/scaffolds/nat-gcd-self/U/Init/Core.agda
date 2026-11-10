{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of Nat:gcd~uself
-- Lean module Init.Core
module U.Init.Core where
import U.Init.Prelude

Decidable:byCases:match~u1 : {p₀ : Set} → (motive₁ : U.Init.Prelude.Decidable p₀ → Set) → (dec₂ : U.Init.Prelude.Decidable p₀) → ((h₃ : p₀) → motive₁ (U.Init.Prelude.Decidable:isTrue {p₀} h₃)) → ((h₃ : U.Init.Prelude.Not p₀) → motive₁ (U.Init.Prelude.Decidable:isFalse {p₀} h₃)) → motive₁ dec₂
Decidable:byCases:match~u1 {p₀} motive₁ dec₂ h1₃ h2₄ = U.Init.Prelude.Decidable:casesOn {p₀} {λ (x₅ : U.Init.Prelude.Decidable p₀) → motive₁ x₅} dec₂ (λ (h₅ : U.Init.Prelude.Not p₀) → h2₄ h₅) (λ (h₅ : p₀) → h1₃ h₅)

Decidable:byCases : {p₀ : Set} → {q₁ : Set} → ⦃ _ : U.Init.Prelude.Decidable p₀ ⦄ → (p₀ → q₁) → (U.Init.Prelude.Not p₀ → q₁) → q₁
Decidable:byCases {p₀} {q₁} ⦃ dec₂ ⦄ h1₃ h2₄ = Decidable:byCases:match~u1 {p₀} (λ (dec₅ : U.Init.Prelude.Decidable p₀) → q₁) dec₂ (λ (h₅ : p₀) → h1₃ h₅) (λ (h₅ : U.Init.Prelude.Not p₀) → h2₄ h₅)

-- theorem
opaque
  Decidable:em : (p₀ : Set) → ⦃ _ : U.Init.Prelude.Decidable p₀ ⦄ → U.Init.Prelude.Or p₀ (U.Init.Prelude.Not p₀)
  Decidable:em p₀ ⦃ inst₁ ⦄ = Decidable:byCases {p₀} {U.Init.Prelude.Or p₀ (U.Init.Prelude.Not p₀)} ⦃ inst₁ ⦄ (U.Init.Prelude.Or:inl {p₀} {U.Init.Prelude.Not p₀}) (U.Init.Prelude.Or:inr {p₀} {U.Init.Prelude.Not p₀})

Eq:mpr : {α₀ : Set} → {β₁ : Set} → U.Init.Prelude.Eq {Set} α₀ β₁ → β₁ → α₀
Eq:mpr {α₀} {β₁} h₂ b₃ = U.Init.Prelude.Eq:rec {Set} {β₁} {λ (x₄ : Set) → λ (h₅ : U.Init.Prelude.Eq {Set} β₁ x₄) → x₄} b₃ {α₀} (U.Init.Prelude.Eq:symm {Set} {α₀} {β₁} h₂)

record Iff (a₀ : Set) (b₁ : Set) : Set where
  constructor Iff:intro
  field
    mp₂ : a₀ → b₁
    mpr₃ : b₁ → a₀

postulate Iff:rec : {a₀ : Set} → {b₁ : Set} → {motive₂ : Iff a₀ b₁ → Set} → ((mp₃ : a₀ → b₁) → (mpr₄ : b₁ → a₀) → motive₂ (Iff:intro {a₀} {b₁} mp₃ mpr₄)) → (t₃ : Iff a₀ b₁) → motive₂ t₃

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

postulate propext : {a₀ : Set} → {b₁ : Set} → Iff a₀ b₁ → U.Init.Prelude.Eq {Set} a₀ b₁

-- theorem
opaque
  trivial : U.Init.Prelude.True
  trivial = U.Init.Prelude.True:intro

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

iteInduction : {α₀ : Set} → {c₁ : Set} → ⦃ inst₂ : U.Init.Prelude.Decidable c₁ ⦄ → {motive₃ : α₀ → Set} → {t₄ : α₀} → {e₅ : α₀} → (c₁ → motive₃ t₄) → (U.Init.Prelude.Not c₁ → motive₃ e₅) → motive₃ (U.Init.Prelude.ite {α₀} c₁ ⦃ inst₂ ⦄ t₄ e₅)
iteInduction {α₀} {c₁} ⦃ inst₂ ⦄ {motive₃} {t₄} {e₅} hpos₆ hneg₇ = Decidable:byCases:match~u1 {c₁} (λ (inst₈ : U.Init.Prelude.Decidable c₁) → motive₃ (U.Init.Prelude.ite {α₀} c₁ ⦃ inst₈ ⦄ t₄ e₅)) inst₂ (λ (h₈ : c₁) → hpos₆ h₈) (λ (h₈ : U.Init.Prelude.Not c₁) → hneg₇ h₈)
