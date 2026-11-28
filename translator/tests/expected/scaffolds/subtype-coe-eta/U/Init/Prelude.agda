{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of Subtype:coe~ueta
-- Lean module Init.Prelude
module U.Init.Prelude where

data Eq {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl : (a₁ : α₀) → Eq {α₀} a₁ a₁
{-# BUILTIN REWRITE Eq #-}

-- recursor
Eq:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → Eq {α₀} a₁ a₂ → Set} → motive₂ a₁ (Eq:refl {α₀} a₁) → {a₃ : α₀} → (t₄ : Eq {α₀} a₁ a₃) → motive₂ a₃ t₄
Eq:rec {α₀} {a₁} {motive₂} refl₃ {_} (Eq:refl _) = refl₃

Eq:casesOn : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → Eq {α₀} a₁ a₂ → Set} → {a₃ : α₀} → (t₄ : Eq {α₀} a₁ a₃) → motive₂ a₁ (Eq:refl {α₀} a₁) → motive₂ a₃ t₄
Eq:casesOn {α₀} {a₁} {motive₂} {a₃} t₄ refl₅ = Eq:rec {α₀} {a₁} {motive₂} refl₅ {a₃} t₄

Eq:ndrec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : α₀ → Set} → motive₂ a₁ → {b₃ : α₀} → Eq {α₀} a₁ b₃ → motive₂ b₃
Eq:ndrec {α₀} {a₁} {motive₂} m₃ {b₄} h₅ = Eq:rec {α₀} {a₁} {λ (x₆ : α₀) → λ (x₇ : Eq {α₀} a₁ x₆) → motive₂ x₆} m₃ {b₄} h₅

rfl : {α₀ : Set} → {a₁ : α₀} → Eq {α₀} a₁ a₁
rfl {α₀} {a₁} = Eq:refl {α₀} a₁

-- theorem
opaque
  Eq:symm : {α₀ : Set} → {a₁ : α₀} → {b₂ : α₀} → Eq {α₀} a₁ b₂ → Eq {α₀} b₂ a₁
  Eq:symm {α₀} {a₁} {b₂} h₃ = Eq:rec {α₀} {a₁} {λ (x₄ : α₀) → λ (h₅ : Eq {α₀} a₁ x₄) → Eq {α₀} x₄ a₁} (rfl {α₀} {a₁}) {b₂} h₃

data HEq {α₀ : Set} : α₀ → {β₁ : Set} → β₁ → Set where
  HEq:refl : (a₁ : α₀) → HEq {α₀} a₁ {α₀} a₁

-- recursor
HEq:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : {β₂ : Set} → (a₃ : β₂) → HEq {α₀} a₁ {β₂} a₃ → Set} → motive₂ {α₀} a₁ (HEq:refl {α₀} a₁) → {β₃ : Set} → {a₄ : β₃} → (t₅ : HEq {α₀} a₁ {β₃} a₄) → motive₂ {β₃} a₄ t₅
HEq:rec {α₀} {a₁} {motive₂} refl₃ {_} {_} (HEq:refl _) = refl₃

record Subtype {α₀ : Set} (p₁ : α₀ → Set) : Set where
  constructor Subtype:mk
  field
    val₂ : α₀
    property₃ : p₁ val₂

-- recursor
Subtype:rec : {α₀ : Set} → {p₁ : α₀ → Set} → {motive₂ : Subtype {α₀} p₁ → Set} → ((val₃ : α₀) → (property₄ : p₁ val₃) → motive₂ (Subtype:mk {α₀} {p₁} val₃ property₄)) → (t₃ : Subtype {α₀} p₁) → motive₂ t₃
Subtype:rec {α₀} {p₁} {motive₂} mk₃ (Subtype:mk val₄ property₅) = mk₃ val₄ property₅

Subtype:casesOn : {α₀ : Set} → {p₁ : α₀ → Set} → {motive₂ : Subtype {α₀} p₁ → Set} → (t₃ : Subtype {α₀} p₁) → ((val₄ : α₀) → (property₅ : p₁ val₄) → motive₂ (Subtype:mk {α₀} {p₁} val₄ property₅)) → motive₂ t₃
Subtype:casesOn {α₀} {p₁} {motive₂} t₃ mk₄ = Subtype:rec {α₀} {p₁} {motive₂} (λ (val₅ : α₀) → λ (property₆ : p₁ val₅) → mk₄ val₅ property₆) t₃

Subtype:val : {α₀ : Set} → {p₁ : α₀ → Set} → Subtype {α₀} p₁ → α₀
Subtype:val {α₀} {p₁} self₂ = Subtype.val₂ {α₀} {p₁} self₂

cast : {α₀ : Set} → {β₁ : Set} → Eq {Set} α₀ β₁ → α₀ → β₁
cast {α₀} {β₁} h₂ a₃ = Eq:rec {Set} {α₀} {λ (x₄ : Set) → λ (x₅ : Eq {Set} α₀ x₄) → x₄} a₃ {β₁} h₂

-- theorem
opaque
  eq~uof~uheq : {α₀ : Set} → {a₁ : α₀} → {a₂ : α₀} → HEq {α₀} a₁ {α₀} a₂ → Eq {α₀} a₁ a₂
  eq~uof~uheq {α₀} {a₁} {a₂} h₃ = let this₄ : (α₄ : Set) → (β₅ : Set) → (a₆ : α₄) → (b₇ : β₅) → HEq {α₄} a₆ {β₅} b₇ → (h₈ : Eq {Set} α₄ β₅) → Eq {β₅} (cast {α₄} {β₅} h₈ a₆) b₇; this₄ = λ (x₄ : Set) → λ (x₅ : Set) → λ (x₆ : x₄) → λ (x₇ : x₅) → λ (h₈ : HEq {x₄} x₆ {x₅} x₇) → HEq:rec {x₄} {x₆} {λ {x₉ : Set} → λ (x₁₀ : x₉) → λ (x₁₁ : HEq {x₄} x₆ {x₉} x₁₀) → (h₁₂ : Eq {Set} x₄ x₉) → Eq {x₉} (cast {x₄} {x₉} h₁₂ x₆) x₁₀} (λ (x₉ : Eq {Set} x₄ x₄) → rfl {x₄} {cast {x₄} {x₄} x₉ x₆}) {x₅} {x₇} h₈ in this₄ α₀ α₀ a₁ a₂ h₃ (rfl {Set} {α₀})
