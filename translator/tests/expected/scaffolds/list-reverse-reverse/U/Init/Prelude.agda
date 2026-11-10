{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of List:reverse~ureverse
-- Lean module Init.Prelude
module U.Init.Prelude where

data Eq {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl : (a₁ : α₀) → Eq {α₀} a₁ a₁
{-# BUILTIN REWRITE Eq #-}

postulate Eq:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → Eq {α₀} a₁ a₂ → Set} → motive₂ a₁ (Eq:refl {α₀} a₁) → {a₃ : α₀} → (t₄ : Eq {α₀} a₁ a₃) → motive₂ a₃ t₄

rfl : {α₀ : Set} → {a₁ : α₀} → Eq {α₀} a₁ a₁
rfl {α₀} {a₁} = Eq:refl {α₀} a₁

-- theorem
opaque
  Eq:symm : {α₀ : Set} → {a₁ : α₀} → {b₂ : α₀} → Eq {α₀} a₁ b₂ → Eq {α₀} b₂ a₁
  Eq:symm {α₀} {a₁} {b₂} h₃ = Eq:rec {α₀} {a₁} {λ (x₄ : α₀) → λ (h₅ : Eq {α₀} a₁ x₄) → Eq {α₀} x₄ a₁} (rfl {α₀} {a₁}) {b₂} h₃

-- theorem
opaque
  Eq:trans : {α₀ : Set} → {a₁ : α₀} → {b₂ : α₀} → {c₃ : α₀} → Eq {α₀} a₁ b₂ → Eq {α₀} b₂ c₃ → Eq {α₀} a₁ c₃
  Eq:trans {α₀} {a₁} {b₂} {c₃} h₄ h₅ = Eq:rec {α₀} {b₂} {λ (x₆ : α₀) → λ (h₇ : Eq {α₀} b₂ x₆) → Eq {α₀} a₁ x₆} h₄ {c₃} h₅

data List (α₀ : Set) : Set where
  List:nil : List α₀
  List:cons : α₀ → List α₀ → List α₀

postulate List:rec : {α₀ : Set} → {motive₁ : List α₀ → Set} → motive₁ (List:nil {α₀}) → ((head₂ : α₀) → (tail₃ : List α₀) → motive₁ tail₃ → motive₁ (List:cons {α₀} head₂ tail₃)) → (t₂ : List α₀) → motive₁ t₂

record PProd (α₀ : Set) (β₁ : Set) : Set where
  constructor PProd:mk
  field
    fst₂ : α₀
    snd₃ : β₁

postulate PProd:rec : {α₀ : Set} → {β₁ : Set} → {motive₂ : PProd α₀ β₁ → Set} → ((fst₃ : α₀) → (snd₄ : β₁) → motive₂ (PProd:mk {α₀} {β₁} fst₃ snd₄)) → (t₃ : PProd α₀ β₁) → motive₂ t₃

record PUnit : Set where
  constructor PUnit:unit

postulate PUnit:rec : {motive₀ : PUnit → Set} → motive₀ PUnit:unit → (t₁ : PUnit) → motive₀ t₁

List:below : {α₀ : Set} → {_ : List α₀ → Set} → List α₀ → Set
List:below {α₀} {motive₁} t₂ = List:rec {α₀} {λ (t₃ : List α₀) → Set} PUnit (λ (head₃ : α₀) → λ (tail₄ : List α₀) → λ (tailih₅ : Set) → PProd (motive₁ tail₄) tailih₅) t₂

List:brecOn:go : {α₀ : Set} → {motive₁ : List α₀ → Set} → (t₂ : List α₀) → ((t₃ : List α₀) → List:below {α₀} {motive₁} t₃ → motive₁ t₃) → PProd (motive₁ t₂) (List:below {α₀} {motive₁} t₂)
List:brecOn:go {α₀} {motive₁} t₂ F1₃ = List:rec {α₀} {λ (t₄ : List α₀) → PProd (motive₁ t₄) (List:below {α₀} {motive₁} t₄)} (PProd:mk {motive₁ (List:nil {α₀})} {PUnit} (F1₃ (List:nil {α₀}) PUnit:unit) PUnit:unit) (λ (head₄ : α₀) → λ (tail₅ : List α₀) → λ (tailih₆ : PProd (motive₁ tail₅) (List:below {α₀} {motive₁} tail₅)) → PProd:mk {motive₁ (List:cons {α₀} head₄ tail₅)} {PProd (motive₁ tail₅) (List:below {α₀} {motive₁} tail₅)} (F1₃ (List:cons {α₀} head₄ tail₅) tailih₆) tailih₆) t₂

List:brecOn : {α₀ : Set} → {motive₁ : List α₀ → Set} → (t₂ : List α₀) → ((t₃ : List α₀) → List:below {α₀} {motive₁} t₃ → motive₁ t₃) → motive₁ t₂
List:brecOn {α₀} {motive₁} t₂ F1₃ = PProd.fst₂ {motive₁ t₂} {List:below {α₀} {motive₁} t₂} (List:brecOn:go {α₀} {motive₁} t₂ F1₃)

List:casesOn : {α₀ : Set} → {motive₁ : List α₀ → Set} → (t₂ : List α₀) → motive₁ (List:nil {α₀}) → ((head₃ : α₀) → (tail₄ : List α₀) → motive₁ (List:cons {α₀} head₃ tail₄)) → motive₁ t₂
List:casesOn {α₀} {motive₁} t₂ nil₃ cons₄ = List:rec {α₀} {motive₁} nil₃ (λ (head₅ : α₀) → λ (tail₆ : List α₀) → λ (tailih₇ : motive₁ tail₆) → cons₄ head₅ tail₆) t₂

record True : Set where
  constructor True:intro

postulate True:rec : {motive₀ : True → Set} → motive₀ True:intro → (t₁ : True) → motive₀ t₁

-- theorem
opaque
  congrArg : {α₀ : Set} → {β₁ : Set} → {a₂ : α₀} → {a₃ : α₀} → (f₄ : α₀ → β₁) → Eq {α₀} a₂ a₃ → Eq {β₁} (f₄ a₂) (f₄ a₃)
  congrArg {α₀} {β₁} {a₂} {a₃} f₄ h₅ = Eq:rec {α₀} {a₂} {λ (x₆ : α₀) → λ (h₇ : Eq {α₀} a₂ x₆) → Eq {β₁} (f₄ a₂) (f₄ x₆)} (rfl {β₁} {f₄ a₂}) {a₃} h₅

-- theorem
opaque
  congrFun~x27~ : {α₀ : Set} → {β₁ : Set} → {f₂ : α₀ → β₁} → {g₃ : α₀ → β₁} → Eq {α₀ → β₁} f₂ g₃ → (a₄ : α₀) → Eq {β₁} (f₂ a₄) (g₃ a₄)
  congrFun~x27~ {α₀} {β₁} {f₂} {g₃} h₄ a₅ = Eq:rec {α₀ → β₁} {f₂} {λ (x₆ : α₀ → β₁) → λ (h₇ : Eq {α₀ → β₁} f₂ x₆) → Eq {β₁} (f₂ a₅) (x₆ a₅)} (rfl {β₁} {f₂ a₅}) {g₃} h₄

id : {α₀ : Set} → α₀ → α₀
id {α₀} a₁ = a₁
