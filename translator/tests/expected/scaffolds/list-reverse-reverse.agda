-- File: translator/tests/expected/scaffolds/list-reverse-reverse.agda
{-# OPTIONS --type-in-type #-}
-- lean2agda, profile U: the scaffold of the closure of List:reverse~ureverse
module U.Init.Data.List.Lemmas where

data Eq {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl : (a₁ : α₀) → Eq {α₀} a₁ a₁

postulate Eq:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → Eq {α₀} a₁ a₂ → Set} → motive₂ a₁ (Eq:refl {α₀} a₁) → {a₃ : α₀} → (t₄ : Eq {α₀} a₁ a₃) → motive₂ a₃ t₄

postulate rfl : {α₀ : Set} → {a₁ : α₀} → Eq {α₀} a₁ a₁

postulate Eq:symm : {α₀ : Set} → {a₁ : α₀} → {b₂ : α₀} → Eq {α₀} a₁ b₂ → Eq {α₀} b₂ a₁

postulate Eq:mpr : {α₀ : Set} → {β₁ : Set} → Eq {Set} α₀ β₁ → β₁ → α₀

postulate Eq:trans : {α₀ : Set} → {a₁ : α₀} → {b₂ : α₀} → {c₃ : α₀} → Eq {α₀} a₁ b₂ → Eq {α₀} b₂ c₃ → Eq {α₀} a₁ c₃

record Iff (a₀ : Set) (b₁ : Set) : Set where
  constructor Iff:intro
  field
    mp₂ : a₀ → b₁
    mpr₃ : b₁ → a₀

postulate Iff:rec : {a₀ : Set} → {b₁ : Set} → {motive₂ : Iff a₀ b₁ → Set} → ((mp₃ : a₀ → b₁) → (mpr₄ : b₁ → a₀) → motive₂ (Iff:intro {a₀} {b₁} mp₃ mpr₄)) → (t₃ : Iff a₀ b₁) → motive₂ t₃

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

postulate List:below : {α₀ : Set} → {_ : List α₀ → Set} → List α₀ → Set

postulate List:brecOn:go : {α₀ : Set} → {motive₁ : List α₀ → Set} → (t₂ : List α₀) → ((t₃ : List α₀) → List:below {α₀} {motive₁} t₃ → motive₁ t₃) → PProd (motive₁ t₂) (List:below {α₀} {motive₁} t₂)

postulate List:brecOn : {α₀ : Set} → {motive₁ : List α₀ → Set} → (t₂ : List α₀) → ((t₃ : List α₀) → List:below {α₀} {motive₁} t₃ → motive₁ t₃) → motive₁ t₂

postulate List:casesOn : {α₀ : Set} → {motive₁ : List α₀ → Set} → (t₂ : List α₀) → motive₁ (List:nil {α₀}) → ((head₃ : α₀) → (tail₄ : List α₀) → motive₁ (List:cons {α₀} head₃ tail₄)) → motive₁ t₂

postulate List:reverseAux:match~u1 : {α₀ : Set} → (motive₁ : List α₀ → List α₀ → Set) → (x₂ : List α₀) → (x₃ : List α₀) → ((r₄ : List α₀) → motive₁ (List:nil {α₀}) r₄) → ((a₄ : α₀) → (l₅ : List α₀) → (r₆ : List α₀) → motive₁ (List:cons {α₀} a₄ l₅) r₆) → motive₁ x₂ x₃

postulate List:reverseAux:~uf : {α₀ : Set} → (x₁ : List α₀) → List:below {α₀} {λ (x₂ : List α₀) → List α₀ → List α₀} x₁ → List α₀ → List α₀

postulate List:reverseAux : {α₀ : Set} → List α₀ → List α₀ → List α₀

postulate List:reverse : {α₀ : Set} → List α₀ → List α₀

record True : Set where
  constructor True:intro

postulate True:rec : {motive₀ : True → Set} → motive₀ True:intro → (t₁ : True) → motive₀ t₁

postulate congrArg : {α₀ : Set} → {β₁ : Set} → {a₂ : α₀} → {a₃ : α₀} → (f₄ : α₀ → β₁) → Eq {α₀} a₂ a₃ → Eq {β₁} (f₄ a₂) (f₄ a₃)

postulate congrFun~x27~ : {α₀ : Set} → {β₁ : Set} → {f₂ : α₀ → β₁} → {g₃ : α₀ → β₁} → Eq {α₀ → β₁} f₂ g₃ → (a₄ : α₀) → Eq {β₁} (f₂ a₄) (g₃ a₄)

postulate propext : {a₀ : Set} → {b₁ : Set} → Iff a₀ b₁ → Eq {Set} a₀ b₁

postulate trivial : True

postulate eq~utrue : {p₀ : Set} → p₀ → Eq {Set} p₀ True

postulate eq~uself : {α₀ : Set} → (a₁ : α₀) → Eq {Set} (Eq {α₀} a₁ a₁) True

postulate of~ueq~utrue : {p₀ : Set} → Eq {Set} p₀ True → p₀

postulate List:reverseAux~ureverseAux~unil : {α₀ : Set} → {as₁ : List α₀} → {bs₂ : List α₀} → Eq {List α₀} (List:reverseAux {α₀} (List:reverseAux {α₀} as₁ bs₂) (List:nil {α₀})) (List:reverseAux {α₀} bs₂ as₁)

postulate id : {α₀ : Set} → α₀ → α₀

List:reverse~ureverse : {α₀ : Set} → (as₁ : List α₀) → Eq {List α₀} (List:reverse {α₀} (List:reverse {α₀} as₁)) as₁
List:reverse~ureverse {α₀} as₁ = id {Eq {List α₀} (List:reverse {α₀} (List:reverse {α₀} as₁)) as₁} (Eq:mpr {Eq {List α₀} (List:reverseAux {α₀} (List:reverseAux {α₀} as₁ (List:nil {α₀})) (List:nil {α₀})) as₁} {Eq {List α₀} (List:reverseAux {α₀} (List:nil {α₀}) as₁) as₁} (id {Eq {Set} (Eq {List α₀} (List:reverseAux {α₀} (List:reverseAux {α₀} as₁ (List:nil {α₀})) (List:nil {α₀})) as₁) (Eq {List α₀} (List:reverseAux {α₀} (List:nil {α₀}) as₁) as₁)} (congrArg {List α₀} {Set} {List:reverseAux {α₀} (List:reverseAux {α₀} as₁ (List:nil {α₀})) (List:nil {α₀})} {List:reverseAux {α₀} (List:nil {α₀}) as₁} (λ (a₂ : List α₀) → Eq {List α₀} a₂ as₁) (List:reverseAux~ureverseAux~unil {α₀} {as₁} {List:nil {α₀}}))) (Eq:refl {List α₀} (List:reverseAux {α₀} (List:nil {α₀}) as₁)))
