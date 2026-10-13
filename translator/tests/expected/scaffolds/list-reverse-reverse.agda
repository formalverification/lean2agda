-- File: translator/tests/expected/scaffolds/list-reverse-reverse.agda
{-# OPTIONS --type-in-type #-}
-- lean2agda, profile U: the scaffold of the closure of List:reverse~ureverse
module U.Init.Data.List.Lemmas where

data Eq {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl : (a₁ : α₀) → Eq {α₀} a₁ a₁

postulate Eq:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → Eq {α₀} a₁ a₂ → Set} → motive₂ a₁ (Eq:refl {α₀} a₁) → {a₃ : α₀} → (t₄ : Eq {α₀} a₁ a₃) → motive₂ a₃ t₄

rfl : {α₀ : Set} → {a₁ : α₀} → Eq {α₀} a₁ a₁
rfl {α₀} {a₁} = Eq:refl {α₀} a₁

-- theorem
opaque
  Eq:symm : {α₀ : Set} → {a₁ : α₀} → {b₂ : α₀} → Eq {α₀} a₁ b₂ → Eq {α₀} b₂ a₁
  Eq:symm {α₀} {a₁} {b₂} h₃ = Eq:rec {α₀} {a₁} {λ (x₄ : α₀) → λ (h₅ : Eq {α₀} a₁ x₄) → Eq {α₀} x₄ a₁} (rfl {α₀} {a₁}) {b₂} h₃

Eq:mpr : {α₀ : Set} → {β₁ : Set} → Eq {Set} α₀ β₁ → β₁ → α₀
Eq:mpr {α₀} {β₁} h₂ b₃ = Eq:rec {Set} {β₁} {λ (x₄ : Set) → λ (h₅ : Eq {Set} β₁ x₄) → x₄} b₃ {α₀} (Eq:symm {Set} {α₀} {β₁} h₂)

-- theorem
opaque
  Eq:trans : {α₀ : Set} → {a₁ : α₀} → {b₂ : α₀} → {c₃ : α₀} → Eq {α₀} a₁ b₂ → Eq {α₀} b₂ c₃ → Eq {α₀} a₁ c₃
  Eq:trans {α₀} {a₁} {b₂} {c₃} h₄ h₅ = Eq:rec {α₀} {b₂} {λ (x₆ : α₀) → λ (h₇ : Eq {α₀} b₂ x₆) → Eq {α₀} a₁ x₆} h₄ {c₃} h₅

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

List:below : {α₀ : Set} → {_ : List α₀ → Set} → List α₀ → Set
List:below {α₀} {motive₁} t₂ = List:rec {α₀} {λ (t₃ : List α₀) → Set} PUnit (λ (head₃ : α₀) → λ (tail₄ : List α₀) → λ (tailih₅ : Set) → PProd (motive₁ tail₄) tailih₅) t₂

List:brecOn:go : {α₀ : Set} → {motive₁ : List α₀ → Set} → (t₂ : List α₀) → ((t₃ : List α₀) → List:below {α₀} {motive₁} t₃ → motive₁ t₃) → PProd (motive₁ t₂) (List:below {α₀} {motive₁} t₂)
List:brecOn:go {α₀} {motive₁} t₂ F1₃ = List:rec {α₀} {λ (t₄ : List α₀) → PProd (motive₁ t₄) (List:below {α₀} {motive₁} t₄)} (PProd:mk {motive₁ (List:nil {α₀})} {PUnit} (F1₃ (List:nil {α₀}) PUnit:unit) PUnit:unit) (λ (head₄ : α₀) → λ (tail₅ : List α₀) → λ (tailih₆ : PProd (motive₁ tail₅) (List:below {α₀} {motive₁} tail₅)) → PProd:mk {motive₁ (List:cons {α₀} head₄ tail₅)} {PProd (motive₁ tail₅) (List:below {α₀} {motive₁} tail₅)} (F1₃ (List:cons {α₀} head₄ tail₅) tailih₆) tailih₆) t₂

List:brecOn : {α₀ : Set} → {motive₁ : List α₀ → Set} → (t₂ : List α₀) → ((t₃ : List α₀) → List:below {α₀} {motive₁} t₃ → motive₁ t₃) → motive₁ t₂
List:brecOn {α₀} {motive₁} t₂ F1₃ = PProd.fst₂ {motive₁ t₂} {List:below {α₀} {motive₁} t₂} (List:brecOn:go {α₀} {motive₁} t₂ F1₃)

List:casesOn : {α₀ : Set} → {motive₁ : List α₀ → Set} → (t₂ : List α₀) → motive₁ (List:nil {α₀}) → ((head₃ : α₀) → (tail₄ : List α₀) → motive₁ (List:cons {α₀} head₃ tail₄)) → motive₁ t₂
List:casesOn {α₀} {motive₁} t₂ nil₃ cons₄ = List:rec {α₀} {motive₁} nil₃ (λ (head₅ : α₀) → λ (tail₆ : List α₀) → λ (tailih₇ : motive₁ tail₆) → cons₄ head₅ tail₆) t₂

List:reverseAux:match~u1 : {α₀ : Set} → (motive₁ : List α₀ → List α₀ → Set) → (x₂ : List α₀) → (x₃ : List α₀) → ((r₄ : List α₀) → motive₁ (List:nil {α₀}) r₄) → ((a₄ : α₀) → (l₅ : List α₀) → (r₆ : List α₀) → motive₁ (List:cons {α₀} a₄ l₅) r₆) → motive₁ x₂ x₃
List:reverseAux:match~u1 {α₀} motive₁ x₂ x₃ h1₄ h2₅ = List:casesOn {α₀} {λ (x₆ : List α₀) → motive₁ x₆ x₃} x₂ (h1₄ x₃) (λ (head₆ : α₀) → λ (tail₇ : List α₀) → h2₅ head₆ tail₇ x₃)

List:reverseAux:~uf : {α₀ : Set} → (x₁ : List α₀) → List:below {α₀} {λ (x₂ : List α₀) → List α₀ → List α₀} x₁ → List α₀ → List α₀
List:reverseAux:~uf {α₀} x₁ f₂ x₃ = List:reverseAux:match~u1 {α₀} (λ (x₄ : List α₀) → λ (x₅ : List α₀) → List:below {α₀} {λ (x₆ : List α₀) → List α₀ → List α₀} x₄ → List α₀) x₁ x₃ (λ (r₄ : List α₀) → λ (x₅ : List:below {α₀} {λ (x₅ : List α₀) → List α₀ → List α₀} (List:nil {α₀})) → r₄) (λ (a₄ : α₀) → λ (l₅ : List α₀) → λ (r₆ : List α₀) → λ (x₇ : List:below {α₀} {λ (x₇ : List α₀) → List α₀ → List α₀} (List:cons {α₀} a₄ l₅)) → PProd.fst₂ {(λ (x₈ : List α₀) → List α₀ → List α₀) l₅} {List:rec {α₀} {λ (t₈ : List α₀) → Set} PUnit (λ (head₈ : α₀) → λ (tail₉ : List α₀) → λ (tailih₁₀ : Set) → PProd ((λ (x₁₁ : List α₀) → List α₀ → List α₀) tail₉) tailih₁₀) l₅} x₇ (List:cons {α₀} a₄ r₆)) f₂

List:reverseAux : {α₀ : Set} → List α₀ → List α₀ → List α₀
List:reverseAux {α₀} x₁ x₂ = List:brecOn {α₀} {λ (x₃ : List α₀) → List α₀ → List α₀} x₁ (List:reverseAux:~uf {α₀}) x₂

List:reverse : {α₀ : Set} → List α₀ → List α₀
List:reverse {α₀} as₁ = List:reverseAux {α₀} as₁ (List:nil {α₀})

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

postulate propext : {a₀ : Set} → {b₁ : Set} → Iff a₀ b₁ → Eq {Set} a₀ b₁

-- theorem
opaque
  trivial : True
  trivial = True:intro

-- theorem
opaque
  eq~utrue : {p₀ : Set} → p₀ → Eq {Set} p₀ True
  eq~utrue {p₀} h₁ = propext {p₀} {True} (Iff:intro {p₀} {True} (λ (x₂ : p₀) → trivial) (λ (x₂ : True) → h₁))

-- theorem
opaque
  eq~uself : {α₀ : Set} → (a₁ : α₀) → Eq {Set} (Eq {α₀} a₁ a₁) True
  eq~uself {α₀} a₁ = eq~utrue {Eq {α₀} a₁ a₁} (rfl {α₀} {a₁})

-- theorem
opaque
  of~ueq~utrue : {p₀ : Set} → Eq {Set} p₀ True → p₀
  of~ueq~utrue {p₀} h₁ = Eq:rec {Set} {True} {λ (x₂ : Set) → λ (h₃ : Eq {Set} True x₂) → x₂} trivial {p₀} (Eq:symm {Set} {p₀} {True} h₁)

-- theorem
opaque
  List:reverseAux~ureverseAux~unil : {α₀ : Set} → {as₁ : List α₀} → {bs₂ : List α₀} → Eq {List α₀} (List:reverseAux {α₀} (List:reverseAux {α₀} as₁ bs₂) (List:nil {α₀})) (List:reverseAux {α₀} bs₂ as₁)
  List:reverseAux~ureverseAux~unil {α₀} {as₁} {bs₂} = List:rec {α₀} {λ (as₃ : List α₀) → {bs₄ : List α₀} → Eq {List α₀} (List:reverseAux {α₀} (List:reverseAux {α₀} as₃ bs₄) (List:nil {α₀})) (List:reverseAux {α₀} bs₄ as₃)} (λ {bs₃ : List α₀} → Eq:refl {List α₀} (List:reverseAux {α₀} (List:reverseAux {α₀} (List:nil {α₀}) bs₃) (List:nil {α₀}))) (λ (a₃ : α₀) → λ (as₄ : List α₀) → λ (ih₅ : {bs₅ : List α₀} → Eq {List α₀} (List:reverseAux {α₀} (List:reverseAux {α₀} as₄ bs₅) (List:nil {α₀})) (List:reverseAux {α₀} bs₅ as₄)) → λ {bs₆ : List α₀} → of~ueq~utrue {Eq {List α₀} (List:reverseAux {α₀} (List:reverseAux {α₀} (List:cons {α₀} a₃ as₄) bs₆) (List:nil {α₀})) (List:reverseAux {α₀} bs₆ (List:cons {α₀} a₃ as₄))} (Eq:trans {Set} {Eq {List α₀} (List:reverseAux {α₀} (List:reverseAux {α₀} (List:cons {α₀} a₃ as₄) bs₆) (List:nil {α₀})) (List:reverseAux {α₀} bs₆ (List:cons {α₀} a₃ as₄))} {Eq {List α₀} (List:reverseAux {α₀} bs₆ (List:cons {α₀} a₃ as₄)) (List:reverseAux {α₀} bs₆ (List:cons {α₀} a₃ as₄))} {True} (congrFun~x27~ {List α₀} {Set} {Eq {List α₀} (List:reverseAux {α₀} (List:reverseAux {α₀} (List:cons {α₀} a₃ as₄) bs₆) (List:nil {α₀}))} {Eq {List α₀} (List:reverseAux {α₀} bs₆ (List:cons {α₀} a₃ as₄))} (congrArg {List α₀} {List α₀ → Set} {List:reverseAux {α₀} (List:reverseAux {α₀} (List:cons {α₀} a₃ as₄) bs₆) (List:nil {α₀})} {List:reverseAux {α₀} bs₆ (List:cons {α₀} a₃ as₄)} (Eq {List α₀}) ((λ {bs₇ : List α₀} → ih₅ {bs₇}) {List:cons {α₀} a₃ bs₆})) (List:reverseAux {α₀} bs₆ (List:cons {α₀} a₃ as₄))) (eq~uself {List α₀} (List:reverseAux {α₀} bs₆ (List:cons {α₀} a₃ as₄))))) as₁ {bs₂}

id : {α₀ : Set} → α₀ → α₀
id {α₀} a₁ = a₁

-- theorem
opaque
  List:reverse~ureverse : {α₀ : Set} → (as₁ : List α₀) → Eq {List α₀} (List:reverse {α₀} (List:reverse {α₀} as₁)) as₁
  List:reverse~ureverse {α₀} as₁ = id {Eq {List α₀} (List:reverse {α₀} (List:reverse {α₀} as₁)) as₁} (Eq:mpr {Eq {List α₀} (List:reverseAux {α₀} (List:reverseAux {α₀} as₁ (List:nil {α₀})) (List:nil {α₀})) as₁} {Eq {List α₀} (List:reverseAux {α₀} (List:nil {α₀}) as₁) as₁} (id {Eq {Set} (Eq {List α₀} (List:reverseAux {α₀} (List:reverseAux {α₀} as₁ (List:nil {α₀})) (List:nil {α₀})) as₁) (Eq {List α₀} (List:reverseAux {α₀} (List:nil {α₀}) as₁) as₁)} (congrArg {List α₀} {Set} {List:reverseAux {α₀} (List:reverseAux {α₀} as₁ (List:nil {α₀})) (List:nil {α₀})} {List:reverseAux {α₀} (List:nil {α₀}) as₁} (λ (a₂ : List α₀) → Eq {List α₀} a₂ as₁) (List:reverseAux~ureverseAux~unil {α₀} {as₁} {List:nil {α₀}}))) (Eq:refl {List α₀} (List:reverseAux {α₀} (List:nil {α₀}) as₁)))
