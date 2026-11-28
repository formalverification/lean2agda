{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of Multiset:map~umap
-- Lean module Init.Prelude
module U.Init.Prelude where

data Eq {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl : (a₁ : α₀) → Eq {α₀} a₁ a₁
{-# BUILTIN REWRITE Eq #-}

-- recursor
Eq:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → Eq {α₀} a₁ a₂ → Set} → motive₂ a₁ (Eq:refl {α₀} a₁) → {a₃ : α₀} → (t₄ : Eq {α₀} a₁ a₃) → motive₂ a₃ t₄
Eq:rec {α₀} {a₁} {motive₂} refl₃ {_} (Eq:refl _) = refl₃

rfl : {α₀ : Set} → {a₁ : α₀} → Eq {α₀} a₁ a₁
rfl {α₀} {a₁} = Eq:refl {α₀} a₁

-- theorem
opaque
  Eq:symm : {α₀ : Set} → {a₁ : α₀} → {b₂ : α₀} → Eq {α₀} a₁ b₂ → Eq {α₀} b₂ a₁
  Eq:symm {α₀} {a₁} {b₂} h₃ = Eq:rec {α₀} {a₁} {λ (x₄ : α₀) → λ (h₅ : Eq {α₀} a₁ x₄) → Eq {α₀} x₄ a₁} (rfl {α₀} {a₁}) {b₂} h₃

Eq:ndrec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : α₀ → Set} → motive₂ a₁ → {b₃ : α₀} → Eq {α₀} a₁ b₃ → motive₂ b₃
Eq:ndrec {α₀} {a₁} {motive₂} m₃ {b₄} h₅ = Eq:rec {α₀} {a₁} {λ (x₆ : α₀) → λ (x₇ : Eq {α₀} a₁ x₆) → motive₂ x₆} m₃ {b₄} h₅

-- theorem
opaque
  Eq:subst : {α₀ : Set} → {motive₁ : α₀ → Set} → {a₂ : α₀} → {b₃ : α₀} → Eq {α₀} a₂ b₃ → motive₁ a₂ → motive₁ b₃
  Eq:subst {α₀} {motive₁} {a₂} {b₃} h₄ h₅ = Eq:ndrec {α₀} {a₂} {motive₁} h₅ {b₃} h₄

-- theorem
opaque
  Eq:trans : {α₀ : Set} → {a₁ : α₀} → {b₂ : α₀} → {c₃ : α₀} → Eq {α₀} a₁ b₂ → Eq {α₀} b₂ c₃ → Eq {α₀} a₁ c₃
  Eq:trans {α₀} {a₁} {b₂} {c₃} h₄ h₅ = Eq:rec {α₀} {b₂} {λ (x₆ : α₀) → λ (h₇ : Eq {α₀} b₂ x₆) → Eq {α₀} a₁ x₆} h₄ {c₃} h₅

Function:comp : {α₀ : Set} → {β₁ : Set} → {δ₂ : Set} → (β₁ → δ₂) → (α₀ → β₁) → α₀ → δ₂
Function:comp {α₀} {β₁} {δ₂} f₃ g₄ x₅ = f₃ (g₄ x₅)

data HEq {α₀ : Set} : α₀ → {β₁ : Set} → β₁ → Set where
  HEq:refl : (a₁ : α₀) → HEq {α₀} a₁ {α₀} a₁

-- recursor
HEq:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : {β₂ : Set} → (a₃ : β₂) → HEq {α₀} a₁ {β₂} a₃ → Set} → motive₂ {α₀} a₁ (HEq:refl {α₀} a₁) → {β₃ : Set} → {a₄ : β₃} → (t₅ : HEq {α₀} a₁ {β₃} a₄) → motive₂ {β₃} a₄ t₅
HEq:rec {α₀} {a₁} {motive₂} refl₃ {_} {_} (HEq:refl _) = refl₃

data List (α₀ : Set) : Set where
  List:nil : List α₀
  List:cons : α₀ → List α₀ → List α₀

-- recursor
List:rec : {α₀ : Set} → {motive₁ : List α₀ → Set} → motive₁ (List:nil {α₀}) → ((head₂ : α₀) → (tail₃ : List α₀) → motive₁ tail₃ → motive₁ (List:cons {α₀} head₂ tail₃)) → (t₂ : List α₀) → motive₁ t₂
List:rec {α₀} {motive₁} nil₂ cons₃ List:nil = nil₂
List:rec {α₀} {motive₁} nil₂ cons₃ (List:cons head₄ tail₅) = cons₃ head₄ tail₅ (List:rec {α₀} {motive₁} nil₂ cons₃ tail₅)

record PProd (α₀ : Set) (β₁ : Set) : Set where
  constructor PProd:mk
  field
    fst₂ : α₀
    snd₃ : β₁

-- recursor
PProd:rec : {α₀ : Set} → {β₁ : Set} → {motive₂ : PProd α₀ β₁ → Set} → ((fst₃ : α₀) → (snd₄ : β₁) → motive₂ (PProd:mk {α₀} {β₁} fst₃ snd₄)) → (t₃ : PProd α₀ β₁) → motive₂ t₃
PProd:rec {α₀} {β₁} {motive₂} mk₃ (PProd:mk fst₄ snd₅) = mk₃ fst₄ snd₅

record PUnit : Set where
  constructor PUnit:unit

-- recursor
PUnit:rec : {motive₀ : PUnit → Set} → motive₀ PUnit:unit → (t₁ : PUnit) → motive₀ t₁
PUnit:rec {motive₀} unit₁ PUnit:unit = unit₁

List:below : {α₀ : Set} → {_ : List α₀ → Set} → List α₀ → Set
List:below {α₀} {motive₁} t₂ = List:rec {α₀} {λ (t₃ : List α₀) → Set} PUnit (λ (head₃ : α₀) → λ (tail₄ : List α₀) → λ (tailih₅ : Set) → PProd (motive₁ tail₄) tailih₅) t₂

Unit : Set
Unit = PUnit

List:casesOn : {α₀ : Set} → {motive₁ : List α₀ → Set} → (t₂ : List α₀) → motive₁ (List:nil {α₀}) → ((head₃ : α₀) → (tail₄ : List α₀) → motive₁ (List:cons {α₀} head₃ tail₄)) → motive₁ t₂
List:casesOn {α₀} {motive₁} t₂ nil₃ cons₄ = List:rec {α₀} {motive₁} nil₃ (λ (head₅ : α₀) → λ (tail₆ : List α₀) → λ (tailih₇ : motive₁ tail₆) → cons₄ head₅ tail₆) t₂

Unit:unit : Unit
Unit:unit = PUnit:unit

List:brecOn:go : {α₀ : Set} → {motive₁ : List α₀ → Set} → (t₂ : List α₀) → ((t₃ : List α₀) → List:below {α₀} {motive₁} t₃ → motive₁ t₃) → PProd (motive₁ t₂) (List:below {α₀} {motive₁} t₂)
List:brecOn:go {α₀} {motive₁} t₂ F1₃ = List:rec {α₀} {λ (t₄ : List α₀) → PProd (motive₁ t₄) (List:below {α₀} {motive₁} t₄)} (PProd:mk {motive₁ (List:nil {α₀})} {PUnit} (F1₃ (List:nil {α₀}) PUnit:unit) PUnit:unit) (λ (head₄ : α₀) → λ (tail₅ : List α₀) → λ (tailih₆ : PProd (motive₁ tail₅) (List:below {α₀} {motive₁} tail₅)) → PProd:mk {motive₁ (List:cons {α₀} head₄ tail₅)} {PProd (motive₁ tail₅) (List:below {α₀} {motive₁} tail₅)} (F1₃ (List:cons {α₀} head₄ tail₅) tailih₆) tailih₆) t₂

List:brecOn : {α₀ : Set} → {motive₁ : List α₀ → Set} → (t₂ : List α₀) → ((t₃ : List α₀) → List:below {α₀} {motive₁} t₃ → motive₁ t₃) → motive₁ t₂
List:brecOn {α₀} {motive₁} t₂ F1₃ = PProd.fst₂ {motive₁ t₂} {List:below {α₀} {motive₁} t₂} (List:brecOn:go {α₀} {motive₁} t₂ F1₃)

record True : Set where
  constructor True:intro

-- recursor
True:rec : {motive₀ : True → Set} → motive₀ True:intro → (t₁ : True) → motive₀ t₁
True:rec {motive₀} intro₁ True:intro = intro₁

data Option (α₀ : Set) : Set where
  Option:none : Option α₀
  Option:some : α₀ → Option α₀

-- recursor
Option:rec : {α₀ : Set} → {motive₁ : Option α₀ → Set} → motive₁ (Option:none {α₀}) → ((val₂ : α₀) → motive₁ (Option:some {α₀} val₂)) → (t₂ : Option α₀) → motive₁ t₂
Option:rec {α₀} {motive₁} none₂ some₃ Option:none = none₂
Option:rec {α₀} {motive₁} none₂ some₃ (Option:some val₄) = some₃ val₄

Option:casesOn : {α₀ : Set} → {motive₁ : Option α₀ → Set} → (t₂ : Option α₀) → motive₁ (Option:none {α₀}) → ((val₃ : α₀) → motive₁ (Option:some {α₀} val₃)) → motive₁ t₂
Option:casesOn {α₀} {motive₁} t₂ none₃ some₄ = Option:rec {α₀} {motive₁} none₃ (λ (val₅ : α₀) → some₄ val₅) t₂

-- theorem
opaque
  congrArg : {α₀ : Set} → {β₁ : Set} → {a₂ : α₀} → {a₃ : α₀} → (f₄ : α₀ → β₁) → Eq {α₀} a₂ a₃ → Eq {β₁} (f₄ a₂) (f₄ a₃)
  congrArg {α₀} {β₁} {a₂} {a₃} f₄ h₅ = Eq:rec {α₀} {a₂} {λ (x₆ : α₀) → λ (h₇ : Eq {α₀} a₂ x₆) → Eq {β₁} (f₄ a₂) (f₄ x₆)} (rfl {β₁} {f₄ a₂}) {a₃} h₅

-- theorem
opaque
  congrFun~x27~ : {α₀ : Set} → {β₁ : Set} → {f₂ : α₀ → β₁} → {g₃ : α₀ → β₁} → Eq {α₀ → β₁} f₂ g₃ → (a₄ : α₀) → Eq {β₁} (f₂ a₄) (g₃ a₄)
  congrFun~x27~ {α₀} {β₁} {f₂} {g₃} h₄ a₅ = Eq:rec {α₀ → β₁} {f₂} {λ (x₆ : α₀ → β₁) → λ (h₇ : Eq {α₀ → β₁} f₂ x₆) → Eq {β₁} (f₂ a₅) (x₆ a₅)} (rfl {β₁} {f₂ a₅}) {g₃} h₄

Option:noConfusionType : Set → {α₀ : Set} → Option α₀ → {α₁ : Set} → Option α₁ → Set
Option:noConfusionType P₀ {α₁} t₂ {α₃} t₄ = Option:casesOn {α₁} {λ (t₅ : Option α₁) → Set} t₂ (Option:casesOn {α₃} {λ (t₅ : Option α₃) → Set} t₄ (P₀ → P₀) (λ (val₅ : α₃) → P₀)) (λ (val₅ : α₁) → Option:casesOn {α₃} {λ (t₆ : Option α₃) → Set} t₄ P₀ (λ (val₆ : α₃) → (HEq {α₁} val₅ {α₃} val₆ → P₀) → P₀))

cast : {α₀ : Set} → {β₁ : Set} → Eq {Set} α₀ β₁ → α₀ → β₁
cast {α₀} {β₁} h₂ a₃ = Eq:rec {Set} {α₀} {λ (x₄ : Set) → λ (x₅ : Eq {Set} α₀ x₄) → x₄} a₃ {β₁} h₂

-- theorem
opaque
  eq~uof~uheq : {α₀ : Set} → {a₁ : α₀} → {a₂ : α₀} → HEq {α₀} a₁ {α₀} a₂ → Eq {α₀} a₁ a₂
  eq~uof~uheq {α₀} {a₁} {a₂} h₃ = let this₄ : (α₄ : Set) → (β₅ : Set) → (a₆ : α₄) → (b₇ : β₅) → HEq {α₄} a₆ {β₅} b₇ → (h₈ : Eq {Set} α₄ β₅) → Eq {β₅} (cast {α₄} {β₅} h₈ a₆) b₇; this₄ = λ (x₄ : Set) → λ (x₅ : Set) → λ (x₆ : x₄) → λ (x₇ : x₅) → λ (h₈ : HEq {x₄} x₆ {x₅} x₇) → HEq:rec {x₄} {x₆} {λ {x₉ : Set} → λ (x₁₀ : x₉) → λ (x₁₁ : HEq {x₄} x₆ {x₉} x₁₀) → (h₁₂ : Eq {Set} x₄ x₉) → Eq {x₉} (cast {x₄} {x₉} h₁₂ x₆) x₁₀} (λ (x₉ : Eq {Set} x₄ x₄) → rfl {x₄} {cast {x₄} {x₄} x₉ x₆}) {x₅} {x₇} h₈ in this₄ α₀ α₀ a₁ a₂ h₃ (rfl {Set} {α₀})

Option:noConfusion : {P₀ : Set} → {α₁ : Set} → {t₂ : Option α₁} → {α₃ : Set} → {t₄ : Option α₃} → Eq {Set} α₁ α₃ → HEq {Option α₁} t₂ {Option α₃} t₄ → Option:noConfusionType P₀ {α₁} t₂ {α₃} t₄
Option:noConfusion {P₀} {α₁} {t₂} {α₃} {t₄} eq1₅ eq2₆ = Eq:ndrec {Set} {α₁} {λ (α₇ : Set) → {t₈ : Option α₇} → HEq {Option α₁} t₂ {Option α₇} t₈ → Option:noConfusionType P₀ {α₁} t₂ {α₇} t₈} (λ {t₇ : Option α₁} → λ (eq2₈ : HEq {Option α₁} t₂ {Option α₁} t₇) → Eq:ndrec {Option α₁} {t₂} {λ (t₉ : Option α₁) → Option:noConfusionType P₀ {α₁} t₂ {α₁} t₉} (Option:casesOn {α₁} {λ (t₉ : Option α₁) → Option:noConfusionType P₀ {α₁} t₉ {α₁} t₉} t₂ (λ (k₉ : P₀) → k₉) (λ (val₉ : α₁) → λ (k₁₀ : HEq {α₁} val₉ {α₁} val₉ → P₀) → k₁₀ (HEq:refl {α₁} val₉))) {t₇} (eq~uof~uheq {Option α₁} {t₂} {t₇} eq2₈)) {α₃} eq1₅ {t₄} eq2₆

-- theorem
opaque
  heq~uof~ueq : {α₀ : Set} → {a₁ : α₀} → {a₂ : α₀} → Eq {α₀} a₁ a₂ → HEq {α₀} a₁ {α₀} a₂
  heq~uof~ueq {α₀} {a₁} {a₂} h₃ = Eq:subst {α₀} {HEq {α₀} a₁ {α₀}} {a₁} {a₂} h₃ (HEq:refl {α₀} a₁)

id : {α₀ : Set} → α₀ → α₀
id {α₀} a₁ = a₁

Option:some:noConfusion : {α₀ : Set} → {P₁ : Set} → {val₂ : α₀} → {val₃ : α₀} → Eq {Option α₀} (Option:some {α₀} val₂) (Option:some {α₀} val₃) → (HEq {α₀} val₂ {α₀} val₃ → P₁) → P₁
Option:some:noConfusion {α₀} {P₁} {val₂} {val₃} eq₄ k₅ = id {P₁} (Option:noConfusion {P₁} {α₀} {Option:some {α₀} val₂} {α₀} {Option:some {α₀} val₃} (Eq:refl {Set} α₀) (heq~uof~ueq {Option α₀} {Option:some {α₀} val₂} {Option:some {α₀} val₃} eq₄) k₅)

-- theorem
opaque
  congr : {α₀ : Set} → {β₁ : Set} → {f₂ : α₀ → β₁} → {f₃ : α₀ → β₁} → {a₄ : α₀} → {a₅ : α₀} → Eq {α₀ → β₁} f₂ f₃ → Eq {α₀} a₄ a₅ → Eq {β₁} (f₂ a₄) (f₃ a₅)
  congr {α₀} {β₁} {f₂} {f₃} {a₄} {a₅} h₆ h₇ = Eq:rec {α₀ → β₁} {f₂} {λ (x₈ : α₀ → β₁) → λ (h₉ : Eq {α₀ → β₁} f₂ x₈) → Eq {β₁} (f₂ a₄) (x₈ a₅)} (Eq:rec {α₀} {a₄} {λ (x₈ : α₀) → λ (h₉ : Eq {α₀} a₄ x₈) → Eq {β₁} (f₂ a₄) (f₂ x₈)} (rfl {β₁} {f₂ a₄}) {a₅} h₇) {f₃} h₆

instDecidableEqList:match~u1 : {α₀ : Set} → (motive₁ : List α₀ → Set) → (ys₂ : List α₀) → (Unit → motive₁ (List:nil {α₀})) → ((head₃ : α₀) → (tail₄ : List α₀) → motive₁ (List:cons {α₀} head₃ tail₄)) → motive₁ ys₂
instDecidableEqList:match~u1 {α₀} motive₁ ys₂ h1₃ h2₄ = List:casesOn {α₀} {λ (x₅ : List α₀) → motive₁ x₅} ys₂ (h1₃ Unit:unit) (λ (head₅ : α₀) → λ (tail₆ : List α₀) → h2₄ head₅ tail₆)

List:map:~uf : {α₀ : Set} → {β₁ : Set} → (α₀ → β₁) → (x₂ : List α₀) → List:below {α₀} {λ (x₃ : List α₀) → List β₁} x₂ → List β₁
List:map:~uf {α₀} {β₁} f₂ x₃ f₄ = instDecidableEqList:match~u1 {α₀} (λ (x₅ : List α₀) → List:below {α₀} {λ (x₆ : List α₀) → List β₁} x₅ → List β₁) x₃ (λ (x₅ : Unit) → λ (x₆ : List:below {α₀} {λ (x₆ : List α₀) → List β₁} (List:nil {α₀})) → List:nil {β₁}) (λ (a₅ : α₀) → λ (as₆ : List α₀) → λ (x₇ : List:below {α₀} {λ (x₇ : List α₀) → List β₁} (List:cons {α₀} a₅ as₆)) → List:cons {β₁} (f₂ a₅) (PProd.fst₂ {(λ (x₈ : List α₀) → List β₁) as₆} {List:rec {α₀} {λ (t₈ : List α₀) → Set} PUnit (λ (head₈ : α₀) → λ (tail₉ : List α₀) → λ (tailih₁₀ : Set) → PProd ((λ (x₁₁ : List α₀) → List β₁) tail₉) tailih₁₀) as₆} x₇)) f₄

List:map : {α₀ : Set} → {β₁ : Set} → (α₀ → β₁) → List α₀ → List β₁
List:map {α₀} {β₁} f₂ x₃ = List:brecOn {α₀} {λ (x₄ : List α₀) → List β₁} x₃ (List:map:~uf {α₀} {β₁} f₂)

postulate Quot : {α₀ : Set} → (α₀ → α₀ → Set) → Set

postulate Quot:mk : {α₀ : Set} → (r₁ : α₀ → α₀ → Set) → α₀ → Quot {α₀} r₁

postulate Quot:ind : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {β₂ : Quot {α₀} r₁ → Set} → ((a₃ : α₀) → β₂ (Quot:mk {α₀} r₁ a₃)) → (q₃ : Quot {α₀} r₁) → β₂ q₃

-- computation rule
postulate Quot:ind-β : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {β₂ : Quot {α₀} r₁ → Set} → (mk₃ : (a₃ : α₀) → β₂ (Quot:mk {α₀} r₁ a₃)) → (a₄ : α₀) → Eq {β₂ (Quot:mk {α₀} r₁ a₄)} (Quot:ind {α₀} {r₁} {β₂} mk₃ (Quot:mk {α₀} r₁ a₄)) (mk₃ a₄)
{-# REWRITE Quot:ind-β #-}

postulate Quot:lift : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {β₂ : Set} → (f₃ : α₀ → β₂) → ((a₄ : α₀) → (b₅ : α₀) → r₁ a₄ b₅ → Eq {β₂} (f₃ a₄) (f₃ b₅)) → Quot {α₀} r₁ → β₂

-- computation rule
postulate Quot:lift-β : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {β₂ : Set} → (f₃ : α₀ → β₂) → (h₄ : (a₄ : α₀) → (b₅ : α₀) → r₁ a₄ b₅ → Eq {β₂} (f₃ a₄) (f₃ b₅)) → (a₅ : α₀) → Eq {β₂} (Quot:lift {α₀} {r₁} {β₂} f₃ h₄ (Quot:mk {α₀} r₁ a₅)) (f₃ a₅)
{-# REWRITE Quot:lift-β #-}
