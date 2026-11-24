{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of Lists~x27~:Subset:refl
-- Lean module Init.Prelude
module U.Init.Prelude where

record And (a₀ : Set) (b₁ : Set) : Set where
  constructor And:intro
  field
    left₂ : a₀
    right₃ : b₁

-- recursor
And:rec : {a₀ : Set} → {b₁ : Set} → {motive₂ : And a₀ b₁ → Set} → ((left₃ : a₀) → (right₄ : b₁) → motive₂ (And:intro {a₀} {b₁} left₃ right₄)) → (t₃ : And a₀ b₁) → motive₂ t₃
And:rec {a₀} {b₁} {motive₂} intro₃ (And:intro left₄ right₅) = intro₃ left₄ right₅

And:casesOn : {a₀ : Set} → {b₁ : Set} → {motive₂ : And a₀ b₁ → Set} → (t₃ : And a₀ b₁) → ((left₄ : a₀) → (right₅ : b₁) → motive₂ (And:intro {a₀} {b₁} left₄ right₅)) → motive₂ t₃
And:casesOn {a₀} {b₁} {motive₂} t₃ intro₄ = And:rec {a₀} {b₁} {motive₂} (λ (left₅ : a₀) → λ (right₆ : b₁) → intro₄ left₅ right₆) t₃

-- theorem
opaque
  And:left : {a₀ : Set} → {b₁ : Set} → And a₀ b₁ → a₀
  And:left {a₀} {b₁} self₂ = And.left₂ {a₀} {b₁} self₂

-- theorem
opaque
  And:right : {a₀ : Set} → {b₁ : Set} → And a₀ b₁ → b₁
  And:right {a₀} {b₁} self₂ = And.right₃ {a₀} {b₁} self₂

data Bool : Set where
  Bool:false : Bool
  Bool:true : Bool
{-# BUILTIN BOOL Bool #-}
{-# BUILTIN FALSE Bool:false #-}
{-# BUILTIN TRUE Bool:true #-}

-- recursor
Bool:rec : {motive₀ : Bool → Set} → motive₀ Bool:false → motive₀ Bool:true → (t₁ : Bool) → motive₀ t₁
Bool:rec {motive₀} false₁ true₂ Bool:false = false₁
Bool:rec {motive₀} false₁ true₂ Bool:true = true₂

Bool:casesOn : {motive₀ : Bool → Set} → (t₁ : Bool) → motive₀ Bool:false → motive₀ Bool:true → motive₀ t₁
Bool:casesOn {motive₀} t₁ false₂ true₃ = Bool:rec {motive₀} false₂ true₃ t₁

data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

-- recursor
Nat:rec : {motive₀ : Nat → Set} → motive₀ Nat:zero → ((n₁ : Nat) → motive₀ n₁ → motive₀ (Nat:succ n₁)) → (t₁ : Nat) → motive₀ t₁
Nat:rec {motive₀} zero₁ succ₂ Nat:zero = zero₁
Nat:rec {motive₀} zero₁ succ₂ (Nat:succ n₃) = succ₂ n₃ (Nat:rec {motive₀} zero₁ succ₂ n₃)

Bool:ctorIdx : Bool → Nat
Bool:ctorIdx x₀ = Bool:casesOn {λ (x₁ : Bool) → Nat} x₀ 0 1

Bool:noConfusionType : Set → Bool → Bool → Set
Bool:noConfusionType P₀ t₁ t₂ = Bool:casesOn {λ (t₃ : Bool) → Set} t₁ (Bool:casesOn {λ (t₃ : Bool) → Set} t₂ (P₀ → P₀) P₀) (Bool:casesOn {λ (t₃ : Bool) → Set} t₂ P₀ (P₀ → P₀))

data Eq {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl : (a₁ : α₀) → Eq {α₀} a₁ a₁
{-# BUILTIN REWRITE Eq #-}

-- recursor
Eq:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → Eq {α₀} a₁ a₂ → Set} → motive₂ a₁ (Eq:refl {α₀} a₁) → {a₃ : α₀} → (t₄ : Eq {α₀} a₁ a₃) → motive₂ a₃ t₄
Eq:rec {α₀} {a₁} {motive₂} refl₃ {_} (Eq:refl _) = refl₃

Eq:ndrec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : α₀ → Set} → motive₂ a₁ → {b₃ : α₀} → Eq {α₀} a₁ b₃ → motive₂ b₃
Eq:ndrec {α₀} {a₁} {motive₂} m₃ {b₄} h₅ = Eq:rec {α₀} {a₁} {λ (x₆ : α₀) → λ (x₇ : Eq {α₀} a₁ x₆) → motive₂ x₆} m₃ {b₄} h₅

Bool:noConfusion : {P₀ : Set} → {t₁ : Bool} → {t₂ : Bool} → Eq {Bool} t₁ t₂ → Bool:noConfusionType P₀ t₁ t₂
Bool:noConfusion {P₀} {t₁} {t₂} eq₃ = Eq:ndrec {Bool} {t₁} {λ (t₄ : Bool) → Bool:noConfusionType P₀ t₁ t₄} (Bool:casesOn {λ (t₄ : Bool) → Bool:noConfusionType P₀ t₄ t₄} t₁ (λ (k₄ : P₀) → k₄) (λ (k₄ : P₀) → k₄)) {t₂} eq₃

data False : Set where

-- recursor
False:rec : (motive₀ : False → Set) → (t₁ : False) → motive₀ t₁
False:rec motive₀ ()

Not : Set → Set
Not a₀ = a₀ → False

data Decidable (p₀ : Set) : Set where
  Decidable:isFalse : Not p₀ → Decidable p₀
  Decidable:isTrue : p₀ → Decidable p₀

-- recursor
Decidable:rec : {p₀ : Set} → {motive₁ : Decidable p₀ → Set} → ((h₂ : Not p₀) → motive₁ (Decidable:isFalse {p₀} h₂)) → ((h₂ : p₀) → motive₁ (Decidable:isTrue {p₀} h₂)) → (t₂ : Decidable p₀) → motive₁ t₂
Decidable:rec {p₀} {motive₁} isFalse₂ isTrue₃ (Decidable:isFalse h₄) = isFalse₂ h₄
Decidable:rec {p₀} {motive₁} isFalse₂ isTrue₃ (Decidable:isTrue h₄) = isTrue₃ h₄

Decidable:casesOn : {p₀ : Set} → {motive₁ : Decidable p₀ → Set} → (t₂ : Decidable p₀) → ((h₃ : Not p₀) → motive₁ (Decidable:isFalse {p₀} h₃)) → ((h₃ : p₀) → motive₁ (Decidable:isTrue {p₀} h₃)) → motive₁ t₂
Decidable:casesOn {p₀} {motive₁} t₂ isFalse₃ isTrue₄ = Decidable:rec {p₀} {motive₁} (λ (h₅ : Not p₀) → isFalse₃ h₅) (λ (h₅ : p₀) → isTrue₄ h₅) t₂

Eq:casesOn : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → Eq {α₀} a₁ a₂ → Set} → {a₃ : α₀} → (t₄ : Eq {α₀} a₁ a₃) → motive₂ a₁ (Eq:refl {α₀} a₁) → motive₂ a₃ t₄
Eq:casesOn {α₀} {a₁} {motive₂} {a₃} t₄ refl₅ = Eq:rec {α₀} {a₁} {motive₂} refl₅ {a₃} t₄

rfl : {α₀ : Set} → {a₁ : α₀} → Eq {α₀} a₁ a₁
rfl {α₀} {a₁} = Eq:refl {α₀} a₁

-- theorem
opaque
  Eq:symm : {α₀ : Set} → {a₁ : α₀} → {b₂ : α₀} → Eq {α₀} a₁ b₂ → Eq {α₀} b₂ a₁
  Eq:symm {α₀} {a₁} {b₂} h₃ = Eq:rec {α₀} {a₁} {λ (x₄ : α₀) → λ (h₅ : Eq {α₀} a₁ x₄) → Eq {α₀} x₄ a₁} (rfl {α₀} {a₁}) {b₂} h₃

-- theorem
opaque
  Eq:subst : {α₀ : Set} → {motive₁ : α₀ → Set} → {a₂ : α₀} → {b₃ : α₀} → Eq {α₀} a₂ b₃ → motive₁ a₂ → motive₁ b₃
  Eq:subst {α₀} {motive₁} {a₂} {b₃} h₄ h₅ = Eq:ndrec {α₀} {a₂} {motive₁} h₅ {b₃} h₄

-- theorem
opaque
  Eq:trans : {α₀ : Set} → {a₁ : α₀} → {b₂ : α₀} → {c₃ : α₀} → Eq {α₀} a₁ b₂ → Eq {α₀} b₂ c₃ → Eq {α₀} a₁ c₃
  Eq:trans {α₀} {a₁} {b₂} {c₃} h₄ h₅ = Eq:rec {α₀} {b₂} {λ (x₆ : α₀) → λ (h₇ : Eq {α₀} b₂ x₆) → Eq {α₀} a₁ x₆} h₄ {c₃} h₅

False:elim : {C₀ : Set} → False → C₀
False:elim {C₀} h₁ = False:rec (λ (x₂ : False) → C₀) h₁

Function:comp : {α₀ : Set} → {β₁ : Set} → {δ₂ : Set} → (β₁ → δ₂) → (α₀ → β₁) → α₀ → δ₂
Function:comp {α₀} {β₁} {δ₂} f₃ g₄ x₅ = f₃ (g₄ x₅)

data HEq {α₀ : Set} : α₀ → {β₁ : Set} → β₁ → Set where
  HEq:refl : (a₁ : α₀) → HEq {α₀} a₁ {α₀} a₁

-- recursor
HEq:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : {β₂ : Set} → (a₃ : β₂) → HEq {α₀} a₁ {β₂} a₃ → Set} → motive₂ {α₀} a₁ (HEq:refl {α₀} a₁) → {β₃ : Set} → {a₄ : β₃} → (t₅ : HEq {α₀} a₁ {β₃} a₄) → motive₂ {β₃} a₄ t₅
HEq:rec {α₀} {a₁} {motive₂} refl₃ {_} {_} (HEq:refl _) = refl₃

cast : {α₀ : Set} → {β₁ : Set} → Eq {Set} α₀ β₁ → α₀ → β₁
cast {α₀} {β₁} h₂ a₃ = Eq:rec {Set} {α₀} {λ (x₄ : Set) → λ (x₅ : Eq {Set} α₀ x₄) → x₄} a₃ {β₁} h₂

-- theorem
opaque
  eq~uof~uheq : {α₀ : Set} → {a₁ : α₀} → {a₂ : α₀} → HEq {α₀} a₁ {α₀} a₂ → Eq {α₀} a₁ a₂
  eq~uof~uheq {α₀} {a₁} {a₂} h₃ = let this₄ : (α₄ : Set) → (β₅ : Set) → (a₆ : α₄) → (b₇ : β₅) → HEq {α₄} a₆ {β₅} b₇ → (h₈ : Eq {Set} α₄ β₅) → Eq {β₅} (cast {α₄} {β₅} h₈ a₆) b₇; this₄ = λ (x₄ : Set) → λ (x₅ : Set) → λ (x₆ : x₄) → λ (x₇ : x₅) → λ (h₈ : HEq {x₄} x₆ {x₅} x₇) → HEq:rec {x₄} {x₆} {λ {x₉ : Set} → λ (x₁₀ : x₉) → λ (x₁₁ : HEq {x₄} x₆ {x₉} x₁₀) → (h₁₂ : Eq {Set} x₄ x₉) → Eq {x₉} (cast {x₄} {x₉} h₁₂ x₆) x₁₀} (λ (x₉ : Eq {Set} x₄ x₄) → rfl {x₄} {cast {x₄} {x₄} x₉ x₆}) {x₅} {x₇} h₈ in this₄ α₀ α₀ a₁ a₂ h₃ (rfl {Set} {α₀})

data List (α₀ : Set) : Set where
  List:nil : List α₀
  List:cons : α₀ → List α₀ → List α₀

-- recursor
List:rec : {α₀ : Set} → {motive₁ : List α₀ → Set} → motive₁ (List:nil {α₀}) → ((head₂ : α₀) → (tail₃ : List α₀) → motive₁ tail₃ → motive₁ (List:cons {α₀} head₂ tail₃)) → (t₂ : List α₀) → motive₁ t₂
List:rec {α₀} {motive₁} nil₂ cons₃ List:nil = nil₂
List:rec {α₀} {motive₁} nil₂ cons₃ (List:cons head₄ tail₅) = cons₃ head₄ tail₅ (List:rec {α₀} {motive₁} nil₂ cons₃ tail₅)

outParam : Set → Set
outParam α₀ = α₀

record Membership (α₀ : outParam Set) (γ₁ : Set) : Set where
  constructor Membership:mk
  field
    mem₂ : γ₁ → α₀ → Set

-- recursor
Membership:rec : {α₀ : Set} → {γ₁ : Set} → {motive₂ : Membership α₀ γ₁ → Set} → ((mem₃ : γ₁ → α₀ → Set) → motive₂ (Membership:mk {α₀} {γ₁} mem₃)) → (t₃ : Membership α₀ γ₁) → motive₂ t₃
Membership:rec {α₀} {γ₁} {motive₂} mk₃ (Membership:mk mem₄) = mk₃ mem₄

Membership:mem : {α₀ : outParam Set} → {γ₁ : Set} → ⦃ _ : Membership α₀ γ₁ ⦄ → γ₁ → α₀ → Set
Membership:mem {α₀} {γ₁} ⦃ self₂ ⦄ = Membership.mem₂ {α₀} {γ₁} self₂

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

List:brecOn:go : {α₀ : Set} → {motive₁ : List α₀ → Set} → (t₂ : List α₀) → ((t₃ : List α₀) → List:below {α₀} {motive₁} t₃ → motive₁ t₃) → PProd (motive₁ t₂) (List:below {α₀} {motive₁} t₂)
List:brecOn:go {α₀} {motive₁} t₂ F1₃ = List:rec {α₀} {λ (t₄ : List α₀) → PProd (motive₁ t₄) (List:below {α₀} {motive₁} t₄)} (PProd:mk {motive₁ (List:nil {α₀})} {PUnit} (F1₃ (List:nil {α₀}) PUnit:unit) PUnit:unit) (λ (head₄ : α₀) → λ (tail₅ : List α₀) → λ (tailih₆ : PProd (motive₁ tail₅) (List:below {α₀} {motive₁} tail₅)) → PProd:mk {motive₁ (List:cons {α₀} head₄ tail₅)} {PProd (motive₁ tail₅) (List:below {α₀} {motive₁} tail₅)} (F1₃ (List:cons {α₀} head₄ tail₅) tailih₆) tailih₆) t₂

List:brecOn : {α₀ : Set} → {motive₁ : List α₀ → Set} → (t₂ : List α₀) → ((t₃ : List α₀) → List:below {α₀} {motive₁} t₃ → motive₁ t₃) → motive₁ t₂
List:brecOn {α₀} {motive₁} t₂ F1₃ = PProd.fst₂ {motive₁ t₂} {List:below {α₀} {motive₁} t₂} (List:brecOn:go {α₀} {motive₁} t₂ F1₃)

List:casesOn : {α₀ : Set} → {motive₁ : List α₀ → Set} → (t₂ : List α₀) → motive₁ (List:nil {α₀}) → ((head₃ : α₀) → (tail₄ : List α₀) → motive₁ (List:cons {α₀} head₃ tail₄)) → motive₁ t₂
List:casesOn {α₀} {motive₁} t₂ nil₃ cons₄ = List:rec {α₀} {motive₁} nil₃ (λ (head₅ : α₀) → λ (tail₆ : List α₀) → λ (tailih₇ : motive₁ tail₆) → cons₄ head₅ tail₆) t₂

List:noConfusionType : Set → {α₀ : Set} → List α₀ → {α₁ : Set} → List α₁ → Set
List:noConfusionType P₀ {α₁} t₂ {α₃} t₄ = List:casesOn {α₁} {λ (t₅ : List α₁) → Set} t₂ (List:casesOn {α₃} {λ (t₅ : List α₃) → Set} t₄ (P₀ → P₀) (λ (head₅ : α₃) → λ (tail₆ : List α₃) → P₀)) (λ (head₅ : α₁) → λ (tail₆ : List α₁) → List:casesOn {α₃} {λ (t₇ : List α₃) → Set} t₄ P₀ (λ (head₇ : α₃) → λ (tail₈ : List α₃) → (HEq {α₁} head₅ {α₃} head₇ → HEq {List α₁} tail₆ {List α₃} tail₈ → P₀) → P₀))

List:noConfusion : {P₀ : Set} → {α₁ : Set} → {t₂ : List α₁} → {α₃ : Set} → {t₄ : List α₃} → Eq {Set} α₁ α₃ → HEq {List α₁} t₂ {List α₃} t₄ → List:noConfusionType P₀ {α₁} t₂ {α₃} t₄
List:noConfusion {P₀} {α₁} {t₂} {α₃} {t₄} eq1₅ eq2₆ = Eq:ndrec {Set} {α₁} {λ (α₇ : Set) → {t₈ : List α₇} → HEq {List α₁} t₂ {List α₇} t₈ → List:noConfusionType P₀ {α₁} t₂ {α₇} t₈} (λ {t₇ : List α₁} → λ (eq2₈ : HEq {List α₁} t₂ {List α₁} t₇) → Eq:ndrec {List α₁} {t₂} {λ (t₉ : List α₁) → List:noConfusionType P₀ {α₁} t₂ {α₁} t₉} (List:casesOn {α₁} {λ (t₉ : List α₁) → List:noConfusionType P₀ {α₁} t₉ {α₁} t₉} t₂ (λ (k₉ : P₀) → k₉) (λ (head₉ : α₁) → λ (tail₁₀ : List α₁) → λ (k₁₁ : HEq {α₁} head₉ {α₁} head₉ → HEq {List α₁} tail₁₀ {List α₁} tail₁₀ → P₀) → k₁₁ (HEq:refl {α₁} head₉) (HEq:refl {List α₁} tail₁₀))) {t₇} (eq~uof~uheq {List α₁} {t₂} {t₇} eq2₈)) {α₃} eq1₅ {t₄} eq2₆

-- theorem
opaque
  heq~uof~ueq : {α₀ : Set} → {a₁ : α₀} → {a₂ : α₀} → Eq {α₀} a₁ a₂ → HEq {α₀} a₁ {α₀} a₂
  heq~uof~ueq {α₀} {a₁} {a₂} h₃ = Eq:subst {α₀} {HEq {α₀} a₁ {α₀}} {a₁} {a₂} h₃ (HEq:refl {α₀} a₁)

id : {α₀ : Set} → α₀ → α₀
id {α₀} a₁ = a₁

List:cons:noConfusion : {α₀ : Set} → {P₁ : Set} → {head₂ : α₀} → {tail₃ : List α₀} → {head₄ : α₀} → {tail₅ : List α₀} → Eq {List α₀} (List:cons {α₀} head₂ tail₃) (List:cons {α₀} head₄ tail₅) → (HEq {α₀} head₂ {α₀} head₄ → HEq {List α₀} tail₃ {List α₀} tail₅ → P₁) → P₁
List:cons:noConfusion {α₀} {P₁} {head₂} {tail₃} {head₄} {tail₅} eq₆ k₇ = id {P₁} (List:noConfusion {P₁} {α₀} {List:cons {α₀} head₂ tail₃} {α₀} {List:cons {α₀} head₄ tail₅} (Eq:refl {Set} α₀) (heq~uof~ueq {List α₀} {List:cons {α₀} head₂ tail₃} {List:cons {α₀} head₄ tail₅} eq₆) k₇)

data Or (a₀ : Set) (b₁ : Set) : Set where
  Or:inl : a₀ → Or a₀ b₁
  Or:inr : b₁ → Or a₀ b₁

-- recursor
Or:rec : {a₀ : Set} → {b₁ : Set} → {motive₂ : Or a₀ b₁ → Set} → ((h₃ : a₀) → motive₂ (Or:inl {a₀} {b₁} h₃)) → ((h₃ : b₁) → motive₂ (Or:inr {a₀} {b₁} h₃)) → (t₃ : Or a₀ b₁) → motive₂ t₃
Or:rec {a₀} {b₁} {motive₂} inl₃ inr₄ (Or:inl h₅) = inl₃ h₅
Or:rec {a₀} {b₁} {motive₂} inl₃ inr₄ (Or:inr h₅) = inr₄ h₅

record True : Set where
  constructor True:intro

-- recursor
True:rec : {motive₀ : True → Set} → motive₀ True:intro → (t₁ : True) → motive₀ t₁
True:rec {motive₀} intro₁ True:intro = intro₁

Unit : Set
Unit = PUnit

Or:casesOn : {a₀ : Set} → {b₁ : Set} → {motive₂ : Or a₀ b₁ → Set} → (t₃ : Or a₀ b₁) → ((h₄ : a₀) → motive₂ (Or:inl {a₀} {b₁} h₄)) → ((h₄ : b₁) → motive₂ (Or:inr {a₀} {b₁} h₄)) → motive₂ t₃
Or:casesOn {a₀} {b₁} {motive₂} t₃ inl₄ inr₅ = Or:rec {a₀} {b₁} {motive₂} (λ (h₆ : a₀) → inl₄ h₆) (λ (h₆ : b₁) → inr₅ h₆) t₃

Unit:unit : Unit
Unit:unit = PUnit:unit

-- theorem
opaque
  congrArg : {α₀ : Set} → {β₁ : Set} → {a₂ : α₀} → {a₃ : α₀} → (f₄ : α₀ → β₁) → Eq {α₀} a₂ a₃ → Eq {β₁} (f₄ a₂) (f₄ a₃)
  congrArg {α₀} {β₁} {a₂} {a₃} f₄ h₅ = Eq:rec {α₀} {a₂} {λ (x₆ : α₀) → λ (h₇ : Eq {α₀} a₂ x₆) → Eq {β₁} (f₄ a₂) (f₄ x₆)} (rfl {β₁} {f₄ a₂}) {a₃} h₅

-- theorem
opaque
  congrFun~x27~ : {α₀ : Set} → {β₁ : Set} → {f₂ : α₀ → β₁} → {g₃ : α₀ → β₁} → Eq {α₀ → β₁} f₂ g₃ → (a₄ : α₀) → Eq {β₁} (f₂ a₄) (g₃ a₄)
  congrFun~x27~ {α₀} {β₁} {f₂} {g₃} h₄ a₅ = Eq:rec {α₀ → β₁} {f₂} {λ (x₆ : α₀ → β₁) → λ (h₇ : Eq {α₀ → β₁} f₂ x₆) → Eq {β₁} (f₂ a₅) (x₆ a₅)} (rfl {β₁} {f₂ a₅}) {g₃} h₄

-- theorem
opaque
  congr : {α₀ : Set} → {β₁ : Set} → {f₂ : α₀ → β₁} → {f₃ : α₀ → β₁} → {a₄ : α₀} → {a₅ : α₀} → Eq {α₀ → β₁} f₂ f₃ → Eq {α₀} a₄ a₅ → Eq {β₁} (f₂ a₄) (f₃ a₅)
  congr {α₀} {β₁} {f₂} {f₃} {a₄} {a₅} h₆ h₇ = Eq:rec {α₀ → β₁} {f₂} {λ (x₈ : α₀ → β₁) → λ (h₉ : Eq {α₀ → β₁} f₂ x₈) → Eq {β₁} (f₂ a₄) (x₈ a₅)} (Eq:rec {α₀} {a₄} {λ (x₈ : α₀) → λ (h₉ : Eq {α₀} a₄ x₈) → Eq {β₁} (f₂ a₄) (f₂ x₈)} (rfl {β₁} {f₂ a₄}) {a₅} h₇) {f₃} h₆

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

Nat:below : {_ : Nat → Set} → Nat → Set
Nat:below {motive₀} t₁ = Nat:rec {λ (t₂ : Nat) → Set} PUnit (λ (n₂ : Nat) → λ (nih₃ : Set) → PProd (motive₀ n₂) nih₃) t₁

Nat:casesOn : {motive₀ : Nat → Set} → (t₁ : Nat) → motive₀ Nat:zero → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ t₁
Nat:casesOn {motive₀} t₁ zero₂ succ₃ = Nat:rec {motive₀} zero₂ (λ (n₄ : Nat) → λ (nih₅ : motive₀ n₄) → succ₃ n₄) t₁

Nat:ble:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → ((x₃ : Nat) → motive₀ Nat:zero x₃) → ((n₃ : Nat) → motive₀ (Nat:succ n₃) Nat:zero) → ((n₃ : Nat) → (m₄ : Nat) → motive₀ (Nat:succ n₃) (Nat:succ m₄)) → motive₀ x₁ x₂
Nat:ble:match~u1 motive₀ x₁ x₂ h1₃ h2₄ h3₅ = Nat:casesOn {λ (x₆ : Nat) → motive₀ x₆ x₂} x₁ (h1₃ x₂) (λ (n₆ : Nat) → Nat:casesOn {λ (x₇ : Nat) → motive₀ (Nat:succ n₆) x₇} x₂ (h2₄ n₆) (λ (n₇ : Nat) → h3₅ n₆ n₇))

Nat:ble:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Nat → Bool} x₀ → Nat → Bool
Nat:ble:~uf x₀ f₁ x₂ = Nat:ble:match~u1 (λ (x₃ : Nat) → λ (x₄ : Nat) → Nat:below {λ (x₅ : Nat) → Nat → Bool} x₃ → Bool) x₀ x₂ (λ (x₃ : Nat) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Bool} Nat:zero) → Bool:true) (λ (n₃ : Nat) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Bool} (Nat:succ n₃)) → Bool:false) (λ (n₃ : Nat) → λ (m₄ : Nat) → λ (x₅ : Nat:below {λ (x₅ : Nat) → Nat → Bool} (Nat:succ n₃)) → PProd.fst₂ {(λ (x₆ : Nat) → Nat → Bool) n₃} {Nat:rec {λ (t₆ : Nat) → Set} PUnit (λ (n₆ : Nat) → λ (nih₇ : Set) → PProd ((λ (x₈ : Nat) → Nat → Bool) n₆) nih₇) n₃} x₅ m₄) f₁

Nat:brecOn:go : {motive₀ : Nat → Set} → (t₁ : Nat) → ((t₂ : Nat) → Nat:below {motive₀} t₂ → motive₀ t₂) → PProd (motive₀ t₁) (Nat:below {motive₀} t₁)
Nat:brecOn:go {motive₀} t₁ F1₂ = Nat:rec {λ (t₃ : Nat) → PProd (motive₀ t₃) (Nat:below {motive₀} t₃)} (PProd:mk {motive₀ Nat:zero} {PUnit} (F1₂ Nat:zero PUnit:unit) PUnit:unit) (λ (n₃ : Nat) → λ (nih₄ : PProd (motive₀ n₃) (Nat:below {motive₀} n₃)) → PProd:mk {motive₀ (Nat:succ n₃)} {PProd (motive₀ n₃) (Nat:below {motive₀} n₃)} (F1₂ (Nat:succ n₃) nih₄) nih₄) t₁

Nat:brecOn : {motive₀ : Nat → Set} → (t₁ : Nat) → ((t₂ : Nat) → Nat:below {motive₀} t₂ → motive₀ t₂) → motive₀ t₁
Nat:brecOn {motive₀} t₁ F1₂ = PProd.fst₂ {motive₀ t₁} {Nat:below {motive₀} t₁} (Nat:brecOn:go {motive₀} t₁ F1₂)

-- operation table
Nat:blt-builtin : Nat → Nat → Bool
Nat:blt-builtin n₀ Nat:zero = Bool:false
Nat:blt-builtin Nat:zero (Nat:succ m₁) = Bool:true
Nat:blt-builtin (Nat:succ n₀) (Nat:succ m₁) = Nat:blt-builtin n₀ m₁
{-# BUILTIN NATLESS Nat:blt-builtin #-}

-- operation table
Nat:ble : Nat → Nat → Bool
Nat:ble x₀ x₁ = Nat:blt-builtin x₀ (Nat:succ x₁)

record PULift (α₀ : Set) : Set where
  constructor PULift:up
  field
    down₁ : α₀

-- recursor
PULift:rec : {α₀ : Set} → {motive₁ : PULift α₀ → Set} → ((down₂ : α₀) → motive₁ (PULift:up {α₀} down₂)) → (t₂ : PULift α₀) → motive₁ t₂
PULift:rec {α₀} {motive₁} up₂ (PULift:up down₃) = up₂ down₃

cond:match~u1 : (motive₀ : Bool → Set) → (c₁ : Bool) → (Unit → motive₀ Bool:true) → (Unit → motive₀ Bool:false) → motive₀ c₁
cond:match~u1 motive₀ c₁ h1₂ h2₃ = Bool:casesOn {λ (x₄ : Bool) → motive₀ x₄} c₁ (h2₃ Unit:unit) (h1₂ Unit:unit)

cond : {α₀ : Set} → Bool → α₀ → α₀ → α₀
cond {α₀} c₁ x₂ y₃ = cond:match~u1 (λ (c₄ : Bool) → α₀) c₁ (λ (x₄ : Unit) → x₂) (λ (x₄ : Unit) → y₃)

PULift:down : {α₀ : Set} → PULift α₀ → α₀
PULift:down {α₀} self₁ = PULift.down₁ {α₀} self₁

Nat:beq:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → (Unit → motive₀ Nat:zero Nat:zero) → ((n₃ : Nat) → motive₀ Nat:zero (Nat:succ n₃)) → ((n₃ : Nat) → motive₀ (Nat:succ n₃) Nat:zero) → ((n₃ : Nat) → (m₄ : Nat) → motive₀ (Nat:succ n₃) (Nat:succ m₄)) → motive₀ x₁ x₂
Nat:beq:match~u1 motive₀ x₁ x₂ h1₃ h2₄ h3₅ h4₆ = Nat:casesOn {λ (x₇ : Nat) → motive₀ x₇ x₂} x₁ (Nat:casesOn {λ (x₇ : Nat) → motive₀ Nat:zero x₇} x₂ (h1₃ Unit:unit) (λ (n₇ : Nat) → h2₄ n₇)) (λ (n₇ : Nat) → Nat:casesOn {λ (x₈ : Nat) → motive₀ (Nat:succ n₇) x₈} x₂ (h3₅ n₇) (λ (n₈ : Nat) → h4₆ n₇ n₈))

Nat:beq:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Nat → Bool} x₀ → Nat → Bool
Nat:beq:~uf x₀ f₁ x₂ = Nat:beq:match~u1 (λ (x₃ : Nat) → λ (x₄ : Nat) → Nat:below {λ (x₅ : Nat) → Nat → Bool} x₃ → Bool) x₀ x₂ (λ (x₃ : Unit) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Bool} Nat:zero) → Bool:true) (λ (n₃ : Nat) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Bool} Nat:zero) → Bool:false) (λ (n₃ : Nat) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Bool} (Nat:succ n₃)) → Bool:false) (λ (n₃ : Nat) → λ (m₄ : Nat) → λ (x₅ : Nat:below {λ (x₅ : Nat) → Nat → Bool} (Nat:succ n₃)) → PProd.fst₂ {(λ (x₆ : Nat) → Nat → Bool) n₃} {Nat:rec {λ (t₆ : Nat) → Set} PUnit (λ (n₆ : Nat) → λ (nih₇ : Set) → PProd ((λ (x₈ : Nat) → Nat → Bool) n₆) nih₇) n₃} x₅ m₄) f₁

-- operation table
Nat:beq : Nat → Nat → Bool
Nat:beq Nat:zero Nat:zero = Bool:true
Nat:beq (Nat:succ n₀) (Nat:succ m₁) = Nat:beq n₀ m₁
Nat:beq Nat:zero (Nat:succ m₁) = Bool:false
Nat:beq (Nat:succ n₀) Nat:zero = Bool:false
{-# BUILTIN NATEQUALS Nat:beq #-}

Nat:decEq:match~u1 : (motive₀ : Bool → Set) → (x₁ : Bool) → (Eq {Bool} x₁ Bool:true → motive₀ Bool:true) → (Eq {Bool} x₁ Bool:false → motive₀ Bool:false) → motive₀ x₁
Nat:decEq:match~u1 motive₀ x₁ h1₂ h2₃ = (λ (x₄ : Bool) → Bool:casesOn {λ (x₅ : Bool) → Eq {Bool} x₁ x₅ → motive₀ x₅} x₄ h2₃ h1₂) x₁ (Eq:refl {Bool} x₁)

~uprivate:Init:Prelude:~n0:Nat:eq~uof~ubeq~ueq~utrue:match~u1~u1 : (motive₀ : (x₀ : Nat) → (x₁ : Nat) → Eq {Bool} (Nat:beq x₀ x₁) Bool:true → Set) → (x₁ : Nat) → (x₂ : Nat) → (x₃ : Eq {Bool} (Nat:beq x₁ x₂) Bool:true) → ((x₄ : Eq {Bool} (Nat:beq Nat:zero Nat:zero) Bool:true) → motive₀ Nat:zero Nat:zero x₄) → ((n₄ : Nat) → (h₅ : Eq {Bool} (Nat:beq Nat:zero (Nat:succ n₄)) Bool:true) → motive₀ Nat:zero (Nat:succ n₄) h₅) → ((n₄ : Nat) → (h₅ : Eq {Bool} (Nat:beq (Nat:succ n₄) Nat:zero) Bool:true) → motive₀ (Nat:succ n₄) Nat:zero h₅) → ((n₄ : Nat) → (m₅ : Nat) → (h₆ : Eq {Bool} (Nat:beq (Nat:succ n₄) (Nat:succ m₅)) Bool:true) → motive₀ (Nat:succ n₄) (Nat:succ m₅) h₆) → motive₀ x₁ x₂ x₃
~uprivate:Init:Prelude:~n0:Nat:eq~uof~ubeq~ueq~utrue:match~u1~u1 motive₀ x₁ x₂ x₃ h1₄ h2₅ h3₆ h4₇ = Nat:casesOn {λ (x₈ : Nat) → (x₉ : Eq {Bool} (Nat:beq x₈ x₂) Bool:true) → motive₀ x₈ x₂ x₉} x₁ (λ (x₈ : Eq {Bool} (Nat:beq Nat:zero x₂) Bool:true) → Nat:casesOn {λ (x₉ : Nat) → (x₁₀ : Eq {Bool} (Nat:beq Nat:zero x₉) Bool:true) → motive₀ Nat:zero x₉ x₁₀} x₂ (λ (x₉ : Eq {Bool} (Nat:beq Nat:zero Nat:zero) Bool:true) → h1₄ x₉) (λ (n₉ : Nat) → λ (x₁₀ : Eq {Bool} (Nat:beq Nat:zero (Nat:succ n₉)) Bool:true) → h2₅ n₉ x₁₀) x₈) (λ (n₈ : Nat) → λ (x₉ : Eq {Bool} (Nat:beq (Nat:succ n₈) x₂) Bool:true) → Nat:casesOn {λ (x₁₀ : Nat) → (x₁₁ : Eq {Bool} (Nat:beq (Nat:succ n₈) x₁₀) Bool:true) → motive₀ (Nat:succ n₈) x₁₀ x₁₁} x₂ (λ (x₁₀ : Eq {Bool} (Nat:beq (Nat:succ n₈) Nat:zero) Bool:true) → h3₆ n₈ x₁₀) (λ (n₁₀ : Nat) → λ (x₁₁ : Eq {Bool} (Nat:beq (Nat:succ n₈) (Nat:succ n₁₀)) Bool:true) → h4₇ n₈ n₁₀ x₁₁) x₉) x₃

Nat:eq~uof~ubeq~ueq~utrue:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → (x₂ : Nat) → Eq {Bool} (Nat:beq x₁ x₂) Bool:true → Eq {Nat} x₁ x₂} x₀ → (x₁ : Nat) → Eq {Bool} (Nat:beq x₀ x₁) Bool:true → Eq {Nat} x₀ x₁
Nat:eq~uof~ubeq~ueq~utrue:~uf x₀ f₁ x₂ x₃ = ~uprivate:Init:Prelude:~n0:Nat:eq~uof~ubeq~ueq~utrue:match~u1~u1 (λ (x₄ : Nat) → λ (x₅ : Nat) → λ (x₆ : Eq {Bool} (Nat:beq x₄ x₅) Bool:true) → Nat:below {λ (x₇ : Nat) → (x₈ : Nat) → Eq {Bool} (Nat:beq x₇ x₈) Bool:true → Eq {Nat} x₇ x₈} x₄ → Eq {Nat} x₄ x₅) x₀ x₂ x₃ (λ (x₄ : Eq {Bool} (Nat:beq Nat:zero Nat:zero) Bool:true) → λ (x₅ : Nat:below {λ (x₅ : Nat) → (x₆ : Nat) → Eq {Bool} (Nat:beq x₅ x₆) Bool:true → Eq {Nat} x₅ x₆} Nat:zero) → rfl {Nat} {Nat:zero}) (λ (n₄ : Nat) → λ (h₅ : Eq {Bool} (Nat:beq Nat:zero (Nat:succ n₄)) Bool:true) → λ (x₆ : Nat:below {λ (x₆ : Nat) → (x₇ : Nat) → Eq {Bool} (Nat:beq x₆ x₇) Bool:true → Eq {Nat} x₆ x₇} Nat:zero) → Bool:noConfusion {Eq {Nat} Nat:zero (Nat:succ n₄)} {Nat:beq Nat:zero (Nat:succ n₄)} {Bool:true} h₅) (λ (n₄ : Nat) → λ (h₅ : Eq {Bool} (Nat:beq (Nat:succ n₄) Nat:zero) Bool:true) → λ (x₆ : Nat:below {λ (x₆ : Nat) → (x₇ : Nat) → Eq {Bool} (Nat:beq x₆ x₇) Bool:true → Eq {Nat} x₆ x₇} (Nat:succ n₄)) → Bool:noConfusion {Eq {Nat} (Nat:succ n₄) Nat:zero} {Nat:beq (Nat:succ n₄) Nat:zero} {Bool:true} h₅) (λ (n₄ : Nat) → λ (m₅ : Nat) → λ (h₆ : Eq {Bool} (Nat:beq (Nat:succ n₄) (Nat:succ m₅)) Bool:true) → λ (x₇ : Nat:below {λ (x₇ : Nat) → (x₈ : Nat) → Eq {Bool} (Nat:beq x₇ x₈) Bool:true → Eq {Nat} x₇ x₈} (Nat:succ n₄)) → let this₈ : Eq {Bool} (Nat:beq n₄ m₅) Bool:true; this₈ = h₆ in let this₉ : Eq {Nat} n₄ m₅; this₉ = PProd.fst₂ {(λ (x₉ : Nat) → (x₁₀ : Nat) → Eq {Bool} (Nat:beq x₉ x₁₀) Bool:true → Eq {Nat} x₉ x₁₀) n₄} {Nat:rec {λ (t₉ : Nat) → Set} PUnit (λ (n₉ : Nat) → λ (nih₁₀ : Set) → PProd ((λ (x₁₁ : Nat) → (x₁₂ : Nat) → Eq {Bool} (Nat:beq x₁₁ x₁₂) Bool:true → Eq {Nat} x₁₁ x₁₂) n₉) nih₁₀) n₄} x₇ m₅ this₈ in Eq:rec {Nat} {n₄} {λ (x₁₀ : Nat) → λ (h₁₁ : Eq {Nat} n₄ x₁₀) → Eq {Nat} (Nat:succ n₄) (Nat:succ x₁₀)} (rfl {Nat} {Nat:succ n₄}) {m₅} this₉) f₁

-- theorem
opaque
  Nat:eq~uof~ubeq~ueq~utrue : {n₀ : Nat} → {m₁ : Nat} → Eq {Bool} (Nat:beq n₀ m₁) Bool:true → Eq {Nat} n₀ m₁
  Nat:eq~uof~ubeq~ueq~utrue {x₀} {x₁} x₂ = Nat:brecOn {λ (x₃ : Nat) → (x₄ : Nat) → Eq {Bool} (Nat:beq x₃ x₄) Bool:true → Eq {Nat} x₃ x₄} x₀ Nat:eq~uof~ubeq~ueq~utrue:~uf x₁ x₂

Nat:noConfusionType : Set → Nat → Nat → Set
Nat:noConfusionType P₀ t₁ t₂ = Nat:casesOn {λ (t₃ : Nat) → Set} t₁ (Nat:casesOn {λ (t₃ : Nat) → Set} t₂ (P₀ → P₀) (λ (n₃ : Nat) → P₀)) (λ (n₃ : Nat) → Nat:casesOn {λ (t₄ : Nat) → Set} t₂ P₀ (λ (n₄ : Nat) → (Eq {Nat} n₃ n₄ → P₀) → P₀))

Nat:noConfusion : {P₀ : Set} → {t₁ : Nat} → {t₂ : Nat} → Eq {Nat} t₁ t₂ → Nat:noConfusionType P₀ t₁ t₂
Nat:noConfusion {P₀} {t₁} {t₂} eq₃ = Eq:ndrec {Nat} {t₁} {λ (t₄ : Nat) → Nat:noConfusionType P₀ t₁ t₄} (Nat:casesOn {λ (t₄ : Nat) → Nat:noConfusionType P₀ t₄ t₄} t₁ (λ (k₄ : P₀) → k₄) (λ (n₄ : Nat) → λ (k₅ : Eq {Nat} n₄ n₄ → P₀) → k₅ (Eq:refl {Nat} n₄))) {t₂} eq₃

~uprivate:Init:Prelude:~n0:Nat:ne~uof~ubeq~ueq~ufalse:match~u1~u1 : (motive₀ : (x₀ : Nat) → (x₁ : Nat) → Eq {Bool} (Nat:beq x₀ x₁) Bool:false → Eq {Nat} x₀ x₁ → Set) → (x₁ : Nat) → (x₂ : Nat) → (x₃ : Eq {Bool} (Nat:beq x₁ x₂) Bool:false) → (x₄ : Eq {Nat} x₁ x₂) → ((h₅ : Eq {Bool} (Nat:beq Nat:zero Nat:zero) Bool:false) → (x₆ : Eq {Nat} Nat:zero Nat:zero) → motive₀ Nat:zero Nat:zero h₅ x₆) → ((n₅ : Nat) → (x₆ : Eq {Bool} (Nat:beq Nat:zero (Nat:succ n₅)) Bool:false) → (h₇ : Eq {Nat} Nat:zero (Nat:succ n₅)) → motive₀ Nat:zero (Nat:succ n₅) x₆ h₇) → ((n₅ : Nat) → (x₆ : Eq {Bool} (Nat:beq (Nat:succ n₅) Nat:zero) Bool:false) → (h₇ : Eq {Nat} (Nat:succ n₅) Nat:zero) → motive₀ (Nat:succ n₅) Nat:zero x₆ h₇) → ((n₅ : Nat) → (m₆ : Nat) → (h₇ : Eq {Bool} (Nat:beq (Nat:succ n₅) (Nat:succ m₆)) Bool:false) → (h₈ : Eq {Nat} (Nat:succ n₅) (Nat:succ m₆)) → motive₀ (Nat:succ n₅) (Nat:succ m₆) h₇ h₈) → motive₀ x₁ x₂ x₃ x₄
~uprivate:Init:Prelude:~n0:Nat:ne~uof~ubeq~ueq~ufalse:match~u1~u1 motive₀ x₁ x₂ x₃ x₄ h1₅ h2₆ h3₇ h4₈ = Nat:casesOn {λ (x₉ : Nat) → (x₁₀ : Eq {Bool} (Nat:beq x₉ x₂) Bool:false) → (x₁₁ : Eq {Nat} x₉ x₂) → motive₀ x₉ x₂ x₁₀ x₁₁} x₁ (λ (x₉ : Eq {Bool} (Nat:beq Nat:zero x₂) Bool:false) → λ (x₁₀ : Eq {Nat} Nat:zero x₂) → Nat:casesOn {λ (x₁₁ : Nat) → (x₁₂ : Eq {Bool} (Nat:beq Nat:zero x₁₁) Bool:false) → (x₁₃ : Eq {Nat} Nat:zero x₁₁) → motive₀ Nat:zero x₁₁ x₁₂ x₁₃} x₂ (λ (x₁₁ : Eq {Bool} (Nat:beq Nat:zero Nat:zero) Bool:false) → λ (x₁₂ : Eq {Nat} Nat:zero Nat:zero) → h1₅ x₁₁ x₁₂) (λ (n₁₁ : Nat) → λ (x₁₂ : Eq {Bool} (Nat:beq Nat:zero (Nat:succ n₁₁)) Bool:false) → λ (x₁₃ : Eq {Nat} Nat:zero (Nat:succ n₁₁)) → h2₆ n₁₁ x₁₂ x₁₃) x₉ x₁₀) (λ (n₉ : Nat) → λ (x₁₀ : Eq {Bool} (Nat:beq (Nat:succ n₉) x₂) Bool:false) → λ (x₁₁ : Eq {Nat} (Nat:succ n₉) x₂) → Nat:casesOn {λ (x₁₂ : Nat) → (x₁₃ : Eq {Bool} (Nat:beq (Nat:succ n₉) x₁₂) Bool:false) → (x₁₄ : Eq {Nat} (Nat:succ n₉) x₁₂) → motive₀ (Nat:succ n₉) x₁₂ x₁₃ x₁₄} x₂ (λ (x₁₂ : Eq {Bool} (Nat:beq (Nat:succ n₉) Nat:zero) Bool:false) → λ (x₁₃ : Eq {Nat} (Nat:succ n₉) Nat:zero) → h3₇ n₉ x₁₂ x₁₃) (λ (n₁₂ : Nat) → λ (x₁₃ : Eq {Bool} (Nat:beq (Nat:succ n₉) (Nat:succ n₁₂)) Bool:false) → λ (x₁₄ : Eq {Nat} (Nat:succ n₉) (Nat:succ n₁₂)) → h4₈ n₉ n₁₂ x₁₃ x₁₄) x₁₀ x₁₁) x₃ x₄

absurd : {a₀ : Set} → {b₁ : Set} → a₀ → Not a₀ → b₁
absurd {a₀} {b₁} h₂ h₃ = False:rec (λ (x₄ : False) → b₁) (h₃ h₂)

Nat:ne~uof~ubeq~ueq~ufalse:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → (x₂ : Nat) → Eq {Bool} (Nat:beq x₁ x₂) Bool:false → Eq {Nat} x₁ x₂ → False} x₀ → (x₁ : Nat) → Eq {Bool} (Nat:beq x₀ x₁) Bool:false → Eq {Nat} x₀ x₁ → False
Nat:ne~uof~ubeq~ueq~ufalse:~uf x₀ f₁ x₂ x₃ x₄ = ~uprivate:Init:Prelude:~n0:Nat:ne~uof~ubeq~ueq~ufalse:match~u1~u1 (λ (x₅ : Nat) → λ (x₆ : Nat) → λ (x₇ : Eq {Bool} (Nat:beq x₅ x₆) Bool:false) → λ (x₈ : Eq {Nat} x₅ x₆) → Nat:below {λ (x₉ : Nat) → (x₁₀ : Nat) → Eq {Bool} (Nat:beq x₉ x₁₀) Bool:false → Eq {Nat} x₉ x₁₀ → False} x₅ → False) x₀ x₂ x₃ x₄ (λ (h₅ : Eq {Bool} (Nat:beq Nat:zero Nat:zero) Bool:false) → λ (x₆ : Eq {Nat} Nat:zero Nat:zero) → λ (x₇ : Nat:below {λ (x₇ : Nat) → (x₈ : Nat) → Eq {Bool} (Nat:beq x₇ x₈) Bool:false → Eq {Nat} x₇ x₈ → False} Nat:zero) → Bool:noConfusion {False} {Nat:beq Nat:zero Nat:zero} {Bool:false} h₅) (λ (n₅ : Nat) → λ (x₆ : Eq {Bool} (Nat:beq Nat:zero (Nat:succ n₅)) Bool:false) → λ (h₇ : Eq {Nat} Nat:zero (Nat:succ n₅)) → λ (x₈ : Nat:below {λ (x₈ : Nat) → (x₉ : Nat) → Eq {Bool} (Nat:beq x₈ x₉) Bool:false → Eq {Nat} x₈ x₉ → False} Nat:zero) → Nat:noConfusion {False} {Nat:zero} {Nat:succ n₅} h₇) (λ (n₅ : Nat) → λ (x₆ : Eq {Bool} (Nat:beq (Nat:succ n₅) Nat:zero) Bool:false) → λ (h₇ : Eq {Nat} (Nat:succ n₅) Nat:zero) → λ (x₈ : Nat:below {λ (x₈ : Nat) → (x₉ : Nat) → Eq {Bool} (Nat:beq x₈ x₉) Bool:false → Eq {Nat} x₈ x₉ → False} (Nat:succ n₅)) → Nat:noConfusion {False} {Nat:succ n₅} {Nat:zero} h₇) (λ (n₅ : Nat) → λ (m₆ : Nat) → λ (h₇ : Eq {Bool} (Nat:beq (Nat:succ n₅) (Nat:succ m₆)) Bool:false) → λ (h₈ : Eq {Nat} (Nat:succ n₅) (Nat:succ m₆)) → λ (x₉ : Nat:below {λ (x₉ : Nat) → (x₁₀ : Nat) → Eq {Bool} (Nat:beq x₉ x₁₀) Bool:false → Eq {Nat} x₉ x₁₀ → False} (Nat:succ n₅)) → let this₁₀ : Eq {Bool} (Nat:beq n₅ m₆) Bool:false; this₁₀ = h₇ in Nat:noConfusion {False} {Nat:succ n₅} {Nat:succ m₆} h₈ (λ (h₁₁ : Eq {Nat} n₅ m₆) → absurd {Eq {Nat} n₅ m₆} {False} h₁₁ (PProd.fst₂ {(λ (x₁₂ : Nat) → (x₁₃ : Nat) → Eq {Bool} (Nat:beq x₁₂ x₁₃) Bool:false → Eq {Nat} x₁₂ x₁₃ → False) n₅} {Nat:rec {λ (t₁₂ : Nat) → Set} PUnit (λ (n₁₂ : Nat) → λ (nih₁₃ : Set) → PProd ((λ (x₁₄ : Nat) → (x₁₅ : Nat) → Eq {Bool} (Nat:beq x₁₄ x₁₅) Bool:false → Eq {Nat} x₁₄ x₁₅ → False) n₁₂) nih₁₃) n₅} x₉ m₆ this₁₀))) f₁

-- theorem
opaque
  Nat:ne~uof~ubeq~ueq~ufalse : {n₀ : Nat} → {m₁ : Nat} → Eq {Bool} (Nat:beq n₀ m₁) Bool:false → Not (Eq {Nat} n₀ m₁)
  Nat:ne~uof~ubeq~ueq~ufalse {x₀} {x₁} x₂ x₃ = Nat:brecOn {λ (x₄ : Nat) → (x₅ : Nat) → Eq {Bool} (Nat:beq x₄ x₅) Bool:false → Eq {Nat} x₄ x₅ → False} x₀ Nat:ne~uof~ubeq~ueq~ufalse:~uf x₁ x₂ x₃

Nat:decEq : (n₀ : Nat) → (m₁ : Nat) → Decidable (Eq {Nat} n₀ m₁)
Nat:decEq n₀ m₁ = Nat:decEq:match~u1 (λ (x₂ : Bool) → Decidable (Eq {Nat} n₀ m₁)) (Nat:beq n₀ m₁) (λ (h₂ : Eq {Bool} (Nat:beq n₀ m₁) Bool:true) → Decidable:isTrue {Eq {Nat} n₀ m₁} (Nat:eq~uof~ubeq~ueq~utrue {n₀} {m₁} h₂)) (λ (h₂ : Eq {Bool} (Nat:beq n₀ m₁) Bool:false) → Decidable:isFalse {Eq {Nat} n₀ m₁} (Nat:ne~uof~ubeq~ueq~ufalse {n₀} {m₁} h₂))

dite : {α₀ : Set} → (c₁ : Set) → ⦃ _ : Decidable c₁ ⦄ → (c₁ → α₀) → (Not c₁ → α₀) → α₀
dite {α₀} c₁ ⦃ h₂ ⦄ t₃ e₄ = Decidable:casesOn {c₁} {λ (x₅ : Decidable c₁) → α₀} h₂ e₄ t₃

~uprivate:Init:Prelude:~n0:noConfusion~uof~uNat:aux:match~u1~u1 : (motive₀ : Nat → Set) → (x₁ : Nat) → (Unit → motive₀ Nat:zero) → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ x₁
~uprivate:Init:Prelude:~n0:noConfusion~uof~uNat:aux:match~u1~u1 motive₀ x₁ h1₂ h2₃ = Nat:casesOn {λ (x₄ : Nat) → motive₀ x₄} x₁ (h1₂ Unit:unit) (λ (n₄ : Nat) → h2₃ n₄)

~uprivate:Init:Prelude:~n0:noConfusion~uof~uNat:aux:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Bool:rec {λ (x₂ : Bool) → Set} False True (Nat:beq x₁ x₁)} x₀ → Bool:rec {λ (x₁ : Bool) → Set} False True (Nat:beq x₀ x₀)
~uprivate:Init:Prelude:~n0:noConfusion~uof~uNat:aux:~uf x₀ f₁ = ~uprivate:Init:Prelude:~n0:noConfusion~uof~uNat:aux:match~u1~u1 (λ (x₂ : Nat) → Nat:below {λ (x₃ : Nat) → Bool:rec {λ (x₄ : Bool) → Set} False True (Nat:beq x₃ x₃)} x₂ → Bool:rec {λ (x₃ : Bool) → Set} False True (Nat:beq x₂ x₂)) x₀ (λ (x₂ : Unit) → λ (x₃ : Nat:below {λ (x₃ : Nat) → Bool:rec {λ (x₄ : Bool) → Set} False True (Nat:beq x₃ x₃)} Nat:zero) → True:intro) (λ (n₂ : Nat) → λ (x₃ : Nat:below {λ (x₃ : Nat) → Bool:rec {λ (x₄ : Bool) → Set} False True (Nat:beq x₃ x₃)} (Nat:succ n₂)) → PProd.fst₂ {(λ (x₄ : Nat) → Bool:rec {λ (x₅ : Bool) → Set} False True (Nat:beq x₄ x₄)) n₂} {Nat:rec {λ (t₄ : Nat) → Set} PUnit (λ (n₄ : Nat) → λ (nih₅ : Set) → PProd ((λ (x₆ : Nat) → Bool:rec {λ (x₇ : Bool) → Set} False True (Nat:beq x₆ x₆)) n₄) nih₅) n₂} x₃) f₁

-- theorem
opaque
  ~uprivate:Init:Prelude:~n0:noConfusion~uof~uNat:aux : (a₀ : Nat) → Bool:rec {λ (x₁ : Bool) → Set} False True (Nat:beq a₀ a₀)
  ~uprivate:Init:Prelude:~n0:noConfusion~uof~uNat:aux x₀ = Nat:brecOn {λ (x₁ : Nat) → Bool:rec {λ (x₂ : Bool) → Set} False True (Nat:beq x₁ x₁)} x₀ ~uprivate:Init:Prelude:~n0:noConfusion~uof~uNat:aux:~uf

-- theorem
opaque
  noConfusion~uof~uNat : {α₀ : Set} → (f₁ : α₀ → Nat) → {a₂ : α₀} → {b₃ : α₀} → Eq {α₀} a₂ b₃ → Bool:rec {λ (x₄ : Bool) → Set} False True (Nat:beq (f₁ a₂) (f₁ b₃))
  noConfusion~uof~uNat {α₀} f₁ {a₂} {b₃} h₄ = Eq:rec {Nat} {f₁ a₂} {λ (x₅ : Nat) → λ (h₆ : Eq {Nat} (f₁ a₂) x₅) → Bool:rec {λ (x₇ : Bool) → Set} False True (Nat:beq (f₁ a₂) x₅)} (~uprivate:Init:Prelude:~n0:noConfusion~uof~uNat:aux (f₁ a₂)) {f₁ b₃} (congrArg {α₀} {Nat} {a₂} {b₃} f₁ h₄)
