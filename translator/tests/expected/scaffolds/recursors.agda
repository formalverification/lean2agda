-- File: translator/tests/expected/scaffolds/recursors.agda
{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of RecursorFixtures:Doc RecursorFixtures:Doc:~usizeOf~u1 RecursorFixtures:Doc:~usizeOf~u2 RecursorFixtures:Doc:~usizeOf~u2~ueq RecursorFixtures:Doc:~usizeOf~u3 and 251 more
module U.TranslatorTests.Input.Recursors where

record Add (α₀ : Set) : Set where
  constructor Add:mk
  field
    add₁ : α₀ → α₀ → α₀

-- recursor
Add:rec : {α₀ : Set} → {motive₁ : Add α₀ → Set} → ((add₂ : α₀ → α₀ → α₀) → motive₁ (Add:mk {α₀} add₂)) → (t₂ : Add α₀) → motive₁ t₂
Add:rec {α₀} {motive₁} mk₂ (Add:mk add₃) = mk₂ add₃

Add:add : {α₀ : Set} → ⦃ _ : Add α₀ ⦄ → α₀ → α₀ → α₀
Add:add {α₀} ⦃ self₁ ⦄ = Add.add₁ {α₀} self₁

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

data List (α₀ : Set) : Set where
  List:nil : List α₀
  List:cons : α₀ → List α₀ → List α₀

-- recursor
List:rec : {α₀ : Set} → {motive₁ : List α₀ → Set} → motive₁ (List:nil {α₀}) → ((head₂ : α₀) → (tail₃ : List α₀) → motive₁ tail₃ → motive₁ (List:cons {α₀} head₂ tail₃)) → (t₂ : List α₀) → motive₁ t₂
List:rec {α₀} {motive₁} nil₂ cons₃ List:nil = nil₂
List:rec {α₀} {motive₁} nil₂ cons₃ (List:cons head₄ tail₅) = cons₃ head₄ tail₅ (List:rec {α₀} {motive₁} nil₂ cons₃ tail₅)

record Array (α₀ : Set) : Set where
  constructor Array:mk
  field
    toList₁ : List α₀

-- recursor
Array:rec : {α₀ : Set} → {motive₁ : Array α₀ → Set} → ((toList₂ : List α₀) → motive₁ (Array:mk {α₀} toList₂)) → (t₂ : Array α₀) → motive₁ t₂
Array:rec {α₀} {motive₁} mk₂ (Array:mk toList₃) = mk₂ toList₃

outParam : Set → Set
outParam α₀ = α₀

record HAdd (α₀ : Set) (β₁ : Set) (γ₂ : outParam Set) : Set where
  constructor HAdd:mk
  field
    hAdd₃ : α₀ → β₁ → γ₂

-- recursor
HAdd:rec : {α₀ : Set} → {β₁ : Set} → {γ₂ : Set} → {motive₃ : HAdd α₀ β₁ γ₂ → Set} → ((hAdd₄ : α₀ → β₁ → γ₂) → motive₃ (HAdd:mk {α₀} {β₁} {γ₂} hAdd₄)) → (t₄ : HAdd α₀ β₁ γ₂) → motive₃ t₄
HAdd:rec {α₀} {β₁} {γ₂} {motive₃} mk₄ (HAdd:mk hAdd₅) = mk₄ hAdd₅

HAdd:hAdd : {α₀ : Set} → {β₁ : Set} → {γ₂ : outParam Set} → ⦃ _ : HAdd α₀ β₁ γ₂ ⦄ → α₀ → β₁ → γ₂
HAdd:hAdd {α₀} {β₁} {γ₂} ⦃ self₃ ⦄ = HAdd.hAdd₃ {α₀} {β₁} {γ₂} self₃

data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

-- recursor
Nat:rec : {motive₀ : Nat → Set} → motive₀ Nat:zero → ((n₁ : Nat) → motive₀ n₁ → motive₀ (Nat:succ n₁)) → (t₁ : Nat) → motive₀ t₁
Nat:rec {motive₀} zero₁ succ₂ Nat:zero = zero₁
Nat:rec {motive₀} zero₁ succ₂ (Nat:succ n₃) = succ₂ n₃ (Nat:rec {motive₀} zero₁ succ₂ n₃)

record OfNat (α₀ : Set) (x₁ : Nat) : Set where
  constructor OfNat:mk
  field
    ofNat₂ : α₀

-- recursor
OfNat:rec : {α₀ : Set} → {x₁ : Nat} → {motive₂ : OfNat α₀ x₁ → Set} → ((ofNat₃ : α₀) → motive₂ (OfNat:mk {α₀} {x₁} ofNat₃)) → (t₃ : OfNat α₀ x₁) → motive₂ t₃
OfNat:rec {α₀} {x₁} {motive₂} mk₃ (OfNat:mk ofNat₄) = mk₃ ofNat₄

OfNat:ofNat : {α₀ : Set} → (x₁ : Nat) → ⦃ _ : OfNat α₀ x₁ ⦄ → α₀
OfNat:ofNat {α₀} x₁ ⦃ self₂ ⦄ = OfNat.ofNat₂ {α₀} {x₁} self₂

record SizeOf (α₀ : Set) : Set where
  constructor SizeOf:mk
  field
    sizeOf₁ : α₀ → Nat

-- recursor
SizeOf:rec : {α₀ : Set} → {motive₁ : SizeOf α₀ → Set} → ((sizeOf₂ : α₀ → Nat) → motive₁ (SizeOf:mk {α₀} sizeOf₂)) → (t₂ : SizeOf α₀) → motive₁ t₂
SizeOf:rec {α₀} {motive₁} mk₂ (SizeOf:mk sizeOf₃) = mk₂ sizeOf₃

SizeOf:sizeOf : {α₀ : Set} → ⦃ _ : SizeOf α₀ ⦄ → α₀ → Nat
SizeOf:sizeOf {α₀} ⦃ self₁ ⦄ = SizeOf.sizeOf₁ {α₀} self₁

Nat:casesOn : {motive₀ : Nat → Set} → (t₁ : Nat) → motive₀ Nat:zero → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ t₁
Nat:casesOn {motive₀} t₁ zero₂ succ₃ = Nat:rec {motive₀} zero₂ (λ (n₄ : Nat) → λ (nih₅ : motive₀ n₄) → succ₃ n₄) t₁

Nat:add:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → ((a₃ : Nat) → motive₀ a₃ Nat:zero) → ((a₃ : Nat) → (b₄ : Nat) → motive₀ a₃ (Nat:succ b₄)) → motive₀ x₁ x₂
Nat:add:match~u1 motive₀ x₁ x₂ h1₃ h2₄ = Nat:casesOn {λ (x₅ : Nat) → motive₀ x₁ x₅} x₂ (h1₃ x₁) (λ (n₅ : Nat) → h2₄ x₁ n₅)

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

Nat:below : {_ : Nat → Set} → Nat → Set
Nat:below {motive₀} t₁ = Nat:rec {λ (t₂ : Nat) → Set} PUnit (λ (n₂ : Nat) → λ (nih₃ : Set) → PProd (motive₀ n₂) nih₃) t₁

Nat:add:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Nat → Nat} x₀ → Nat → Nat
Nat:add:~uf x₀ f₁ x₂ = Nat:add:match~u1 (λ (x₃ : Nat) → λ (x₄ : Nat) → Nat:below {λ (x₅ : Nat) → Nat → Nat} x₄ → Nat) x₂ x₀ (λ (a₃ : Nat) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Nat} Nat:zero) → a₃) (λ (a₃ : Nat) → λ (b₄ : Nat) → λ (x₅ : Nat:below {λ (x₅ : Nat) → Nat → Nat} (Nat:succ b₄)) → Nat:succ (PProd.fst₂ {(λ (x₆ : Nat) → Nat → Nat) b₄} {Nat:rec {λ (t₆ : Nat) → Set} PUnit (λ (n₆ : Nat) → λ (nih₇ : Set) → PProd ((λ (x₈ : Nat) → Nat → Nat) n₆) nih₇) b₄} x₅ a₃)) f₁

Nat:brecOn:go : {motive₀ : Nat → Set} → (t₁ : Nat) → ((t₂ : Nat) → Nat:below {motive₀} t₂ → motive₀ t₂) → PProd (motive₀ t₁) (Nat:below {motive₀} t₁)
Nat:brecOn:go {motive₀} t₁ F1₂ = Nat:rec {λ (t₃ : Nat) → PProd (motive₀ t₃) (Nat:below {motive₀} t₃)} (PProd:mk {motive₀ Nat:zero} {PUnit} (F1₂ Nat:zero PUnit:unit) PUnit:unit) (λ (n₃ : Nat) → λ (nih₄ : PProd (motive₀ n₃) (Nat:below {motive₀} n₃)) → PProd:mk {motive₀ (Nat:succ n₃)} {PProd (motive₀ n₃) (Nat:below {motive₀} n₃)} (F1₂ (Nat:succ n₃) nih₄) nih₄) t₁

Nat:brecOn : {motive₀ : Nat → Set} → (t₁ : Nat) → ((t₂ : Nat) → Nat:below {motive₀} t₂ → motive₀ t₂) → motive₀ t₁
Nat:brecOn {motive₀} t₁ F1₂ = PProd.fst₂ {motive₀ t₁} {Nat:below {motive₀} t₁} (Nat:brecOn:go {motive₀} t₁ F1₂)

Nat:add : Nat → Nat → Nat
Nat:add x₀ x₁ = Nat:brecOn {λ (x₂ : Nat) → Nat → Nat} x₁ Nat:add:~uf x₀

instAddNat : Add Nat
instAddNat = Add:mk {Nat} Nat:add

instHAdd : {α₀ : Set} → ⦃ _ : Add α₀ ⦄ → HAdd α₀ α₀ α₀
instHAdd {α₀} ⦃ inst₁ ⦄ = HAdd:mk {α₀} {α₀} {α₀} (λ (a₂ : α₀) → λ (b₃ : α₀) → Add:add {α₀} ⦃ inst₁ ⦄ a₂ b₃)

instOfNatNat : (n₀ : Nat) → OfNat Nat n₀
instOfNatNat n₀ = OfNat:mk {Nat} {n₀} n₀

List:~usizeOf~u1 : {α₀ : Set} → ⦃ _ : SizeOf α₀ ⦄ → List α₀ → Nat
List:~usizeOf~u1 {α₀} ⦃ inst₁ ⦄ t₂ = List:rec {α₀} {λ (t₃ : List α₀) → Nat} (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (λ (head₃ : α₀) → λ (tail₄ : List α₀) → λ (tailih₅ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {α₀} ⦃ inst₁ ⦄ head₃)) tailih₅) t₂

List:~usizeOf~uinst : (α₀ : Set) → ⦃ _ : SizeOf α₀ ⦄ → SizeOf (List α₀)
List:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ = SizeOf:mk {List α₀} (λ (m₂ : List α₀) → List:~usizeOf~u1 {α₀} ⦃ inst₁ ⦄ m₂)

Array:~usizeOf~u1 : {α₀ : Set} → ⦃ _ : SizeOf α₀ ⦄ → Array α₀ → Nat
Array:~usizeOf~u1 {α₀} ⦃ inst₁ ⦄ t₂ = Array:rec {α₀} {λ (t₃ : Array α₀) → Nat} (λ (toList₃ : List α₀) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {List α₀} ⦃ List:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ ⦄ toList₃)) t₂

Array:~usizeOf~uinst : (α₀ : Set) → ⦃ _ : SizeOf α₀ ⦄ → SizeOf (Array α₀)
Array:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ = SizeOf:mk {Array α₀} (λ (m₂ : Array α₀) → Array:~usizeOf~u1 {α₀} ⦃ inst₁ ⦄ m₂)

Array:casesOn : {α₀ : Set} → {motive₁ : Array α₀ → Set} → (t₂ : Array α₀) → ((toList₃ : List α₀) → motive₁ (Array:mk {α₀} toList₃)) → motive₁ t₂
Array:casesOn {α₀} {motive₁} t₂ mk₃ = Array:rec {α₀} {motive₁} (λ (toList₄ : List α₀) → mk₃ toList₄) t₂

data Eq {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl : (a₁ : α₀) → Eq {α₀} a₁ a₁
{-# BUILTIN REWRITE Eq #-}

-- recursor
Eq:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → Eq {α₀} a₁ a₂ → Set} → motive₂ a₁ (Eq:refl {α₀} a₁) → {a₃ : α₀} → (t₄ : Eq {α₀} a₁ a₃) → motive₂ a₃ t₄
Eq:rec {α₀} {a₁} {motive₂} refl₃ {_} (Eq:refl _) = refl₃

-- theorem
opaque
  Array:mk:sizeOf~uspec : {α₀ : Set} → ⦃ inst₁ : SizeOf α₀ ⦄ → (toList₂ : List α₀) → Eq {Nat} (SizeOf:sizeOf {Array α₀} ⦃ Array:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ ⦄ (Array:mk {α₀} toList₂)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {List α₀} ⦃ List:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ ⦄ toList₂))
  Array:mk:sizeOf~uspec {α₀} ⦃ inst₁ ⦄ toList₂ = Eq:refl {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {List α₀} ⦃ List:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ ⦄ toList₂))

data Bool : Set where
  Bool:false : Bool
  Bool:true : Bool

-- recursor
Bool:rec : {motive₀ : Bool → Set} → motive₀ Bool:false → motive₀ Bool:true → (t₁ : Bool) → motive₀ t₁
Bool:rec {motive₀} false₁ true₂ Bool:false = false₁
Bool:rec {motive₀} false₁ true₂ Bool:true = true₂

Bool:casesOn : {motive₀ : Bool → Set} → (t₁ : Bool) → motive₀ Bool:false → motive₀ Bool:true → motive₀ t₁
Bool:casesOn {motive₀} t₁ false₂ true₃ = Bool:rec {motive₀} false₂ true₃ t₁

Bool:ctorIdx : Bool → Nat
Bool:ctorIdx x₀ = Bool:casesOn {λ (x₁ : Bool) → Nat} x₀ 0 1

Unit : Set
Unit = PUnit

Unit:unit : Unit
Unit:unit = PUnit:unit

Bool:decEq:match~u1 : (motive₀ : Bool → Bool → Set) → (a₁ : Bool) → (b₂ : Bool) → (Unit → motive₀ Bool:false Bool:false) → (Unit → motive₀ Bool:false Bool:true) → (Unit → motive₀ Bool:true Bool:false) → (Unit → motive₀ Bool:true Bool:true) → motive₀ a₁ b₂
Bool:decEq:match~u1 motive₀ a₁ b₂ h1₃ h2₄ h3₅ h4₆ = Bool:casesOn {λ (x₇ : Bool) → motive₀ x₇ b₂} a₁ (Bool:casesOn {λ (x₇ : Bool) → motive₀ Bool:false x₇} b₂ (h1₃ Unit:unit) (h2₄ Unit:unit)) (Bool:casesOn {λ (x₇ : Bool) → motive₀ Bool:true x₇} b₂ (h3₅ Unit:unit) (h4₆ Unit:unit))

Bool:noConfusionType : Set → Bool → Bool → Set
Bool:noConfusionType P₀ t₁ t₂ = Bool:casesOn {λ (t₃ : Bool) → Set} t₁ (Bool:casesOn {λ (t₃ : Bool) → Set} t₂ (P₀ → P₀) P₀) (Bool:casesOn {λ (t₃ : Bool) → Set} t₂ P₀ (P₀ → P₀))

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

rfl : {α₀ : Set} → {a₁ : α₀} → Eq {α₀} a₁ a₁
rfl {α₀} {a₁} = Eq:refl {α₀} a₁

Bool:decEq : (a₀ : Bool) → (b₁ : Bool) → Decidable (Eq {Bool} a₀ b₁)
Bool:decEq a₀ b₁ = Bool:decEq:match~u1 (λ (a₂ : Bool) → λ (b₃ : Bool) → Decidable (Eq {Bool} a₂ b₃)) a₀ b₁ (λ (x₂ : Unit) → Decidable:isTrue {Eq {Bool} Bool:false Bool:false} (rfl {Bool} {Bool:false})) (λ (x₂ : Unit) → Decidable:isFalse {Eq {Bool} Bool:false Bool:true} (λ (h₃ : Eq {Bool} Bool:false Bool:true) → Bool:noConfusion {False} {Bool:false} {Bool:true} h₃)) (λ (x₂ : Unit) → Decidable:isFalse {Eq {Bool} Bool:true Bool:false} (λ (h₃ : Eq {Bool} Bool:true Bool:false) → Bool:noConfusion {False} {Bool:true} {Bool:false} h₃)) (λ (x₂ : Unit) → Decidable:isTrue {Eq {Bool} Bool:true Bool:true} (rfl {Bool} {Bool:true}))

Decidable:casesOn : {p₀ : Set} → {motive₁ : Decidable p₀ → Set} → (t₂ : Decidable p₀) → ((h₃ : Not p₀) → motive₁ (Decidable:isFalse {p₀} h₃)) → ((h₃ : p₀) → motive₁ (Decidable:isTrue {p₀} h₃)) → motive₁ t₂
Decidable:casesOn {p₀} {motive₁} t₂ isFalse₃ isTrue₄ = Decidable:rec {p₀} {motive₁} (λ (h₅ : Not p₀) → isFalse₃ h₅) (λ (h₅ : p₀) → isTrue₄ h₅) t₂

DecidableEq : Set → Set
DecidableEq α₀ = (a₁ : α₀) → (b₂ : α₀) → Decidable (Eq {α₀} a₁ b₂)

Eq:casesOn : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → Eq {α₀} a₁ a₂ → Set} → {a₃ : α₀} → (t₄ : Eq {α₀} a₁ a₃) → motive₂ a₁ (Eq:refl {α₀} a₁) → motive₂ a₃ t₄
Eq:casesOn {α₀} {a₁} {motive₂} {a₃} t₄ refl₅ = Eq:rec {α₀} {a₁} {motive₂} refl₅ {a₃} t₄

record Iff (a₀ : Set) (b₁ : Set) : Set where
  constructor Iff:intro
  field
    mp₂ : a₀ → b₁
    mpr₃ : b₁ → a₀

-- recursor
Iff:rec : {a₀ : Set} → {b₁ : Set} → {motive₂ : Iff a₀ b₁ → Set} → ((mp₃ : a₀ → b₁) → (mpr₄ : b₁ → a₀) → motive₂ (Iff:intro {a₀} {b₁} mp₃ mpr₄)) → (t₃ : Iff a₀ b₁) → motive₂ t₃
Iff:rec {a₀} {b₁} {motive₂} intro₃ (Iff:intro mp₄ mpr₅) = intro₃ mp₄ mpr₅

postulate propext : {a₀ : Set} → {b₁ : Set} → Iff a₀ b₁ → Eq {Set} a₀ b₁

-- theorem
opaque
  Eq:propIntro : {a₀ : Set} → {b₁ : Set} → (a₀ → b₁) → (b₁ → a₀) → Eq {Set} a₀ b₁
  Eq:propIntro {a₀} {b₁} h₂ h₃ = propext {a₀} {b₁} (Iff:intro {a₀} {b₁} h₂ h₃)

-- theorem
opaque
  Eq:subst : {α₀ : Set} → {motive₁ : α₀ → Set} → {a₂ : α₀} → {b₃ : α₀} → Eq {α₀} a₂ b₃ → motive₁ a₂ → motive₁ b₃
  Eq:subst {α₀} {motive₁} {a₂} {b₃} h₄ h₅ = Eq:ndrec {α₀} {a₂} {motive₁} h₅ {b₃} h₄

-- theorem
opaque
  Eq:symm : {α₀ : Set} → {a₁ : α₀} → {b₂ : α₀} → Eq {α₀} a₁ b₂ → Eq {α₀} b₂ a₁
  Eq:symm {α₀} {a₁} {b₂} h₃ = Eq:rec {α₀} {a₁} {λ (x₄ : α₀) → λ (h₅ : Eq {α₀} a₁ x₄) → Eq {α₀} x₄ a₁} (rfl {α₀} {a₁}) {b₂} h₃

-- theorem
opaque
  Eq:trans : {α₀ : Set} → {a₁ : α₀} → {b₂ : α₀} → {c₃ : α₀} → Eq {α₀} a₁ b₂ → Eq {α₀} b₂ c₃ → Eq {α₀} a₁ c₃
  Eq:trans {α₀} {a₁} {b₂} {c₃} h₄ h₅ = Eq:rec {α₀} {b₂} {λ (x₆ : α₀) → λ (h₇ : Eq {α₀} b₂ x₆) → Eq {α₀} a₁ x₆} h₄ {c₃} h₅

False:elim : {C₀ : Set} → False → C₀
False:elim {C₀} h₁ = False:rec (λ (x₂ : False) → C₀) h₁

record LT (α₀ : Set) : Set where
  constructor LT:mk
  field
    lt₁ : α₀ → α₀ → Set

-- recursor
LT:rec : {α₀ : Set} → {motive₁ : LT α₀ → Set} → ((lt₂ : α₀ → α₀ → Set) → motive₁ (LT:mk {α₀} lt₂)) → (t₂ : LT α₀) → motive₁ t₂
LT:rec {α₀} {motive₁} mk₂ (LT:mk lt₃) = mk₂ lt₃

LT:lt : {α₀ : Set} → ⦃ _ : LT α₀ ⦄ → α₀ → α₀ → Set
LT:lt {α₀} ⦃ self₁ ⦄ = LT.lt₁ {α₀} self₁

data Nat:le (n₀ : Nat) : Nat → Set where
  Nat:le:refl : Nat:le n₀ n₀
  Nat:le:step : {m₁ : Nat} → Nat:le n₀ m₁ → Nat:le n₀ (Nat:succ m₁)

-- recursor
Nat:le:rec : {n₀ : Nat} → {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} → motive₁ n₀ (Nat:le:refl {n₀}) → ({m₂ : Nat} → (a₃ : Nat:le n₀ m₂) → motive₁ m₂ a₃ → motive₁ (Nat:succ m₂) (Nat:le:step {n₀} {m₂} a₃)) → {a₂ : Nat} → (t₃ : Nat:le n₀ a₂) → motive₁ a₂ t₃
Nat:le:rec {n₀} {motive₁} refl₂ step₃ {_} Nat:le:refl = refl₂
Nat:le:rec {n₀} {motive₁} refl₂ step₃ {_} (Nat:le:step {m₅} a₆) = step₃ {m₅} a₆ (Nat:le:rec {n₀} {motive₁} refl₂ step₃ {m₅} a₆)

Nat:lt : Nat → Nat → Set
Nat:lt n₀ m₁ = Nat:le (Nat:succ n₀) m₁

instLTNat : LT Nat
instLTNat = LT:mk {Nat} Nat:lt

record Fin (n₀ : Nat) : Set where
  constructor Fin:mk
  field
    val₁ : Nat
    isLt₂ : LT:lt {Nat} ⦃ instLTNat ⦄ val₁ n₀

-- recursor
Fin:rec : {n₀ : Nat} → {motive₁ : Fin n₀ → Set} → ((val₂ : Nat) → (isLt₃ : LT:lt {Nat} ⦃ instLTNat ⦄ val₂ n₀) → motive₁ (Fin:mk {n₀} val₂ isLt₃)) → (t₂ : Fin n₀) → motive₁ t₂
Fin:rec {n₀} {motive₁} mk₂ (Fin:mk val₃ isLt₄) = mk₂ val₃ isLt₄

default:sizeOf:match~u1 : (α₀ : Set) → (motive₁ : α₀ → Set) → (x₂ : α₀) → ((x₃ : α₀) → motive₁ x₃) → motive₁ x₂
default:sizeOf:match~u1 α₀ motive₁ x₂ h1₃ = h1₃ x₂

default:sizeOf : (α₀ : Set) → α₀ → Nat
default:sizeOf α₀ x₁ = default:sizeOf:match~u1 α₀ (λ (x₂ : α₀) → Nat) x₁ (λ (x₂ : α₀) → OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)

instSizeOfDefault : (α₀ : Set) → SizeOf α₀
instSizeOfDefault α₀ = SizeOf:mk {α₀} (default:sizeOf α₀)

instSizeOfNat : SizeOf Nat
instSizeOfNat = SizeOf:mk {Nat} (λ (n₀ : Nat) → n₀)

Fin:~usizeOf~u1 : {n₀ : Nat} → Fin n₀ → Nat
Fin:~usizeOf~u1 {n₀} t₁ = Fin:rec {n₀} {λ (t₂ : Fin n₀) → Nat} (λ (val₂ : Nat) → λ (isLt₃ : LT:lt {Nat} ⦃ instLTNat ⦄ val₂ n₀) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {Nat} ⦃ instSizeOfNat ⦄ val₂)) (SizeOf:sizeOf {LT:lt {Nat} ⦃ instLTNat ⦄ val₂ n₀} ⦃ instSizeOfDefault (LT:lt {Nat} ⦃ instLTNat ⦄ val₂ n₀) ⦄ isLt₃)) t₁

Fin:~usizeOf~uinst : (n₀ : Nat) → SizeOf (Fin n₀)
Fin:~usizeOf~uinst n₀ = SizeOf:mk {Fin n₀} (λ (m₁ : Fin n₀) → Fin:~usizeOf~u1 {n₀} m₁)

record HMod (α₀ : Set) (β₁ : Set) (γ₂ : outParam Set) : Set where
  constructor HMod:mk
  field
    hMod₃ : α₀ → β₁ → γ₂

-- recursor
HMod:rec : {α₀ : Set} → {β₁ : Set} → {γ₂ : Set} → {motive₃ : HMod α₀ β₁ γ₂ → Set} → ((hMod₄ : α₀ → β₁ → γ₂) → motive₃ (HMod:mk {α₀} {β₁} {γ₂} hMod₄)) → (t₄ : HMod α₀ β₁ γ₂) → motive₃ t₄
HMod:rec {α₀} {β₁} {γ₂} {motive₃} mk₄ (HMod:mk hMod₅) = mk₄ hMod₅

HMod:hMod : {α₀ : Set} → {β₁ : Set} → {γ₂ : outParam Set} → ⦃ _ : HMod α₀ β₁ γ₂ ⦄ → α₀ → β₁ → γ₂
HMod:hMod {α₀} {β₁} {γ₂} ⦃ self₃ ⦄ = HMod.hMod₃ {α₀} {β₁} {γ₂} self₃

record Mod (α₀ : Set) : Set where
  constructor Mod:mk
  field
    mod₁ : α₀ → α₀ → α₀

-- recursor
Mod:rec : {α₀ : Set} → {motive₁ : Mod α₀ → Set} → ((mod₂ : α₀ → α₀ → α₀) → motive₁ (Mod:mk {α₀} mod₂)) → (t₂ : Mod α₀) → motive₁ t₂
Mod:rec {α₀} {motive₁} mk₂ (Mod:mk mod₃) = mk₂ mod₃

record LE (α₀ : Set) : Set where
  constructor LE:mk
  field
    le₁ : α₀ → α₀ → Set

-- recursor
LE:rec : {α₀ : Set} → {motive₁ : LE α₀ → Set} → ((le₂ : α₀ → α₀ → Set) → motive₁ (LE:mk {α₀} le₂)) → (t₂ : LE α₀) → motive₁ t₂
LE:rec {α₀} {motive₁} mk₂ (LE:mk le₃) = mk₂ le₃

LE:le : {α₀ : Set} → ⦃ _ : LE α₀ ⦄ → α₀ → α₀ → Set
LE:le {α₀} ⦃ self₁ ⦄ = LE.le₁ {α₀} self₁

Nat:ble:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → ((x₃ : Nat) → motive₀ Nat:zero x₃) → ((n₃ : Nat) → motive₀ (Nat:succ n₃) Nat:zero) → ((n₃ : Nat) → (m₄ : Nat) → motive₀ (Nat:succ n₃) (Nat:succ m₄)) → motive₀ x₁ x₂
Nat:ble:match~u1 motive₀ x₁ x₂ h1₃ h2₄ h3₅ = Nat:casesOn {λ (x₆ : Nat) → motive₀ x₆ x₂} x₁ (h1₃ x₂) (λ (n₆ : Nat) → Nat:casesOn {λ (x₇ : Nat) → motive₀ (Nat:succ n₆) x₇} x₂ (h2₄ n₆) (λ (n₇ : Nat) → h3₅ n₆ n₇))

Nat:ble:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Nat → Bool} x₀ → Nat → Bool
Nat:ble:~uf x₀ f₁ x₂ = Nat:ble:match~u1 (λ (x₃ : Nat) → λ (x₄ : Nat) → Nat:below {λ (x₅ : Nat) → Nat → Bool} x₃ → Bool) x₀ x₂ (λ (x₃ : Nat) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Bool} Nat:zero) → Bool:true) (λ (n₃ : Nat) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Bool} (Nat:succ n₃)) → Bool:false) (λ (n₃ : Nat) → λ (m₄ : Nat) → λ (x₅ : Nat:below {λ (x₅ : Nat) → Nat → Bool} (Nat:succ n₃)) → PProd.fst₂ {(λ (x₆ : Nat) → Nat → Bool) n₃} {Nat:rec {λ (t₆ : Nat) → Set} PUnit (λ (n₆ : Nat) → λ (nih₇ : Set) → PProd ((λ (x₈ : Nat) → Nat → Bool) n₆) nih₇) n₃} x₅ m₄) f₁

Nat:ble : Nat → Nat → Bool
Nat:ble x₀ x₁ = Nat:brecOn {λ (x₂ : Nat) → Nat → Bool} x₀ Nat:ble:~uf x₁

data Nat:le:below {n₀ : Nat} {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} : {a₂ : Nat} → Nat:le n₀ a₂ → Set where
  Nat:le:below:refl : Nat:le:below {n₀} {motive₁} {n₀} (Nat:le:refl {n₀})
  Nat:le:below:step : {m₂ : Nat} → (a₃ : Nat:le n₀ m₂) → Nat:le:below {n₀} {motive₁} {m₂} a₃ → motive₁ m₂ a₃ → Nat:le:below {n₀} {motive₁} {Nat:succ m₂} (Nat:le:step {n₀} {m₂} a₃)

-- recursor
Nat:le:below:rec : {n₀ : Nat} → {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} → {motive₂ : {a₂ : Nat} → (t₃ : Nat:le n₀ a₂) → Nat:le:below {n₀} {motive₁} {a₂} t₃ → Set} → motive₂ {n₀} (Nat:le:refl {n₀}) (Nat:le:below:refl {n₀} {motive₁}) → ({m₃ : Nat} → (a₄ : Nat:le n₀ m₃) → (ih₅ : Nat:le:below {n₀} {motive₁} {m₃} a₄) → (aih₆ : motive₁ m₃ a₄) → motive₂ {m₃} a₄ ih₅ → motive₂ {Nat:succ m₃} (Nat:le:step {n₀} {m₃} a₄) (Nat:le:below:step {n₀} {motive₁} {m₃} a₄ ih₅ aih₆)) → {a₃ : Nat} → {t₄ : Nat:le n₀ a₃} → (t₅ : Nat:le:below {n₀} {motive₁} {a₃} t₄) → motive₂ {a₃} t₄ t₅
Nat:le:below:rec {n₀} {motive₁} {motive₂} refl₃ step₄ {_} {_} Nat:le:below:refl = refl₃
Nat:le:below:rec {n₀} {motive₁} {motive₂} refl₃ step₄ {_} {_} (Nat:le:below:step {m₇} a₈ ih₉ aih₁₀) = step₄ {m₇} a₈ ih₉ aih₁₀ (Nat:le:below:rec {n₀} {motive₁} {motive₂} refl₃ step₄ {m₇} {a₈} ih₉)

-- theorem
opaque
  Nat:le:brecOn : {n₀ : Nat} → {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} → {a₂ : Nat} → (t₃ : Nat:le n₀ a₂) → ((a₄ : Nat) → (t₅ : Nat:le n₀ a₄) → Nat:le:below {n₀} {motive₁} {a₄} t₅ → motive₁ a₄ t₅) → motive₁ a₂ t₃
  Nat:le:brecOn {n₀} {motive₁} {a₂} t₃ F1₄ = F1₄ a₂ t₃ (Nat:le:rec {n₀} {λ (a₅ : Nat) → λ (t₆ : Nat:le n₀ a₅) → Nat:le:below {n₀} {motive₁} {a₅} t₆} (Nat:le:below:refl {n₀} {motive₁}) (λ {m₅ : Nat} → λ (a₆ : Nat:le n₀ m₅) → λ (ih₇ : Nat:le:below {n₀} {motive₁} {m₅} a₆) → Nat:le:below:step {n₀} {motive₁} {m₅} a₆ ih₇ (F1₄ m₅ a₆ ih₇)) {a₂} t₃)

data HEq {α₀ : Set} : α₀ → {β₁ : Set} → β₁ → Set where
  HEq:refl : (a₁ : α₀) → HEq {α₀} a₁ {α₀} a₁

-- recursor
HEq:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : {β₂ : Set} → (a₃ : β₂) → HEq {α₀} a₁ {β₂} a₃ → Set} → motive₂ {α₀} a₁ (HEq:refl {α₀} a₁) → {β₃ : Set} → {a₄ : β₃} → (t₅ : HEq {α₀} a₁ {β₃} a₄) → motive₂ {β₃} a₄ t₅
HEq:rec {α₀} {a₁} {motive₂} refl₃ {_} {_} (HEq:refl _) = refl₃

Nat:le:below:casesOn : {n₀ : Nat} → {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} → {motive₂ : {a₂ : Nat} → (t₃ : Nat:le n₀ a₂) → Nat:le:below {n₀} {motive₁} {a₂} t₃ → Set} → {a₃ : Nat} → {t₄ : Nat:le n₀ a₃} → (t₅ : Nat:le:below {n₀} {motive₁} {a₃} t₄) → motive₂ {n₀} (Nat:le:refl {n₀}) (Nat:le:below:refl {n₀} {motive₁}) → ({m₆ : Nat} → (a₇ : Nat:le n₀ m₆) → (ih₈ : Nat:le:below {n₀} {motive₁} {m₆} a₇) → (aih₉ : motive₁ m₆ a₇) → motive₂ {Nat:succ m₆} (Nat:le:step {n₀} {m₆} a₇) (Nat:le:below:step {n₀} {motive₁} {m₆} a₇ ih₈ aih₉)) → motive₂ {a₃} t₄ t₅
Nat:le:below:casesOn {n₀} {motive₁} {motive₂} {a₃} {t₄} t₅ refl₆ step₇ = Nat:le:below:rec {n₀} {motive₁} {motive₂} refl₆ (λ {m₈ : Nat} → λ (a₉ : Nat:le n₀ m₈) → λ (ih₁₀ : Nat:le:below {n₀} {motive₁} {m₈} a₉) → λ (aih₁₁ : motive₁ m₈ a₉) → λ (ihih₁₂ : motive₂ {m₈} a₉ ih₁₀) → step₇ {m₈} a₉ ih₁₀ aih₁₁) {a₃} {t₄} t₅

cast : {α₀ : Set} → {β₁ : Set} → Eq {Set} α₀ β₁ → α₀ → β₁
cast {α₀} {β₁} h₂ a₃ = Eq:rec {Set} {α₀} {λ (x₄ : Set) → λ (x₅ : Eq {Set} α₀ x₄) → x₄} a₃ {β₁} h₂

-- theorem
opaque
  eq~uof~uheq : {α₀ : Set} → {a₁ : α₀} → {a₂ : α₀} → HEq {α₀} a₁ {α₀} a₂ → Eq {α₀} a₁ a₂
  eq~uof~uheq {α₀} {a₁} {a₂} h₃ = let this₄ : (α₄ : Set) → (β₅ : Set) → (a₆ : α₄) → (b₇ : β₅) → HEq {α₄} a₆ {β₅} b₇ → (h₈ : Eq {Set} α₄ β₅) → Eq {β₅} (cast {α₄} {β₅} h₈ a₆) b₇; this₄ = λ (x₄ : Set) → λ (x₅ : Set) → λ (x₆ : x₄) → λ (x₇ : x₅) → λ (h₈ : HEq {x₄} x₆ {x₅} x₇) → HEq:rec {x₄} {x₆} {λ {x₉ : Set} → λ (x₁₀ : x₉) → λ (x₁₁ : HEq {x₄} x₆ {x₉} x₁₀) → (h₁₂ : Eq {Set} x₄ x₉) → Eq {x₉} (cast {x₄} {x₉} h₁₂ x₆) x₁₀} (λ (x₉ : Eq {Set} x₄ x₄) → rfl {x₄} {cast {x₄} {x₄} x₉ x₆}) {x₅} {x₇} h₈ in this₄ α₀ α₀ a₁ a₂ h₃ (rfl {Set} {α₀})

instLENat : LE Nat
instLENat = LE:mk {Nat} Nat:le

~uprivate:Init:Prelude:~n0:Nat:succ~ule~usucc:match~u1~u7 : {n₀ : Nat} → (funType1₁ : {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → Set) → (motive₂ : (m₂ : Nat) → (x₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₂) → Nat:le:below {n₀} {λ (m₄ : Nat) → λ (x₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₄) → funType1₁ {m₄} x₅} {m₂} x₃ → Set) → (m₃ : Nat) → (x₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₃) → (below₅ : Nat:le:below {n₀} {λ (m₅ : Nat) → λ (x₆ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₅) → funType1₁ {m₅} x₆} {m₃} x₄) → (Unit → motive₂ n₀ (Nat:le:refl {n₀}) (Nat:le:below:refl {n₀} {λ (m₆ : Nat) → λ (x₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₆) → funType1₁ {m₆} x₇})) → ((m₆ : Nat) → (h₇ : Nat:le n₀ m₆) → (ih₈ : Nat:le:below {n₀} {λ (m₈ : Nat) → λ (x₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₈) → funType1₁ {m₈} x₉} {m₆} h₇) → (aih₉ : funType1₁ {m₆} h₇) → motive₂ (Nat:succ m₆) (Nat:le:step {n₀} {m₆} h₇) (Nat:le:below:step {n₀} {λ (m₁₀ : Nat) → λ (x₁₁ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₀) → funType1₁ {m₁₀} x₁₁} {m₆} h₇ ih₈ aih₉)) → motive₂ m₃ x₄ below₅
~uprivate:Init:Prelude:~n0:Nat:succ~ule~usucc:match~u1~u7 {n₀} funType1₁ motive₂ m₃ x₄ below₅ h1₆ h2₇ = Nat:le:below:casesOn {n₀} {λ (m₈ : Nat) → λ (x₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₈) → funType1₁ {m₈} x₉} {λ {a₈ : Nat} → λ (t₉ : Nat:le n₀ a₈) → λ (x₁₀ : Nat:le:below {n₀} {λ (m₁₀ : Nat) → λ (x₁₁ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₀) → funType1₁ {m₁₀} x₁₁} {a₈} t₉) → Eq {Nat} m₃ a₈ → HEq {LE:le {Nat} ⦃ instLENat ⦄ n₀ m₃} x₄ {Nat:le n₀ a₈} t₉ → HEq {Nat:le:below {n₀} {λ (m₁₁ : Nat) → λ (x₁₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₁) → funType1₁ {m₁₁} x₁₂} {m₃} x₄} below₅ {Nat:le:below {n₀} {λ (m₁₁ : Nat) → λ (x₁₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₁) → funType1₁ {m₁₁} x₁₂} {a₈} t₉} x₁₀ → motive₂ m₃ x₄ below₅} {m₃} {x₄} below₅ (λ (h₈ : Eq {Nat} m₃ n₀) → Eq:ndrec {Nat} {n₀} {λ (m₉ : Nat) → (x₁₀ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₉) → (below₁₁ : Nat:le:below {n₀} {λ (m₁₁ : Nat) → λ (x₁₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₁) → funType1₁ {m₁₁} x₁₂} {m₉} x₁₀) → HEq {LE:le {Nat} ⦃ instLENat ⦄ n₀ m₉} x₁₀ {Nat:le n₀ n₀} (Nat:le:refl {n₀}) → HEq {Nat:le:below {n₀} {λ (m₁₂ : Nat) → λ (x₁₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₂) → funType1₁ {m₁₂} x₁₃} {m₉} x₁₀} below₁₁ {Nat:le:below {n₀} {λ (m₁₂ : Nat) → λ (x₁₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₂) → funType1₁ {m₁₂} x₁₃} {n₀} (Nat:le:refl {n₀})} (Nat:le:below:refl {n₀} {λ (m₁₂ : Nat) → λ (x₁₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₂) → funType1₁ {m₁₂} x₁₃}) → motive₂ m₉ x₁₀ below₁₁} (λ (x₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ n₀) → λ (below₁₀ : Nat:le:below {n₀} {λ (m₁₀ : Nat) → λ (x₁₁ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₀) → funType1₁ {m₁₀} x₁₁} {n₀} x₉) → λ (h₁₁ : HEq {LE:le {Nat} ⦃ instLENat ⦄ n₀ n₀} x₉ {Nat:le n₀ n₀} (Nat:le:refl {n₀})) → Eq:ndrec {LE:le {Nat} ⦃ instLENat ⦄ n₀ n₀} {Nat:le:refl {n₀}} {λ (x₁₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ n₀) → (below₁₃ : Nat:le:below {n₀} {λ (m₁₃ : Nat) → λ (x₁₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₃) → funType1₁ {m₁₃} x₁₄} {n₀} x₁₂) → HEq {Nat:le:below {n₀} {λ (m₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} x₁₅} {n₀} x₁₂} below₁₃ {Nat:le:below {n₀} {λ (m₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} x₁₅} {n₀} (Nat:le:refl {n₀})} (Nat:le:below:refl {n₀} {λ (m₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} x₁₅}) → motive₂ n₀ x₁₂ below₁₃} (λ (below₁₂ : Nat:le:below {n₀} {λ (m₁₂ : Nat) → λ (x₁₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₂) → funType1₁ {m₁₂} x₁₃} {n₀} (Nat:le:refl {n₀})) → λ (h₁₃ : HEq {Nat:le:below {n₀} {λ (m₁₃ : Nat) → λ (x₁₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₃) → funType1₁ {m₁₃} x₁₄} {n₀} (Nat:le:refl {n₀})} below₁₂ {Nat:le:below {n₀} {λ (m₁₃ : Nat) → λ (x₁₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₃) → funType1₁ {m₁₃} x₁₄} {n₀} (Nat:le:refl {n₀})} (Nat:le:below:refl {n₀} {λ (m₁₃ : Nat) → λ (x₁₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₃) → funType1₁ {m₁₃} x₁₄})) → Eq:ndrec {Nat:le:below {n₀} {λ (m₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} x₁₅} {n₀} (Nat:le:refl {n₀})} {Nat:le:below:refl {n₀} {λ (m₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} x₁₅}} {λ (below₁₄ : Nat:le:below {n₀} {λ (m₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} x₁₅} {n₀} (Nat:le:refl {n₀})) → motive₂ n₀ (Nat:le:refl {n₀}) below₁₄} (h1₆ Unit:unit) {below₁₂} (Eq:symm {Nat:le:below {n₀} {λ (m₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} x₁₅} {n₀} (Nat:le:refl {n₀})} {below₁₂} {Nat:le:below:refl {n₀} {λ (m₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} x₁₅}} (eq~uof~uheq {Nat:le:below {n₀} {λ (m₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} x₁₅} {n₀} (Nat:le:refl {n₀})} {below₁₂} {Nat:le:below:refl {n₀} {λ (m₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} x₁₅}} h₁₃))) {x₉} (Eq:symm {LE:le {Nat} ⦃ instLENat ⦄ n₀ n₀} {x₉} {Nat:le:refl {n₀}} (eq~uof~uheq {LE:le {Nat} ⦃ instLENat ⦄ n₀ n₀} {x₉} {Nat:le:refl {n₀}} h₁₁)) below₁₀) {m₃} (Eq:symm {Nat} {m₃} {n₀} h₈) x₄ below₅) (λ {m₈ : Nat} → λ (a₉ : Nat:le n₀ m₈) → λ (ih₁₀ : Nat:le:below {n₀} {λ (m₁₀ : Nat) → λ (x₁₁ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₀) → funType1₁ {m₁₀} x₁₁} {m₈} a₉) → λ (aih₁₁ : funType1₁ {m₈} a₉) → λ (h₁₂ : Eq {Nat} m₃ (Nat:succ m₈)) → Eq:ndrec {Nat} {Nat:succ m₈} {λ (m₁₃ : Nat) → (x₁₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₃) → (below₁₅ : Nat:le:below {n₀} {λ (m₁₅ : Nat) → λ (x₁₆ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₅) → funType1₁ {m₁₅} x₁₆} {m₁₃} x₁₄) → HEq {LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₃} x₁₄ {Nat:le n₀ (Nat:succ m₈)} (Nat:le:step {n₀} {m₈} a₉) → HEq {Nat:le:below {n₀} {λ (m₁₆ : Nat) → λ (x₁₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₆) → funType1₁ {m₁₆} x₁₇} {m₁₃} x₁₄} below₁₅ {Nat:le:below {n₀} {λ (m₁₆ : Nat) → λ (x₁₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₆) → funType1₁ {m₁₆} x₁₇} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)} (Nat:le:below:step {n₀} {λ (m₁₆ : Nat) → λ (x₁₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₆) → funType1₁ {m₁₆} x₁₇} {m₈} a₉ ih₁₀ aih₁₁) → motive₂ m₁₃ x₁₄ below₁₅} (λ (x₁₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₈)) → λ (below₁₄ : Nat:le:below {n₀} {λ (m₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} x₁₅} {Nat:succ m₈} x₁₃) → λ (h₁₅ : HEq {LE:le {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₈)} x₁₃ {Nat:le n₀ (Nat:succ m₈)} (Nat:le:step {n₀} {m₈} a₉)) → Eq:ndrec {LE:le {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₈)} {Nat:le:step {n₀} {m₈} a₉} {λ (x₁₆ : LE:le {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₈)) → (below₁₇ : Nat:le:below {n₀} {λ (m₁₇ : Nat) → λ (x₁₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₇) → funType1₁ {m₁₇} x₁₈} {Nat:succ m₈} x₁₆) → HEq {Nat:le:below {n₀} {λ (m₁₈ : Nat) → λ (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} x₁₉} {Nat:succ m₈} x₁₆} below₁₇ {Nat:le:below {n₀} {λ (m₁₈ : Nat) → λ (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} x₁₉} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)} (Nat:le:below:step {n₀} {λ (m₁₈ : Nat) → λ (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} x₁₉} {m₈} a₉ ih₁₀ aih₁₁) → motive₂ (Nat:succ m₈) x₁₆ below₁₇} (λ (below₁₆ : Nat:le:below {n₀} {λ (m₁₆ : Nat) → λ (x₁₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₆) → funType1₁ {m₁₆} x₁₇} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)) → λ (h₁₇ : HEq {Nat:le:below {n₀} {λ (m₁₇ : Nat) → λ (x₁₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₇) → funType1₁ {m₁₇} x₁₈} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)} below₁₆ {Nat:le:below {n₀} {λ (m₁₇ : Nat) → λ (x₁₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₇) → funType1₁ {m₁₇} x₁₈} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)} (Nat:le:below:step {n₀} {λ (m₁₇ : Nat) → λ (x₁₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₇) → funType1₁ {m₁₇} x₁₈} {m₈} a₉ ih₁₀ aih₁₁)) → Eq:ndrec {Nat:le:below {n₀} {λ (m₁₈ : Nat) → λ (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} x₁₉} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)} {Nat:le:below:step {n₀} {λ (m₁₈ : Nat) → λ (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} x₁₉} {m₈} a₉ ih₁₀ aih₁₁} {λ (below₁₈ : Nat:le:below {n₀} {λ (m₁₈ : Nat) → λ (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} x₁₉} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)) → motive₂ (Nat:succ m₈) (Nat:le:step {n₀} {m₈} a₉) below₁₈} (h2₇ m₈ a₉ ih₁₀ aih₁₁) {below₁₆} (Eq:symm {Nat:le:below {n₀} {λ (m₁₈ : Nat) → λ (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} x₁₉} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)} {below₁₆} {Nat:le:below:step {n₀} {λ (m₁₈ : Nat) → λ (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} x₁₉} {m₈} a₉ ih₁₀ aih₁₁} (eq~uof~uheq {Nat:le:below {n₀} {λ (m₁₈ : Nat) → λ (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} x₁₉} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)} {below₁₆} {Nat:le:below:step {n₀} {λ (m₁₈ : Nat) → λ (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} x₁₉} {m₈} a₉ ih₁₀ aih₁₁} h₁₇))) {x₁₃} (Eq:symm {LE:le {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₈)} {x₁₃} {Nat:le:step {n₀} {m₈} a₉} (eq~uof~uheq {LE:le {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₈)} {x₁₃} {Nat:le:step {n₀} {m₈} a₉} h₁₅)) below₁₄) {m₃} (Eq:symm {Nat} {m₃} {Nat:succ m₈} h₁₂) x₄ below₅) (Eq:refl {Nat} m₃) (HEq:refl {LE:le {Nat} ⦃ instLENat ⦄ n₀ m₃} x₄) (HEq:refl {Nat:le:below {n₀} {λ (m₈ : Nat) → λ (x₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₈) → funType1₁ {m₈} x₉} {m₃} x₄} below₅)

-- theorem
opaque
  Nat:succ~ule~usucc : {n₀ : Nat} → {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₀) (Nat:succ m₁)
  Nat:succ~ule~usucc {n₀} {m₁} x₂ = let funType1₃ : {m₃ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₃ → Set; funType1₃ = λ {m₃ : Nat} → λ (x₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₃) → LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₀) (Nat:succ m₃) in Nat:le:brecOn {n₀} {λ (m₄ : Nat) → λ (x₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₄) → funType1₃ {m₄} x₅} {m₁} x₂ (λ (m₄ : Nat) → λ (x₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₄) → λ (x₆ : Nat:le:below {n₀} {λ (m₆ : Nat) → λ (x₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₆) → funType1₃ {m₆} x₇} {m₄} x₅) → ~uprivate:Init:Prelude:~n0:Nat:succ~ule~usucc:match~u1~u7 {n₀} funType1₃ (λ (m₇ : Nat) → λ (x₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₇) → λ (below₉ : Nat:le:below {n₀} {λ (m₉ : Nat) → λ (x₁₀ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₉) → funType1₃ {m₉} x₁₀} {m₇} x₈) → LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₀) (Nat:succ m₇)) m₄ x₅ x₆ (λ (x₇ : Unit) → Nat:le:refl {Nat:succ n₀}) (λ (m₇ : Nat) → λ (h₈ : Nat:le n₀ m₇) → λ (ih₉ : Nat:le:below {n₀} {λ (m₉ : Nat) → λ (x₁₀ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₉) → funType1₃ {m₉} x₁₀} {m₇} h₈) → λ (aih₁₀ : funType1₃ {m₇} h₈) → Nat:le:step {Nat:succ n₀} {HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ m₇ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)} aih₁₀))

~uprivate:Init:Prelude:~n0:Nat:zero~ule:match~u1~u1 : (motive₀ : Nat → Set) → (x₁ : Nat) → (Unit → motive₀ Nat:zero) → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ x₁
~uprivate:Init:Prelude:~n0:Nat:zero~ule:match~u1~u1 motive₀ x₁ h1₂ h2₃ = Nat:casesOn {λ (x₄ : Nat) → motive₀ x₄} x₁ (h1₂ Unit:unit) (λ (n₄ : Nat) → h2₃ n₄)

Nat:zero~ule:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₁} x₀ → LE:le {Nat} ⦃ instLENat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₀
Nat:zero~ule:~uf x₀ f₁ = ~uprivate:Init:Prelude:~n0:Nat:zero~ule:match~u1~u1 (λ (x₂ : Nat) → Nat:below {λ (x₃ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₃} x₂ → LE:le {Nat} ⦃ instLENat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₂) x₀ (λ (x₂ : Unit) → λ (x₃ : Nat:below {λ (x₃ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₃} Nat:zero) → Nat:le:refl {OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄}) (λ (n₂ : Nat) → λ (x₃ : Nat:below {λ (x₃ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₃} (Nat:succ n₂)) → Nat:le:step {OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄} {n₂} (PProd.fst₂ {(λ (x₄ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₄) n₂} {Nat:rec {λ (t₄ : Nat) → Set} PUnit (λ (n₄ : Nat) → λ (nih₅ : Set) → PProd ((λ (x₆ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₆) n₄) nih₅) n₂} x₃)) f₁

-- theorem
opaque
  Nat:zero~ule : (n₀ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) n₀
  Nat:zero~ule x₀ = Nat:brecOn {λ (x₁ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₁} x₀ Nat:zero~ule:~uf

Nat:beq:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → (Unit → motive₀ Nat:zero Nat:zero) → ((n₃ : Nat) → motive₀ Nat:zero (Nat:succ n₃)) → ((n₃ : Nat) → motive₀ (Nat:succ n₃) Nat:zero) → ((n₃ : Nat) → (m₄ : Nat) → motive₀ (Nat:succ n₃) (Nat:succ m₄)) → motive₀ x₁ x₂
Nat:beq:match~u1 motive₀ x₁ x₂ h1₃ h2₄ h3₅ h4₆ = Nat:casesOn {λ (x₇ : Nat) → motive₀ x₇ x₂} x₁ (Nat:casesOn {λ (x₇ : Nat) → motive₀ Nat:zero x₇} x₂ (h1₃ Unit:unit) (λ (n₇ : Nat) → h2₄ n₇)) (λ (n₇ : Nat) → Nat:casesOn {λ (x₈ : Nat) → motive₀ (Nat:succ n₇) x₈} x₂ (h3₅ n₇) (λ (n₈ : Nat) → h4₆ n₇ n₈))

Nat:beq:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Nat → Bool} x₀ → Nat → Bool
Nat:beq:~uf x₀ f₁ x₂ = Nat:beq:match~u1 (λ (x₃ : Nat) → λ (x₄ : Nat) → Nat:below {λ (x₅ : Nat) → Nat → Bool} x₃ → Bool) x₀ x₂ (λ (x₃ : Unit) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Bool} Nat:zero) → Bool:true) (λ (n₃ : Nat) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Bool} Nat:zero) → Bool:false) (λ (n₃ : Nat) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Bool} (Nat:succ n₃)) → Bool:false) (λ (n₃ : Nat) → λ (m₄ : Nat) → λ (x₅ : Nat:below {λ (x₅ : Nat) → Nat → Bool} (Nat:succ n₃)) → PProd.fst₂ {(λ (x₆ : Nat) → Nat → Bool) n₃} {Nat:rec {λ (t₆ : Nat) → Set} PUnit (λ (n₆ : Nat) → λ (nih₇ : Set) → PProd ((λ (x₈ : Nat) → Nat → Bool) n₆) nih₇) n₃} x₅ m₄) f₁

Nat:beq : Nat → Nat → Bool
Nat:beq x₀ x₁ = Nat:brecOn {λ (x₂ : Nat) → Nat → Bool} x₀ Nat:beq:~uf x₁

record True : Set where
  constructor True:intro

-- recursor
True:rec : {motive₀ : True → Set} → motive₀ True:intro → (t₁ : True) → motive₀ t₁
True:rec {motive₀} intro₁ True:intro = intro₁

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
  congrArg : {α₀ : Set} → {β₁ : Set} → {a₂ : α₀} → {a₃ : α₀} → (f₄ : α₀ → β₁) → Eq {α₀} a₂ a₃ → Eq {β₁} (f₄ a₂) (f₄ a₃)
  congrArg {α₀} {β₁} {a₂} {a₃} f₄ h₅ = Eq:rec {α₀} {a₂} {λ (x₆ : α₀) → λ (h₇ : Eq {α₀} a₂ x₆) → Eq {β₁} (f₄ a₂) (f₄ x₆)} (rfl {β₁} {f₄ a₂}) {a₃} h₅

-- theorem
opaque
  noConfusion~uof~uNat : {α₀ : Set} → (f₁ : α₀ → Nat) → {a₂ : α₀} → {b₃ : α₀} → Eq {α₀} a₂ b₃ → Bool:rec {λ (x₄ : Bool) → Set} False True (Nat:beq (f₁ a₂) (f₁ b₃))
  noConfusion~uof~uNat {α₀} f₁ {a₂} {b₃} h₄ = Eq:rec {Nat} {f₁ a₂} {λ (x₅ : Nat) → λ (h₆ : Eq {Nat} (f₁ a₂) x₅) → Bool:rec {λ (x₇ : Bool) → Set} False True (Nat:beq (f₁ a₂) x₅)} (~uprivate:Init:Prelude:~n0:noConfusion~uof~uNat:aux (f₁ a₂)) {f₁ b₃} (congrArg {α₀} {Nat} {a₂} {b₃} f₁ h₄)

~uprivate:Init:Prelude:~n0:Nat:le~uof~uble~ueq~utrue:match~u1~u1 : (motive₀ : (n₀ : Nat) → (m₁ : Nat) → Eq {Bool} (Nat:ble n₀ m₁) Bool:true → Set) → (n₁ : Nat) → (m₂ : Nat) → (h₃ : Eq {Bool} (Nat:ble n₁ m₂) Bool:true) → ((x₄ : Nat) → (h₅ : Eq {Bool} (Nat:ble (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₄) Bool:true) → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₄ h₅) → ((n₄ : Nat) → (n₅ : Nat) → (h₆ : Eq {Bool} (Nat:ble (Nat:succ n₄) (Nat:succ n₅)) Bool:true) → motive₀ (Nat:succ n₄) (Nat:succ n₅) h₆) → motive₀ n₁ m₂ h₃
~uprivate:Init:Prelude:~n0:Nat:le~uof~uble~ueq~utrue:match~u1~u1 motive₀ n₁ m₂ h₃ h1₄ h2₅ = Nat:casesOn {λ (x₆ : Nat) → (h₇ : Eq {Bool} (Nat:ble x₆ m₂) Bool:true) → motive₀ x₆ m₂ h₇} n₁ (λ (h₆ : Eq {Bool} (Nat:ble Nat:zero m₂) Bool:true) → h1₄ m₂ h₆) (λ (n₆ : Nat) → λ (h₇ : Eq {Bool} (Nat:ble (Nat:succ n₆) m₂) Bool:true) → Nat:casesOn {λ (x₈ : Nat) → (h₉ : Eq {Bool} (Nat:ble (Nat:succ n₆) x₈) Bool:true) → motive₀ (Nat:succ n₆) x₈ h₉} m₂ (λ (h₈ : Eq {Bool} (Nat:ble (Nat:succ n₆) Nat:zero) Bool:true) → False:elim {motive₀ (Nat:succ n₆) Nat:zero h₈} (Eq:casesOn {Bool} {Nat:ble (Nat:succ n₆) Nat:zero} {λ (a₉ : Bool) → λ (x₁₀ : Eq {Bool} (Nat:ble (Nat:succ n₆) Nat:zero) a₉) → Eq {Bool} Bool:true a₉ → HEq {Eq {Bool} (Nat:ble (Nat:succ n₆) Nat:zero) Bool:true} h₈ {Eq {Bool} (Nat:ble (Nat:succ n₆) Nat:zero) a₉} x₁₀ → False} {Bool:true} h₈ (λ (h₉ : Eq {Bool} Bool:true (Nat:ble (Nat:succ n₆) Nat:zero)) → False:elim {HEq {Eq {Bool} (Nat:ble (Nat:succ n₆) Nat:zero) Bool:true} h₈ {Eq {Bool} (Nat:ble (Nat:succ n₆) Nat:zero) (Nat:ble (Nat:succ n₆) Nat:zero)} (Eq:refl {Bool} (Nat:ble (Nat:succ n₆) Nat:zero)) → False} (noConfusion~uof~uNat {Bool} Bool:ctorIdx {Bool:true} {Bool:false} h₉)) (Eq:refl {Bool} Bool:true) (HEq:refl {Eq {Bool} (Nat:ble (Nat:succ n₆) Nat:zero) Bool:true} h₈))) (λ (n₈ : Nat) → λ (h₉ : Eq {Bool} (Nat:ble (Nat:succ n₆) (Nat:succ n₈)) Bool:true) → h2₅ n₆ n₈ h₉) h₇) h₃

Nat:le~uof~uble~ueq~utrue:~uf : {n₀ : Nat} → Nat:below {λ (n₁ : Nat) → {m₂ : Nat} → Eq {Bool} (Nat:ble n₁ m₂) Bool:true → LE:le {Nat} ⦃ instLENat ⦄ n₁ m₂} n₀ → {m₁ : Nat} → Eq {Bool} (Nat:ble n₀ m₁) Bool:true → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁
Nat:le~uof~uble~ueq~utrue:~uf {n₀} f₁ {m₂} h₃ = ~uprivate:Init:Prelude:~n0:Nat:le~uof~uble~ueq~utrue:match~u1~u1 (λ (n₄ : Nat) → λ (m₅ : Nat) → λ (h₆ : Eq {Bool} (Nat:ble n₄ m₅) Bool:true) → Nat:below {λ (n₇ : Nat) → {m₈ : Nat} → Eq {Bool} (Nat:ble n₇ m₈) Bool:true → LE:le {Nat} ⦃ instLENat ⦄ n₇ m₈} n₄ → LE:le {Nat} ⦃ instLENat ⦄ n₄ m₅) n₀ m₂ h₃ (λ (x₄ : Nat) → λ (h₅ : Eq {Bool} (Nat:ble (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₄) Bool:true) → λ (x₆ : Nat:below {λ (n₆ : Nat) → {m₇ : Nat} → Eq {Bool} (Nat:ble n₆ m₇) Bool:true → LE:le {Nat} ⦃ instLENat ⦄ n₆ m₇} (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → Nat:zero~ule x₄) (λ (n₄ : Nat) → λ (n₅ : Nat) → λ (h₆ : Eq {Bool} (Nat:ble (Nat:succ n₄) (Nat:succ n₅)) Bool:true) → λ (x₇ : Nat:below {λ (n₇ : Nat) → {m₈ : Nat} → Eq {Bool} (Nat:ble n₇ m₈) Bool:true → LE:le {Nat} ⦃ instLENat ⦄ n₇ m₈} (Nat:succ n₄)) → Nat:succ~ule~usucc {n₄} {n₅} (PProd.fst₂ {(λ {n₈ : Nat} → {m₉ : Nat} → Eq {Bool} (Nat:ble n₈ m₉) Bool:true → LE:le {Nat} ⦃ instLENat ⦄ n₈ m₉) {n₄}} {Nat:rec {λ (t₈ : Nat) → Set} PUnit (λ (n₈ : Nat) → λ (nih₉ : Set) → PProd ((λ {n₁₀ : Nat} → {m₁₁ : Nat} → Eq {Bool} (Nat:ble n₁₀ m₁₁) Bool:true → LE:le {Nat} ⦃ instLENat ⦄ n₁₀ m₁₁) {n₈}) nih₉) n₄} x₇ {n₅} h₆)) f₁

-- theorem
opaque
  Nat:le~uof~uble~ueq~utrue : {n₀ : Nat} → {m₁ : Nat} → Eq {Bool} (Nat:ble n₀ m₁) Bool:true → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁
  Nat:le~uof~uble~ueq~utrue {n₀} {m₁} h₂ = Nat:brecOn {λ (n₃ : Nat) → {m₄ : Nat} → Eq {Bool} (Nat:ble n₃ m₄) Bool:true → LE:le {Nat} ⦃ instLENat ⦄ n₃ m₄} n₀ (λ (t₃ : Nat) → λ (f₄ : Nat:below {λ (n₄ : Nat) → {m₅ : Nat} → Eq {Bool} (Nat:ble n₄ m₅) Bool:true → LE:le {Nat} ⦃ instLENat ⦄ n₄ m₅} t₃) → Nat:le~uof~uble~ueq~utrue:~uf {t₃} f₄) {m₁} h₂

~uprivate:Init:Prelude:~n0:Nat:ble~uself~ueq~utrue:match~u1~u1 : (motive₀ : Nat → Set) → (x₁ : Nat) → (Unit → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ x₁
~uprivate:Init:Prelude:~n0:Nat:ble~uself~ueq~utrue:match~u1~u1 motive₀ x₁ h1₂ h2₃ = Nat:casesOn {λ (x₄ : Nat) → motive₀ x₄} x₁ (h1₂ Unit:unit) (λ (n₄ : Nat) → h2₃ n₄)

Nat:ble~uself~ueq~utrue:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Eq {Bool} (Nat:ble x₁ x₁) Bool:true} x₀ → Eq {Bool} (Nat:ble x₀ x₀) Bool:true
Nat:ble~uself~ueq~utrue:~uf x₀ f₁ = ~uprivate:Init:Prelude:~n0:Nat:ble~uself~ueq~utrue:match~u1~u1 (λ (x₂ : Nat) → Nat:below {λ (x₃ : Nat) → Eq {Bool} (Nat:ble x₃ x₃) Bool:true} x₂ → Eq {Bool} (Nat:ble x₂ x₂) Bool:true) x₀ (λ (x₂ : Unit) → λ (x₃ : Nat:below {λ (x₃ : Nat) → Eq {Bool} (Nat:ble x₃ x₃) Bool:true} (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → rfl {Bool} {Nat:ble (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)}) (λ (n₂ : Nat) → λ (x₃ : Nat:below {λ (x₃ : Nat) → Eq {Bool} (Nat:ble x₃ x₃) Bool:true} (Nat:succ n₂)) → PProd.fst₂ {(λ (x₄ : Nat) → Eq {Bool} (Nat:ble x₄ x₄) Bool:true) n₂} {Nat:rec {λ (t₄ : Nat) → Set} PUnit (λ (n₄ : Nat) → λ (nih₅ : Set) → PProd ((λ (x₆ : Nat) → Eq {Bool} (Nat:ble x₆ x₆) Bool:true) n₄) nih₅) n₂} x₃) f₁

-- theorem
opaque
  Nat:ble~uself~ueq~utrue : (n₀ : Nat) → Eq {Bool} (Nat:ble n₀ n₀) Bool:true
  Nat:ble~uself~ueq~utrue x₀ = Nat:brecOn {λ (x₁ : Nat) → Eq {Bool} (Nat:ble x₁ x₁) Bool:true} x₀ Nat:ble~uself~ueq~utrue:~uf

~uprivate:Init:Prelude:~n0:Nat:ble~usucc~ueq~utrue:match~u1~u1 : (motive₀ : (x₀ : Nat) → (x₁ : Nat) → Eq {Bool} (Nat:ble x₀ x₁) Bool:true → Set) → (x₁ : Nat) → (x₂ : Nat) → (x₃ : Eq {Bool} (Nat:ble x₁ x₂) Bool:true) → ((x₄ : Nat) → (x₅ : Eq {Bool} (Nat:ble (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₄) Bool:true) → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₄ x₅) → ((n₄ : Nat) → (n₅ : Nat) → (h₆ : Eq {Bool} (Nat:ble (Nat:succ n₄) (Nat:succ n₅)) Bool:true) → motive₀ (Nat:succ n₄) (Nat:succ n₅) h₆) → motive₀ x₁ x₂ x₃
~uprivate:Init:Prelude:~n0:Nat:ble~usucc~ueq~utrue:match~u1~u1 motive₀ x₁ x₂ x₃ h1₄ h2₅ = Nat:casesOn {λ (x₆ : Nat) → (x₇ : Eq {Bool} (Nat:ble x₆ x₂) Bool:true) → motive₀ x₆ x₂ x₇} x₁ (λ (x₆ : Eq {Bool} (Nat:ble Nat:zero x₂) Bool:true) → h1₄ x₂ x₆) (λ (n₆ : Nat) → λ (x₇ : Eq {Bool} (Nat:ble (Nat:succ n₆) x₂) Bool:true) → Nat:casesOn {λ (x₈ : Nat) → (x₉ : Eq {Bool} (Nat:ble (Nat:succ n₆) x₈) Bool:true) → motive₀ (Nat:succ n₆) x₈ x₉} x₂ (λ (x₈ : Eq {Bool} (Nat:ble (Nat:succ n₆) Nat:zero) Bool:true) → False:elim {motive₀ (Nat:succ n₆) Nat:zero x₈} (Eq:casesOn {Bool} {Nat:ble (Nat:succ n₆) Nat:zero} {λ (a₉ : Bool) → λ (x₁₀ : Eq {Bool} (Nat:ble (Nat:succ n₆) Nat:zero) a₉) → Eq {Bool} Bool:true a₉ → HEq {Eq {Bool} (Nat:ble (Nat:succ n₆) Nat:zero) Bool:true} x₈ {Eq {Bool} (Nat:ble (Nat:succ n₆) Nat:zero) a₉} x₁₀ → False} {Bool:true} x₈ (λ (h₉ : Eq {Bool} Bool:true (Nat:ble (Nat:succ n₆) Nat:zero)) → False:elim {HEq {Eq {Bool} (Nat:ble (Nat:succ n₆) Nat:zero) Bool:true} x₈ {Eq {Bool} (Nat:ble (Nat:succ n₆) Nat:zero) (Nat:ble (Nat:succ n₆) Nat:zero)} (Eq:refl {Bool} (Nat:ble (Nat:succ n₆) Nat:zero)) → False} (noConfusion~uof~uNat {Bool} Bool:ctorIdx {Bool:true} {Bool:false} h₉)) (Eq:refl {Bool} Bool:true) (HEq:refl {Eq {Bool} (Nat:ble (Nat:succ n₆) Nat:zero) Bool:true} x₈))) (λ (n₈ : Nat) → λ (x₉ : Eq {Bool} (Nat:ble (Nat:succ n₆) (Nat:succ n₈)) Bool:true) → h2₅ n₆ n₈ x₉) x₇) x₃

Nat:ble~usucc~ueq~utrue:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → (x₂ : Nat) → Eq {Bool} (Nat:ble x₁ x₂) Bool:true → Eq {Bool} (Nat:ble x₁ (Nat:succ x₂)) Bool:true} x₀ → (x₁ : Nat) → Eq {Bool} (Nat:ble x₀ x₁) Bool:true → Eq {Bool} (Nat:ble x₀ (Nat:succ x₁)) Bool:true
Nat:ble~usucc~ueq~utrue:~uf x₀ f₁ x₂ x₃ = ~uprivate:Init:Prelude:~n0:Nat:ble~usucc~ueq~utrue:match~u1~u1 (λ (x₄ : Nat) → λ (x₅ : Nat) → λ (x₆ : Eq {Bool} (Nat:ble x₄ x₅) Bool:true) → Nat:below {λ (x₇ : Nat) → (x₈ : Nat) → Eq {Bool} (Nat:ble x₇ x₈) Bool:true → Eq {Bool} (Nat:ble x₇ (Nat:succ x₈)) Bool:true} x₄ → Eq {Bool} (Nat:ble x₄ (Nat:succ x₅)) Bool:true) x₀ x₂ x₃ (λ (x₄ : Nat) → λ (x₅ : Eq {Bool} (Nat:ble (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₄) Bool:true) → λ (x₆ : Nat:below {λ (x₆ : Nat) → (x₇ : Nat) → Eq {Bool} (Nat:ble x₆ x₇) Bool:true → Eq {Bool} (Nat:ble x₆ (Nat:succ x₇)) Bool:true} (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → rfl {Bool} {Nat:ble (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ x₄)}) (λ (n₄ : Nat) → λ (n₅ : Nat) → λ (h₆ : Eq {Bool} (Nat:ble (Nat:succ n₄) (Nat:succ n₅)) Bool:true) → λ (x₇ : Nat:below {λ (x₇ : Nat) → (x₈ : Nat) → Eq {Bool} (Nat:ble x₇ x₈) Bool:true → Eq {Bool} (Nat:ble x₇ (Nat:succ x₈)) Bool:true} (Nat:succ n₄)) → PProd.fst₂ {(λ (x₈ : Nat) → (x₉ : Nat) → Eq {Bool} (Nat:ble x₈ x₉) Bool:true → Eq {Bool} (Nat:ble x₈ (Nat:succ x₉)) Bool:true) n₄} {Nat:rec {λ (t₈ : Nat) → Set} PUnit (λ (n₈ : Nat) → λ (nih₉ : Set) → PProd ((λ (x₁₀ : Nat) → (x₁₁ : Nat) → Eq {Bool} (Nat:ble x₁₀ x₁₁) Bool:true → Eq {Bool} (Nat:ble x₁₀ (Nat:succ x₁₁)) Bool:true) n₈) nih₉) n₄} x₇ n₅ h₆) f₁

-- theorem
opaque
  Nat:ble~usucc~ueq~utrue : {n₀ : Nat} → {m₁ : Nat} → Eq {Bool} (Nat:ble n₀ m₁) Bool:true → Eq {Bool} (Nat:ble n₀ (Nat:succ m₁)) Bool:true
  Nat:ble~usucc~ueq~utrue {x₀} {x₁} x₂ = Nat:brecOn {λ (x₃ : Nat) → (x₄ : Nat) → Eq {Bool} (Nat:ble x₃ x₄) Bool:true → Eq {Bool} (Nat:ble x₃ (Nat:succ x₄)) Bool:true} x₀ Nat:ble~usucc~ueq~utrue:~uf x₁ x₂

~uprivate:Init:Prelude:~n0:Nat:ble~ueq~utrue~uof~ule:match~u1~u7 : {n₀ : Nat} → (funType1₁ : {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → Set) → (motive₂ : (m₂ : Nat) → (h₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₂) → Nat:le:below {n₀} {λ (m₄ : Nat) → λ (h₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₄) → funType1₁ {m₄} h₅} {m₂} h₃ → Set) → (m₃ : Nat) → (h₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₃) → (below₅ : Nat:le:below {n₀} {λ (m₅ : Nat) → λ (h₆ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₅) → funType1₁ {m₅} h₆} {m₃} h₄) → (Unit → motive₂ n₀ (Nat:le:refl {n₀}) (Nat:le:below:refl {n₀} {λ (m₆ : Nat) → λ (h₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₆) → funType1₁ {m₆} h₇})) → ((m₆ : Nat) → (h₇ : Nat:le n₀ m₆) → (ih₈ : Nat:le:below {n₀} {λ (m₈ : Nat) → λ (h₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₈) → funType1₁ {m₈} h₉} {m₆} h₇) → (aih₉ : funType1₁ {m₆} h₇) → motive₂ (Nat:succ m₆) (Nat:le:step {n₀} {m₆} h₇) (Nat:le:below:step {n₀} {λ (m₁₀ : Nat) → λ (h₁₁ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₀) → funType1₁ {m₁₀} h₁₁} {m₆} h₇ ih₈ aih₉)) → motive₂ m₃ h₄ below₅
~uprivate:Init:Prelude:~n0:Nat:ble~ueq~utrue~uof~ule:match~u1~u7 {n₀} funType1₁ motive₂ m₃ h₄ below₅ h1₆ h2₇ = Nat:le:below:casesOn {n₀} {λ (m₈ : Nat) → λ (h₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₈) → funType1₁ {m₈} h₉} {λ {a₈ : Nat} → λ (t₉ : Nat:le n₀ a₈) → λ (x₁₀ : Nat:le:below {n₀} {λ (m₁₀ : Nat) → λ (h₁₁ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₀) → funType1₁ {m₁₀} h₁₁} {a₈} t₉) → Eq {Nat} m₃ a₈ → HEq {LE:le {Nat} ⦃ instLENat ⦄ n₀ m₃} h₄ {Nat:le n₀ a₈} t₉ → HEq {Nat:le:below {n₀} {λ (m₁₁ : Nat) → λ (h₁₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₁) → funType1₁ {m₁₁} h₁₂} {m₃} h₄} below₅ {Nat:le:below {n₀} {λ (m₁₁ : Nat) → λ (h₁₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₁) → funType1₁ {m₁₁} h₁₂} {a₈} t₉} x₁₀ → motive₂ m₃ h₄ below₅} {m₃} {h₄} below₅ (λ (h₈ : Eq {Nat} m₃ n₀) → Eq:ndrec {Nat} {n₀} {λ (m₉ : Nat) → (h₁₀ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₉) → (below₁₁ : Nat:le:below {n₀} {λ (m₁₁ : Nat) → λ (h₁₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₁) → funType1₁ {m₁₁} h₁₂} {m₉} h₁₀) → HEq {LE:le {Nat} ⦃ instLENat ⦄ n₀ m₉} h₁₀ {Nat:le n₀ n₀} (Nat:le:refl {n₀}) → HEq {Nat:le:below {n₀} {λ (m₁₂ : Nat) → λ (h₁₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₂) → funType1₁ {m₁₂} h₁₃} {m₉} h₁₀} below₁₁ {Nat:le:below {n₀} {λ (m₁₂ : Nat) → λ (h₁₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₂) → funType1₁ {m₁₂} h₁₃} {n₀} (Nat:le:refl {n₀})} (Nat:le:below:refl {n₀} {λ (m₁₂ : Nat) → λ (h₁₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₂) → funType1₁ {m₁₂} h₁₃}) → motive₂ m₉ h₁₀ below₁₁} (λ (h₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ n₀) → λ (below₁₀ : Nat:le:below {n₀} {λ (m₁₀ : Nat) → λ (h₁₁ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₀) → funType1₁ {m₁₀} h₁₁} {n₀} h₉) → λ (h₁₁ : HEq {LE:le {Nat} ⦃ instLENat ⦄ n₀ n₀} h₉ {Nat:le n₀ n₀} (Nat:le:refl {n₀})) → Eq:ndrec {LE:le {Nat} ⦃ instLENat ⦄ n₀ n₀} {Nat:le:refl {n₀}} {λ (h₁₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ n₀) → (below₁₃ : Nat:le:below {n₀} {λ (m₁₃ : Nat) → λ (h₁₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₃) → funType1₁ {m₁₃} h₁₄} {n₀} h₁₂) → HEq {Nat:le:below {n₀} {λ (m₁₄ : Nat) → λ (h₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} h₁₅} {n₀} h₁₂} below₁₃ {Nat:le:below {n₀} {λ (m₁₄ : Nat) → λ (h₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} h₁₅} {n₀} (Nat:le:refl {n₀})} (Nat:le:below:refl {n₀} {λ (m₁₄ : Nat) → λ (h₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} h₁₅}) → motive₂ n₀ h₁₂ below₁₃} (λ (below₁₂ : Nat:le:below {n₀} {λ (m₁₂ : Nat) → λ (h₁₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₂) → funType1₁ {m₁₂} h₁₃} {n₀} (Nat:le:refl {n₀})) → λ (h₁₃ : HEq {Nat:le:below {n₀} {λ (m₁₃ : Nat) → λ (h₁₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₃) → funType1₁ {m₁₃} h₁₄} {n₀} (Nat:le:refl {n₀})} below₁₂ {Nat:le:below {n₀} {λ (m₁₃ : Nat) → λ (h₁₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₃) → funType1₁ {m₁₃} h₁₄} {n₀} (Nat:le:refl {n₀})} (Nat:le:below:refl {n₀} {λ (m₁₃ : Nat) → λ (h₁₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₃) → funType1₁ {m₁₃} h₁₄})) → Eq:ndrec {Nat:le:below {n₀} {λ (m₁₄ : Nat) → λ (h₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} h₁₅} {n₀} (Nat:le:refl {n₀})} {Nat:le:below:refl {n₀} {λ (m₁₄ : Nat) → λ (h₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} h₁₅}} {λ (below₁₄ : Nat:le:below {n₀} {λ (m₁₄ : Nat) → λ (h₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} h₁₅} {n₀} (Nat:le:refl {n₀})) → motive₂ n₀ (Nat:le:refl {n₀}) below₁₄} (h1₆ Unit:unit) {below₁₂} (Eq:symm {Nat:le:below {n₀} {λ (m₁₄ : Nat) → λ (h₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} h₁₅} {n₀} (Nat:le:refl {n₀})} {below₁₂} {Nat:le:below:refl {n₀} {λ (m₁₄ : Nat) → λ (h₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} h₁₅}} (eq~uof~uheq {Nat:le:below {n₀} {λ (m₁₄ : Nat) → λ (h₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} h₁₅} {n₀} (Nat:le:refl {n₀})} {below₁₂} {Nat:le:below:refl {n₀} {λ (m₁₄ : Nat) → λ (h₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} h₁₅}} h₁₃))) {h₉} (Eq:symm {LE:le {Nat} ⦃ instLENat ⦄ n₀ n₀} {h₉} {Nat:le:refl {n₀}} (eq~uof~uheq {LE:le {Nat} ⦃ instLENat ⦄ n₀ n₀} {h₉} {Nat:le:refl {n₀}} h₁₁)) below₁₀) {m₃} (Eq:symm {Nat} {m₃} {n₀} h₈) h₄ below₅) (λ {m₈ : Nat} → λ (a₉ : Nat:le n₀ m₈) → λ (ih₁₀ : Nat:le:below {n₀} {λ (m₁₀ : Nat) → λ (h₁₁ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₀) → funType1₁ {m₁₀} h₁₁} {m₈} a₉) → λ (aih₁₁ : funType1₁ {m₈} a₉) → λ (h₁₂ : Eq {Nat} m₃ (Nat:succ m₈)) → Eq:ndrec {Nat} {Nat:succ m₈} {λ (m₁₃ : Nat) → (h₁₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₃) → (below₁₅ : Nat:le:below {n₀} {λ (m₁₅ : Nat) → λ (h₁₆ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₅) → funType1₁ {m₁₅} h₁₆} {m₁₃} h₁₄) → HEq {LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₃} h₁₄ {Nat:le n₀ (Nat:succ m₈)} (Nat:le:step {n₀} {m₈} a₉) → HEq {Nat:le:below {n₀} {λ (m₁₆ : Nat) → λ (h₁₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₆) → funType1₁ {m₁₆} h₁₇} {m₁₃} h₁₄} below₁₅ {Nat:le:below {n₀} {λ (m₁₆ : Nat) → λ (h₁₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₆) → funType1₁ {m₁₆} h₁₇} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)} (Nat:le:below:step {n₀} {λ (m₁₆ : Nat) → λ (h₁₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₆) → funType1₁ {m₁₆} h₁₇} {m₈} a₉ ih₁₀ aih₁₁) → motive₂ m₁₃ h₁₄ below₁₅} (λ (h₁₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₈)) → λ (below₁₄ : Nat:le:below {n₀} {λ (m₁₄ : Nat) → λ (h₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} h₁₅} {Nat:succ m₈} h₁₃) → λ (h₁₅ : HEq {LE:le {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₈)} h₁₃ {Nat:le n₀ (Nat:succ m₈)} (Nat:le:step {n₀} {m₈} a₉)) → Eq:ndrec {LE:le {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₈)} {Nat:le:step {n₀} {m₈} a₉} {λ (h₁₆ : LE:le {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₈)) → (below₁₇ : Nat:le:below {n₀} {λ (m₁₇ : Nat) → λ (h₁₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₇) → funType1₁ {m₁₇} h₁₈} {Nat:succ m₈} h₁₆) → HEq {Nat:le:below {n₀} {λ (m₁₈ : Nat) → λ (h₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} h₁₉} {Nat:succ m₈} h₁₆} below₁₇ {Nat:le:below {n₀} {λ (m₁₈ : Nat) → λ (h₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} h₁₉} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)} (Nat:le:below:step {n₀} {λ (m₁₈ : Nat) → λ (h₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} h₁₉} {m₈} a₉ ih₁₀ aih₁₁) → motive₂ (Nat:succ m₈) h₁₆ below₁₇} (λ (below₁₆ : Nat:le:below {n₀} {λ (m₁₆ : Nat) → λ (h₁₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₆) → funType1₁ {m₁₆} h₁₇} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)) → λ (h₁₇ : HEq {Nat:le:below {n₀} {λ (m₁₇ : Nat) → λ (h₁₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₇) → funType1₁ {m₁₇} h₁₈} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)} below₁₆ {Nat:le:below {n₀} {λ (m₁₇ : Nat) → λ (h₁₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₇) → funType1₁ {m₁₇} h₁₈} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)} (Nat:le:below:step {n₀} {λ (m₁₇ : Nat) → λ (h₁₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₇) → funType1₁ {m₁₇} h₁₈} {m₈} a₉ ih₁₀ aih₁₁)) → Eq:ndrec {Nat:le:below {n₀} {λ (m₁₈ : Nat) → λ (h₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} h₁₉} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)} {Nat:le:below:step {n₀} {λ (m₁₈ : Nat) → λ (h₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} h₁₉} {m₈} a₉ ih₁₀ aih₁₁} {λ (below₁₈ : Nat:le:below {n₀} {λ (m₁₈ : Nat) → λ (h₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} h₁₉} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)) → motive₂ (Nat:succ m₈) (Nat:le:step {n₀} {m₈} a₉) below₁₈} (h2₇ m₈ a₉ ih₁₀ aih₁₁) {below₁₆} (Eq:symm {Nat:le:below {n₀} {λ (m₁₈ : Nat) → λ (h₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} h₁₉} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)} {below₁₆} {Nat:le:below:step {n₀} {λ (m₁₈ : Nat) → λ (h₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} h₁₉} {m₈} a₉ ih₁₀ aih₁₁} (eq~uof~uheq {Nat:le:below {n₀} {λ (m₁₈ : Nat) → λ (h₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} h₁₉} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)} {below₁₆} {Nat:le:below:step {n₀} {λ (m₁₈ : Nat) → λ (h₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} h₁₉} {m₈} a₉ ih₁₀ aih₁₁} h₁₇))) {h₁₃} (Eq:symm {LE:le {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₈)} {h₁₃} {Nat:le:step {n₀} {m₈} a₉} (eq~uof~uheq {LE:le {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₈)} {h₁₃} {Nat:le:step {n₀} {m₈} a₉} h₁₅)) below₁₄) {m₃} (Eq:symm {Nat} {m₃} {Nat:succ m₈} h₁₂) h₄ below₅) (Eq:refl {Nat} m₃) (HEq:refl {LE:le {Nat} ⦃ instLENat ⦄ n₀ m₃} h₄) (HEq:refl {Nat:le:below {n₀} {λ (m₈ : Nat) → λ (h₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₈) → funType1₁ {m₈} h₉} {m₃} h₄} below₅)

-- theorem
opaque
  Nat:ble~ueq~utrue~uof~ule : {n₀ : Nat} → {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → Eq {Bool} (Nat:ble n₀ m₁) Bool:true
  Nat:ble~ueq~utrue~uof~ule {n₀} {m₁} h₂ = let funType1₃ : {m₃ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₃ → Set; funType1₃ = λ {m₃ : Nat} → λ (h₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₃) → Eq {Bool} (Nat:ble n₀ m₃) Bool:true in Nat:le:brecOn {n₀} {λ (m₄ : Nat) → λ (h₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₄) → funType1₃ {m₄} h₅} {m₁} h₂ (λ (m₄ : Nat) → λ (h₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₄) → λ (x₆ : Nat:le:below {n₀} {λ (m₆ : Nat) → λ (h₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₆) → funType1₃ {m₆} h₇} {m₄} h₅) → ~uprivate:Init:Prelude:~n0:Nat:ble~ueq~utrue~uof~ule:match~u1~u7 {n₀} funType1₃ (λ (m₇ : Nat) → λ (h₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₇) → λ (below₉ : Nat:le:below {n₀} {λ (m₉ : Nat) → λ (h₁₀ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₉) → funType1₃ {m₉} h₁₀} {m₇} h₈) → Eq {Bool} (Nat:ble n₀ m₇) Bool:true) m₄ h₅ x₆ (λ (x₇ : Unit) → Nat:ble~uself~ueq~utrue n₀) (λ (m₇ : Nat) → λ (h₈ : Nat:le n₀ m₇) → λ (ih₉ : Nat:le:below {n₀} {λ (m₉ : Nat) → λ (h₁₀ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₉) → funType1₃ {m₉} h₁₀} {m₇} h₈) → λ (aih₁₀ : funType1₃ {m₇} h₈) → Nat:ble~usucc~ueq~utrue {n₀} {m₇} aih₁₀))

absurd : {a₀ : Set} → {b₁ : Set} → a₀ → Not a₀ → b₁
absurd {a₀} {b₁} h₂ h₃ = False:rec (λ (x₄ : False) → b₁) (h₃ h₂)

-- theorem
opaque
  Nat:not~ule~uof~unot~uble~ueq~utrue : {n₀ : Nat} → {m₁ : Nat} → Not (Eq {Bool} (Nat:ble n₀ m₁) Bool:true) → Not (LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁)
  Nat:not~ule~uof~unot~uble~ueq~utrue {n₀} {m₁} h₂ h₃ = absurd {Eq {Bool} (Nat:ble n₀ m₁) Bool:true} {False} (Nat:ble~ueq~utrue~uof~ule {n₀} {m₁} h₃) h₂

dite : {α₀ : Set} → (c₁ : Set) → ⦃ _ : Decidable c₁ ⦄ → (c₁ → α₀) → (Not c₁ → α₀) → α₀
dite {α₀} c₁ ⦃ h₂ ⦄ t₃ e₄ = Decidable:casesOn {c₁} {λ (x₅ : Decidable c₁) → α₀} h₂ e₄ t₃

instDecidableEqBool : DecidableEq Bool
instDecidableEqBool = Bool:decEq

Nat:decLe : (n₀ : Nat) → (m₁ : Nat) → Decidable (LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁)
Nat:decLe n₀ m₁ = dite {Decidable (LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁)} (Eq {Bool} (Nat:ble n₀ m₁) Bool:true) ⦃ instDecidableEqBool (Nat:ble n₀ m₁) Bool:true ⦄ (λ (h₂ : Eq {Bool} (Nat:ble n₀ m₁) Bool:true) → Decidable:isTrue {LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁} (Nat:le~uof~uble~ueq~utrue {n₀} {m₁} h₂)) (λ (h₂ : Not (Eq {Bool} (Nat:ble n₀ m₁) Bool:true)) → Decidable:isFalse {LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁} (Nat:not~ule~uof~unot~uble~ueq~utrue {n₀} {m₁} h₂))

namedPattern : {α₀ : Set} → (x₁ : α₀) → (a₂ : α₀) → Eq {α₀} x₁ a₂ → α₀
namedPattern {α₀} x₁ a₂ h₃ = a₂

Nat:mod:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → ((x₃ : Nat) → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₃) → ((n₃ : Nat) → (n₄ : Nat) → (h₅ : Eq {Nat} n₃ (Nat:succ n₄)) → (m₆ : Nat) → motive₀ (namedPattern {Nat} n₃ (Nat:succ n₄) h₅) m₆) → motive₀ x₁ x₂
Nat:mod:match~u1 motive₀ x₁ x₂ h1₃ h2₄ = Nat:casesOn {λ (x₅ : Nat) → motive₀ x₅ x₂} x₁ (h1₃ x₂) (λ (n₅ : Nat) → h2₄ (Nat:succ n₅) n₅ (Eq:refl {Nat} (Nat:succ n₅)) x₂)

Nat:decLt : (n₀ : Nat) → (m₁ : Nat) → Decidable (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁)
Nat:decLt n₀ m₁ = Nat:decLe (Nat:succ n₀) m₁

-- theorem
opaque
  Nat:le~urefl : (n₀ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ n₀ n₀
  Nat:le~urefl n₀ = Nat:le:refl {n₀}

-- theorem
opaque
  Nat:lt~uadd~uone : (n₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ n₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))
  Nat:lt~uadd~uone n₀ = Nat:le~urefl (Nat:succ n₀)

-- theorem
opaque
  Nat:lt~usucc~uself : (n₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ n₀ (Nat:succ n₀)
  Nat:lt~usucc~uself n₀ = Nat:lt~uadd~uone n₀

record HSub (α₀ : Set) (β₁ : Set) (γ₂ : outParam Set) : Set where
  constructor HSub:mk
  field
    hSub₃ : α₀ → β₁ → γ₂

-- recursor
HSub:rec : {α₀ : Set} → {β₁ : Set} → {γ₂ : Set} → {motive₃ : HSub α₀ β₁ γ₂ → Set} → ((hSub₄ : α₀ → β₁ → γ₂) → motive₃ (HSub:mk {α₀} {β₁} {γ₂} hSub₄)) → (t₄ : HSub α₀ β₁ γ₂) → motive₃ t₄
HSub:rec {α₀} {β₁} {γ₂} {motive₃} mk₄ (HSub:mk hSub₅) = mk₄ hSub₅

HSub:hSub : {α₀ : Set} → {β₁ : Set} → {γ₂ : outParam Set} → ⦃ _ : HSub α₀ β₁ γ₂ ⦄ → α₀ → β₁ → γ₂
HSub:hSub {α₀} {β₁} {γ₂} ⦃ self₃ ⦄ = HSub.hSub₃ {α₀} {β₁} {γ₂} self₃

Nat:ctorIdx : Nat → Nat
Nat:ctorIdx x₀ = Nat:casesOn {λ (x₁ : Nat) → Nat} x₀ 0 (λ (n₁ : Nat) → 1)

Nat:le:casesOn : {n₀ : Nat} → {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} → {a₂ : Nat} → (t₃ : Nat:le n₀ a₂) → motive₁ n₀ (Nat:le:refl {n₀}) → ({m₄ : Nat} → (a₅ : Nat:le n₀ m₄) → motive₁ (Nat:succ m₄) (Nat:le:step {n₀} {m₄} a₅)) → motive₁ a₂ t₃
Nat:le:casesOn {n₀} {motive₁} {a₂} t₃ refl₄ step₅ = Nat:le:rec {n₀} {motive₁} refl₄ (λ {m₆ : Nat} → λ (a₇ : Nat:le n₀ m₆) → λ (aih₈ : motive₁ m₆ a₇) → step₅ {m₆} a₇) {a₂} t₃

Nat:div:go:match~u1 : (x₀ : Nat) → (motive₁ : (fuel₁ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₀ fuel₁ → Set) → (fuel₂ : Nat) → (hfuel₃ : LT:lt {Nat} ⦃ instLTNat ⦄ x₀ fuel₂) → ((fuel₄ : Nat) → (hfuel₅ : LT:lt {Nat} ⦃ instLTNat ⦄ x₀ (Nat:succ fuel₄)) → motive₁ (Nat:succ fuel₄) hfuel₅) → motive₁ fuel₂ hfuel₃
Nat:div:go:match~u1 x₀ motive₁ fuel₂ hfuel₃ h1₄ = Nat:casesOn {λ (x₅ : Nat) → (hfuel₆ : LT:lt {Nat} ⦃ instLTNat ⦄ x₀ x₅) → motive₁ x₅ hfuel₆} fuel₂ (λ (hfuel₅ : LT:lt {Nat} ⦃ instLTNat ⦄ x₀ Nat:zero) → False:elim {motive₁ Nat:zero hfuel₅} (Nat:le:casesOn {Nat:succ x₀} {λ (a₆ : Nat) → λ (x₇ : Nat:le (Nat:succ x₀) a₆) → Eq {Nat} Nat:zero a₆ → HEq {LT:lt {Nat} ⦃ instLTNat ⦄ x₀ Nat:zero} hfuel₅ {Nat:le (Nat:succ x₀) a₆} x₇ → False} {Nat:zero} hfuel₅ (λ (h₆ : Eq {Nat} Nat:zero (Nat:succ x₀)) → False:elim {HEq {LT:lt {Nat} ⦃ instLTNat ⦄ x₀ Nat:zero} hfuel₅ {Nat:le (Nat:succ x₀) (Nat:succ x₀)} (Nat:le:refl {Nat:succ x₀}) → False} (noConfusion~uof~uNat {Nat} Nat:ctorIdx {Nat:zero} {Nat:succ x₀} h₆)) (λ {m₆ : Nat} → λ (a₇ : Nat:le (Nat:succ x₀) m₆) → λ (h₈ : Eq {Nat} Nat:zero (Nat:succ m₆)) → False:elim {HEq {LT:lt {Nat} ⦃ instLTNat ⦄ x₀ Nat:zero} hfuel₅ {Nat:le (Nat:succ x₀) (Nat:succ m₆)} (Nat:le:step {Nat:succ x₀} {m₆} a₇) → False} (noConfusion~uof~uNat {Nat} Nat:ctorIdx {Nat:zero} {Nat:succ m₆} h₈)) (Eq:refl {Nat} Nat:zero) (HEq:refl {LT:lt {Nat} ⦃ instLTNat ⦄ x₀ Nat:zero} hfuel₅))) (λ (n₅ : Nat) → λ (hfuel₆ : LT:lt {Nat} ⦃ instLTNat ⦄ x₀ (Nat:succ n₅)) → h1₄ n₅ hfuel₆) hfuel₃

~uprivate:Init:Prelude:~n0:Nat:le~utrans:match~u1~u10 : {n₀ : Nat} → {m₁ : Nat} → (funType1₂ : {k₂ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → LE:le {Nat} ⦃ instLENat ⦄ m₁ k₂ → Set) → (motive₃ : (k₃ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → (x₄ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₃) → Nat:le:below {m₁} {λ (k₅ : Nat) → λ (x₆ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₅) → (x₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₅} x₇ x₆} {k₃} x₄ → Set) → (k₄ : Nat) → (x₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → (x₆ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₄) → (below₇ : Nat:le:below {m₁} {λ (k₇ : Nat) → λ (x₈ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₇) → (x₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₇} x₉ x₈} {k₄} x₆) → ((h₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → motive₃ m₁ h₈ (Nat:le:refl {m₁}) (Nat:le:below:refl {m₁} {λ (k₉ : Nat) → λ (x₁₀ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₉) → (x₁₁ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₉} x₁₁ x₁₀})) → ((h₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → (m₉ : Nat) → (h₁₀ : Nat:le m₁ m₉) → (ih₁₁ : Nat:le:below {m₁} {λ (k₁₁ : Nat) → λ (x₁₂ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₁) → (x₁₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₁} x₁₃ x₁₂} {m₉} h₁₀) → (aih₁₂ : (x₁₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {m₉} x₁₂ h₁₀) → motive₃ (Nat:succ m₉) h₈ (Nat:le:step {m₁} {m₉} h₁₀) (Nat:le:below:step {m₁} {λ (k₁₃ : Nat) → λ (x₁₄ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₃) → (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₃} x₁₅ x₁₄} {m₉} h₁₀ ih₁₁ aih₁₂)) → motive₃ k₄ x₅ x₆ below₇
~uprivate:Init:Prelude:~n0:Nat:le~utrans:match~u1~u10 {n₀} {m₁} funType1₂ motive₃ k₄ x₅ x₆ below₇ h1₈ h2₉ = Nat:le:below:casesOn {m₁} {λ (k₁₀ : Nat) → λ (x₁₁ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₀) → (x₁₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₀} x₁₂ x₁₁} {λ {a₁₀ : Nat} → λ (t₁₁ : Nat:le m₁ a₁₀) → λ (x₁₂ : Nat:le:below {m₁} {λ (k₁₂ : Nat) → λ (x₁₃ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₂) → (x₁₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₂} x₁₄ x₁₃} {a₁₀} t₁₁) → Eq {Nat} k₄ a₁₀ → HEq {LE:le {Nat} ⦃ instLENat ⦄ m₁ k₄} x₆ {Nat:le m₁ a₁₀} t₁₁ → HEq {Nat:le:below {m₁} {λ (k₁₃ : Nat) → λ (x₁₄ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₃) → (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₃} x₁₅ x₁₄} {k₄} x₆} below₇ {Nat:le:below {m₁} {λ (k₁₃ : Nat) → λ (x₁₄ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₃) → (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₃} x₁₅ x₁₄} {a₁₀} t₁₁} x₁₂ → motive₃ k₄ x₅ x₆ below₇} {k₄} {x₆} below₇ (λ (h₁₀ : Eq {Nat} k₄ m₁) → Eq:ndrec {Nat} {m₁} {λ (k₁₁ : Nat) → (x₁₂ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₁) → (below₁₃ : Nat:le:below {m₁} {λ (k₁₃ : Nat) → λ (x₁₄ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₃) → (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₃} x₁₅ x₁₄} {k₁₁} x₁₂) → HEq {LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₁} x₁₂ {Nat:le m₁ m₁} (Nat:le:refl {m₁}) → HEq {Nat:le:below {m₁} {λ (k₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₄) → (x₁₆ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₄} x₁₆ x₁₅} {k₁₁} x₁₂} below₁₃ {Nat:le:below {m₁} {λ (k₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₄) → (x₁₆ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₄} x₁₆ x₁₅} {m₁} (Nat:le:refl {m₁})} (Nat:le:below:refl {m₁} {λ (k₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₄) → (x₁₆ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₄} x₁₆ x₁₅}) → motive₃ k₁₁ x₅ x₁₂ below₁₃} (λ (x₁₁ : LE:le {Nat} ⦃ instLENat ⦄ m₁ m₁) → λ (below₁₂ : Nat:le:below {m₁} {λ (k₁₂ : Nat) → λ (x₁₃ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₂) → (x₁₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₂} x₁₄ x₁₃} {m₁} x₁₁) → λ (h₁₃ : HEq {LE:le {Nat} ⦃ instLENat ⦄ m₁ m₁} x₁₁ {Nat:le m₁ m₁} (Nat:le:refl {m₁})) → Eq:ndrec {LE:le {Nat} ⦃ instLENat ⦄ m₁ m₁} {Nat:le:refl {m₁}} {λ (x₁₄ : LE:le {Nat} ⦃ instLENat ⦄ m₁ m₁) → (below₁₅ : Nat:le:below {m₁} {λ (k₁₅ : Nat) → λ (x₁₆ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₅) → (x₁₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₅} x₁₇ x₁₆} {m₁} x₁₄) → HEq {Nat:le:below {m₁} {λ (k₁₆ : Nat) → λ (x₁₇ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₆) → (x₁₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₆} x₁₈ x₁₇} {m₁} x₁₄} below₁₅ {Nat:le:below {m₁} {λ (k₁₆ : Nat) → λ (x₁₇ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₆) → (x₁₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₆} x₁₈ x₁₇} {m₁} (Nat:le:refl {m₁})} (Nat:le:below:refl {m₁} {λ (k₁₆ : Nat) → λ (x₁₇ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₆) → (x₁₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₆} x₁₈ x₁₇}) → motive₃ m₁ x₅ x₁₄ below₁₅} (λ (below₁₄ : Nat:le:below {m₁} {λ (k₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₄) → (x₁₆ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₄} x₁₆ x₁₅} {m₁} (Nat:le:refl {m₁})) → λ (h₁₅ : HEq {Nat:le:below {m₁} {λ (k₁₅ : Nat) → λ (x₁₆ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₅) → (x₁₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₅} x₁₇ x₁₆} {m₁} (Nat:le:refl {m₁})} below₁₄ {Nat:le:below {m₁} {λ (k₁₅ : Nat) → λ (x₁₆ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₅) → (x₁₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₅} x₁₇ x₁₆} {m₁} (Nat:le:refl {m₁})} (Nat:le:below:refl {m₁} {λ (k₁₅ : Nat) → λ (x₁₆ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₅) → (x₁₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₅} x₁₇ x₁₆})) → Eq:ndrec {Nat:le:below {m₁} {λ (k₁₆ : Nat) → λ (x₁₇ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₆) → (x₁₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₆} x₁₈ x₁₇} {m₁} (Nat:le:refl {m₁})} {Nat:le:below:refl {m₁} {λ (k₁₆ : Nat) → λ (x₁₇ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₆) → (x₁₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₆} x₁₈ x₁₇}} {λ (below₁₆ : Nat:le:below {m₁} {λ (k₁₆ : Nat) → λ (x₁₇ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₆) → (x₁₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₆} x₁₈ x₁₇} {m₁} (Nat:le:refl {m₁})) → motive₃ m₁ x₅ (Nat:le:refl {m₁}) below₁₆} (h1₈ x₅) {below₁₄} (Eq:symm {Nat:le:below {m₁} {λ (k₁₆ : Nat) → λ (x₁₇ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₆) → (x₁₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₆} x₁₈ x₁₇} {m₁} (Nat:le:refl {m₁})} {below₁₄} {Nat:le:below:refl {m₁} {λ (k₁₆ : Nat) → λ (x₁₇ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₆) → (x₁₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₆} x₁₈ x₁₇}} (eq~uof~uheq {Nat:le:below {m₁} {λ (k₁₆ : Nat) → λ (x₁₇ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₆) → (x₁₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₆} x₁₈ x₁₇} {m₁} (Nat:le:refl {m₁})} {below₁₄} {Nat:le:below:refl {m₁} {λ (k₁₆ : Nat) → λ (x₁₇ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₆) → (x₁₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₆} x₁₈ x₁₇}} h₁₅))) {x₁₁} (Eq:symm {LE:le {Nat} ⦃ instLENat ⦄ m₁ m₁} {x₁₁} {Nat:le:refl {m₁}} (eq~uof~uheq {LE:le {Nat} ⦃ instLENat ⦄ m₁ m₁} {x₁₁} {Nat:le:refl {m₁}} h₁₃)) below₁₂) {k₄} (Eq:symm {Nat} {k₄} {m₁} h₁₀) x₆ below₇) (λ {m₁₀ : Nat} → λ (a₁₁ : Nat:le m₁ m₁₀) → λ (ih₁₂ : Nat:le:below {m₁} {λ (k₁₂ : Nat) → λ (x₁₃ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₂) → (x₁₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₂} x₁₄ x₁₃} {m₁₀} a₁₁) → λ (aih₁₃ : (x₁₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {m₁₀} x₁₃ a₁₁) → λ (h₁₄ : Eq {Nat} k₄ (Nat:succ m₁₀)) → Eq:ndrec {Nat} {Nat:succ m₁₀} {λ (k₁₅ : Nat) → (x₁₆ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₅) → (below₁₇ : Nat:le:below {m₁} {λ (k₁₇ : Nat) → λ (x₁₈ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₇) → (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₇} x₁₉ x₁₈} {k₁₅} x₁₆) → HEq {LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₅} x₁₆ {Nat:le m₁ (Nat:succ m₁₀)} (Nat:le:step {m₁} {m₁₀} a₁₁) → HEq {Nat:le:below {m₁} {λ (k₁₈ : Nat) → λ (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₈) → (x₂₀ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₈} x₂₀ x₁₉} {k₁₅} x₁₆} below₁₇ {Nat:le:below {m₁} {λ (k₁₈ : Nat) → λ (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₈) → (x₂₀ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₈} x₂₀ x₁₉} {Nat:succ m₁₀} (Nat:le:step {m₁} {m₁₀} a₁₁)} (Nat:le:below:step {m₁} {λ (k₁₈ : Nat) → λ (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₈) → (x₂₀ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₈} x₂₀ x₁₉} {m₁₀} a₁₁ ih₁₂ aih₁₃) → motive₃ k₁₅ x₅ x₁₆ below₁₇} (λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ m₁₀)) → λ (below₁₆ : Nat:le:below {m₁} {λ (k₁₆ : Nat) → λ (x₁₇ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₆) → (x₁₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₆} x₁₈ x₁₇} {Nat:succ m₁₀} x₁₅) → λ (h₁₇ : HEq {LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ m₁₀)} x₁₅ {Nat:le m₁ (Nat:succ m₁₀)} (Nat:le:step {m₁} {m₁₀} a₁₁)) → Eq:ndrec {LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ m₁₀)} {Nat:le:step {m₁} {m₁₀} a₁₁} {λ (x₁₈ : LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ m₁₀)) → (below₁₉ : Nat:le:below {m₁} {λ (k₁₉ : Nat) → λ (x₂₀ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₉) → (x₂₁ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₉} x₂₁ x₂₀} {Nat:succ m₁₀} x₁₈) → HEq {Nat:le:below {m₁} {λ (k₂₀ : Nat) → λ (x₂₁ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₂₀) → (x₂₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₂₀} x₂₂ x₂₁} {Nat:succ m₁₀} x₁₈} below₁₉ {Nat:le:below {m₁} {λ (k₂₀ : Nat) → λ (x₂₁ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₂₀) → (x₂₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₂₀} x₂₂ x₂₁} {Nat:succ m₁₀} (Nat:le:step {m₁} {m₁₀} a₁₁)} (Nat:le:below:step {m₁} {λ (k₂₀ : Nat) → λ (x₂₁ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₂₀) → (x₂₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₂₀} x₂₂ x₂₁} {m₁₀} a₁₁ ih₁₂ aih₁₃) → motive₃ (Nat:succ m₁₀) x₅ x₁₈ below₁₉} (λ (below₁₈ : Nat:le:below {m₁} {λ (k₁₈ : Nat) → λ (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₈) → (x₂₀ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₈} x₂₀ x₁₉} {Nat:succ m₁₀} (Nat:le:step {m₁} {m₁₀} a₁₁)) → λ (h₁₉ : HEq {Nat:le:below {m₁} {λ (k₁₉ : Nat) → λ (x₂₀ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₉) → (x₂₁ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₉} x₂₁ x₂₀} {Nat:succ m₁₀} (Nat:le:step {m₁} {m₁₀} a₁₁)} below₁₈ {Nat:le:below {m₁} {λ (k₁₉ : Nat) → λ (x₂₀ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₉) → (x₂₁ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₉} x₂₁ x₂₀} {Nat:succ m₁₀} (Nat:le:step {m₁} {m₁₀} a₁₁)} (Nat:le:below:step {m₁} {λ (k₁₉ : Nat) → λ (x₂₀ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₉) → (x₂₁ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₉} x₂₁ x₂₀} {m₁₀} a₁₁ ih₁₂ aih₁₃)) → Eq:ndrec {Nat:le:below {m₁} {λ (k₂₀ : Nat) → λ (x₂₁ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₂₀) → (x₂₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₂₀} x₂₂ x₂₁} {Nat:succ m₁₀} (Nat:le:step {m₁} {m₁₀} a₁₁)} {Nat:le:below:step {m₁} {λ (k₂₀ : Nat) → λ (x₂₁ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₂₀) → (x₂₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₂₀} x₂₂ x₂₁} {m₁₀} a₁₁ ih₁₂ aih₁₃} {λ (below₂₀ : Nat:le:below {m₁} {λ (k₂₀ : Nat) → λ (x₂₁ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₂₀) → (x₂₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₂₀} x₂₂ x₂₁} {Nat:succ m₁₀} (Nat:le:step {m₁} {m₁₀} a₁₁)) → motive₃ (Nat:succ m₁₀) x₅ (Nat:le:step {m₁} {m₁₀} a₁₁) below₂₀} (h2₉ x₅ m₁₀ a₁₁ ih₁₂ aih₁₃) {below₁₈} (Eq:symm {Nat:le:below {m₁} {λ (k₂₀ : Nat) → λ (x₂₁ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₂₀) → (x₂₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₂₀} x₂₂ x₂₁} {Nat:succ m₁₀} (Nat:le:step {m₁} {m₁₀} a₁₁)} {below₁₈} {Nat:le:below:step {m₁} {λ (k₂₀ : Nat) → λ (x₂₁ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₂₀) → (x₂₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₂₀} x₂₂ x₂₁} {m₁₀} a₁₁ ih₁₂ aih₁₃} (eq~uof~uheq {Nat:le:below {m₁} {λ (k₂₀ : Nat) → λ (x₂₁ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₂₀) → (x₂₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₂₀} x₂₂ x₂₁} {Nat:succ m₁₀} (Nat:le:step {m₁} {m₁₀} a₁₁)} {below₁₈} {Nat:le:below:step {m₁} {λ (k₂₀ : Nat) → λ (x₂₁ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₂₀) → (x₂₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₂₀} x₂₂ x₂₁} {m₁₀} a₁₁ ih₁₂ aih₁₃} h₁₉))) {x₁₅} (Eq:symm {LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ m₁₀)} {x₁₅} {Nat:le:step {m₁} {m₁₀} a₁₁} (eq~uof~uheq {LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ m₁₀)} {x₁₅} {Nat:le:step {m₁} {m₁₀} a₁₁} h₁₇)) below₁₆) {k₄} (Eq:symm {Nat} {k₄} {Nat:succ m₁₀} h₁₄) x₆ below₇) (Eq:refl {Nat} k₄) (HEq:refl {LE:le {Nat} ⦃ instLENat ⦄ m₁ k₄} x₆) (HEq:refl {Nat:le:below {m₁} {λ (k₁₀ : Nat) → λ (x₁₁ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₀) → (x₁₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₀} x₁₂ x₁₁} {k₄} x₆} below₇)

-- theorem
opaque
  Nat:le~utrans : {n₀ : Nat} → {m₁ : Nat} → {k₂ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → LE:le {Nat} ⦃ instLENat ⦄ m₁ k₂ → LE:le {Nat} ⦃ instLENat ⦄ n₀ k₂
  Nat:le~utrans {n₀} {m₁} {k₂} x₃ x₄ = let funType1₅ : {k₅ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → LE:le {Nat} ⦃ instLENat ⦄ m₁ k₅ → Set; funType1₅ = λ {k₅ : Nat} → λ (x₆ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → λ (x₇ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₅) → LE:le {Nat} ⦃ instLENat ⦄ n₀ k₅ in Nat:le:brecOn {m₁} {λ (k₆ : Nat) → λ (x₇ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₆) → (x₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₅ {k₆} x₈ x₇} {k₂} x₄ (λ (k₆ : Nat) → λ (x₇ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₆) → λ (x₈ : Nat:le:below {m₁} {λ (k₈ : Nat) → λ (x₉ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₈) → (x₁₀ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₅ {k₈} x₁₀ x₉} {k₆} x₇) → λ (x₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → ~uprivate:Init:Prelude:~n0:Nat:le~utrans:match~u1~u10 {n₀} {m₁} funType1₅ (λ (k₁₀ : Nat) → λ (x₁₁ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → λ (x₁₂ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₀) → λ (below₁₃ : Nat:le:below {m₁} {λ (k₁₃ : Nat) → λ (x₁₄ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₃) → (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₅ {k₁₃} x₁₅ x₁₄} {k₁₀} x₁₂) → LE:le {Nat} ⦃ instLENat ⦄ n₀ k₁₀) k₆ x₉ x₇ x₈ (λ (h₁₀ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → h₁₀) (λ (h₁₀ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → λ (m₁₁ : Nat) → λ (h₁₂ : Nat:le m₁ m₁₁) → λ (ih₁₃ : Nat:le:below {m₁} {λ (k₁₃ : Nat) → λ (x₁₄ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₃) → (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₅ {k₁₃} x₁₅ x₁₄} {m₁₁} h₁₂) → λ (aih₁₄ : (x₁₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₅ {m₁₁} x₁₄ h₁₂) → Nat:le:step {n₀} {m₁₁} (aih₁₄ h₁₀))) x₃

-- theorem
opaque
  Nat:lt~uof~ult~uof~ule : {n₀ : Nat} → {m₁ : Nat} → {k₂ : Nat} → LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁ → LE:le {Nat} ⦃ instLENat ⦄ m₁ k₂ → LT:lt {Nat} ⦃ instLTNat ⦄ n₀ k₂
  Nat:lt~uof~ult~uof~ule {n₀} {m₁} {k₂} = Nat:le~utrans {Nat:succ n₀} {m₁} {k₂}

-- theorem
opaque
  Nat:le~usucc : (n₀ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ n₀)
  Nat:le~usucc n₀ = Nat:le:step {n₀} {n₀} (Nat:le:refl {n₀})

Nat:pow:match~u1 : (motive₀ : Nat → Set) → (x₁ : Nat) → (Unit → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ x₁
Nat:pow:match~u1 motive₀ x₁ h1₂ h2₃ = Nat:casesOn {λ (x₄ : Nat) → motive₀ x₄} x₁ (h1₂ Unit:unit) (λ (n₄ : Nat) → h2₃ n₄)

Nat:pred : Nat → Nat
Nat:pred x₀ = Nat:pow:match~u1 (λ (x₁ : Nat) → Nat) x₀ (λ (x₁ : Unit) → OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (λ (a₁ : Nat) → a₁)

~uprivate:Init:Prelude:~n0:Nat:pred~ule~upred:match~u1~u1 : (motive₀ : (x₀ : Nat) → (x₁ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ x₀ x₁ → Set) → (x₁ : Nat) → (x₂ : Nat) → (x₃ : LE:le {Nat} ⦃ instLENat ⦄ x₁ x₂) → ((n₄ : Nat) → motive₀ n₄ n₄ (Nat:le:refl {n₄})) → ((n₄ : Nat) → (h₅ : Nat:le (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) n₄) → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₄) (Nat:le:step {OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄} {n₄} h₅)) → ((n₄ : Nat) → (n₅ : Nat) → (h₆ : Nat:le (Nat:succ n₄) n₅) → motive₀ (Nat:succ n₄) (Nat:succ n₅) (Nat:le:step {Nat:succ n₄} {n₅} h₆)) → motive₀ x₁ x₂ x₃
~uprivate:Init:Prelude:~n0:Nat:pred~ule~upred:match~u1~u1 motive₀ x₁ x₂ x₃ h1₄ h2₅ h3₆ = Nat:le:casesOn {x₁} {λ (a₇ : Nat) → λ (x₈ : Nat:le x₁ a₇) → Eq {Nat} x₂ a₇ → HEq {LE:le {Nat} ⦃ instLENat ⦄ x₁ x₂} x₃ {Nat:le x₁ a₇} x₈ → motive₀ x₁ x₂ x₃} {x₂} x₃ (λ (h₇ : Eq {Nat} x₂ x₁) → Eq:ndrec {Nat} {x₁} {λ (x₈ : Nat) → (x₉ : LE:le {Nat} ⦃ instLENat ⦄ x₁ x₈) → HEq {LE:le {Nat} ⦃ instLENat ⦄ x₁ x₈} x₉ {Nat:le x₁ x₁} (Nat:le:refl {x₁}) → motive₀ x₁ x₈ x₉} (λ (x₈ : LE:le {Nat} ⦃ instLENat ⦄ x₁ x₁) → λ (h₉ : HEq {LE:le {Nat} ⦃ instLENat ⦄ x₁ x₁} x₈ {Nat:le x₁ x₁} (Nat:le:refl {x₁})) → Eq:ndrec {LE:le {Nat} ⦃ instLENat ⦄ x₁ x₁} {Nat:le:refl {x₁}} {λ (x₁₀ : LE:le {Nat} ⦃ instLENat ⦄ x₁ x₁) → motive₀ x₁ x₁ x₁₀} (h1₄ x₁) {x₈} (Eq:symm {LE:le {Nat} ⦃ instLENat ⦄ x₁ x₁} {x₈} {Nat:le:refl {x₁}} (eq~uof~uheq {LE:le {Nat} ⦃ instLENat ⦄ x₁ x₁} {x₈} {Nat:le:refl {x₁}} h₉))) {x₂} (Eq:symm {Nat} {x₂} {x₁} h₇) x₃) (λ {m₇ : Nat} → λ (a₈ : Nat:le x₁ m₇) → λ (h₉ : Eq {Nat} x₂ (Nat:succ m₇)) → Eq:ndrec {Nat} {Nat:succ m₇} {λ (x₁₀ : Nat) → (x₁₁ : LE:le {Nat} ⦃ instLENat ⦄ x₁ x₁₀) → HEq {LE:le {Nat} ⦃ instLENat ⦄ x₁ x₁₀} x₁₁ {Nat:le x₁ (Nat:succ m₇)} (Nat:le:step {x₁} {m₇} a₈) → motive₀ x₁ x₁₀ x₁₁} (λ (x₁₀ : LE:le {Nat} ⦃ instLENat ⦄ x₁ (Nat:succ m₇)) → λ (h₁₁ : HEq {LE:le {Nat} ⦃ instLENat ⦄ x₁ (Nat:succ m₇)} x₁₀ {Nat:le x₁ (Nat:succ m₇)} (Nat:le:step {x₁} {m₇} a₈)) → Eq:ndrec {LE:le {Nat} ⦃ instLENat ⦄ x₁ (Nat:succ m₇)} {Nat:le:step {x₁} {m₇} a₈} {λ (x₁₂ : LE:le {Nat} ⦃ instLENat ⦄ x₁ (Nat:succ m₇)) → motive₀ x₁ (Nat:succ m₇) x₁₂} (Nat:casesOn {λ (x₁₂ : Nat) → (a₁₃ : Nat:le x₁₂ m₇) → motive₀ x₁₂ (Nat:succ m₇) (Nat:le:step {x₁₂} {m₇} a₁₃)} x₁ (λ (a₁₂ : Nat:le Nat:zero m₇) → h2₅ m₇ a₁₂) (λ (n₁₂ : Nat) → λ (a₁₃ : Nat:le (Nat:succ n₁₂) m₇) → h3₆ n₁₂ m₇ a₁₃) a₈) {x₁₀} (Eq:symm {LE:le {Nat} ⦃ instLENat ⦄ x₁ (Nat:succ m₇)} {x₁₀} {Nat:le:step {x₁} {m₇} a₈} (eq~uof~uheq {LE:le {Nat} ⦃ instLENat ⦄ x₁ (Nat:succ m₇)} {x₁₀} {Nat:le:step {x₁} {m₇} a₈} h₁₁))) {x₂} (Eq:symm {Nat} {x₂} {Nat:succ m₇} h₉) x₃) (Eq:refl {Nat} x₂) (HEq:refl {LE:le {Nat} ⦃ instLENat ⦄ x₁ x₂} x₃)

-- theorem
opaque
  Nat:pred~ule~upred : {n₀ : Nat} → {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → LE:le {Nat} ⦃ instLENat ⦄ (Nat:pred n₀) (Nat:pred m₁)
  Nat:pred~ule~upred {x₀} {x₁} x₂ = ~uprivate:Init:Prelude:~n0:Nat:pred~ule~upred:match~u1~u1 (λ (x₃ : Nat) → λ (x₄ : Nat) → λ (x₅ : LE:le {Nat} ⦃ instLENat ⦄ x₃ x₄) → LE:le {Nat} ⦃ instLENat ⦄ (Nat:pred x₃) (Nat:pred x₄)) x₀ x₁ x₂ (λ (n₃ : Nat) → Nat:le:refl {Nat:pred n₃}) (λ (n₃ : Nat) → λ (h₄ : Nat:le (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) n₃) → h₄) (λ (n₃ : Nat) → λ (n₄ : Nat) → λ (h₅ : Nat:le (Nat:succ n₃) n₄) → Nat:le~utrans {Nat:pred (Nat:succ n₃)} {Nat:succ (Nat:pred (Nat:succ n₃))} {Nat:pred (Nat:succ n₄)} (Nat:le~usucc (Nat:pred (Nat:succ n₃))) h₅)

-- theorem
opaque
  Nat:le~uof~usucc~ule~usucc : {n₀ : Nat} → {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₀) (Nat:succ m₁) → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁
  Nat:le~uof~usucc~ule~usucc {n₀} {m₁} = Nat:pred~ule~upred {Nat:succ n₀} {Nat:succ m₁}

Nat:noConfusionType : Set → Nat → Nat → Set
Nat:noConfusionType P₀ t₁ t₂ = Nat:casesOn {λ (t₃ : Nat) → Set} t₁ (Nat:casesOn {λ (t₃ : Nat) → Set} t₂ (P₀ → P₀) (λ (n₃ : Nat) → P₀)) (λ (n₃ : Nat) → Nat:casesOn {λ (t₄ : Nat) → Set} t₂ P₀ (λ (n₄ : Nat) → (Eq {Nat} n₃ n₄ → P₀) → P₀))

Nat:noConfusion : {P₀ : Set} → {t₁ : Nat} → {t₂ : Nat} → Eq {Nat} t₁ t₂ → Nat:noConfusionType P₀ t₁ t₂
Nat:noConfusion {P₀} {t₁} {t₂} eq₃ = Eq:ndrec {Nat} {t₁} {λ (t₄ : Nat) → Nat:noConfusionType P₀ t₁ t₄} (Nat:casesOn {λ (t₄ : Nat) → Nat:noConfusionType P₀ t₄ t₄} t₁ (λ (k₄ : P₀) → k₄) (λ (n₄ : Nat) → λ (k₅ : Eq {Nat} n₄ n₄ → P₀) → k₅ (Eq:refl {Nat} n₄))) {t₂} eq₃

-- theorem
opaque
  Nat:not~usucc~ule~uzero : (n₀ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₀) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) → False
  Nat:not~usucc~ule~uzero n₀ = let this₁ : (m₁ : Nat) → Eq {Nat} m₁ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) → LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₀) m₁ → False; this₁ = λ (x₁ : Nat) → λ (hm₂ : Eq {Nat} x₁ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → λ (hle₃ : LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₀) x₁) → Nat:le:casesOn {Nat:succ n₀} {λ (m₄ : Nat) → λ (x₅ : Nat:le (Nat:succ n₀) m₄) → Eq {Nat} m₄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) → False} {x₁} hle₃ (λ (h₄ : Eq {Nat} (Nat:succ n₀) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → Nat:noConfusion {False} {Nat:succ n₀} {OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄} h₄) (λ {m₄ : Nat} → λ (x₅ : Nat:le (Nat:succ n₀) m₄) → λ (h₆ : Eq {Nat} (Nat:succ m₄) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → Nat:noConfusion {False} {Nat:succ m₄} {OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄} h₆) hm₂ in this₁ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (rfl {Nat} {OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄})

~uprivate:Init:Prelude:~n0:Nat:not~usucc~ule~uself:match~u1~u1 : (motive₀ : Nat → Set) → (x₁ : Nat) → (Unit → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ x₁
~uprivate:Init:Prelude:~n0:Nat:not~usucc~ule~uself:match~u1~u1 motive₀ x₁ h1₂ h2₃ = Nat:casesOn {λ (x₄ : Nat) → motive₀ x₄} x₁ (h1₂ Unit:unit) (λ (n₄ : Nat) → h2₃ n₄)

Nat:not~usucc~ule~uself:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Not (LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ x₁) x₁)} x₀ → Not (LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ x₀) x₀)
Nat:not~usucc~ule~uself:~uf x₀ f₁ = ~uprivate:Init:Prelude:~n0:Nat:not~usucc~ule~uself:match~u1~u1 (λ (x₂ : Nat) → Nat:below {λ (x₃ : Nat) → Not (LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ x₃) x₃)} x₂ → Not (LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ x₂) x₂)) x₀ (λ (x₂ : Unit) → λ (x₃ : Nat:below {λ (x₃ : Nat) → Not (LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ x₃) x₃)} (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → Nat:not~usucc~ule~uzero (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) (λ (n₂ : Nat) → λ (x₃ : Nat:below {λ (x₃ : Nat) → Not (LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ x₃) x₃)} (Nat:succ n₂)) → λ (h₄ : LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ (Nat:succ n₂)) (Nat:succ n₂)) → absurd {LE:le {Nat} ⦃ instLENat ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₂ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) n₂} {False} (Nat:le~uof~usucc~ule~usucc {HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₂ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)} {n₂} h₄) (PProd.fst₂ {(λ (x₅ : Nat) → Not (LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ x₅) x₅)) n₂} {Nat:rec {λ (t₅ : Nat) → Set} PUnit (λ (n₅ : Nat) → λ (nih₆ : Set) → PProd ((λ (x₇ : Nat) → Not (LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ x₇) x₇)) n₅) nih₆) n₂} x₃)) f₁

-- theorem
opaque
  Nat:not~usucc~ule~uself : (n₀ : Nat) → Not (LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₀) n₀)
  Nat:not~usucc~ule~uself x₀ = Nat:brecOn {λ (x₁ : Nat) → Not (LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ x₁) x₁)} x₀ Nat:not~usucc~ule~uself:~uf

-- theorem
opaque
  Nat:lt~uirrefl : (n₀ : Nat) → Not (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ n₀)
  Nat:lt~uirrefl n₀ = Nat:not~usucc~ule~uself n₀

-- theorem
opaque
  Nat:lt~usucc~uof~ule : {n₀ : Nat} → {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → LT:lt {Nat} ⦃ instLTNat ⦄ n₀ (Nat:succ m₁)
  Nat:lt~usucc~uof~ule {n₀} {m₁} = Nat:succ~ule~usucc {n₀} {m₁}

~uprivate:Init:Prelude:~n0:Nat:pred~ule:match~u1~u1 : (motive₀ : Nat → Set) → (x₁ : Nat) → (Unit → motive₀ Nat:zero) → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ x₁
~uprivate:Init:Prelude:~n0:Nat:pred~ule:match~u1~u1 motive₀ x₁ h1₂ h2₃ = Nat:casesOn {λ (x₄ : Nat) → motive₀ x₄} x₁ (h1₂ Unit:unit) (λ (n₄ : Nat) → h2₃ n₄)

-- theorem
opaque
  Nat:pred~ule : (n₀ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ (Nat:pred n₀) n₀
  Nat:pred~ule x₀ = ~uprivate:Init:Prelude:~n0:Nat:pred~ule:match~u1~u1 (λ (x₁ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ (Nat:pred x₁) x₁) x₀ (λ (x₁ : Unit) → Nat:le:refl {Nat:pred Nat:zero}) (λ (n₁ : Nat) → Nat:le~usucc (Nat:pred (Nat:succ n₁)))

Nat:mul:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → ((x₃ : Nat) → motive₀ x₃ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → ((a₃ : Nat) → (b₄ : Nat) → motive₀ a₃ (Nat:succ b₄)) → motive₀ x₁ x₂
Nat:mul:match~u1 motive₀ x₁ x₂ h1₃ h2₄ = Nat:casesOn {λ (x₅ : Nat) → motive₀ x₁ x₅} x₂ (h1₃ x₁) (λ (n₅ : Nat) → h2₄ x₁ n₅)

Nat:sub:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Nat → Nat} x₀ → Nat → Nat
Nat:sub:~uf x₀ f₁ x₂ = Nat:mul:match~u1 (λ (x₃ : Nat) → λ (x₄ : Nat) → Nat:below {λ (x₅ : Nat) → Nat → Nat} x₄ → Nat) x₂ x₀ (λ (a₃ : Nat) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Nat} (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → a₃) (λ (a₃ : Nat) → λ (b₄ : Nat) → λ (x₅ : Nat:below {λ (x₅ : Nat) → Nat → Nat} (Nat:succ b₄)) → Nat:pred (PProd.fst₂ {(λ (x₆ : Nat) → Nat → Nat) b₄} {Nat:rec {λ (t₆ : Nat) → Set} PUnit (λ (n₆ : Nat) → λ (nih₇ : Set) → PProd ((λ (x₈ : Nat) → Nat → Nat) n₆) nih₇) b₄} x₅ a₃)) f₁

Nat:sub : Nat → Nat → Nat
Nat:sub x₀ x₁ = Nat:brecOn {λ (x₂ : Nat) → Nat → Nat} x₁ Nat:sub:~uf x₀

record Sub (α₀ : Set) : Set where
  constructor Sub:mk
  field
    sub₁ : α₀ → α₀ → α₀

-- recursor
Sub:rec : {α₀ : Set} → {motive₁ : Sub α₀ → Set} → ((sub₂ : α₀ → α₀ → α₀) → motive₁ (Sub:mk {α₀} sub₂)) → (t₂ : Sub α₀) → motive₁ t₂
Sub:rec {α₀} {motive₁} mk₂ (Sub:mk sub₃) = mk₂ sub₃

Sub:sub : {α₀ : Set} → ⦃ _ : Sub α₀ ⦄ → α₀ → α₀ → α₀
Sub:sub {α₀} ⦃ self₁ ⦄ = Sub.sub₁ {α₀} self₁

instHSub : {α₀ : Set} → ⦃ _ : Sub α₀ ⦄ → HSub α₀ α₀ α₀
instHSub {α₀} ⦃ inst₁ ⦄ = HSub:mk {α₀} {α₀} {α₀} (λ (a₂ : α₀) → λ (b₃ : α₀) → Sub:sub {α₀} ⦃ inst₁ ⦄ a₂ b₃)

instSubNat : Sub Nat
instSubNat = Sub:mk {Nat} Nat:sub

-- theorem
opaque
  Nat:sub~ule : (n₀ : Nat) → (m₁ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ n₀ m₁) n₀
  Nat:sub~ule n₀ m₁ = Nat:rec {λ (x₂ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ n₀ x₂) n₀} (Nat:le~urefl (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ n₀ Nat:zero)) (λ (x₂ : Nat) → λ (ih₃ : LE:le {Nat} ⦃ instLENat ⦄ (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ n₀ x₂) n₀) → Nat:le~utrans {HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ n₀ (Nat:succ x₂)} {Nat:sub n₀ x₂} {n₀} (Nat:pred~ule (Nat:sub n₀ x₂)) ih₃) m₁

-- theorem
opaque
  Nat:succ~usub~usucc~ueq~usub : (n₀ : Nat) → (m₁ : Nat) → Eq {Nat} (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ (Nat:succ n₀) (Nat:succ m₁)) (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ n₀ m₁)
  Nat:succ~usub~usucc~ueq~usub n₀ m₁ = Nat:rec {λ (x₂ : Nat) → Eq {Nat} (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ (Nat:succ n₀) (Nat:succ x₂)) (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ n₀ x₂)} (rfl {Nat} {HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ (Nat:succ n₀) (Nat:succ Nat:zero)}) (λ (x₂ : Nat) → λ (ih₃ : Eq {Nat} (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ (Nat:succ n₀) (Nat:succ x₂)) (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ n₀ x₂)) → congrArg {Nat} {Nat} {Nat:sub (Nat:succ n₀) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ x₂ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} {Nat:sub n₀ x₂} Nat:pred ih₃) m₁

~uprivate:Init:Prelude:~n0:Nat:sub~ult:match~u1~u1:~ushare:~n1 : Set
~uprivate:Init:Prelude:~n0:Nat:sub~ult:match~u1~u1:~ushare:~n1 = (x₀ : Nat) → (x₁ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₀ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₁ → Set

~uprivate:Init:Prelude:~n0:Nat:sub~ult:match~u1~u1 : (motive₀ : ~uprivate:Init:Prelude:~n0:Nat:sub~ult:match~u1~u1:~ushare:~n1) → (x₁ : Nat) → (x₂ : Nat) → (x₃ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₁) → (x₄ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₂) → ((x₅ : Nat) → (h1₆ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → (x₇ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₅) → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₅ h1₆ x₇) → ((n₅ : Nat) → (x₆ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₅)) → (h2₇ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → motive₀ (Nat:succ n₅) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₆ h2₇) → ((n₅ : Nat) → (m₆ : Nat) → (x₇ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₅)) → (x₈ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ m₆)) → motive₀ (Nat:succ n₅) (Nat:succ m₆) x₇ x₈) → motive₀ x₁ x₂ x₃ x₄
~uprivate:Init:Prelude:~n0:Nat:sub~ult:match~u1~u1 motive₀ x₁ x₂ x₃ x₄ h1₅ h2₆ h3₇ = Nat:casesOn {λ (x₈ : Nat) → (x₉ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₈) → motive₀ x₈ x₂ x₉ x₄} x₁ (λ (x₈ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) Nat:zero) → h1₅ x₂ x₈ x₄) (λ (n₈ : Nat) → λ (x₉ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₈)) → Nat:casesOn {λ (x₁₀ : Nat) → (x₁₁ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₁₀) → motive₀ (Nat:succ n₈) x₁₀ x₉ x₁₁} x₂ (λ (x₁₀ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) Nat:zero) → h2₆ n₈ x₉ x₁₀) (λ (n₁₀ : Nat) → λ (x₁₁ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₁₀)) → h3₇ n₈ n₁₀ x₉ x₁₁) x₄) x₃

-- theorem
opaque
  Nat:sub~ult : {n₀ : Nat} → {m₁ : Nat} → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) n₀ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) m₁ → LT:lt {Nat} ⦃ instLTNat ⦄ (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ n₀ m₁) n₀
  Nat:sub~ult {x₀} {x₁} x₂ x₃ = ~uprivate:Init:Prelude:~n0:Nat:sub~ult:match~u1~u1 (λ (x₄ : Nat) → λ (x₅ : Nat) → λ (x₆ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₄) → λ (x₇ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₅) → LT:lt {Nat} ⦃ instLTNat ⦄ (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ x₄ x₅) x₄) x₀ x₁ x₂ x₃ (λ (x₄ : Nat) → λ (h1₅ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → λ (x₆ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₄) → absurd {LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)} {LT:lt {Nat} ⦃ instLTNat ⦄ (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₄) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)} h1₅ (Nat:lt~uirrefl (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄))) (λ (n₄ : Nat) → λ (x₅ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₄)) → λ (h2₆ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → absurd {LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)} {LT:lt {Nat} ⦃ instLTNat ⦄ (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ (Nat:succ n₄) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) (Nat:succ n₄)} h2₆ (Nat:lt~uirrefl (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄))) (λ (n₄ : Nat) → λ (m₅ : Nat) → λ (x₆ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₄)) → λ (x₇ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ m₅)) → Eq:rec {Nat} {HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ n₄ m₅} {λ (x₈ : Nat) → λ (h₉ : Eq {Nat} (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ n₄ m₅) x₈) → LT:lt {Nat} ⦃ instLTNat ⦄ x₈ (Nat:succ n₄)} (let this₈ : LT:lt {Nat} ⦃ instLTNat ⦄ (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ n₄ m₅) (Nat:succ n₄); this₈ = Nat:lt~usucc~uof~ule {HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ n₄ m₅} {n₄} (Nat:sub~ule n₄ m₅) in this₈) {HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ (Nat:succ n₄) (Nat:succ m₅)} (Eq:symm {Nat} {HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ (Nat:succ n₄) (Nat:succ m₅)} {HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ n₄ m₅} (Nat:succ~usub~usucc~ueq~usub n₄ m₅)))

~uprivate:Init:Prelude:~n0:Nat:div~urec~ulemma:match~u1~u1 : {x₀ : Nat} → {y₁ : Nat} → (motive₂ : And (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) (LE:le {Nat} ⦃ instLENat ⦄ y₁ x₀) → Set) → (x₃ : And (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) (LE:le {Nat} ⦃ instLENat ⦄ y₁ x₀)) → ((ypos₄ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) → (ylex₅ : LE:le {Nat} ⦃ instLENat ⦄ y₁ x₀) → motive₂ (And:intro {LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁} {LE:le {Nat} ⦃ instLENat ⦄ y₁ x₀} ypos₄ ylex₅)) → motive₂ x₃
~uprivate:Init:Prelude:~n0:Nat:div~urec~ulemma:match~u1~u1 {x₀} {y₁} motive₂ x₃ h1₄ = And:casesOn {LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁} {LE:le {Nat} ⦃ instLENat ⦄ y₁ x₀} {λ (x₅ : And (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) (LE:le {Nat} ⦃ instLENat ⦄ y₁ x₀)) → motive₂ x₅} x₃ (λ (left₅ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) → λ (right₆ : LE:le {Nat} ⦃ instLENat ⦄ y₁ x₀) → h1₄ left₅ right₆)

-- theorem
opaque
  Nat:div~urec~ulemma : {x₀ : Nat} → {y₁ : Nat} → And (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) (LE:le {Nat} ⦃ instLENat ⦄ y₁ x₀) → LT:lt {Nat} ⦃ instLTNat ⦄ (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ x₀ y₁) x₀
  Nat:div~urec~ulemma {x₀} {y₁} x₂ = ~uprivate:Init:Prelude:~n0:Nat:div~urec~ulemma:match~u1~u1 {x₀} {y₁} (λ (x₃ : And (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) (LE:le {Nat} ⦃ instLENat ⦄ y₁ x₀)) → LT:lt {Nat} ⦃ instLTNat ⦄ (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ x₀ y₁) x₀) x₂ (λ (ypos₃ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) → λ (ylex₄ : LE:le {Nat} ⦃ instLENat ⦄ y₁ x₀) → Nat:sub~ult {x₀} {y₁} (Nat:lt~uof~ult~uof~ule {OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄} {y₁} {x₀} ypos₃ ylex₄) ypos₃)

-- theorem
opaque
  Nat:le~uof~ult~usucc : {m₀ : Nat} → {n₁ : Nat} → LT:lt {Nat} ⦃ instLTNat ⦄ m₀ (Nat:succ n₁) → LE:le {Nat} ⦃ instLENat ⦄ m₀ n₁
  Nat:le~uof~ult~usucc {m₀} {n₁} = Nat:le~uof~usucc~ule~usucc {m₀} {n₁}

-- theorem
opaque
  Nat:div~urec~ufuel~ulemma : {x₀ : Nat} → {y₁ : Nat} → {fuel₂ : Nat} → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁ → LE:le {Nat} ⦃ instLENat ⦄ y₁ x₀ → LT:lt {Nat} ⦃ instLTNat ⦄ x₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ fuel₂ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) → LT:lt {Nat} ⦃ instLTNat ⦄ (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ x₀ y₁) fuel₂
  Nat:div~urec~ufuel~ulemma {x₀} {y₁} {fuel₂} hy₃ hle₄ hfuel₅ = Nat:lt~uof~ult~uof~ule {HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ x₀ y₁} {x₀} {fuel₂} (Nat:div~urec~ulemma {x₀} {y₁} (And:intro {LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁} {LE:le {Nat} ⦃ instLENat ⦄ y₁ x₀} hy₃ hle₄)) (Nat:le~uof~ult~usucc {x₀} {fuel₂} hfuel₅)

Nat:modCore:go:~uf : (y₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀ → (fuel₁ : Nat) → Nat:below {λ (fuel₂ : Nat) → (x₃ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₃ fuel₂ → Nat} fuel₁ → (x₂ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₂ fuel₁ → Nat
Nat:modCore:go:~uf y₀ hy₁ fuel₂ f₃ x₄ hfuel₅ = Nat:div:go:match~u1 x₄ (λ (fuel₆ : Nat) → λ (hfuel₇ : LT:lt {Nat} ⦃ instLTNat ⦄ x₄ fuel₆) → Nat:below {λ (fuel₈ : Nat) → (x₉ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₉ fuel₈ → Nat} fuel₆ → Nat) fuel₂ hfuel₅ (λ (fuel₆ : Nat) → λ (hfuel₇ : LT:lt {Nat} ⦃ instLTNat ⦄ x₄ (Nat:succ fuel₆)) → λ (x₈ : Nat:below {λ (fuel₈ : Nat) → (x₉ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₉ fuel₈ → Nat} (Nat:succ fuel₆)) → dite {Nat} (LE:le {Nat} ⦃ instLENat ⦄ y₀ x₄) ⦃ Nat:decLe y₀ x₄ ⦄ (λ (h₉ : LE:le {Nat} ⦃ instLENat ⦄ y₀ x₄) → PProd.fst₂ {(λ (fuel₁₀ : Nat) → (x₁₁ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₁₁ fuel₁₀ → Nat) fuel₆} {Nat:rec {λ (t₁₀ : Nat) → Set} PUnit (λ (n₁₀ : Nat) → λ (nih₁₁ : Set) → PProd ((λ (fuel₁₂ : Nat) → (x₁₃ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₁₃ fuel₁₂ → Nat) n₁₀) nih₁₁) fuel₆} x₈ (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ x₄ y₀) (Nat:div~urec~ufuel~ulemma {x₄} {y₀} {fuel₆} hy₁ h₉ hfuel₇)) (λ (x₉ : Not (LE:le {Nat} ⦃ instLENat ⦄ y₀ x₄)) → x₄)) f₃

Nat:modCore:go : (y₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀ → (fuel₁ : Nat) → (x₂ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₂ fuel₁ → Nat
Nat:modCore:go y₀ hy₁ fuel₂ x₃ hfuel₄ = Nat:brecOn {λ (fuel₅ : Nat) → (x₆ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₆ fuel₅ → Nat} fuel₂ (Nat:modCore:go:~uf y₀ hy₁) x₃ hfuel₄

Nat:modCore : Nat → Nat → Nat
Nat:modCore x₀ y₁ = dite {Nat} (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) ⦃ Nat:decLt (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁ ⦄ (λ (hy₂ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) → Nat:modCore:go y₁ hy₂ (Nat:succ x₀) x₀ (Nat:lt~usucc~uself x₀)) (λ (x₂ : Not (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁)) → x₀)

ite : {α₀ : Set} → (c₁ : Set) → ⦃ _ : Decidable c₁ ⦄ → α₀ → α₀ → α₀
ite {α₀} c₁ ⦃ h₂ ⦄ t₃ e₄ = Decidable:casesOn {c₁} {λ (x₅ : Decidable c₁) → α₀} h₂ (λ (x₅ : Not c₁) → e₄) (λ (x₅ : c₁) → t₃)

Nat:mod : Nat → Nat → Nat
Nat:mod x₀ x₁ = Nat:mod:match~u1 (λ (x₂ : Nat) → λ (x₃ : Nat) → Nat) x₀ x₁ (λ (x₂ : Nat) → OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (λ (n₂ : Nat) → λ (n₃ : Nat) → λ (h₄ : Eq {Nat} n₂ (Nat:succ n₃)) → λ (m₅ : Nat) → ite {Nat} (LE:le {Nat} ⦃ instLENat ⦄ m₅ n₂) ⦃ Nat:decLe m₅ n₂ ⦄ (Nat:modCore n₂ m₅) n₂)

Nat:instMod : Mod Nat
Nat:instMod = Mod:mk {Nat} Nat:mod

GE:ge : {α₀ : Set} → ⦃ _ : LE α₀ ⦄ → α₀ → α₀ → Set
GE:ge {α₀} ⦃ inst₁ ⦄ a₂ b₃ = LE:le {α₀} ⦃ inst₁ ⦄ b₃ a₂

data Or (a₀ : Set) (b₁ : Set) : Set where
  Or:inl : a₀ → Or a₀ b₁
  Or:inr : b₁ → Or a₀ b₁

-- recursor
Or:rec : {a₀ : Set} → {b₁ : Set} → {motive₂ : Or a₀ b₁ → Set} → ((h₃ : a₀) → motive₂ (Or:inl {a₀} {b₁} h₃)) → ((h₃ : b₁) → motive₂ (Or:inr {a₀} {b₁} h₃)) → (t₃ : Or a₀ b₁) → motive₂ t₃
Or:rec {a₀} {b₁} {motive₂} inl₃ inr₄ (Or:inl h₅) = inl₃ h₅
Or:rec {a₀} {b₁} {motive₂} inl₃ inr₄ (Or:inr h₅) = inr₄ h₅

Or:casesOn : {a₀ : Set} → {b₁ : Set} → {motive₂ : Or a₀ b₁ → Set} → (t₃ : Or a₀ b₁) → ((h₄ : a₀) → motive₂ (Or:inl {a₀} {b₁} h₄)) → ((h₄ : b₁) → motive₂ (Or:inr {a₀} {b₁} h₄)) → motive₂ t₃
Or:casesOn {a₀} {b₁} {motive₂} t₃ inl₄ inr₅ = Or:rec {a₀} {b₁} {motive₂} (λ (h₆ : a₀) → inl₄ h₆) (λ (h₆ : b₁) → inr₅ h₆) t₃

~uprivate:Init:Prelude:~n0:Nat:eq~uor~ult~uof~ule:match~u1~u1 : (n₀ : Nat) → (m₁ : Nat) → (motive₂ : Or (Eq {Nat} n₀ m₁) (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁) → Set) → (x₃ : Or (Eq {Nat} n₀ m₁) (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁)) → ((h₄ : Eq {Nat} n₀ m₁) → motive₂ (Or:inl {Eq {Nat} n₀ m₁} {LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁} h₄)) → ((h₄ : LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁) → motive₂ (Or:inr {Eq {Nat} n₀ m₁} {LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁} h₄)) → motive₂ x₃
~uprivate:Init:Prelude:~n0:Nat:eq~uor~ult~uof~ule:match~u1~u1 n₀ m₁ motive₂ x₃ h1₄ h2₅ = Or:casesOn {Eq {Nat} n₀ m₁} {LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁} {λ (x₆ : Or (Eq {Nat} n₀ m₁) (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁)) → motive₂ x₆} x₃ (λ (h₆ : Eq {Nat} n₀ m₁) → h1₄ h₆) (λ (h₆ : LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁) → h2₅ h₆)

~uprivate:Init:Prelude:~n0:Nat:eq~uor~ult~uof~ule:match~u1~u3 : (motive₀ : (x₀ : Nat) → (x₁ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ x₀ x₁ → Set) → (x₁ : Nat) → (x₂ : Nat) → (x₃ : LE:le {Nat} ⦃ instLENat ⦄ x₁ x₂) → ((x₄ : LE:le {Nat} ⦃ instLENat ⦄ Nat:zero Nat:zero) → motive₀ Nat:zero Nat:zero x₄) → ((n₄ : Nat) → (x₅ : LE:le {Nat} ⦃ instLENat ⦄ Nat:zero (Nat:succ n₄)) → motive₀ Nat:zero (Nat:succ n₄) x₅) → ((n₄ : Nat) → (h₅ : LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₄) Nat:zero) → motive₀ (Nat:succ n₄) Nat:zero h₅) → ((n₄ : Nat) → (m₅ : Nat) → (h₆ : LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₄) (Nat:succ m₅)) → motive₀ (Nat:succ n₄) (Nat:succ m₅) h₆) → motive₀ x₁ x₂ x₃
~uprivate:Init:Prelude:~n0:Nat:eq~uor~ult~uof~ule:match~u1~u3 motive₀ x₁ x₂ x₃ h1₄ h2₅ h3₆ h4₇ = Nat:casesOn {λ (x₈ : Nat) → (x₉ : LE:le {Nat} ⦃ instLENat ⦄ x₈ x₂) → motive₀ x₈ x₂ x₉} x₁ (λ (x₈ : LE:le {Nat} ⦃ instLENat ⦄ Nat:zero x₂) → Nat:casesOn {λ (x₉ : Nat) → (x₁₀ : LE:le {Nat} ⦃ instLENat ⦄ Nat:zero x₉) → motive₀ Nat:zero x₉ x₁₀} x₂ (λ (x₉ : LE:le {Nat} ⦃ instLENat ⦄ Nat:zero Nat:zero) → h1₄ x₉) (λ (n₉ : Nat) → λ (x₁₀ : LE:le {Nat} ⦃ instLENat ⦄ Nat:zero (Nat:succ n₉)) → h2₅ n₉ x₁₀) x₈) (λ (n₈ : Nat) → λ (x₉ : LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₈) x₂) → Nat:casesOn {λ (x₁₀ : Nat) → (x₁₁ : LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₈) x₁₀) → motive₀ (Nat:succ n₈) x₁₀ x₁₁} x₂ (λ (x₁₀ : LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₈) Nat:zero) → h3₆ n₈ x₁₀) (λ (n₁₀ : Nat) → λ (x₁₁ : LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₈) (Nat:succ n₁₀)) → h4₇ n₈ n₁₀ x₁₁) x₉) x₃

Nat:eq~uor~ult~uof~ule:~uf:~ushare:~n1 : Nat → Set
Nat:eq~uor~ult~uof~ule:~uf:~ushare:~n1 = Nat:below {λ (x₀ : Nat) → (x₁ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ x₀ x₁ → Or (Eq {Nat} x₀ x₁) (LT:lt {Nat} ⦃ instLTNat ⦄ x₀ x₁)}

Nat:eq~uor~ult~uof~ule:~uf:~ushare:~n2 : Set
Nat:eq~uor~ult~uof~ule:~uf:~ushare:~n2 = Nat:eq~uor~ult~uof~ule:~uf:~ushare:~n1 Nat:zero

Nat:eq~uor~ult~uof~ule:~uf : (x₀ : Nat) → Nat:eq~uor~ult~uof~ule:~uf:~ushare:~n1 x₀ → (x₁ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ x₀ x₁ → Or (Eq {Nat} x₀ x₁) (LT:lt {Nat} ⦃ instLTNat ⦄ x₀ x₁)
Nat:eq~uor~ult~uof~ule:~uf x₀ f₁ x₂ x₃ = ~uprivate:Init:Prelude:~n0:Nat:eq~uor~ult~uof~ule:match~u1~u3 (λ (x₄ : Nat) → λ (x₅ : Nat) → λ (x₆ : LE:le {Nat} ⦃ instLENat ⦄ x₄ x₅) → Nat:eq~uor~ult~uof~ule:~uf:~ushare:~n1 x₄ → Or (Eq {Nat} x₄ x₅) (LT:lt {Nat} ⦃ instLTNat ⦄ x₄ x₅)) x₀ x₂ x₃ (λ (x₄ : LE:le {Nat} ⦃ instLENat ⦄ Nat:zero Nat:zero) → λ (x₅ : Nat:eq~uor~ult~uof~ule:~uf:~ushare:~n2) → Or:inl {Eq {Nat} Nat:zero Nat:zero} {LT:lt {Nat} ⦃ instLTNat ⦄ Nat:zero Nat:zero} (rfl {Nat} {Nat:zero})) (λ (n₄ : Nat) → λ (x₅ : LE:le {Nat} ⦃ instLENat ⦄ Nat:zero (Nat:succ n₄)) → λ (x₆ : Nat:eq~uor~ult~uof~ule:~uf:~ushare:~n2) → Or:inr {Eq {Nat} Nat:zero (Nat:succ n₄)} {LT:lt {Nat} ⦃ instLTNat ⦄ Nat:zero (Nat:succ n₄)} (Nat:succ~ule~usucc {Nat:zero} {n₄} (Nat:zero~ule n₄))) (λ (n₄ : Nat) → λ (h₅ : LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₄) Nat:zero) → λ (x₆ : Nat:eq~uor~ult~uof~ule:~uf:~ushare:~n1 (Nat:succ n₄)) → absurd {LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₄) Nat:zero} {Or (Eq {Nat} (Nat:succ n₄) Nat:zero) (LT:lt {Nat} ⦃ instLTNat ⦄ (Nat:succ n₄) Nat:zero)} h₅ (Nat:not~usucc~ule~uzero n₄)) (λ (n₄ : Nat) → λ (m₅ : Nat) → λ (h₆ : LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₄) (Nat:succ m₅)) → λ (x₇ : Nat:eq~uor~ult~uof~ule:~uf:~ushare:~n1 (Nat:succ n₄)) → let this₈ : LE:le {Nat} ⦃ instLENat ⦄ n₄ m₅; this₈ = Nat:le~uof~usucc~ule~usucc {n₄} {m₅} h₆ in ~uprivate:Init:Prelude:~n0:Nat:eq~uor~ult~uof~ule:match~u1~u1 n₄ m₅ (λ (x₉ : Or (Eq {Nat} n₄ m₅) (LT:lt {Nat} ⦃ instLTNat ⦄ n₄ m₅)) → Or (Eq {Nat} (Nat:succ n₄) (Nat:succ m₅)) (LT:lt {Nat} ⦃ instLTNat ⦄ (Nat:succ n₄) (Nat:succ m₅))) (PProd.fst₂ {(λ (x₉ : Nat) → (x₁₀ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ x₉ x₁₀ → Or (Eq {Nat} x₉ x₁₀) (LT:lt {Nat} ⦃ instLTNat ⦄ x₉ x₁₀)) n₄} {Nat:rec {λ (t₉ : Nat) → Set} PUnit (λ (n₉ : Nat) → λ (nih₁₀ : Set) → PProd ((λ (x₁₁ : Nat) → (x₁₂ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ x₁₁ x₁₂ → Or (Eq {Nat} x₁₁ x₁₂) (LT:lt {Nat} ⦃ instLTNat ⦄ x₁₁ x₁₂)) n₉) nih₁₀) n₄} x₇ m₅ this₈) (λ (h₉ : Eq {Nat} n₄ m₅) → Or:inl {Eq {Nat} (Nat:succ n₄) (Nat:succ m₅)} {LT:lt {Nat} ⦃ instLTNat ⦄ (Nat:succ n₄) (Nat:succ m₅)} (Eq:rec {Nat} {n₄} {λ (x₁₀ : Nat) → λ (h₁₁ : Eq {Nat} n₄ x₁₀) → Eq {Nat} (Nat:succ n₄) (Nat:succ x₁₀)} (rfl {Nat} {Nat:succ n₄}) {m₅} h₉)) (λ (h₉ : LT:lt {Nat} ⦃ instLTNat ⦄ n₄ m₅) → Or:inr {Eq {Nat} (Nat:succ n₄) (Nat:succ m₅)} {LT:lt {Nat} ⦃ instLTNat ⦄ (Nat:succ n₄) (Nat:succ m₅)} (Nat:succ~ule~usucc {HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)} {m₅} h₉))) f₁

-- theorem
opaque
  Nat:eq~uor~ult~uof~ule : {n₀ : Nat} → {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → Or (Eq {Nat} n₀ m₁) (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁)
  Nat:eq~uor~ult~uof~ule {x₀} {x₁} x₂ = Nat:brecOn {λ (x₃ : Nat) → (x₄ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ x₃ x₄ → Or (Eq {Nat} x₃ x₄) (LT:lt {Nat} ⦃ instLTNat ⦄ x₃ x₄)} x₀ Nat:eq~uor~ult~uof~ule:~uf x₁ x₂

-- theorem
opaque
  Nat:le~usucc~uof~ule : {n₀ : Nat} → {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → LE:le {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₁)
  Nat:le~usucc~uof~ule {n₀} {m₁} h₂ = Nat:le:step {n₀} {m₁} h₂

~uprivate:Init:Prelude:~n0:Nat:lt~uor~uge:match~u1~u1 : (n₀ : Nat) → (m₁ : Nat) → (motive₂ : Or (Eq {Nat} m₁ n₀) (LT:lt {Nat} ⦃ instLTNat ⦄ m₁ n₀) → Set) → (x₃ : Or (Eq {Nat} m₁ n₀) (LT:lt {Nat} ⦃ instLTNat ⦄ m₁ n₀)) → ((h1₄ : Eq {Nat} m₁ n₀) → motive₂ (Or:inl {Eq {Nat} m₁ n₀} {LT:lt {Nat} ⦃ instLTNat ⦄ m₁ n₀} h1₄)) → ((h1₄ : LT:lt {Nat} ⦃ instLTNat ⦄ m₁ n₀) → motive₂ (Or:inr {Eq {Nat} m₁ n₀} {LT:lt {Nat} ⦃ instLTNat ⦄ m₁ n₀} h1₄)) → motive₂ x₃
~uprivate:Init:Prelude:~n0:Nat:lt~uor~uge:match~u1~u1 n₀ m₁ motive₂ x₃ h1₄ h2₅ = Or:casesOn {Eq {Nat} m₁ n₀} {LT:lt {Nat} ⦃ instLTNat ⦄ m₁ n₀} {λ (x₆ : Or (Eq {Nat} m₁ n₀) (LT:lt {Nat} ⦃ instLTNat ⦄ m₁ n₀)) → motive₂ x₆} x₃ (λ (h₆ : Eq {Nat} m₁ n₀) → h1₄ h₆) (λ (h₆ : LT:lt {Nat} ⦃ instLTNat ⦄ m₁ n₀) → h2₅ h₆)

~uprivate:Init:Prelude:~n0:Nat:lt~uor~uge:match~u1~u3 : (n₀ : Nat) → (m₁ : Nat) → (motive₂ : Or (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁) (GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₁) → Set) → (x₃ : Or (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁) (GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₁)) → ((h₄ : LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁) → motive₂ (Or:inl {LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁} {GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₁} h₄)) → ((h₄ : GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₁) → motive₂ (Or:inr {LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁} {GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₁} h₄)) → motive₂ x₃
~uprivate:Init:Prelude:~n0:Nat:lt~uor~uge:match~u1~u3 n₀ m₁ motive₂ x₃ h1₄ h2₅ = Or:casesOn {LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁} {GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₁} {λ (x₆ : Or (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁) (GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₁)) → motive₂ x₆} x₃ (λ (h₆ : LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁) → h1₄ h₆) (λ (h₆ : GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₁) → h2₅ h₆)

~uprivate:Init:Prelude:~n0:Nat:lt~uor~uge:match~u1~u5 : (motive₀ : Nat → Set) → (m₁ : Nat) → (Unit → motive₀ Nat:zero) → ((m₂ : Nat) → motive₀ (Nat:succ m₂)) → motive₀ m₁
~uprivate:Init:Prelude:~n0:Nat:lt~uor~uge:match~u1~u5 motive₀ m₁ h1₂ h2₃ = Nat:casesOn {λ (x₄ : Nat) → motive₀ x₄} m₁ (h1₂ Unit:unit) (λ (n₄ : Nat) → h2₃ n₄)

Nat:lt~uor~uge:~uf : (n₀ : Nat) → (m₁ : Nat) → Nat:below {λ (m₂ : Nat) → Or (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₂) (GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₂)} m₁ → Or (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁) (GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₁)
Nat:lt~uor~uge:~uf n₀ m₁ f₂ = ~uprivate:Init:Prelude:~n0:Nat:lt~uor~uge:match~u1~u5 (λ (m₃ : Nat) → Nat:below {λ (m₄ : Nat) → Or (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₄) (GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₄)} m₃ → Or (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₃) (GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₃)) m₁ (λ (x₃ : Unit) → λ (x₄ : Nat:below {λ (m₄ : Nat) → Or (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₄) (GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₄)} Nat:zero) → Or:inr {LT:lt {Nat} ⦃ instLTNat ⦄ n₀ Nat:zero} {GE:ge {Nat} ⦃ instLENat ⦄ n₀ Nat:zero} (Nat:zero~ule n₀)) (λ (m₃ : Nat) → λ (x₄ : Nat:below {λ (m₄ : Nat) → Or (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₄) (GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₄)} (Nat:succ m₃)) → ~uprivate:Init:Prelude:~n0:Nat:lt~uor~uge:match~u1~u3 n₀ m₃ (λ (x₅ : Or (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₃) (GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₃)) → Or (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ (Nat:succ m₃)) (GE:ge {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₃))) (PProd.fst₂ {(λ (m₅ : Nat) → Or (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₅) (GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₅)) m₃} {Nat:rec {λ (t₅ : Nat) → Set} PUnit (λ (n₅ : Nat) → λ (nih₆ : Set) → PProd ((λ (m₇ : Nat) → Or (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₇) (GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₇)) n₅) nih₆) m₃} x₄) (λ (h₅ : LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₃) → Or:inl {LT:lt {Nat} ⦃ instLTNat ⦄ n₀ (Nat:succ m₃)} {GE:ge {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₃)} (Nat:le~usucc~uof~ule {Nat:succ n₀} {m₃} h₅)) (λ (h₅ : GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₃) → ~uprivate:Init:Prelude:~n0:Nat:lt~uor~uge:match~u1~u1 n₀ m₃ (λ (x₆ : Or (Eq {Nat} m₃ n₀) (LT:lt {Nat} ⦃ instLTNat ⦄ m₃ n₀)) → Or (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ (Nat:succ m₃)) (GE:ge {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₃))) (Nat:eq~uor~ult~uof~ule {m₃} {n₀} h₅) (λ (h1₆ : Eq {Nat} m₃ n₀) → Or:inl {LT:lt {Nat} ⦃ instLTNat ⦄ n₀ (Nat:succ m₃)} {GE:ge {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₃)} (Eq:rec {Nat} {m₃} {λ (x₇ : Nat) → λ (h₈ : Eq {Nat} m₃ x₇) → LT:lt {Nat} ⦃ instLTNat ⦄ x₇ (Nat:succ m₃)} (Nat:le~urefl (Nat:succ m₃)) {n₀} h1₆)) (λ (h1₆ : LT:lt {Nat} ⦃ instLTNat ⦄ m₃ n₀) → Or:inr {LT:lt {Nat} ⦃ instLTNat ⦄ n₀ (Nat:succ m₃)} {GE:ge {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₃)} h1₆))) f₂

-- theorem
opaque
  Nat:lt~uor~uge : (n₀ : Nat) → (m₁ : Nat) → Or (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁) (GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₁)
  Nat:lt~uor~uge n₀ m₁ = Nat:brecOn {λ (m₂ : Nat) → Or (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₂) (GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₂)} m₁ (Nat:lt~uor~uge:~uf n₀)

~uprivate:Init:Prelude:~n0:Or:elim:match~u1~u1 : {a₀ : Set} → {b₁ : Set} → (motive₂ : Or a₀ b₁ → Set) → (h₃ : Or a₀ b₁) → ((h₄ : a₀) → motive₂ (Or:inl {a₀} {b₁} h₄)) → ((h₄ : b₁) → motive₂ (Or:inr {a₀} {b₁} h₄)) → motive₂ h₃
~uprivate:Init:Prelude:~n0:Or:elim:match~u1~u1 {a₀} {b₁} motive₂ h₃ h1₄ h2₅ = Or:casesOn {a₀} {b₁} {λ (x₆ : Or a₀ b₁) → motive₂ x₆} h₃ (λ (h₆ : a₀) → h1₄ h₆) (λ (h₆ : b₁) → h2₅ h₆)

-- theorem
opaque
  Or:elim : {a₀ : Set} → {b₁ : Set} → {c₂ : Set} → Or a₀ b₁ → (a₀ → c₂) → (b₁ → c₂) → c₂
  Or:elim {a₀} {b₁} {c₂} h₃ left₄ right₅ = ~uprivate:Init:Prelude:~n0:Or:elim:match~u1~u1 {a₀} {b₁} (λ (h₆ : Or a₀ b₁) → c₂) h₃ (λ (h₆ : a₀) → left₄ h₆) (λ (h₆ : b₁) → right₅ h₆)

id : {α₀ : Set} → α₀ → α₀
id {α₀} a₁ = a₁

-- theorem
opaque
  Or:resolve~uright : {a₀ : Set} → {b₁ : Set} → Or a₀ b₁ → Not b₁ → a₀
  Or:resolve~uright {a₀} {b₁} h₂ nb₃ = Or:elim {a₀} {b₁} {a₀} h₂ (id {a₀}) (λ (x₄ : b₁) → absurd {b₁} {a₀} x₄ nb₃)

-- theorem
opaque
  Nat:lt~uof~unot~ule : {a₀ : Nat} → {b₁ : Nat} → Not (LE:le {Nat} ⦃ instLENat ⦄ a₀ b₁) → LT:lt {Nat} ⦃ instLTNat ⦄ b₁ a₀
  Nat:lt~uof~unot~ule {a₀} {b₁} h₂ = Or:resolve~uright {LT:lt {Nat} ⦃ instLTNat ⦄ b₁ a₀} {GE:ge {Nat} ⦃ instLENat ⦄ b₁ a₀} (Nat:lt~uor~uge b₁ a₀) h₂

-- theorem
opaque
  Nat:not~ult~uzero : (n₀ : Nat) → Not (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄))
  Nat:not~ult~uzero n₀ = Nat:not~usucc~ule~uzero n₀

~uprivate:Init:Prelude:~n0:Nat:modCoreGo~ult:match~u1~u1 : {y₀ : Nat} → (x₁ : Nat) → (motive₂ : Decidable (LE:le {Nat} ⦃ instLENat ⦄ y₀ x₁) → Set) → (x₃ : Decidable (LE:le {Nat} ⦃ instLENat ⦄ y₀ x₁)) → ((h₄ : LE:le {Nat} ⦃ instLENat ⦄ y₀ x₁) → motive₂ (Decidable:isTrue {LE:le {Nat} ⦃ instLENat ⦄ y₀ x₁} h₄)) → ((h₄ : Not (LE:le {Nat} ⦃ instLENat ⦄ y₀ x₁)) → motive₂ (Decidable:isFalse {LE:le {Nat} ⦃ instLENat ⦄ y₀ x₁} h₄)) → motive₂ x₃
~uprivate:Init:Prelude:~n0:Nat:modCoreGo~ult:match~u1~u1 {y₀} x₁ motive₂ x₃ h1₄ h2₅ = Decidable:casesOn {LE:le {Nat} ⦃ instLENat ⦄ y₀ x₁} {λ (x₆ : Decidable (LE:le {Nat} ⦃ instLENat ⦄ y₀ x₁)) → motive₂ x₆} x₃ (λ (h₆ : Not (LE:le {Nat} ⦃ instLENat ⦄ y₀ x₁)) → h2₅ h₆) (λ (h₆ : LE:le {Nat} ⦃ instLENat ⦄ y₀ x₁) → h1₄ h₆)

-- theorem
opaque
  Nat:modCoreGo~ult : {fuel₀ : Nat} → {y₁ : Nat} → (hy₂ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) → (x₃ : Nat) → (hfuel₄ : LT:lt {Nat} ⦃ instLTNat ⦄ x₃ fuel₀) → LT:lt {Nat} ⦃ instLTNat ⦄ (Nat:modCore:go y₁ hy₂ fuel₀ x₃ hfuel₄) y₁
  Nat:modCoreGo~ult {fuel₀} {y₁} hy₂ = Nat:rec {λ (x₃ : Nat) → (x₄ : Nat) → (hfuel₅ : LT:lt {Nat} ⦃ instLTNat ⦄ x₄ x₃) → LT:lt {Nat} ⦃ instLTNat ⦄ (Nat:modCore:go y₁ hy₂ x₃ x₄ hfuel₅) y₁} (λ (x₃ : Nat) → λ (h₄ : LT:lt {Nat} ⦃ instLTNat ⦄ x₃ Nat:zero) → absurd {LT:lt {Nat} ⦃ instLTNat ⦄ x₃ Nat:zero} {LT:lt {Nat} ⦃ instLTNat ⦄ (Nat:modCore:go y₁ hy₂ Nat:zero x₃ h₄) y₁} h₄ (Nat:not~ult~uzero x₃)) (λ (x₃ : Nat) → λ (ih₄ : (x₄ : Nat) → (hfuel₅ : LT:lt {Nat} ⦃ instLTNat ⦄ x₄ x₃) → LT:lt {Nat} ⦃ instLTNat ⦄ (Nat:modCore:go y₁ hy₂ x₃ x₄ hfuel₅) y₁) → λ (x₅ : Nat) → λ (x₆ : LT:lt {Nat} ⦃ instLTNat ⦄ x₅ (Nat:succ x₃)) → let this₇ : LT:lt {Nat} ⦃ instLTNat ⦄ (dite {Nat} (LE:le {Nat} ⦃ instLENat ⦄ y₁ x₅) ⦃ Nat:decLe y₁ x₅ ⦄ (λ (h₇ : LE:le {Nat} ⦃ instLENat ⦄ y₁ x₅) → Nat:modCore:go y₁ hy₂ x₃ (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ x₅ y₁) (Nat:div~urec~ufuel~ulemma {x₅} {y₁} {x₃} hy₂ h₇ x₆)) (λ (x₇ : Not (LE:le {Nat} ⦃ instLENat ⦄ y₁ x₅)) → x₅)) y₁; this₇ = ~uprivate:Init:Prelude:~n0:Nat:modCoreGo~ult:match~u1~u1 {y₁} x₅ (λ (x₇ : Decidable (LE:le {Nat} ⦃ instLENat ⦄ y₁ x₅)) → LT:lt {Nat} ⦃ instLTNat ⦄ (dite {Nat} (LE:le {Nat} ⦃ instLENat ⦄ y₁ x₅) ⦃ x₇ ⦄ (λ (h₈ : LE:le {Nat} ⦃ instLENat ⦄ y₁ x₅) → Nat:modCore:go y₁ hy₂ x₃ (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ x₅ y₁) (Nat:div~urec~ufuel~ulemma {x₅} {y₁} {x₃} hy₂ h₈ x₆)) (λ (x₈ : Not (LE:le {Nat} ⦃ instLENat ⦄ y₁ x₅)) → x₅)) y₁) (Nat:decLe y₁ x₅) (λ (h₇ : LE:le {Nat} ⦃ instLENat ⦄ y₁ x₅) → ih₄ (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ x₅ y₁) (Nat:div~urec~ufuel~ulemma {x₅} {y₁} {x₃} hy₂ h₇ x₆)) (λ (h₇ : Not (LE:le {Nat} ⦃ instLENat ⦄ y₁ x₅)) → Nat:lt~uof~unot~ule {y₁} {dite {Nat} (LE:le {Nat} ⦃ instLENat ⦄ y₁ x₅) ⦃ Decidable:isFalse {LE:le {Nat} ⦃ instLENat ⦄ y₁ x₅} h₇ ⦄ (λ (h₈ : LE:le {Nat} ⦃ instLENat ⦄ y₁ x₅) → Nat:modCore:go y₁ hy₂ x₃ (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ x₅ y₁) (Nat:div~urec~ufuel~ulemma {x₅} {y₁} {x₃} hy₂ h₈ x₆)) (λ (x₈ : Not (LE:le {Nat} ⦃ instLENat ⦄ y₁ x₅)) → x₅)} h₇) in this₇) fuel₀

~uprivate:Init:Prelude:~n0:Nat:modCore~ult:match~u1~u1 : {y₀ : Nat} → (motive₁ : Decidable (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀) → Set) → (x₂ : Decidable (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀)) → ((h₃ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀) → motive₁ (Decidable:isTrue {LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀} h₃)) → ((h₃ : Not (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀)) → motive₁ (Decidable:isFalse {LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀} h₃)) → motive₁ x₂
~uprivate:Init:Prelude:~n0:Nat:modCore~ult:match~u1~u1 {y₀} motive₁ x₂ h1₃ h2₄ = Decidable:casesOn {LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀} {λ (x₅ : Decidable (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀)) → motive₁ x₅} x₂ (λ (h₅ : Not (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀)) → h2₄ h₅) (λ (h₅ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀) → h1₃ h₅)

-- theorem
opaque
  Nat:modCore~ult : {x₀ : Nat} → {y₁ : Nat} → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁ → LT:lt {Nat} ⦃ instLTNat ⦄ (Nat:modCore x₀ y₁) y₁
  Nat:modCore~ult {x₀} {y₁} hy₂ = let this₃ : LT:lt {Nat} ⦃ instLTNat ⦄ (dite {Nat} (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) ⦃ Nat:decLt (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁ ⦄ (λ (hy₃ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) → Nat:modCore:go y₁ hy₃ (Nat:succ x₀) x₀ (Nat:lt~usucc~uself x₀)) (λ (x₃ : Not (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁)) → x₀)) y₁; this₃ = ~uprivate:Init:Prelude:~n0:Nat:modCore~ult:match~u1~u1 {y₁} (λ (x₃ : Decidable (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁)) → LT:lt {Nat} ⦃ instLTNat ⦄ (dite {Nat} (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) ⦃ x₃ ⦄ (λ (hy₄ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) → Nat:modCore:go y₁ hy₄ (Nat:succ x₀) x₀ (Nat:lt~usucc~uself x₀)) (λ (x₄ : Not (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁)) → x₀)) y₁) (Nat:decLt (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) (λ (h₃ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) → Nat:modCoreGo~ult {Nat:succ x₀} {y₁} hy₂ x₀ (Nat:lt~usucc~uself x₀)) (λ (h₃ : Not (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁)) → absurd {LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁} {LT:lt {Nat} ⦃ instLTNat ⦄ (dite {Nat} (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) ⦃ Decidable:isFalse {LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁} h₃ ⦄ (λ (hy₄ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) → Nat:modCore:go y₁ hy₄ (Nat:succ x₀) x₀ (Nat:lt~usucc~uself x₀)) (λ (x₄ : Not (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁)) → x₀)) y₁} hy₂ h₃) in this₃

-- theorem
opaque
  Nat:zero~ult~usucc : (n₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₀)
  Nat:zero~ult~usucc n₀ = Nat:succ~ule~usucc {OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄} {n₀} (Nat:zero~ule n₀)

~uprivate:Init:Prelude:~n0:Nat:mod~ult:match~u1~u1 : (n₀ : Nat) → (m₁ : Nat) → (motive₂ : Decidable (LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ n₀)) → Set) → (x₃ : Decidable (LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ n₀))) → ((h₄ : LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ n₀)) → motive₂ (Decidable:isTrue {LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ n₀)} h₄)) → ((h₄ : Not (LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ n₀))) → motive₂ (Decidable:isFalse {LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ n₀)} h₄)) → motive₂ x₃
~uprivate:Init:Prelude:~n0:Nat:mod~ult:match~u1~u1 n₀ m₁ motive₂ x₃ h1₄ h2₅ = Decidable:casesOn {LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ n₀)} {λ (x₆ : Decidable (LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ n₀))) → motive₂ x₆} x₃ (λ (h₆ : Not (LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ n₀))) → h2₅ h₆) (λ (h₆ : LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ n₀)) → h1₄ h₆)

~uprivate:Init:Prelude:~n0:Nat:mod~ult:match~u1~u3 : (motive₀ : Nat → (x₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₀ → Set) → (x₁ : Nat) → (x₂ : Nat) → (x₃ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₂) → ((n₄ : Nat) → (x₅ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₄)) → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₄) x₅) → ((n₄ : Nat) → (m₅ : Nat) → (hm₆ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) m₅) → motive₀ (Nat:succ n₄) m₅ hm₆) → motive₀ x₁ x₂ x₃
~uprivate:Init:Prelude:~n0:Nat:mod~ult:match~u1~u3 motive₀ x₁ x₂ x₃ h1₄ h2₅ = Nat:casesOn {λ (x₆ : Nat) → motive₀ x₆ x₂ x₃} x₁ (Nat:casesOn {λ (x₆ : Nat) → (x₇ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₆) → motive₀ Nat:zero x₆ x₇} x₂ (λ (x₆ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) Nat:zero) → False:elim {motive₀ Nat:zero Nat:zero x₆} (Nat:le:casesOn {Nat:succ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)} {λ (a₇ : Nat) → λ (x₈ : Nat:le (Nat:succ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) a₇) → Eq {Nat} Nat:zero a₇ → HEq {LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) Nat:zero} x₆ {Nat:le (Nat:succ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) a₇} x₈ → False} {Nat:zero} x₆ (λ (h₇ : Eq {Nat} Nat:zero (Nat:succ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄))) → False:elim {HEq {LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) Nat:zero} x₆ {Nat:le (Nat:succ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) (Nat:succ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄))} (Nat:le:refl {Nat:succ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)}) → False} (noConfusion~uof~uNat {Nat} Nat:ctorIdx {Nat:zero} {Nat:succ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)} h₇)) (λ {m₇ : Nat} → λ (a₈ : Nat:le (Nat:succ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) m₇) → λ (h₉ : Eq {Nat} Nat:zero (Nat:succ m₇)) → False:elim {HEq {LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) Nat:zero} x₆ {Nat:le (Nat:succ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) (Nat:succ m₇)} (Nat:le:step {Nat:succ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)} {m₇} a₈) → False} (noConfusion~uof~uNat {Nat} Nat:ctorIdx {Nat:zero} {Nat:succ m₇} h₉)) (Eq:refl {Nat} Nat:zero) (HEq:refl {LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) Nat:zero} x₆))) (λ (n₆ : Nat) → λ (x₇ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₆)) → h1₄ n₆ x₇) x₃) (λ (n₆ : Nat) → h2₅ n₆ x₂ x₃)

Mod:mod : {α₀ : Set} → ⦃ _ : Mod α₀ ⦄ → α₀ → α₀ → α₀
Mod:mod {α₀} ⦃ self₁ ⦄ = Mod.mod₁ {α₀} self₁

instHMod : {α₀ : Set} → ⦃ _ : Mod α₀ ⦄ → HMod α₀ α₀ α₀
instHMod {α₀} ⦃ inst₁ ⦄ = HMod:mk {α₀} {α₀} {α₀} (λ (a₂ : α₀) → λ (b₃ : α₀) → Mod:mod {α₀} ⦃ inst₁ ⦄ a₂ b₃)

-- theorem
opaque
  Nat:mod~ult : (x₀ : Nat) → {y₁ : Nat} → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁ → LT:lt {Nat} ⦃ instLTNat ⦄ (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ x₀ y₁) y₁
  Nat:mod~ult x₀ {x₁} x₂ = ~uprivate:Init:Prelude:~n0:Nat:mod~ult:match~u1~u3 (λ (x₃ : Nat) → λ (x₄ : Nat) → λ (x₅ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₄) → LT:lt {Nat} ⦃ instLTNat ⦄ (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ x₃ x₄) x₄) x₀ x₁ x₂ (λ (n₃ : Nat) → λ (x₄ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₃)) → Nat:zero~ult~usucc n₃) (λ (n₃ : Nat) → λ (m₄ : Nat) → λ (hm₅ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) m₄) → let this₆ : LT:lt {Nat} ⦃ instLTNat ⦄ (ite {Nat} (LE:le {Nat} ⦃ instLENat ⦄ m₄ (Nat:succ n₃)) ⦃ Nat:decLe m₄ (Nat:succ n₃) ⦄ (Nat:modCore (Nat:succ n₃) m₄) (Nat:succ n₃)) m₄; this₆ = ~uprivate:Init:Prelude:~n0:Nat:mod~ult:match~u1~u1 n₃ m₄ (λ (x₆ : Decidable (LE:le {Nat} ⦃ instLENat ⦄ m₄ (Nat:succ n₃))) → LT:lt {Nat} ⦃ instLTNat ⦄ (ite {Nat} (LE:le {Nat} ⦃ instLENat ⦄ m₄ (Nat:succ n₃)) ⦃ x₆ ⦄ (Nat:modCore (Nat:succ n₃) m₄) (Nat:succ n₃)) m₄) (Nat:decLe m₄ (Nat:succ n₃)) (λ (h₆ : LE:le {Nat} ⦃ instLENat ⦄ m₄ (Nat:succ n₃)) → Nat:modCore~ult {Nat:succ n₃} {m₄} hm₅) (λ (h₆ : Not (LE:le {Nat} ⦃ instLENat ⦄ m₄ (Nat:succ n₃))) → Nat:lt~uof~unot~ule {m₄} {ite {Nat} (LE:le {Nat} ⦃ instLENat ⦄ m₄ (Nat:succ n₃)) ⦃ Decidable:isFalse {LE:le {Nat} ⦃ instLENat ⦄ m₄ (Nat:succ n₃)} h₆ ⦄ (Nat:modCore (Nat:succ n₃) m₄) (Nat:succ n₃)} h₆) in this₆)

GT:gt : {α₀ : Set} → ⦃ _ : LT α₀ ⦄ → α₀ → α₀ → Set
GT:gt {α₀} ⦃ inst₁ ⦄ a₂ b₃ = LT:lt {α₀} ⦃ inst₁ ⦄ b₃ a₂

-- theorem
opaque
  Nat:succ~upos : (n₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₀)
  Nat:succ~upos n₀ = Nat:zero~ult~usucc n₀

~uprivate:Init:Data:Nat:Basic:~n0:Nat:eq~uzero~uor~upos:match~u1~u1 : (motive₀ : Nat → Set) → (x₁ : Nat) → (Unit → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ x₁
~uprivate:Init:Data:Nat:Basic:~n0:Nat:eq~uzero~uor~upos:match~u1~u1 motive₀ x₁ h1₂ h2₃ = Nat:casesOn {λ (x₄ : Nat) → motive₀ x₄} x₁ (h1₂ Unit:unit) (λ (n₄ : Nat) → h2₃ n₄)

-- theorem
opaque
  Nat:eq~uzero~uor~upos : (n₀ : Nat) → Or (Eq {Nat} n₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) (GT:gt {Nat} ⦃ instLTNat ⦄ n₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄))
  Nat:eq~uzero~uor~upos x₀ = ~uprivate:Init:Data:Nat:Basic:~n0:Nat:eq~uzero~uor~upos:match~u1~u1 (λ (x₁ : Nat) → Or (Eq {Nat} x₁ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) (GT:gt {Nat} ⦃ instLTNat ⦄ x₁ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄))) x₀ (λ (x₁ : Unit) → Or:inl {Eq {Nat} (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)} {GT:gt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)} (rfl {Nat} {OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄})) (λ (n₁ : Nat) → Or:inr {Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)} {GT:gt {Nat} ⦃ instLTNat ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)} (Nat:succ~upos n₁))

Ne : {α₀ : Set} → α₀ → α₀ → Set
Ne {α₀} a₁ b₂ = Not (Eq {α₀} a₁ b₂)

-- theorem
opaque
  Or:resolve~uleft : {a₀ : Set} → {b₁ : Set} → Or a₀ b₁ → Not a₀ → b₁
  Or:resolve~uleft {a₀} {b₁} h₂ na₃ = Or:elim {a₀} {b₁} {b₁} h₂ (λ (x₄ : a₀) → absurd {a₀} {b₁} x₄ na₃) (id {b₁})

-- theorem
opaque
  Nat:pos~uof~une~uzero : {n₀ : Nat} → Ne {Nat} n₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) n₀
  Nat:pos~uof~une~uzero {n₀} = Or:resolve~uleft {Eq {Nat} n₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)} {GT:gt {Nat} ⦃ instLTNat ⦄ n₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)} (Nat:eq~uzero~uor~upos n₀)

record Zero (α₀ : Set) : Set where
  constructor Zero:mk
  field
    zero₁ : α₀

-- recursor
Zero:rec : {α₀ : Set} → {motive₁ : Zero α₀ → Set} → ((zero₂ : α₀) → motive₁ (Zero:mk {α₀} zero₂)) → (t₂ : Zero α₀) → motive₁ t₂
Zero:rec {α₀} {motive₁} mk₂ (Zero:mk zero₃) = mk₂ zero₃

Zero:zero : {α₀ : Set} → ⦃ _ : Zero α₀ ⦄ → α₀
Zero:zero {α₀} ⦃ self₁ ⦄ = Zero.zero₁ {α₀} self₁

Zero:toOfNat0 : {α₀ : Set} → ⦃ _ : Zero α₀ ⦄ → OfNat α₀ 0
Zero:toOfNat0 {α₀} ⦃ inst₁ ⦄ = OfNat:mk {α₀} {0} (Zero:zero {α₀} ⦃ inst₁ ⦄)

record NeZero {R₀ : Set} ⦃ inst₁ : Zero R₀ ⦄ (n₂ : R₀) : Set where
  constructor NeZero:mk
  field
    out₃ : Ne {R₀} n₂ (OfNat:ofNat {R₀} 0 ⦃ Zero:toOfNat0 {R₀} ⦃ inst₁ ⦄ ⦄)

-- recursor
NeZero:rec : {R₀ : Set} → ⦃ inst₁ : Zero R₀ ⦄ → {n₂ : R₀} → {motive₃ : NeZero {R₀} ⦃ inst₁ ⦄ n₂ → Set} → ((out₄ : Ne {R₀} n₂ (OfNat:ofNat {R₀} 0 ⦃ Zero:toOfNat0 {R₀} ⦃ inst₁ ⦄ ⦄)) → motive₃ (NeZero:mk {R₀} ⦃ inst₁ ⦄ {n₂} out₄)) → (t₄ : NeZero {R₀} ⦃ inst₁ ⦄ n₂) → motive₃ t₄
NeZero:rec {R₀} ⦃ inst₁ ⦄ {n₂} {motive₃} mk₄ (NeZero:mk out₅) = mk₄ out₅

-- theorem
opaque
  NeZero:out : {R₀ : Set} → {inst₁ : Zero R₀} → {n₂ : R₀} → ⦃ _ : NeZero {R₀} ⦃ inst₁ ⦄ n₂ ⦄ → Ne {R₀} n₂ (OfNat:ofNat {R₀} 0 ⦃ Zero:toOfNat0 {R₀} ⦃ inst₁ ⦄ ⦄)
  NeZero:out {R₀} {inst₁} {n₂} ⦃ self₃ ⦄ = NeZero.out₃ {R₀} ⦃ inst₁ ⦄ {n₂} self₃

-- theorem
opaque
  NeZero:ne : {R₀ : Set} → ⦃ inst₁ : Zero R₀ ⦄ → (n₂ : R₀) → ⦃ _ : NeZero {R₀} ⦃ inst₁ ⦄ n₂ ⦄ → Ne {R₀} n₂ (OfNat:ofNat {R₀} 0 ⦃ Zero:toOfNat0 {R₀} ⦃ inst₁ ⦄ ⦄)
  NeZero:ne {R₀} ⦃ inst₁ ⦄ n₂ ⦃ h₃ ⦄ = NeZero:out {R₀} {inst₁} {n₂} ⦃ h₃ ⦄

Zero:ofOfNat0 : {α₀ : Set} → ⦃ _ : OfNat α₀ 0 ⦄ → Zero α₀
Zero:ofOfNat0 {α₀} ⦃ inst₁ ⦄ = Zero:mk {α₀} (OfNat:ofNat {α₀} 0 ⦃ inst₁ ⦄)

-- theorem
opaque
  Nat:pos~uof~uneZero : (n₀ : Nat) → ⦃ _ : NeZero {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ n₀ ⦄ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) n₀
  Nat:pos~uof~uneZero n₀ ⦃ inst₁ ⦄ = Nat:pos~uof~une~uzero {n₀} (NeZero:ne {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ n₀ ⦃ inst₁ ⦄)

-- theorem
opaque
  Fin:ofNat:~uproof~u1 : (n₀ : Nat) → ⦃ _ : NeZero {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ n₀ ⦄ → (a₁ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ a₁ n₀) n₀
  Fin:ofNat:~uproof~u1 n₀ ⦃ inst₁ ⦄ a₂ = Nat:mod~ult a₂ {n₀} (Nat:pos~uof~uneZero n₀ ⦃ inst₁ ⦄)

Fin:ofNat : (n₀ : Nat) → ⦃ _ : NeZero {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ n₀ ⦄ → Nat → Fin n₀
Fin:ofNat n₀ ⦃ inst₁ ⦄ a₂ = Fin:mk {n₀} (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ a₂ n₀) (Fin:ofNat:~uproof~u1 n₀ ⦃ inst₁ ⦄ a₂)

Fin:instOfNat : {n₀ : Nat} → ⦃ _ : NeZero {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ n₀ ⦄ → {i₁ : Nat} → OfNat (Fin n₀) i₁
Fin:instOfNat {n₀} ⦃ inst₁ ⦄ {i₂} = OfNat:mk {Fin n₀} {i₂} (Fin:ofNat n₀ ⦃ inst₁ ⦄ i₂)

Fin:val : {n₀ : Nat} → Fin n₀ → Nat
Fin:val {n₀} self₁ = Fin.val₁ {n₀} self₁

HEq:homo~undrec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : α₀ → Set} → motive₂ a₁ → {b₃ : α₀} → HEq {α₀} a₁ {α₀} b₃ → motive₂ b₃
HEq:homo~undrec {α₀} {a₁} {motive₂} m₃ {b₄} h₅ = Eq:ndrec {α₀} {a₁} {motive₂} m₃ {b₄} (eq~uof~uheq {α₀} {a₁} {b₄} h₅)

~uprivate:Init:Core:~n0:Lean:injEq~uhelper:match~u1~u1 : {P₀ : Set} → {Q₁ : Set} → (motive₂ : And P₀ Q₁ → Set) → (h₃ : And P₀ Q₁) → ((h₄ : P₀) → (h₅ : Q₁) → motive₂ (And:intro {P₀} {Q₁} h₄ h₅)) → motive₂ h₃
~uprivate:Init:Core:~n0:Lean:injEq~uhelper:match~u1~u1 {P₀} {Q₁} motive₂ h₃ h1₄ = And:casesOn {P₀} {Q₁} {λ (x₅ : And P₀ Q₁) → motive₂ x₅} h₃ (λ (left₅ : P₀) → λ (right₆ : Q₁) → h1₄ left₅ right₆)

-- theorem
opaque
  Lean:injEq~uhelper : {P₀ : Set} → {Q₁ : Set} → {R₂ : Set} → (P₀ → Q₁ → R₂) → And P₀ Q₁ → R₂
  Lean:injEq~uhelper {P₀} {Q₁} {R₂} h₃ h₄ = ~uprivate:Init:Core:~n0:Lean:injEq~uhelper:match~u1~u1 {P₀} {Q₁} (λ (h₅ : And P₀ Q₁) → R₂) h₄ (λ (h₅ : P₀) → λ (h₆ : Q₁) → h₃ h₅ h₆)

List:casesOn : {α₀ : Set} → {motive₁ : List α₀ → Set} → (t₂ : List α₀) → motive₁ (List:nil {α₀}) → ((head₃ : α₀) → (tail₄ : List α₀) → motive₁ (List:cons {α₀} head₃ tail₄)) → motive₁ t₂
List:casesOn {α₀} {motive₁} t₂ nil₃ cons₄ = List:rec {α₀} {motive₁} nil₃ (λ (head₅ : α₀) → λ (tail₆ : List α₀) → λ (tailih₇ : motive₁ tail₆) → cons₄ head₅ tail₆) t₂

-- theorem
opaque
  List:cons:sizeOf~uspec : {α₀ : Set} → ⦃ inst₁ : SizeOf α₀ ⦄ → (head₂ : α₀) → (tail₃ : List α₀) → Eq {Nat} (SizeOf:sizeOf {List α₀} ⦃ List:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ ⦄ (List:cons {α₀} head₂ tail₃)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {α₀} ⦃ inst₁ ⦄ head₂)) (SizeOf:sizeOf {List α₀} ⦃ List:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ ⦄ tail₃))
  List:cons:sizeOf~uspec {α₀} ⦃ inst₁ ⦄ head₂ tail₃ = Eq:refl {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {α₀} ⦃ inst₁ ⦄ head₂)) (SizeOf:sizeOf {List α₀} ⦃ List:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ ⦄ tail₃))

List:toArray : {α₀ : Set} → List α₀ → Array α₀
List:toArray {α₀} xs₁ = Array:mk {α₀} xs₁

-- theorem
opaque
  eq~ufalse : {p₀ : Set} → Not p₀ → Eq {Set} p₀ False
  eq~ufalse {p₀} h₁ = propext {p₀} {False} (Iff:intro {p₀} {False} (λ (h₂ : p₀) → absurd {p₀} {False} h₂ h₁) (λ (h₂ : False) → False:elim {p₀} h₂))

-- theorem
opaque
  eq~ufalse~x27~ : {p₀ : Set} → (p₀ → False) → Eq {Set} p₀ False
  eq~ufalse~x27~ {p₀} h₁ = eq~ufalse {p₀} h₁

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
  not~ufalse~ueq~utrue : Eq {Set} (Not False) True
  not~ufalse~ueq~utrue = eq~utrue {Not False} (False:elim {False})

-- theorem
opaque
  of~ueq~utrue : {p₀ : Set} → Eq {Set} p₀ True → p₀
  of~ueq~utrue {p₀} h₁ = Eq:rec {Set} {True} {λ (x₂ : Set) → λ (h₃ : Eq {Set} True x₂) → x₂} trivial {p₀} (Eq:symm {Set} {p₀} {True} h₁)

-- theorem
opaque
  Nat:succ~une~uzero : (n₀ : Nat) → Ne {Nat} (Nat:succ n₀) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)
  Nat:succ~une~uzero n₀ = of~ueq~utrue {Not (Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄))} (Eq:trans {Set} {Not (Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄))} {Not False} {True} (congrArg {Set} {Set} {Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)} {False} Not (eq~ufalse~x27~ {Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)} (λ (h₁ : Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → False:elim {False} (noConfusion~uof~uNat {Nat} Nat:ctorIdx {HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)} {OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄} h₁)))) not~ufalse~ueq~utrue)

-- theorem
opaque
  Nat:instNeZeroSucc : {n₀ : Nat} → NeZero {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))
  Nat:instNeZeroSucc {n₀} = NeZero:mk {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ {HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)} (Nat:succ~une~uzero n₀)

NeZero:casesOn : {R₀ : Set} → ⦃ inst₁ : Zero R₀ ⦄ → {n₂ : R₀} → {motive₃ : NeZero {R₀} ⦃ inst₁ ⦄ n₂ → Set} → (t₄ : NeZero {R₀} ⦃ inst₁ ⦄ n₂) → ((out₅ : Ne {R₀} n₂ (OfNat:ofNat {R₀} 0 ⦃ Zero:toOfNat0 {R₀} ⦃ inst₁ ⦄ ⦄)) → motive₃ (NeZero:mk {R₀} ⦃ inst₁ ⦄ {n₂} out₅)) → motive₃ t₄
NeZero:casesOn {R₀} ⦃ inst₁ ⦄ {n₂} {motive₃} t₄ mk₅ = NeZero:rec {R₀} ⦃ inst₁ ⦄ {n₂} {motive₃} (λ (out₆ : Ne {R₀} n₂ (OfNat:ofNat {R₀} 0 ⦃ Zero:toOfNat0 {R₀} ⦃ inst₁ ⦄ ⦄)) → mk₅ out₆) t₄

record PULift (α₀ : Set) : Set where
  constructor PULift:up
  field
    down₁ : α₀

-- recursor
PULift:rec : {α₀ : Set} → {motive₁ : PULift α₀ → Set} → ((down₂ : α₀) → motive₁ (PULift:up {α₀} down₂)) → (t₂ : PULift α₀) → motive₁ t₂
PULift:rec {α₀} {motive₁} up₂ (PULift:up down₃) = up₂ down₃

PULift:down : {α₀ : Set} → PULift α₀ → α₀
PULift:down {α₀} self₁ = PULift.down₁ {α₀} self₁

record Prod (α₀ : Set) (β₁ : Set) : Set where
  constructor Prod:mk
  field
    fst₂ : α₀
    snd₃ : β₁

-- recursor
Prod:rec : {α₀ : Set} → {β₁ : Set} → {motive₂ : Prod α₀ β₁ → Set} → ((fst₃ : α₀) → (snd₄ : β₁) → motive₂ (Prod:mk {α₀} {β₁} fst₃ snd₄)) → (t₃ : Prod α₀ β₁) → motive₂ t₃
Prod:rec {α₀} {β₁} {motive₂} mk₃ (Prod:mk fst₄ snd₅) = mk₃ fst₄ snd₅

Prod:~usizeOf~u1 : {α₀ : Set} → {β₁ : Set} → ⦃ _ : SizeOf α₀ ⦄ → ⦃ _ : SizeOf β₁ ⦄ → Prod α₀ β₁ → Nat
Prod:~usizeOf~u1 {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ t₄ = Prod:rec {α₀} {β₁} {λ (t₅ : Prod α₀ β₁) → Nat} (λ (fst₅ : α₀) → λ (snd₆ : β₁) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {α₀} ⦃ inst₂ ⦄ fst₅)) (SizeOf:sizeOf {β₁} ⦃ inst₃ ⦄ snd₆)) t₄

Prod:~usizeOf~uinst : (α₀ : Set) → (β₁ : Set) → ⦃ _ : SizeOf α₀ ⦄ → ⦃ _ : SizeOf β₁ ⦄ → SizeOf (Prod α₀ β₁)
Prod:~usizeOf~uinst α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ = SizeOf:mk {Prod α₀ β₁} (λ (m₄ : Prod α₀ β₁) → Prod:~usizeOf~u1 {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ m₄)

Prod:casesOn : {α₀ : Set} → {β₁ : Set} → {motive₂ : Prod α₀ β₁ → Set} → (t₃ : Prod α₀ β₁) → ((fst₄ : α₀) → (snd₅ : β₁) → motive₂ (Prod:mk {α₀} {β₁} fst₄ snd₅)) → motive₂ t₃
Prod:casesOn {α₀} {β₁} {motive₂} t₃ mk₄ = Prod:rec {α₀} {β₁} {motive₂} (λ (fst₅ : α₀) → λ (snd₆ : β₁) → mk₄ fst₅ snd₆) t₃

data RecursorFixtures:Doc : Set where
  RecursorFixtures:Doc:text : Nat → RecursorFixtures:Doc
  RecursorFixtures:Doc:block : Array RecursorFixtures:Doc → RecursorFixtures:Doc

-- recursor
mutual
  RecursorFixtures:Doc:rec : {motive1₀ : RecursorFixtures:Doc → Set} → {motive2₁ : Array RecursorFixtures:Doc → Set} → {motive3₂ : List RecursorFixtures:Doc → Set} → ((n₃ : Nat) → motive1₀ (RecursorFixtures:Doc:text n₃)) → ((kids₃ : Array RecursorFixtures:Doc) → motive2₁ kids₃ → motive1₀ (RecursorFixtures:Doc:block kids₃)) → ((toList₃ : List RecursorFixtures:Doc) → motive3₂ toList₃ → motive2₁ (Array:mk {RecursorFixtures:Doc} toList₃)) → motive3₂ (List:nil {RecursorFixtures:Doc}) → ((head₃ : RecursorFixtures:Doc) → (tail₄ : List RecursorFixtures:Doc) → motive1₀ head₃ → motive3₂ tail₄ → motive3₂ (List:cons {RecursorFixtures:Doc} head₃ tail₄)) → (t₃ : RecursorFixtures:Doc) → motive1₀ t₃
  RecursorFixtures:Doc:rec~u1 : {motive1₀ : RecursorFixtures:Doc → Set} → {motive2₁ : Array RecursorFixtures:Doc → Set} → {motive3₂ : List RecursorFixtures:Doc → Set} → ((n₃ : Nat) → motive1₀ (RecursorFixtures:Doc:text n₃)) → ((kids₃ : Array RecursorFixtures:Doc) → motive2₁ kids₃ → motive1₀ (RecursorFixtures:Doc:block kids₃)) → ((toList₃ : List RecursorFixtures:Doc) → motive3₂ toList₃ → motive2₁ (Array:mk {RecursorFixtures:Doc} toList₃)) → motive3₂ (List:nil {RecursorFixtures:Doc}) → ((head₃ : RecursorFixtures:Doc) → (tail₄ : List RecursorFixtures:Doc) → motive1₀ head₃ → motive3₂ tail₄ → motive3₂ (List:cons {RecursorFixtures:Doc} head₃ tail₄)) → (t₃ : Array RecursorFixtures:Doc) → motive2₁ t₃
  RecursorFixtures:Doc:rec~u2 : {motive1₀ : RecursorFixtures:Doc → Set} → {motive2₁ : Array RecursorFixtures:Doc → Set} → {motive3₂ : List RecursorFixtures:Doc → Set} → ((n₃ : Nat) → motive1₀ (RecursorFixtures:Doc:text n₃)) → ((kids₃ : Array RecursorFixtures:Doc) → motive2₁ kids₃ → motive1₀ (RecursorFixtures:Doc:block kids₃)) → ((toList₃ : List RecursorFixtures:Doc) → motive3₂ toList₃ → motive2₁ (Array:mk {RecursorFixtures:Doc} toList₃)) → motive3₂ (List:nil {RecursorFixtures:Doc}) → ((head₃ : RecursorFixtures:Doc) → (tail₄ : List RecursorFixtures:Doc) → motive1₀ head₃ → motive3₂ tail₄ → motive3₂ (List:cons {RecursorFixtures:Doc} head₃ tail₄)) → (t₃ : List RecursorFixtures:Doc) → motive3₂ t₃
  RecursorFixtures:Doc:rec {motive1₀} {motive2₁} {motive3₂} text₃ block₄ mk₅ nil₆ cons₇ (RecursorFixtures:Doc:text n₈) = text₃ n₈
  RecursorFixtures:Doc:rec {motive1₀} {motive2₁} {motive3₂} text₃ block₄ mk₅ nil₆ cons₇ (RecursorFixtures:Doc:block kids₈) = block₄ kids₈ (RecursorFixtures:Doc:rec~u1 {motive1₀} {motive2₁} {motive3₂} text₃ block₄ mk₅ nil₆ cons₇ kids₈)
  RecursorFixtures:Doc:rec~u1 {motive1₀} {motive2₁} {motive3₂} text₃ block₄ mk₅ nil₆ cons₇ (Array:mk toList₈) = mk₅ toList₈ (RecursorFixtures:Doc:rec~u2 {motive1₀} {motive2₁} {motive3₂} text₃ block₄ mk₅ nil₆ cons₇ toList₈)
  RecursorFixtures:Doc:rec~u2 {motive1₀} {motive2₁} {motive3₂} text₃ block₄ mk₅ nil₆ cons₇ List:nil = nil₆
  RecursorFixtures:Doc:rec~u2 {motive1₀} {motive2₁} {motive3₂} text₃ block₄ mk₅ nil₆ cons₇ (List:cons head₈ tail₉) = cons₇ head₈ tail₉ (RecursorFixtures:Doc:rec {motive1₀} {motive2₁} {motive3₂} text₃ block₄ mk₅ nil₆ cons₇ head₈) (RecursorFixtures:Doc:rec~u2 {motive1₀} {motive2₁} {motive3₂} text₃ block₄ mk₅ nil₆ cons₇ tail₉)

RecursorFixtures:Doc:~usizeOf~u1 : RecursorFixtures:Doc → Nat
RecursorFixtures:Doc:~usizeOf~u1 t₀ = RecursorFixtures:Doc:rec {λ (t₁ : RecursorFixtures:Doc) → Nat} {λ (t₁ : Array RecursorFixtures:Doc) → Nat} {λ (t₁ : List RecursorFixtures:Doc) → Nat} (λ (n₁ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {Nat} ⦃ instSizeOfNat ⦄ n₁)) (λ (kids₁ : Array RecursorFixtures:Doc) → λ (kidsih₂ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) kidsih₂) (λ (toList₁ : List RecursorFixtures:Doc) → λ (toListih₂ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) toListih₂) (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (λ (head₁ : RecursorFixtures:Doc) → λ (tail₂ : List RecursorFixtures:Doc) → λ (headih₃ : Nat) → λ (tailih₄ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) headih₃) tailih₄) t₀

RecursorFixtures:Doc:~usizeOf~u2 : Array RecursorFixtures:Doc → Nat
RecursorFixtures:Doc:~usizeOf~u2 t₀ = RecursorFixtures:Doc:rec~u1 {λ (t₁ : RecursorFixtures:Doc) → Nat} {λ (t₁ : Array RecursorFixtures:Doc) → Nat} {λ (t₁ : List RecursorFixtures:Doc) → Nat} (λ (n₁ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {Nat} ⦃ instSizeOfNat ⦄ n₁)) (λ (kids₁ : Array RecursorFixtures:Doc) → λ (kidsih₂ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) kidsih₂) (λ (toList₁ : List RecursorFixtures:Doc) → λ (toListih₂ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) toListih₂) (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (λ (head₁ : RecursorFixtures:Doc) → λ (tail₂ : List RecursorFixtures:Doc) → λ (headih₃ : Nat) → λ (tailih₄ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) headih₃) tailih₄) t₀

RecursorFixtures:Doc:~usizeOf~u3 : List RecursorFixtures:Doc → Nat
RecursorFixtures:Doc:~usizeOf~u3 t₀ = RecursorFixtures:Doc:rec~u2 {λ (t₁ : RecursorFixtures:Doc) → Nat} {λ (t₁ : Array RecursorFixtures:Doc) → Nat} {λ (t₁ : List RecursorFixtures:Doc) → Nat} (λ (n₁ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {Nat} ⦃ instSizeOfNat ⦄ n₁)) (λ (kids₁ : Array RecursorFixtures:Doc) → λ (kidsih₂ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) kidsih₂) (λ (toList₁ : List RecursorFixtures:Doc) → λ (toListih₂ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) toListih₂) (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (λ (head₁ : RecursorFixtures:Doc) → λ (tail₂ : List RecursorFixtures:Doc) → λ (headih₃ : Nat) → λ (tailih₄ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) headih₃) tailih₄) t₀

RecursorFixtures:Doc:~usizeOf~uinst : SizeOf RecursorFixtures:Doc
RecursorFixtures:Doc:~usizeOf~uinst = SizeOf:mk {RecursorFixtures:Doc} (λ (m₀ : RecursorFixtures:Doc) → RecursorFixtures:Doc:~usizeOf~u1 m₀)

-- theorem
opaque
  RecursorFixtures:Doc:~usizeOf~u3~ueq : (x₀ : List RecursorFixtures:Doc) → Eq {Nat} (RecursorFixtures:Doc:~usizeOf~u3 x₀) (SizeOf:sizeOf {List RecursorFixtures:Doc} ⦃ List:~usizeOf~uinst RecursorFixtures:Doc ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ ⦄ x₀)
  RecursorFixtures:Doc:~usizeOf~u3~ueq x₀ = List:rec {RecursorFixtures:Doc} {λ (t₁ : List RecursorFixtures:Doc) → Eq {Nat} (RecursorFixtures:Doc:~usizeOf~u3 t₁) (SizeOf:sizeOf {List RecursorFixtures:Doc} ⦃ List:~usizeOf~uinst RecursorFixtures:Doc ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ ⦄ t₁)} (Eq:refl {Nat} (SizeOf:sizeOf {List RecursorFixtures:Doc} ⦃ List:~usizeOf~uinst RecursorFixtures:Doc ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ ⦄ (List:nil {RecursorFixtures:Doc}))) (λ (head₁ : RecursorFixtures:Doc) → λ (tail₂ : List RecursorFixtures:Doc) → λ (tailih₃ : Eq {Nat} (RecursorFixtures:Doc:~usizeOf~u3 tail₂) (SizeOf:sizeOf {List RecursorFixtures:Doc} ⦃ List:~usizeOf~uinst RecursorFixtures:Doc ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ ⦄ tail₂)) → Eq:trans {Nat} {Nat:add (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {RecursorFixtures:Doc} ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ head₁)) (RecursorFixtures:Doc:~usizeOf~u3 tail₂)} {Nat:add (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {RecursorFixtures:Doc} ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ head₁)) (SizeOf:sizeOf {List RecursorFixtures:Doc} ⦃ List:~usizeOf~uinst RecursorFixtures:Doc ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ ⦄ tail₂)} {SizeOf:sizeOf {List RecursorFixtures:Doc} ⦃ List:~usizeOf~uinst RecursorFixtures:Doc ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ ⦄ (List:cons {RecursorFixtures:Doc} head₁ tail₂)} (congrArg {Nat} {Nat} {RecursorFixtures:Doc:~usizeOf~u3 tail₂} {SizeOf:sizeOf {List RecursorFixtures:Doc} ⦃ List:~usizeOf~uinst RecursorFixtures:Doc ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ ⦄ tail₂} (Nat:add (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {RecursorFixtures:Doc} ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ head₁))) tailih₃) (Eq:symm {Nat} {SizeOf:sizeOf {List RecursorFixtures:Doc} ⦃ List:~usizeOf~uinst RecursorFixtures:Doc ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ ⦄ (List:cons {RecursorFixtures:Doc} head₁ tail₂)} {HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {RecursorFixtures:Doc} ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ head₁)) (SizeOf:sizeOf {List RecursorFixtures:Doc} ⦃ List:~usizeOf~uinst RecursorFixtures:Doc ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ ⦄ tail₂)} (List:cons:sizeOf~uspec {RecursorFixtures:Doc} ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ head₁ tail₂))) x₀

-- theorem
opaque
  RecursorFixtures:Doc:~usizeOf~u2~ueq : (x₀ : Array RecursorFixtures:Doc) → Eq {Nat} (RecursorFixtures:Doc:~usizeOf~u2 x₀) (SizeOf:sizeOf {Array RecursorFixtures:Doc} ⦃ Array:~usizeOf~uinst RecursorFixtures:Doc ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ ⦄ x₀)
  RecursorFixtures:Doc:~usizeOf~u2~ueq x₀ = Array:rec {RecursorFixtures:Doc} {λ (t₁ : Array RecursorFixtures:Doc) → Eq {Nat} (RecursorFixtures:Doc:~usizeOf~u2 t₁) (SizeOf:sizeOf {Array RecursorFixtures:Doc} ⦃ Array:~usizeOf~uinst RecursorFixtures:Doc ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ ⦄ t₁)} (λ (toList₁ : List RecursorFixtures:Doc) → Eq:trans {Nat} {Nat:add (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (RecursorFixtures:Doc:~usizeOf~u3 toList₁)} {Nat:add (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {List RecursorFixtures:Doc} ⦃ List:~usizeOf~uinst RecursorFixtures:Doc ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ ⦄ toList₁)} {SizeOf:sizeOf {Array RecursorFixtures:Doc} ⦃ Array:~usizeOf~uinst RecursorFixtures:Doc ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ ⦄ (Array:mk {RecursorFixtures:Doc} toList₁)} (congrArg {Nat} {Nat} {RecursorFixtures:Doc:~usizeOf~u3 toList₁} {SizeOf:sizeOf {List RecursorFixtures:Doc} ⦃ List:~usizeOf~uinst RecursorFixtures:Doc ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ ⦄ toList₁} (Nat:add (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (RecursorFixtures:Doc:~usizeOf~u3~ueq toList₁)) (Eq:symm {Nat} {SizeOf:sizeOf {Array RecursorFixtures:Doc} ⦃ Array:~usizeOf~uinst RecursorFixtures:Doc ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ ⦄ (Array:mk {RecursorFixtures:Doc} toList₁)} {HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {List RecursorFixtures:Doc} ⦃ List:~usizeOf~uinst RecursorFixtures:Doc ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ ⦄ toList₁)} (Array:mk:sizeOf~uspec {RecursorFixtures:Doc} ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ toList₁))) x₀

RecursorFixtures:Doc:below : {_ : RecursorFixtures:Doc → Set} → {_ : Array RecursorFixtures:Doc → Set} → {_ : List RecursorFixtures:Doc → Set} → RecursorFixtures:Doc → Set
RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} t₃ = RecursorFixtures:Doc:rec {λ (t₄ : RecursorFixtures:Doc) → Set} {λ (t₄ : Array RecursorFixtures:Doc) → Set} {λ (t₄ : List RecursorFixtures:Doc) → Set} (λ (n₄ : Nat) → PUnit) (λ (kids₄ : Array RecursorFixtures:Doc) → λ (kidsih₅ : Set) → PProd (motive2₁ kids₄) kidsih₅) (λ (toList₄ : List RecursorFixtures:Doc) → λ (toListih₅ : Set) → PProd (motive3₂ toList₄) toListih₅) PUnit (λ (head₄ : RecursorFixtures:Doc) → λ (tail₅ : List RecursorFixtures:Doc) → λ (headih₆ : Set) → λ (tailih₇ : Set) → PProd (PProd (motive1₀ head₄) headih₆) (PProd (motive3₂ tail₅) tailih₇)) t₃

RecursorFixtures:Doc:below~u1 : {_ : RecursorFixtures:Doc → Set} → {_ : Array RecursorFixtures:Doc → Set} → {_ : List RecursorFixtures:Doc → Set} → Array RecursorFixtures:Doc → Set
RecursorFixtures:Doc:below~u1 {motive1₀} {motive2₁} {motive3₂} t₃ = RecursorFixtures:Doc:rec~u1 {λ (t₄ : RecursorFixtures:Doc) → Set} {λ (t₄ : Array RecursorFixtures:Doc) → Set} {λ (t₄ : List RecursorFixtures:Doc) → Set} (λ (n₄ : Nat) → PUnit) (λ (kids₄ : Array RecursorFixtures:Doc) → λ (kidsih₅ : Set) → PProd (motive2₁ kids₄) kidsih₅) (λ (toList₄ : List RecursorFixtures:Doc) → λ (toListih₅ : Set) → PProd (motive3₂ toList₄) toListih₅) PUnit (λ (head₄ : RecursorFixtures:Doc) → λ (tail₅ : List RecursorFixtures:Doc) → λ (headih₆ : Set) → λ (tailih₇ : Set) → PProd (PProd (motive1₀ head₄) headih₆) (PProd (motive3₂ tail₅) tailih₇)) t₃

RecursorFixtures:Doc:below~u2 : {_ : RecursorFixtures:Doc → Set} → {_ : Array RecursorFixtures:Doc → Set} → {_ : List RecursorFixtures:Doc → Set} → List RecursorFixtures:Doc → Set
RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} t₃ = RecursorFixtures:Doc:rec~u2 {λ (t₄ : RecursorFixtures:Doc) → Set} {λ (t₄ : Array RecursorFixtures:Doc) → Set} {λ (t₄ : List RecursorFixtures:Doc) → Set} (λ (n₄ : Nat) → PUnit) (λ (kids₄ : Array RecursorFixtures:Doc) → λ (kidsih₅ : Set) → PProd (motive2₁ kids₄) kidsih₅) (λ (toList₄ : List RecursorFixtures:Doc) → λ (toListih₅ : Set) → PProd (motive3₂ toList₄) toListih₅) PUnit (λ (head₄ : RecursorFixtures:Doc) → λ (tail₅ : List RecursorFixtures:Doc) → λ (headih₆ : Set) → λ (tailih₇ : Set) → PProd (PProd (motive1₀ head₄) headih₆) (PProd (motive3₂ tail₅) tailih₇)) t₃

RecursorFixtures:Doc:casesOn : {motive1₀ : RecursorFixtures:Doc → Set} → (t₁ : RecursorFixtures:Doc) → ((n₂ : Nat) → motive1₀ (RecursorFixtures:Doc:text n₂)) → ((kids₂ : Array RecursorFixtures:Doc) → motive1₀ (RecursorFixtures:Doc:block kids₂)) → motive1₀ t₁
RecursorFixtures:Doc:casesOn {motive1₀} t₁ text₂ block₃ = RecursorFixtures:Doc:rec {motive1₀} {λ (t₄ : Array RecursorFixtures:Doc) → PUnit} {λ (t₄ : List RecursorFixtures:Doc) → PUnit} (λ (n₄ : Nat) → text₂ n₄) (λ (kids₄ : Array RecursorFixtures:Doc) → λ (kidsih₅ : PUnit) → block₃ kids₄) (λ (toList₄ : List RecursorFixtures:Doc) → λ (toListih₅ : PUnit) → PUnit:unit) PUnit:unit (λ (head₄ : RecursorFixtures:Doc) → λ (tail₅ : List RecursorFixtures:Doc) → λ (headih₆ : motive1₀ head₄) → λ (tailih₇ : PUnit) → PUnit:unit) t₁

cond:match~u1 : (motive₀ : Bool → Set) → (c₁ : Bool) → (Unit → motive₀ Bool:true) → (Unit → motive₀ Bool:false) → motive₀ c₁
cond:match~u1 motive₀ c₁ h1₂ h2₃ = Bool:casesOn {λ (x₄ : Bool) → motive₀ x₄} c₁ (h2₃ Unit:unit) (h1₂ Unit:unit)

cond : {α₀ : Set} → Bool → α₀ → α₀ → α₀
cond {α₀} c₁ x₂ y₃ = cond:match~u1 (λ (c₄ : Bool) → α₀) c₁ (λ (x₄ : Unit) → x₂) (λ (x₄ : Unit) → y₃)

RecursorFixtures:Doc:ctorElimType : {_ : RecursorFixtures:Doc → Set} → Nat → Set
RecursorFixtures:Doc:ctorElimType {motive1₀} ctorIdx₁ = cond {Set} (Nat:ble ctorIdx₁ 0) (PULift ((n₂ : Nat) → motive1₀ (RecursorFixtures:Doc:text n₂))) (PULift ((kids₂ : Array RecursorFixtures:Doc) → motive1₀ (RecursorFixtures:Doc:block kids₂)))

RecursorFixtures:Doc:ctorIdx : RecursorFixtures:Doc → Nat
RecursorFixtures:Doc:ctorIdx x₀ = RecursorFixtures:Doc:casesOn {λ (x₁ : RecursorFixtures:Doc) → Nat} x₀ (λ (n₁ : Nat) → 0) (λ (kids₁ : Array RecursorFixtures:Doc) → 1)

RecursorFixtures:Doc:ctorElim : {motive1₀ : RecursorFixtures:Doc → Set} → (ctorIdx₁ : Nat) → (t₂ : RecursorFixtures:Doc) → Eq {Nat} ctorIdx₁ (RecursorFixtures:Doc:ctorIdx t₂) → RecursorFixtures:Doc:ctorElimType {motive1₀} ctorIdx₁ → motive1₀ t₂
RecursorFixtures:Doc:ctorElim {motive1₀} ctorIdx₁ t₂ h₃ k₄ = RecursorFixtures:Doc:casesOn {λ (t₅ : RecursorFixtures:Doc) → Eq {Nat} ctorIdx₁ (RecursorFixtures:Doc:ctorIdx t₅) → motive1₀ t₅} t₂ (λ (n₅ : Nat) → λ (h₆ : Eq {Nat} ctorIdx₁ 0) → PULift:down {(n₇ : Nat) → motive1₀ (RecursorFixtures:Doc:text n₇)} (Eq:ndrec {Nat} {ctorIdx₁} {RecursorFixtures:Doc:ctorElimType {motive1₀}} k₄ {0} h₆) n₅) (λ (kids₅ : Array RecursorFixtures:Doc) → λ (h₆ : Eq {Nat} ctorIdx₁ 1) → PULift:down {(kids₇ : Array RecursorFixtures:Doc) → motive1₀ (RecursorFixtures:Doc:block kids₇)} (Eq:ndrec {Nat} {ctorIdx₁} {RecursorFixtures:Doc:ctorElimType {motive1₀}} k₄ {1} h₆) kids₅) h₃

RecursorFixtures:Doc:block:elim : {motive1₀ : RecursorFixtures:Doc → Set} → (t₁ : RecursorFixtures:Doc) → Eq {Nat} (RecursorFixtures:Doc:ctorIdx t₁) 1 → ((kids₂ : Array RecursorFixtures:Doc) → motive1₀ (RecursorFixtures:Doc:block kids₂)) → motive1₀ t₁
RecursorFixtures:Doc:block:elim {motive1₀} t₁ h₂ block₃ = RecursorFixtures:Doc:ctorElim {motive1₀} 1 t₁ (Eq:symm {Nat} {RecursorFixtures:Doc:ctorIdx t₁} {1} h₂) (PULift:up {(kids₄ : Array RecursorFixtures:Doc) → motive1₀ (RecursorFixtures:Doc:block kids₄)} block₃)

RecursorFixtures:Doc:noConfusionType : Set → RecursorFixtures:Doc → RecursorFixtures:Doc → Set
RecursorFixtures:Doc:noConfusionType P₀ t₁ t₂ = RecursorFixtures:Doc:casesOn {λ (t₃ : RecursorFixtures:Doc) → Set} t₁ (λ (n₃ : Nat) → RecursorFixtures:Doc:casesOn {λ (t₄ : RecursorFixtures:Doc) → Set} t₂ (λ (n₄ : Nat) → (Eq {Nat} n₃ n₄ → P₀) → P₀) (λ (kids₄ : Array RecursorFixtures:Doc) → P₀)) (λ (kids₃ : Array RecursorFixtures:Doc) → RecursorFixtures:Doc:casesOn {λ (t₄ : RecursorFixtures:Doc) → Set} t₂ (λ (n₄ : Nat) → P₀) (λ (kids₄ : Array RecursorFixtures:Doc) → (Eq {Array RecursorFixtures:Doc} kids₃ kids₄ → P₀) → P₀))

RecursorFixtures:Doc:noConfusion : {P₀ : Set} → {t₁ : RecursorFixtures:Doc} → {t₂ : RecursorFixtures:Doc} → Eq {RecursorFixtures:Doc} t₁ t₂ → RecursorFixtures:Doc:noConfusionType P₀ t₁ t₂
RecursorFixtures:Doc:noConfusion {P₀} {t₁} {t₂} eq₃ = Eq:ndrec {RecursorFixtures:Doc} {t₁} {λ (t₄ : RecursorFixtures:Doc) → RecursorFixtures:Doc:noConfusionType P₀ t₁ t₄} (RecursorFixtures:Doc:casesOn {λ (t₄ : RecursorFixtures:Doc) → RecursorFixtures:Doc:noConfusionType P₀ t₄ t₄} t₁ (λ (n₄ : Nat) → λ (k₅ : Eq {Nat} n₄ n₄ → P₀) → k₅ (Eq:refl {Nat} n₄)) (λ (kids₄ : Array RecursorFixtures:Doc) → λ (k₅ : Eq {Array RecursorFixtures:Doc} kids₄ kids₄ → P₀) → k₅ (Eq:refl {Array RecursorFixtures:Doc} kids₄))) {t₂} eq₃

RecursorFixtures:Doc:block:noConfusion : {P₀ : Set} → {kids₁ : Array RecursorFixtures:Doc} → {kids₂ : Array RecursorFixtures:Doc} → Eq {RecursorFixtures:Doc} (RecursorFixtures:Doc:block kids₁) (RecursorFixtures:Doc:block kids₂) → (Eq {Array RecursorFixtures:Doc} kids₁ kids₂ → P₀) → P₀
RecursorFixtures:Doc:block:noConfusion {P₀} {kids₁} {kids₂} eq₃ k₄ = id {P₀} (RecursorFixtures:Doc:noConfusion {P₀} {RecursorFixtures:Doc:block kids₁} {RecursorFixtures:Doc:block kids₂} eq₃ k₄)

-- theorem
opaque
  RecursorFixtures:Doc:block:inj : {kids₀ : Array RecursorFixtures:Doc} → {kids₁ : Array RecursorFixtures:Doc} → Eq {RecursorFixtures:Doc} (RecursorFixtures:Doc:block kids₀) (RecursorFixtures:Doc:block kids₁) → Eq {Array RecursorFixtures:Doc} kids₀ kids₁
  RecursorFixtures:Doc:block:inj {kids₀} {kids₁} x₂ = RecursorFixtures:Doc:block:noConfusion {Eq {Array RecursorFixtures:Doc} kids₀ kids₁} {kids₀} {kids₁} x₂ (λ (kidseq₃ : Eq {Array RecursorFixtures:Doc} kids₀ kids₁) → kidseq₃)

-- theorem
opaque
  RecursorFixtures:Doc:block:injEq : (kids₀ : Array RecursorFixtures:Doc) → (kids₁ : Array RecursorFixtures:Doc) → Eq {Set} (Eq {RecursorFixtures:Doc} (RecursorFixtures:Doc:block kids₀) (RecursorFixtures:Doc:block kids₁)) (Eq {Array RecursorFixtures:Doc} kids₀ kids₁)
  RecursorFixtures:Doc:block:injEq kids₀ kids₁ = Eq:propIntro {Eq {RecursorFixtures:Doc} (RecursorFixtures:Doc:block kids₀) (RecursorFixtures:Doc:block kids₁)} {Eq {Array RecursorFixtures:Doc} kids₀ kids₁} (RecursorFixtures:Doc:block:inj {kids₀} {kids₁}) (Eq:ndrec {Array RecursorFixtures:Doc} {kids₀} {λ (kids₂ : Array RecursorFixtures:Doc) → Eq {RecursorFixtures:Doc} (RecursorFixtures:Doc:block kids₀) (RecursorFixtures:Doc:block kids₂)} (Eq:refl {RecursorFixtures:Doc} (RecursorFixtures:Doc:block kids₀)) {kids₁})

-- theorem
opaque
  RecursorFixtures:Doc:block:sizeOf~uspec : (kids₀ : Array RecursorFixtures:Doc) → Eq {Nat} (SizeOf:sizeOf {RecursorFixtures:Doc} ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ (RecursorFixtures:Doc:block kids₀)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {Array RecursorFixtures:Doc} ⦃ Array:~usizeOf~uinst RecursorFixtures:Doc ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ ⦄ kids₀))
  RecursorFixtures:Doc:block:sizeOf~uspec kids₀ = congrArg {Nat} {Nat} {RecursorFixtures:Doc:~usizeOf~u2 kids₀} {SizeOf:sizeOf {Array RecursorFixtures:Doc} ⦃ Array:~usizeOf~uinst RecursorFixtures:Doc ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ ⦄ kids₀} (Nat:add (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (RecursorFixtures:Doc:~usizeOf~u2~ueq kids₀)

RecursorFixtures:Doc:brecOn:go : {motive1₀ : RecursorFixtures:Doc → Set} → {motive2₁ : Array RecursorFixtures:Doc → Set} → {motive3₂ : List RecursorFixtures:Doc → Set} → (t₃ : RecursorFixtures:Doc) → ((t₄ : RecursorFixtures:Doc) → RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} t₄ → motive1₀ t₄) → ((t₄ : Array RecursorFixtures:Doc) → RecursorFixtures:Doc:below~u1 {motive1₀} {motive2₁} {motive3₂} t₄ → motive2₁ t₄) → ((t₄ : List RecursorFixtures:Doc) → RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} t₄ → motive3₂ t₄) → PProd (motive1₀ t₃) (RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} t₃)
RecursorFixtures:Doc:brecOn:go {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆ = RecursorFixtures:Doc:rec {λ (t₇ : RecursorFixtures:Doc) → PProd (motive1₀ t₇) (RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} t₇)} {λ (t₇ : Array RecursorFixtures:Doc) → PProd (motive2₁ t₇) (RecursorFixtures:Doc:below~u1 {motive1₀} {motive2₁} {motive3₂} t₇)} {λ (t₇ : List RecursorFixtures:Doc) → PProd (motive3₂ t₇) (RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} t₇)} (λ (n₇ : Nat) → PProd:mk {motive1₀ (RecursorFixtures:Doc:text n₇)} {PUnit} (F1₄ (RecursorFixtures:Doc:text n₇) PUnit:unit) PUnit:unit) (λ (kids₇ : Array RecursorFixtures:Doc) → λ (kidsih₈ : PProd (motive2₁ kids₇) (RecursorFixtures:Doc:below~u1 {motive1₀} {motive2₁} {motive3₂} kids₇)) → PProd:mk {motive1₀ (RecursorFixtures:Doc:block kids₇)} {PProd (motive2₁ kids₇) (RecursorFixtures:Doc:below~u1 {motive1₀} {motive2₁} {motive3₂} kids₇)} (F1₄ (RecursorFixtures:Doc:block kids₇) kidsih₈) kidsih₈) (λ (toList₇ : List RecursorFixtures:Doc) → λ (toListih₈ : PProd (motive3₂ toList₇) (RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} toList₇)) → PProd:mk {motive2₁ (Array:mk {RecursorFixtures:Doc} toList₇)} {PProd (motive3₂ toList₇) (RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} toList₇)} (F2₅ (Array:mk {RecursorFixtures:Doc} toList₇) toListih₈) toListih₈) (PProd:mk {motive3₂ (List:nil {RecursorFixtures:Doc})} {PUnit} (F3₆ (List:nil {RecursorFixtures:Doc}) PUnit:unit) PUnit:unit) (λ (head₇ : RecursorFixtures:Doc) → λ (tail₈ : List RecursorFixtures:Doc) → λ (headih₉ : PProd (motive1₀ head₇) (RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} head₇)) → λ (tailih₁₀ : PProd (motive3₂ tail₈) (RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} tail₈)) → PProd:mk {motive3₂ (List:cons {RecursorFixtures:Doc} head₇ tail₈)} {PProd (PProd (motive1₀ head₇) (RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} head₇)) (PProd (motive3₂ tail₈) (RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} tail₈))} (F3₆ (List:cons {RecursorFixtures:Doc} head₇ tail₈) (PProd:mk {PProd (motive1₀ head₇) (RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} head₇)} {PProd (motive3₂ tail₈) (RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} tail₈)} headih₉ tailih₁₀)) (PProd:mk {PProd (motive1₀ head₇) (RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} head₇)} {PProd (motive3₂ tail₈) (RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} tail₈)} headih₉ tailih₁₀)) t₃

RecursorFixtures:Doc:brecOn : {motive1₀ : RecursorFixtures:Doc → Set} → {motive2₁ : Array RecursorFixtures:Doc → Set} → {motive3₂ : List RecursorFixtures:Doc → Set} → (t₃ : RecursorFixtures:Doc) → ((t₄ : RecursorFixtures:Doc) → RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} t₄ → motive1₀ t₄) → ((t₄ : Array RecursorFixtures:Doc) → RecursorFixtures:Doc:below~u1 {motive1₀} {motive2₁} {motive3₂} t₄ → motive2₁ t₄) → ((t₄ : List RecursorFixtures:Doc) → RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} t₄ → motive3₂ t₄) → motive1₀ t₃
RecursorFixtures:Doc:brecOn {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆ = PProd.fst₂ {motive1₀ t₃} {RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} t₃} (RecursorFixtures:Doc:brecOn:go {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆)

-- theorem
opaque
  RecursorFixtures:Doc:brecOn:eq : {motive1₀ : RecursorFixtures:Doc → Set} → {motive2₁ : Array RecursorFixtures:Doc → Set} → {motive3₂ : List RecursorFixtures:Doc → Set} → (t₃ : RecursorFixtures:Doc) → (F1₄ : (t₄ : RecursorFixtures:Doc) → RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} t₄ → motive1₀ t₄) → (F2₅ : (t₅ : Array RecursorFixtures:Doc) → RecursorFixtures:Doc:below~u1 {motive1₀} {motive2₁} {motive3₂} t₅ → motive2₁ t₅) → (F3₆ : (t₆ : List RecursorFixtures:Doc) → RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} t₆ → motive3₂ t₆) → Eq {motive1₀ t₃} (RecursorFixtures:Doc:brecOn {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆) (F1₄ t₃ (PProd.snd₃ {motive1₀ t₃} {RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} t₃} (RecursorFixtures:Doc:brecOn:go {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆)))
  RecursorFixtures:Doc:brecOn:eq {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆ = RecursorFixtures:Doc:casesOn {λ (x₇ : RecursorFixtures:Doc) → Eq {motive1₀ x₇} (RecursorFixtures:Doc:brecOn {motive1₀} {motive2₁} {motive3₂} x₇ F1₄ F2₅ F3₆) (F1₄ x₇ (PProd.snd₃ {motive1₀ x₇} {RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} x₇} (RecursorFixtures:Doc:brecOn:go {motive1₀} {motive2₁} {motive3₂} x₇ F1₄ F2₅ F3₆)))} t₃ (λ (n₇ : Nat) → Eq:refl {motive1₀ (RecursorFixtures:Doc:text n₇)} (RecursorFixtures:Doc:brecOn {motive1₀} {motive2₁} {motive3₂} (RecursorFixtures:Doc:text n₇) F1₄ F2₅ F3₆)) (λ (kids₇ : Array RecursorFixtures:Doc) → Eq:refl {motive1₀ (RecursorFixtures:Doc:block kids₇)} (RecursorFixtures:Doc:brecOn {motive1₀} {motive2₁} {motive3₂} (RecursorFixtures:Doc:block kids₇) F1₄ F2₅ F3₆))

RecursorFixtures:Doc:brecOn~u1:go : {motive1₀ : RecursorFixtures:Doc → Set} → {motive2₁ : Array RecursorFixtures:Doc → Set} → {motive3₂ : List RecursorFixtures:Doc → Set} → (t₃ : Array RecursorFixtures:Doc) → ((t₄ : RecursorFixtures:Doc) → RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} t₄ → motive1₀ t₄) → ((t₄ : Array RecursorFixtures:Doc) → RecursorFixtures:Doc:below~u1 {motive1₀} {motive2₁} {motive3₂} t₄ → motive2₁ t₄) → ((t₄ : List RecursorFixtures:Doc) → RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} t₄ → motive3₂ t₄) → PProd (motive2₁ t₃) (RecursorFixtures:Doc:below~u1 {motive1₀} {motive2₁} {motive3₂} t₃)
RecursorFixtures:Doc:brecOn~u1:go {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆ = RecursorFixtures:Doc:rec~u1 {λ (t₇ : RecursorFixtures:Doc) → PProd (motive1₀ t₇) (RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} t₇)} {λ (t₇ : Array RecursorFixtures:Doc) → PProd (motive2₁ t₇) (RecursorFixtures:Doc:below~u1 {motive1₀} {motive2₁} {motive3₂} t₇)} {λ (t₇ : List RecursorFixtures:Doc) → PProd (motive3₂ t₇) (RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} t₇)} (λ (n₇ : Nat) → PProd:mk {motive1₀ (RecursorFixtures:Doc:text n₇)} {PUnit} (F1₄ (RecursorFixtures:Doc:text n₇) PUnit:unit) PUnit:unit) (λ (kids₇ : Array RecursorFixtures:Doc) → λ (kidsih₈ : PProd (motive2₁ kids₇) (RecursorFixtures:Doc:below~u1 {motive1₀} {motive2₁} {motive3₂} kids₇)) → PProd:mk {motive1₀ (RecursorFixtures:Doc:block kids₇)} {PProd (motive2₁ kids₇) (RecursorFixtures:Doc:below~u1 {motive1₀} {motive2₁} {motive3₂} kids₇)} (F1₄ (RecursorFixtures:Doc:block kids₇) kidsih₈) kidsih₈) (λ (toList₇ : List RecursorFixtures:Doc) → λ (toListih₈ : PProd (motive3₂ toList₇) (RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} toList₇)) → PProd:mk {motive2₁ (Array:mk {RecursorFixtures:Doc} toList₇)} {PProd (motive3₂ toList₇) (RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} toList₇)} (F2₅ (Array:mk {RecursorFixtures:Doc} toList₇) toListih₈) toListih₈) (PProd:mk {motive3₂ (List:nil {RecursorFixtures:Doc})} {PUnit} (F3₆ (List:nil {RecursorFixtures:Doc}) PUnit:unit) PUnit:unit) (λ (head₇ : RecursorFixtures:Doc) → λ (tail₈ : List RecursorFixtures:Doc) → λ (headih₉ : PProd (motive1₀ head₇) (RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} head₇)) → λ (tailih₁₀ : PProd (motive3₂ tail₈) (RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} tail₈)) → PProd:mk {motive3₂ (List:cons {RecursorFixtures:Doc} head₇ tail₈)} {PProd (PProd (motive1₀ head₇) (RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} head₇)) (PProd (motive3₂ tail₈) (RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} tail₈))} (F3₆ (List:cons {RecursorFixtures:Doc} head₇ tail₈) (PProd:mk {PProd (motive1₀ head₇) (RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} head₇)} {PProd (motive3₂ tail₈) (RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} tail₈)} headih₉ tailih₁₀)) (PProd:mk {PProd (motive1₀ head₇) (RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} head₇)} {PProd (motive3₂ tail₈) (RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} tail₈)} headih₉ tailih₁₀)) t₃

RecursorFixtures:Doc:brecOn~u1 : {motive1₀ : RecursorFixtures:Doc → Set} → {motive2₁ : Array RecursorFixtures:Doc → Set} → {motive3₂ : List RecursorFixtures:Doc → Set} → (t₃ : Array RecursorFixtures:Doc) → ((t₄ : RecursorFixtures:Doc) → RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} t₄ → motive1₀ t₄) → ((t₄ : Array RecursorFixtures:Doc) → RecursorFixtures:Doc:below~u1 {motive1₀} {motive2₁} {motive3₂} t₄ → motive2₁ t₄) → ((t₄ : List RecursorFixtures:Doc) → RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} t₄ → motive3₂ t₄) → motive2₁ t₃
RecursorFixtures:Doc:brecOn~u1 {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆ = PProd.fst₂ {motive2₁ t₃} {RecursorFixtures:Doc:below~u1 {motive1₀} {motive2₁} {motive3₂} t₃} (RecursorFixtures:Doc:brecOn~u1:go {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆)

-- theorem
opaque
  RecursorFixtures:Doc:brecOn~u1:eq : {motive1₀ : RecursorFixtures:Doc → Set} → {motive2₁ : Array RecursorFixtures:Doc → Set} → {motive3₂ : List RecursorFixtures:Doc → Set} → (t₃ : Array RecursorFixtures:Doc) → (F1₄ : (t₄ : RecursorFixtures:Doc) → RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} t₄ → motive1₀ t₄) → (F2₅ : (t₅ : Array RecursorFixtures:Doc) → RecursorFixtures:Doc:below~u1 {motive1₀} {motive2₁} {motive3₂} t₅ → motive2₁ t₅) → (F3₆ : (t₆ : List RecursorFixtures:Doc) → RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} t₆ → motive3₂ t₆) → Eq {motive2₁ t₃} (RecursorFixtures:Doc:brecOn~u1 {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆) (F2₅ t₃ (PProd.snd₃ {motive2₁ t₃} {RecursorFixtures:Doc:below~u1 {motive1₀} {motive2₁} {motive3₂} t₃} (RecursorFixtures:Doc:brecOn~u1:go {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆)))
  RecursorFixtures:Doc:brecOn~u1:eq {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆ = Array:casesOn {RecursorFixtures:Doc} {λ (x₇ : Array RecursorFixtures:Doc) → Eq {motive2₁ x₇} (RecursorFixtures:Doc:brecOn~u1 {motive1₀} {motive2₁} {motive3₂} x₇ F1₄ F2₅ F3₆) (F2₅ x₇ (PProd.snd₃ {motive2₁ x₇} {RecursorFixtures:Doc:below~u1 {motive1₀} {motive2₁} {motive3₂} x₇} (RecursorFixtures:Doc:brecOn~u1:go {motive1₀} {motive2₁} {motive3₂} x₇ F1₄ F2₅ F3₆)))} t₃ (λ (toList₇ : List RecursorFixtures:Doc) → Eq:refl {motive2₁ (Array:mk {RecursorFixtures:Doc} toList₇)} (RecursorFixtures:Doc:brecOn~u1 {motive1₀} {motive2₁} {motive3₂} (Array:mk {RecursorFixtures:Doc} toList₇) F1₄ F2₅ F3₆))

RecursorFixtures:Doc:brecOn~u2:go : {motive1₀ : RecursorFixtures:Doc → Set} → {motive2₁ : Array RecursorFixtures:Doc → Set} → {motive3₂ : List RecursorFixtures:Doc → Set} → (t₃ : List RecursorFixtures:Doc) → ((t₄ : RecursorFixtures:Doc) → RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} t₄ → motive1₀ t₄) → ((t₄ : Array RecursorFixtures:Doc) → RecursorFixtures:Doc:below~u1 {motive1₀} {motive2₁} {motive3₂} t₄ → motive2₁ t₄) → ((t₄ : List RecursorFixtures:Doc) → RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} t₄ → motive3₂ t₄) → PProd (motive3₂ t₃) (RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} t₃)
RecursorFixtures:Doc:brecOn~u2:go {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆ = RecursorFixtures:Doc:rec~u2 {λ (t₇ : RecursorFixtures:Doc) → PProd (motive1₀ t₇) (RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} t₇)} {λ (t₇ : Array RecursorFixtures:Doc) → PProd (motive2₁ t₇) (RecursorFixtures:Doc:below~u1 {motive1₀} {motive2₁} {motive3₂} t₇)} {λ (t₇ : List RecursorFixtures:Doc) → PProd (motive3₂ t₇) (RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} t₇)} (λ (n₇ : Nat) → PProd:mk {motive1₀ (RecursorFixtures:Doc:text n₇)} {PUnit} (F1₄ (RecursorFixtures:Doc:text n₇) PUnit:unit) PUnit:unit) (λ (kids₇ : Array RecursorFixtures:Doc) → λ (kidsih₈ : PProd (motive2₁ kids₇) (RecursorFixtures:Doc:below~u1 {motive1₀} {motive2₁} {motive3₂} kids₇)) → PProd:mk {motive1₀ (RecursorFixtures:Doc:block kids₇)} {PProd (motive2₁ kids₇) (RecursorFixtures:Doc:below~u1 {motive1₀} {motive2₁} {motive3₂} kids₇)} (F1₄ (RecursorFixtures:Doc:block kids₇) kidsih₈) kidsih₈) (λ (toList₇ : List RecursorFixtures:Doc) → λ (toListih₈ : PProd (motive3₂ toList₇) (RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} toList₇)) → PProd:mk {motive2₁ (Array:mk {RecursorFixtures:Doc} toList₇)} {PProd (motive3₂ toList₇) (RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} toList₇)} (F2₅ (Array:mk {RecursorFixtures:Doc} toList₇) toListih₈) toListih₈) (PProd:mk {motive3₂ (List:nil {RecursorFixtures:Doc})} {PUnit} (F3₆ (List:nil {RecursorFixtures:Doc}) PUnit:unit) PUnit:unit) (λ (head₇ : RecursorFixtures:Doc) → λ (tail₈ : List RecursorFixtures:Doc) → λ (headih₉ : PProd (motive1₀ head₇) (RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} head₇)) → λ (tailih₁₀ : PProd (motive3₂ tail₈) (RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} tail₈)) → PProd:mk {motive3₂ (List:cons {RecursorFixtures:Doc} head₇ tail₈)} {PProd (PProd (motive1₀ head₇) (RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} head₇)) (PProd (motive3₂ tail₈) (RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} tail₈))} (F3₆ (List:cons {RecursorFixtures:Doc} head₇ tail₈) (PProd:mk {PProd (motive1₀ head₇) (RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} head₇)} {PProd (motive3₂ tail₈) (RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} tail₈)} headih₉ tailih₁₀)) (PProd:mk {PProd (motive1₀ head₇) (RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} head₇)} {PProd (motive3₂ tail₈) (RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} tail₈)} headih₉ tailih₁₀)) t₃

RecursorFixtures:Doc:brecOn~u2 : {motive1₀ : RecursorFixtures:Doc → Set} → {motive2₁ : Array RecursorFixtures:Doc → Set} → {motive3₂ : List RecursorFixtures:Doc → Set} → (t₃ : List RecursorFixtures:Doc) → ((t₄ : RecursorFixtures:Doc) → RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} t₄ → motive1₀ t₄) → ((t₄ : Array RecursorFixtures:Doc) → RecursorFixtures:Doc:below~u1 {motive1₀} {motive2₁} {motive3₂} t₄ → motive2₁ t₄) → ((t₄ : List RecursorFixtures:Doc) → RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} t₄ → motive3₂ t₄) → motive3₂ t₃
RecursorFixtures:Doc:brecOn~u2 {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆ = PProd.fst₂ {motive3₂ t₃} {RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} t₃} (RecursorFixtures:Doc:brecOn~u2:go {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆)

-- theorem
opaque
  RecursorFixtures:Doc:brecOn~u2:eq : {motive1₀ : RecursorFixtures:Doc → Set} → {motive2₁ : Array RecursorFixtures:Doc → Set} → {motive3₂ : List RecursorFixtures:Doc → Set} → (t₃ : List RecursorFixtures:Doc) → (F1₄ : (t₄ : RecursorFixtures:Doc) → RecursorFixtures:Doc:below {motive1₀} {motive2₁} {motive3₂} t₄ → motive1₀ t₄) → (F2₅ : (t₅ : Array RecursorFixtures:Doc) → RecursorFixtures:Doc:below~u1 {motive1₀} {motive2₁} {motive3₂} t₅ → motive2₁ t₅) → (F3₆ : (t₆ : List RecursorFixtures:Doc) → RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} t₆ → motive3₂ t₆) → Eq {motive3₂ t₃} (RecursorFixtures:Doc:brecOn~u2 {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆) (F3₆ t₃ (PProd.snd₃ {motive3₂ t₃} {RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} t₃} (RecursorFixtures:Doc:brecOn~u2:go {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆)))
  RecursorFixtures:Doc:brecOn~u2:eq {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆ = List:casesOn {RecursorFixtures:Doc} {λ (x₇ : List RecursorFixtures:Doc) → Eq {motive3₂ x₇} (RecursorFixtures:Doc:brecOn~u2 {motive1₀} {motive2₁} {motive3₂} x₇ F1₄ F2₅ F3₆) (F3₆ x₇ (PProd.snd₃ {motive3₂ x₇} {RecursorFixtures:Doc:below~u2 {motive1₀} {motive2₁} {motive3₂} x₇} (RecursorFixtures:Doc:brecOn~u2:go {motive1₀} {motive2₁} {motive3₂} x₇ F1₄ F2₅ F3₆)))} t₃ (Eq:refl {motive3₂ (List:nil {RecursorFixtures:Doc})} (RecursorFixtures:Doc:brecOn~u2 {motive1₀} {motive2₁} {motive3₂} (List:nil {RecursorFixtures:Doc}) F1₄ F2₅ F3₆)) (λ (head₇ : RecursorFixtures:Doc) → λ (tail₈ : List RecursorFixtures:Doc) → Eq:refl {motive3₂ (List:cons {RecursorFixtures:Doc} head₇ tail₈)} (RecursorFixtures:Doc:brecOn~u2 {motive1₀} {motive2₁} {motive3₂} (List:cons {RecursorFixtures:Doc} head₇ tail₈) F1₄ F2₅ F3₆))

RecursorFixtures:Doc:recOn : {motive1₀ : RecursorFixtures:Doc → Set} → {motive2₁ : Array RecursorFixtures:Doc → Set} → {motive3₂ : List RecursorFixtures:Doc → Set} → (t₃ : RecursorFixtures:Doc) → ((n₄ : Nat) → motive1₀ (RecursorFixtures:Doc:text n₄)) → ((kids₄ : Array RecursorFixtures:Doc) → motive2₁ kids₄ → motive1₀ (RecursorFixtures:Doc:block kids₄)) → ((toList₄ : List RecursorFixtures:Doc) → motive3₂ toList₄ → motive2₁ (Array:mk {RecursorFixtures:Doc} toList₄)) → motive3₂ (List:nil {RecursorFixtures:Doc}) → ((head₄ : RecursorFixtures:Doc) → (tail₅ : List RecursorFixtures:Doc) → motive1₀ head₄ → motive3₂ tail₅ → motive3₂ (List:cons {RecursorFixtures:Doc} head₄ tail₅)) → motive1₀ t₃
RecursorFixtures:Doc:recOn {motive1₀} {motive2₁} {motive3₂} t₃ text₄ block₅ mk₆ nil₇ cons₈ = RecursorFixtures:Doc:rec {motive1₀} {motive2₁} {motive3₂} text₄ block₅ mk₆ nil₇ cons₈ t₃

RecursorFixtures:Doc:text:elim : {motive1₀ : RecursorFixtures:Doc → Set} → (t₁ : RecursorFixtures:Doc) → Eq {Nat} (RecursorFixtures:Doc:ctorIdx t₁) 0 → ((n₂ : Nat) → motive1₀ (RecursorFixtures:Doc:text n₂)) → motive1₀ t₁
RecursorFixtures:Doc:text:elim {motive1₀} t₁ h₂ text₃ = RecursorFixtures:Doc:ctorElim {motive1₀} 0 t₁ (Eq:symm {Nat} {RecursorFixtures:Doc:ctorIdx t₁} {0} h₂) (PULift:up {(n₄ : Nat) → motive1₀ (RecursorFixtures:Doc:text n₄)} text₃)

RecursorFixtures:Doc:text:noConfusion : {P₀ : Set} → {n₁ : Nat} → {n₂ : Nat} → Eq {RecursorFixtures:Doc} (RecursorFixtures:Doc:text n₁) (RecursorFixtures:Doc:text n₂) → (Eq {Nat} n₁ n₂ → P₀) → P₀
RecursorFixtures:Doc:text:noConfusion {P₀} {n₁} {n₂} eq₃ k₄ = id {P₀} (RecursorFixtures:Doc:noConfusion {P₀} {RecursorFixtures:Doc:text n₁} {RecursorFixtures:Doc:text n₂} eq₃ k₄)

-- theorem
opaque
  RecursorFixtures:Doc:text:inj : {n₀ : Nat} → {n₁ : Nat} → Eq {RecursorFixtures:Doc} (RecursorFixtures:Doc:text n₀) (RecursorFixtures:Doc:text n₁) → Eq {Nat} n₀ n₁
  RecursorFixtures:Doc:text:inj {n₀} {n₁} x₂ = RecursorFixtures:Doc:text:noConfusion {Eq {Nat} n₀ n₁} {n₀} {n₁} x₂ (λ (neq₃ : Eq {Nat} n₀ n₁) → neq₃)

-- theorem
opaque
  RecursorFixtures:Doc:text:injEq : (n₀ : Nat) → (n₁ : Nat) → Eq {Set} (Eq {RecursorFixtures:Doc} (RecursorFixtures:Doc:text n₀) (RecursorFixtures:Doc:text n₁)) (Eq {Nat} n₀ n₁)
  RecursorFixtures:Doc:text:injEq n₀ n₁ = Eq:propIntro {Eq {RecursorFixtures:Doc} (RecursorFixtures:Doc:text n₀) (RecursorFixtures:Doc:text n₁)} {Eq {Nat} n₀ n₁} (RecursorFixtures:Doc:text:inj {n₀} {n₁}) (Eq:ndrec {Nat} {n₀} {λ (n₂ : Nat) → Eq {RecursorFixtures:Doc} (RecursorFixtures:Doc:text n₀) (RecursorFixtures:Doc:text n₂)} (Eq:refl {RecursorFixtures:Doc} (RecursorFixtures:Doc:text n₀)) {n₁})

-- theorem
opaque
  RecursorFixtures:Doc:text:sizeOf~uspec : (n₀ : Nat) → Eq {Nat} (SizeOf:sizeOf {RecursorFixtures:Doc} ⦃ RecursorFixtures:Doc:~usizeOf~uinst ⦄ (RecursorFixtures:Doc:text n₀)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {Nat} ⦃ instSizeOfNat ⦄ n₀))
  RecursorFixtures:Doc:text:sizeOf~uspec n₀ = Eq:refl {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {Nat} ⦃ instSizeOfNat ⦄ n₀))

RecursorFixtures:Doc:total : RecursorFixtures:Doc → Nat
RecursorFixtures:Doc:total d₀ = RecursorFixtures:Doc:rec {λ (x₁ : RecursorFixtures:Doc) → Nat} {λ (x₁ : Array RecursorFixtures:Doc) → Nat} {λ (x₁ : List RecursorFixtures:Doc) → Nat} (λ (n₁ : Nat) → n₁) (λ (x₁ : Array RecursorFixtures:Doc) → λ (s₂ : Nat) → s₂) (λ (x₁ : List RecursorFixtures:Doc) → λ (s₂ : Nat) → s₂) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (λ (x₁ : RecursorFixtures:Doc) → λ (x₂ : List RecursorFixtures:Doc) → λ (a₃ : Nat) → λ (b₄ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ a₃ b₄) d₀

RecursorFixtures:Doc:total~uexample:~ushare:~n1 : Nat
RecursorFixtures:Doc:total~uexample:~ushare:~n1 = RecursorFixtures:Doc:total (RecursorFixtures:Doc:block (List:toArray {RecursorFixtures:Doc} (List:cons {RecursorFixtures:Doc} (RecursorFixtures:Doc:text (OfNat:ofNat {Nat} 2 ⦃ instOfNatNat 2 ⦄)) (List:cons {RecursorFixtures:Doc} (RecursorFixtures:Doc:block (List:toArray {RecursorFixtures:Doc} (List:cons {RecursorFixtures:Doc} (RecursorFixtures:Doc:text (OfNat:ofNat {Nat} 3 ⦃ instOfNatNat 3 ⦄)) (List:nil {RecursorFixtures:Doc})))) (List:cons {RecursorFixtures:Doc} (RecursorFixtures:Doc:text (OfNat:ofNat {Nat} 4 ⦃ instOfNatNat 4 ⦄)) (List:nil {RecursorFixtures:Doc}))))))

-- theorem
opaque
  RecursorFixtures:Doc:total~uexample : Eq {Nat} RecursorFixtures:Doc:total~uexample:~ushare:~n1 (OfNat:ofNat {Nat} 9 ⦃ instOfNatNat 9 ⦄)
  RecursorFixtures:Doc:total~uexample = rfl {Nat} {RecursorFixtures:Doc:total~uexample:~ushare:~n1}

mutual
  data RecursorFixtures:Even : Set where
    RecursorFixtures:Even:zero : RecursorFixtures:Even
    RecursorFixtures:Even:succ : RecursorFixtures:Odd → RecursorFixtures:Even
  record RecursorFixtures:Odd : Set where
    inductive
    no-eta-equality
    pattern
    constructor RecursorFixtures:Odd:succ
    field
      e₀ : RecursorFixtures:Even

-- recursor
mutual
  RecursorFixtures:Even:rec : {motive1₀ : RecursorFixtures:Even → Set} → {motive2₁ : RecursorFixtures:Odd → Set} → motive1₀ RecursorFixtures:Even:zero → ((o₂ : RecursorFixtures:Odd) → motive2₁ o₂ → motive1₀ (RecursorFixtures:Even:succ o₂)) → ((e₂ : RecursorFixtures:Even) → motive1₀ e₂ → motive2₁ (RecursorFixtures:Odd:succ e₂)) → (t₂ : RecursorFixtures:Even) → motive1₀ t₂
  RecursorFixtures:Odd:rec : {motive1₀ : RecursorFixtures:Even → Set} → {motive2₁ : RecursorFixtures:Odd → Set} → motive1₀ RecursorFixtures:Even:zero → ((o₂ : RecursorFixtures:Odd) → motive2₁ o₂ → motive1₀ (RecursorFixtures:Even:succ o₂)) → ((e₂ : RecursorFixtures:Even) → motive1₀ e₂ → motive2₁ (RecursorFixtures:Odd:succ e₂)) → (t₂ : RecursorFixtures:Odd) → motive2₁ t₂
  RecursorFixtures:Even:rec {motive1₀} {motive2₁} zero₂ succ₃ succ₄ RecursorFixtures:Even:zero = zero₂
  RecursorFixtures:Even:rec {motive1₀} {motive2₁} zero₂ succ₃ succ₄ (RecursorFixtures:Even:succ o₅) = succ₃ o₅ (RecursorFixtures:Odd:rec {motive1₀} {motive2₁} zero₂ succ₃ succ₄ o₅)
  RecursorFixtures:Odd:rec {motive1₀} {motive2₁} zero₂ succ₃ succ₄ (RecursorFixtures:Odd:succ e₅) = succ₄ e₅ (RecursorFixtures:Even:rec {motive1₀} {motive2₁} zero₂ succ₃ succ₄ e₅)

RecursorFixtures:Even:~usizeOf~u1 : RecursorFixtures:Even → Nat
RecursorFixtures:Even:~usizeOf~u1 t₀ = RecursorFixtures:Even:rec {λ (t₁ : RecursorFixtures:Even) → Nat} {λ (t₁ : RecursorFixtures:Odd) → Nat} (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (λ (o₁ : RecursorFixtures:Odd) → λ (oih₂ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) oih₂) (λ (e₁ : RecursorFixtures:Even) → λ (eih₂ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) eih₂) t₀

RecursorFixtures:Even:~usizeOf~u2 : RecursorFixtures:Odd → Nat
RecursorFixtures:Even:~usizeOf~u2 t₀ = RecursorFixtures:Odd:rec {λ (t₁ : RecursorFixtures:Even) → Nat} {λ (t₁ : RecursorFixtures:Odd) → Nat} (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (λ (o₁ : RecursorFixtures:Odd) → λ (oih₂ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) oih₂) (λ (e₁ : RecursorFixtures:Even) → λ (eih₂ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) eih₂) t₀

RecursorFixtures:Even:~usizeOf~uinst : SizeOf RecursorFixtures:Even
RecursorFixtures:Even:~usizeOf~uinst = SizeOf:mk {RecursorFixtures:Even} (λ (m₀ : RecursorFixtures:Even) → RecursorFixtures:Even:~usizeOf~u1 m₀)

RecursorFixtures:Even:below : {_ : RecursorFixtures:Even → Set} → {_ : RecursorFixtures:Odd → Set} → RecursorFixtures:Even → Set
RecursorFixtures:Even:below {motive1₀} {motive2₁} t₂ = RecursorFixtures:Even:rec {λ (t₃ : RecursorFixtures:Even) → Set} {λ (t₃ : RecursorFixtures:Odd) → Set} PUnit (λ (o₃ : RecursorFixtures:Odd) → λ (oih₄ : Set) → PProd (motive2₁ o₃) oih₄) (λ (e₃ : RecursorFixtures:Even) → λ (eih₄ : Set) → PProd (motive1₀ e₃) eih₄) t₂

RecursorFixtures:Odd:below : {_ : RecursorFixtures:Even → Set} → {_ : RecursorFixtures:Odd → Set} → RecursorFixtures:Odd → Set
RecursorFixtures:Odd:below {motive1₀} {motive2₁} t₂ = RecursorFixtures:Odd:rec {λ (t₃ : RecursorFixtures:Even) → Set} {λ (t₃ : RecursorFixtures:Odd) → Set} PUnit (λ (o₃ : RecursorFixtures:Odd) → λ (oih₄ : Set) → PProd (motive2₁ o₃) oih₄) (λ (e₃ : RecursorFixtures:Even) → λ (eih₄ : Set) → PProd (motive1₀ e₃) eih₄) t₂

RecursorFixtures:Even:brecOn:go : {motive1₀ : RecursorFixtures:Even → Set} → {motive2₁ : RecursorFixtures:Odd → Set} → (t₂ : RecursorFixtures:Even) → ((t₃ : RecursorFixtures:Even) → RecursorFixtures:Even:below {motive1₀} {motive2₁} t₃ → motive1₀ t₃) → ((t₃ : RecursorFixtures:Odd) → RecursorFixtures:Odd:below {motive1₀} {motive2₁} t₃ → motive2₁ t₃) → PProd (motive1₀ t₂) (RecursorFixtures:Even:below {motive1₀} {motive2₁} t₂)
RecursorFixtures:Even:brecOn:go {motive1₀} {motive2₁} t₂ F1₃ F2₄ = RecursorFixtures:Even:rec {λ (t₅ : RecursorFixtures:Even) → PProd (motive1₀ t₅) (RecursorFixtures:Even:below {motive1₀} {motive2₁} t₅)} {λ (t₅ : RecursorFixtures:Odd) → PProd (motive2₁ t₅) (RecursorFixtures:Odd:below {motive1₀} {motive2₁} t₅)} (PProd:mk {motive1₀ RecursorFixtures:Even:zero} {PUnit} (F1₃ RecursorFixtures:Even:zero PUnit:unit) PUnit:unit) (λ (o₅ : RecursorFixtures:Odd) → λ (oih₆ : PProd (motive2₁ o₅) (RecursorFixtures:Odd:below {motive1₀} {motive2₁} o₅)) → PProd:mk {motive1₀ (RecursorFixtures:Even:succ o₅)} {PProd (motive2₁ o₅) (RecursorFixtures:Odd:below {motive1₀} {motive2₁} o₅)} (F1₃ (RecursorFixtures:Even:succ o₅) oih₆) oih₆) (λ (e₅ : RecursorFixtures:Even) → λ (eih₆ : PProd (motive1₀ e₅) (RecursorFixtures:Even:below {motive1₀} {motive2₁} e₅)) → PProd:mk {motive2₁ (RecursorFixtures:Odd:succ e₅)} {PProd (motive1₀ e₅) (RecursorFixtures:Even:below {motive1₀} {motive2₁} e₅)} (F2₄ (RecursorFixtures:Odd:succ e₅) eih₆) eih₆) t₂

RecursorFixtures:Even:brecOn : {motive1₀ : RecursorFixtures:Even → Set} → {motive2₁ : RecursorFixtures:Odd → Set} → (t₂ : RecursorFixtures:Even) → ((t₃ : RecursorFixtures:Even) → RecursorFixtures:Even:below {motive1₀} {motive2₁} t₃ → motive1₀ t₃) → ((t₃ : RecursorFixtures:Odd) → RecursorFixtures:Odd:below {motive1₀} {motive2₁} t₃ → motive2₁ t₃) → motive1₀ t₂
RecursorFixtures:Even:brecOn {motive1₀} {motive2₁} t₂ F1₃ F2₄ = PProd.fst₂ {motive1₀ t₂} {RecursorFixtures:Even:below {motive1₀} {motive2₁} t₂} (RecursorFixtures:Even:brecOn:go {motive1₀} {motive2₁} t₂ F1₃ F2₄)

RecursorFixtures:Even:casesOn : {motive1₀ : RecursorFixtures:Even → Set} → (t₁ : RecursorFixtures:Even) → motive1₀ RecursorFixtures:Even:zero → ((o₂ : RecursorFixtures:Odd) → motive1₀ (RecursorFixtures:Even:succ o₂)) → motive1₀ t₁
RecursorFixtures:Even:casesOn {motive1₀} t₁ zero₂ succ₃ = RecursorFixtures:Even:rec {motive1₀} {λ (t₄ : RecursorFixtures:Odd) → PUnit} zero₂ (λ (o₄ : RecursorFixtures:Odd) → λ (oih₅ : PUnit) → succ₃ o₄) (λ (e₄ : RecursorFixtures:Even) → λ (eih₅ : motive1₀ e₄) → PUnit:unit) t₁

-- theorem
opaque
  RecursorFixtures:Even:brecOn:eq : {motive1₀ : RecursorFixtures:Even → Set} → {motive2₁ : RecursorFixtures:Odd → Set} → (t₂ : RecursorFixtures:Even) → (F1₃ : (t₃ : RecursorFixtures:Even) → RecursorFixtures:Even:below {motive1₀} {motive2₁} t₃ → motive1₀ t₃) → (F2₄ : (t₄ : RecursorFixtures:Odd) → RecursorFixtures:Odd:below {motive1₀} {motive2₁} t₄ → motive2₁ t₄) → Eq {motive1₀ t₂} (RecursorFixtures:Even:brecOn {motive1₀} {motive2₁} t₂ F1₃ F2₄) (F1₃ t₂ (PProd.snd₃ {motive1₀ t₂} {RecursorFixtures:Even:below {motive1₀} {motive2₁} t₂} (RecursorFixtures:Even:brecOn:go {motive1₀} {motive2₁} t₂ F1₃ F2₄)))
  RecursorFixtures:Even:brecOn:eq {motive1₀} {motive2₁} t₂ F1₃ F2₄ = RecursorFixtures:Even:casesOn {λ (x₅ : RecursorFixtures:Even) → Eq {motive1₀ x₅} (RecursorFixtures:Even:brecOn {motive1₀} {motive2₁} x₅ F1₃ F2₄) (F1₃ x₅ (PProd.snd₃ {motive1₀ x₅} {RecursorFixtures:Even:below {motive1₀} {motive2₁} x₅} (RecursorFixtures:Even:brecOn:go {motive1₀} {motive2₁} x₅ F1₃ F2₄)))} t₂ (Eq:refl {motive1₀ RecursorFixtures:Even:zero} (RecursorFixtures:Even:brecOn {motive1₀} {motive2₁} RecursorFixtures:Even:zero F1₃ F2₄)) (λ (o₅ : RecursorFixtures:Odd) → Eq:refl {motive1₀ (RecursorFixtures:Even:succ o₅)} (RecursorFixtures:Even:brecOn {motive1₀} {motive2₁} (RecursorFixtures:Even:succ o₅) F1₃ F2₄))

RecursorFixtures:Even:ctorElimType : {_ : RecursorFixtures:Even → Set} → Nat → Set
RecursorFixtures:Even:ctorElimType {motive1₀} ctorIdx₁ = cond {Set} (Nat:ble ctorIdx₁ 0) (PULift (motive1₀ RecursorFixtures:Even:zero)) (PULift ((o₂ : RecursorFixtures:Odd) → motive1₀ (RecursorFixtures:Even:succ o₂)))

RecursorFixtures:Even:ctorIdx : RecursorFixtures:Even → Nat
RecursorFixtures:Even:ctorIdx x₀ = RecursorFixtures:Even:casesOn {λ (x₁ : RecursorFixtures:Even) → Nat} x₀ 0 (λ (o₁ : RecursorFixtures:Odd) → 1)

RecursorFixtures:Even:ctorElim : {motive1₀ : RecursorFixtures:Even → Set} → (ctorIdx₁ : Nat) → (t₂ : RecursorFixtures:Even) → Eq {Nat} ctorIdx₁ (RecursorFixtures:Even:ctorIdx t₂) → RecursorFixtures:Even:ctorElimType {motive1₀} ctorIdx₁ → motive1₀ t₂
RecursorFixtures:Even:ctorElim {motive1₀} ctorIdx₁ t₂ h₃ k₄ = RecursorFixtures:Even:casesOn {λ (t₅ : RecursorFixtures:Even) → Eq {Nat} ctorIdx₁ (RecursorFixtures:Even:ctorIdx t₅) → motive1₀ t₅} t₂ (λ (h₅ : Eq {Nat} ctorIdx₁ 0) → PULift:down {motive1₀ RecursorFixtures:Even:zero} (Eq:ndrec {Nat} {ctorIdx₁} {RecursorFixtures:Even:ctorElimType {motive1₀}} k₄ {0} h₅)) (λ (o₅ : RecursorFixtures:Odd) → λ (h₆ : Eq {Nat} ctorIdx₁ 1) → PULift:down {(o₇ : RecursorFixtures:Odd) → motive1₀ (RecursorFixtures:Even:succ o₇)} (Eq:ndrec {Nat} {ctorIdx₁} {RecursorFixtures:Even:ctorElimType {motive1₀}} k₄ {1} h₆) o₅) h₃

RecursorFixtures:Even:noConfusionType : Set → RecursorFixtures:Even → RecursorFixtures:Even → Set
RecursorFixtures:Even:noConfusionType P₀ t₁ t₂ = RecursorFixtures:Even:casesOn {λ (t₃ : RecursorFixtures:Even) → Set} t₁ (RecursorFixtures:Even:casesOn {λ (t₃ : RecursorFixtures:Even) → Set} t₂ (P₀ → P₀) (λ (o₃ : RecursorFixtures:Odd) → P₀)) (λ (o₃ : RecursorFixtures:Odd) → RecursorFixtures:Even:casesOn {λ (t₄ : RecursorFixtures:Even) → Set} t₂ P₀ (λ (o₄ : RecursorFixtures:Odd) → (Eq {RecursorFixtures:Odd} o₃ o₄ → P₀) → P₀))

RecursorFixtures:Even:noConfusion : {P₀ : Set} → {t₁ : RecursorFixtures:Even} → {t₂ : RecursorFixtures:Even} → Eq {RecursorFixtures:Even} t₁ t₂ → RecursorFixtures:Even:noConfusionType P₀ t₁ t₂
RecursorFixtures:Even:noConfusion {P₀} {t₁} {t₂} eq₃ = Eq:ndrec {RecursorFixtures:Even} {t₁} {λ (t₄ : RecursorFixtures:Even) → RecursorFixtures:Even:noConfusionType P₀ t₁ t₄} (RecursorFixtures:Even:casesOn {λ (t₄ : RecursorFixtures:Even) → RecursorFixtures:Even:noConfusionType P₀ t₄ t₄} t₁ (λ (k₄ : P₀) → k₄) (λ (o₄ : RecursorFixtures:Odd) → λ (k₅ : Eq {RecursorFixtures:Odd} o₄ o₄ → P₀) → k₅ (Eq:refl {RecursorFixtures:Odd} o₄))) {t₂} eq₃

RecursorFixtures:Even:recOn : {motive1₀ : RecursorFixtures:Even → Set} → {motive2₁ : RecursorFixtures:Odd → Set} → (t₂ : RecursorFixtures:Even) → motive1₀ RecursorFixtures:Even:zero → ((o₃ : RecursorFixtures:Odd) → motive2₁ o₃ → motive1₀ (RecursorFixtures:Even:succ o₃)) → ((e₃ : RecursorFixtures:Even) → motive1₀ e₃ → motive2₁ (RecursorFixtures:Odd:succ e₃)) → motive1₀ t₂
RecursorFixtures:Even:recOn {motive1₀} {motive2₁} t₂ zero₃ succ₄ succ₅ = RecursorFixtures:Even:rec {motive1₀} {motive2₁} zero₃ succ₄ succ₅ t₂

RecursorFixtures:Even:succ:elim : {motive1₀ : RecursorFixtures:Even → Set} → (t₁ : RecursorFixtures:Even) → Eq {Nat} (RecursorFixtures:Even:ctorIdx t₁) 1 → ((o₂ : RecursorFixtures:Odd) → motive1₀ (RecursorFixtures:Even:succ o₂)) → motive1₀ t₁
RecursorFixtures:Even:succ:elim {motive1₀} t₁ h₂ succ₃ = RecursorFixtures:Even:ctorElim {motive1₀} 1 t₁ (Eq:symm {Nat} {RecursorFixtures:Even:ctorIdx t₁} {1} h₂) (PULift:up {(o₄ : RecursorFixtures:Odd) → motive1₀ (RecursorFixtures:Even:succ o₄)} succ₃)

RecursorFixtures:Even:succ:noConfusion : {P₀ : Set} → {o₁ : RecursorFixtures:Odd} → {o₂ : RecursorFixtures:Odd} → Eq {RecursorFixtures:Even} (RecursorFixtures:Even:succ o₁) (RecursorFixtures:Even:succ o₂) → (Eq {RecursorFixtures:Odd} o₁ o₂ → P₀) → P₀
RecursorFixtures:Even:succ:noConfusion {P₀} {o₁} {o₂} eq₃ k₄ = id {P₀} (RecursorFixtures:Even:noConfusion {P₀} {RecursorFixtures:Even:succ o₁} {RecursorFixtures:Even:succ o₂} eq₃ k₄)

-- theorem
opaque
  RecursorFixtures:Even:succ:inj : {o₀ : RecursorFixtures:Odd} → {o₁ : RecursorFixtures:Odd} → Eq {RecursorFixtures:Even} (RecursorFixtures:Even:succ o₀) (RecursorFixtures:Even:succ o₁) → Eq {RecursorFixtures:Odd} o₀ o₁
  RecursorFixtures:Even:succ:inj {o₀} {o₁} x₂ = RecursorFixtures:Even:succ:noConfusion {Eq {RecursorFixtures:Odd} o₀ o₁} {o₀} {o₁} x₂ (λ (oeq₃ : Eq {RecursorFixtures:Odd} o₀ o₁) → oeq₃)

-- theorem
opaque
  RecursorFixtures:Even:succ:injEq : (o₀ : RecursorFixtures:Odd) → (o₁ : RecursorFixtures:Odd) → Eq {Set} (Eq {RecursorFixtures:Even} (RecursorFixtures:Even:succ o₀) (RecursorFixtures:Even:succ o₁)) (Eq {RecursorFixtures:Odd} o₀ o₁)
  RecursorFixtures:Even:succ:injEq o₀ o₁ = Eq:propIntro {Eq {RecursorFixtures:Even} (RecursorFixtures:Even:succ o₀) (RecursorFixtures:Even:succ o₁)} {Eq {RecursorFixtures:Odd} o₀ o₁} (RecursorFixtures:Even:succ:inj {o₀} {o₁}) (Eq:ndrec {RecursorFixtures:Odd} {o₀} {λ (o₂ : RecursorFixtures:Odd) → Eq {RecursorFixtures:Even} (RecursorFixtures:Even:succ o₀) (RecursorFixtures:Even:succ o₂)} (Eq:refl {RecursorFixtures:Even} (RecursorFixtures:Even:succ o₀)) {o₁})

RecursorFixtures:Odd:~usizeOf~uinst : SizeOf RecursorFixtures:Odd
RecursorFixtures:Odd:~usizeOf~uinst = SizeOf:mk {RecursorFixtures:Odd} (λ (m₀ : RecursorFixtures:Odd) → RecursorFixtures:Even:~usizeOf~u2 m₀)

-- theorem
opaque
  RecursorFixtures:Even:succ:sizeOf~uspec : (o₀ : RecursorFixtures:Odd) → Eq {Nat} (SizeOf:sizeOf {RecursorFixtures:Even} ⦃ RecursorFixtures:Even:~usizeOf~uinst ⦄ (RecursorFixtures:Even:succ o₀)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {RecursorFixtures:Odd} ⦃ RecursorFixtures:Odd:~usizeOf~uinst ⦄ o₀))
  RecursorFixtures:Even:succ:sizeOf~uspec o₀ = Eq:refl {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {RecursorFixtures:Odd} ⦃ RecursorFixtures:Odd:~usizeOf~uinst ⦄ o₀))

RecursorFixtures:Even:toNat : RecursorFixtures:Even → Nat
RecursorFixtures:Even:toNat e₀ = RecursorFixtures:Even:rec {λ (x₁ : RecursorFixtures:Even) → Nat} {λ (x₁ : RecursorFixtures:Odd) → Nat} (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (λ (x₁ : RecursorFixtures:Odd) → λ (n₂ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₂ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (λ (x₁ : RecursorFixtures:Even) → λ (n₂ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₂ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) e₀

-- theorem
opaque
  RecursorFixtures:Even:toNat~uexample : Eq {Nat} (RecursorFixtures:Even:toNat (RecursorFixtures:Even:succ (RecursorFixtures:Odd:succ (RecursorFixtures:Even:succ (RecursorFixtures:Odd:succ RecursorFixtures:Even:zero))))) (OfNat:ofNat {Nat} 4 ⦃ instOfNatNat 4 ⦄)
  RecursorFixtures:Even:toNat~uexample = rfl {Nat} {RecursorFixtures:Even:toNat (RecursorFixtures:Even:succ (RecursorFixtures:Odd:succ (RecursorFixtures:Even:succ (RecursorFixtures:Odd:succ RecursorFixtures:Even:zero))))}

RecursorFixtures:Even:zero:elim : {motive1₀ : RecursorFixtures:Even → Set} → (t₁ : RecursorFixtures:Even) → Eq {Nat} (RecursorFixtures:Even:ctorIdx t₁) 0 → motive1₀ RecursorFixtures:Even:zero → motive1₀ t₁
RecursorFixtures:Even:zero:elim {motive1₀} t₁ h₂ zero₃ = RecursorFixtures:Even:ctorElim {motive1₀} 0 t₁ (Eq:symm {Nat} {RecursorFixtures:Even:ctorIdx t₁} {0} h₂) (PULift:up {motive1₀ RecursorFixtures:Even:zero} zero₃)

-- theorem
opaque
  RecursorFixtures:Even:zero:sizeOf~uspec : Eq {Nat} (SizeOf:sizeOf {RecursorFixtures:Even} ⦃ RecursorFixtures:Even:~usizeOf~uinst ⦄ RecursorFixtures:Even:zero) (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)
  RecursorFixtures:Even:zero:sizeOf~uspec = Eq:refl {Nat} (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)

record RecursorFixtures:Tag (α₀ : Set) : Set where
  constructor RecursorFixtures:Tag:mk
  field
    tag₁ : Nat

-- recursor
RecursorFixtures:Tag:rec : {α₀ : Set} → {motive₁ : RecursorFixtures:Tag α₀ → Set} → ((tag₂ : Nat) → motive₁ (RecursorFixtures:Tag:mk {α₀} tag₂)) → (t₂ : RecursorFixtures:Tag α₀) → motive₁ t₂
RecursorFixtures:Tag:rec {α₀} {motive₁} mk₂ (RecursorFixtures:Tag:mk tag₃) = mk₂ tag₃

data RecursorFixtures:Holder (α₀ : Set) : Set where
  RecursorFixtures:Holder:nil : RecursorFixtures:Holder α₀
  RecursorFixtures:Holder:mk : {_ : Nat} → ⦃ _ : RecursorFixtures:Tag α₀ ⦄ → RecursorFixtures:Holder α₀ → RecursorFixtures:Holder α₀

-- recursor
RecursorFixtures:Holder:rec : {α₀ : Set} → {motive₁ : RecursorFixtures:Holder α₀ → Set} → motive₁ (RecursorFixtures:Holder:nil {α₀}) → ({n₂ : Nat} → ⦃ inst₃ : RecursorFixtures:Tag α₀ ⦄ → (rest₄ : RecursorFixtures:Holder α₀) → motive₁ rest₄ → motive₁ (RecursorFixtures:Holder:mk {α₀} {n₂} ⦃ inst₃ ⦄ rest₄)) → (t₂ : RecursorFixtures:Holder α₀) → motive₁ t₂
RecursorFixtures:Holder:rec {α₀} {motive₁} nil₂ mk₃ RecursorFixtures:Holder:nil = nil₂
RecursorFixtures:Holder:rec {α₀} {motive₁} nil₂ mk₃ (RecursorFixtures:Holder:mk {n₄} ⦃ inst₅ ⦄ rest₆) = mk₃ {n₄} ⦃ inst₅ ⦄ rest₆ (RecursorFixtures:Holder:rec {α₀} {motive₁} nil₂ (λ {n₇ : Nat} → λ ⦃ inst₈ : RecursorFixtures:Tag α₀ ⦄ → λ (rest₉ : RecursorFixtures:Holder α₀) → λ (restih₁₀ : motive₁ rest₉) → mk₃ {n₇} ⦃ inst₈ ⦄ rest₉ restih₁₀) rest₆)

RecursorFixtures:Holder:~usizeOf~u1 : {α₀ : Set} → ⦃ _ : SizeOf α₀ ⦄ → RecursorFixtures:Holder α₀ → Nat
RecursorFixtures:Holder:~usizeOf~u1 {α₀} ⦃ inst₁ ⦄ t₂ = RecursorFixtures:Holder:rec {α₀} {λ (t₃ : RecursorFixtures:Holder α₀) → Nat} (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (λ {n₃ : Nat} → λ ⦃ inst₄ : RecursorFixtures:Tag α₀ ⦄ → λ (rest₅ : RecursorFixtures:Holder α₀) → λ (restih₆ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {Nat} ⦃ instSizeOfNat ⦄ n₃)) (SizeOf:sizeOf {RecursorFixtures:Tag α₀} ⦃ instSizeOfDefault (RecursorFixtures:Tag α₀) ⦄ inst₄)) restih₆) t₂

RecursorFixtures:Holder:~usizeOf~uinst : (α₀ : Set) → ⦃ _ : SizeOf α₀ ⦄ → SizeOf (RecursorFixtures:Holder α₀)
RecursorFixtures:Holder:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ = SizeOf:mk {RecursorFixtures:Holder α₀} (λ (m₂ : RecursorFixtures:Holder α₀) → RecursorFixtures:Holder:~usizeOf~u1 {α₀} ⦃ inst₁ ⦄ m₂)

RecursorFixtures:Holder:below : {α₀ : Set} → {_ : RecursorFixtures:Holder α₀ → Set} → RecursorFixtures:Holder α₀ → Set
RecursorFixtures:Holder:below {α₀} {motive₁} t₂ = RecursorFixtures:Holder:rec {α₀} {λ (t₃ : RecursorFixtures:Holder α₀) → Set} PUnit (λ {n₃ : Nat} → λ ⦃ inst₄ : RecursorFixtures:Tag α₀ ⦄ → λ (rest₅ : RecursorFixtures:Holder α₀) → λ (restih₆ : Set) → PProd (motive₁ rest₅) restih₆) t₂

RecursorFixtures:Holder:brecOn:go : {α₀ : Set} → {motive₁ : RecursorFixtures:Holder α₀ → Set} → (t₂ : RecursorFixtures:Holder α₀) → ((t₃ : RecursorFixtures:Holder α₀) → RecursorFixtures:Holder:below {α₀} {motive₁} t₃ → motive₁ t₃) → PProd (motive₁ t₂) (RecursorFixtures:Holder:below {α₀} {motive₁} t₂)
RecursorFixtures:Holder:brecOn:go {α₀} {motive₁} t₂ F1₃ = RecursorFixtures:Holder:rec {α₀} {λ (t₄ : RecursorFixtures:Holder α₀) → PProd (motive₁ t₄) (RecursorFixtures:Holder:below {α₀} {motive₁} t₄)} (PProd:mk {motive₁ (RecursorFixtures:Holder:nil {α₀})} {PUnit} (F1₃ (RecursorFixtures:Holder:nil {α₀}) PUnit:unit) PUnit:unit) (λ {n₄ : Nat} → λ ⦃ inst₅ : RecursorFixtures:Tag α₀ ⦄ → λ (rest₆ : RecursorFixtures:Holder α₀) → λ (restih₇ : PProd (motive₁ rest₆) (RecursorFixtures:Holder:below {α₀} {motive₁} rest₆)) → PProd:mk {motive₁ (RecursorFixtures:Holder:mk {α₀} {n₄} ⦃ inst₅ ⦄ rest₆)} {PProd (motive₁ rest₆) (RecursorFixtures:Holder:below {α₀} {motive₁} rest₆)} (F1₃ (RecursorFixtures:Holder:mk {α₀} {n₄} ⦃ inst₅ ⦄ rest₆) restih₇) restih₇) t₂

RecursorFixtures:Holder:brecOn : {α₀ : Set} → {motive₁ : RecursorFixtures:Holder α₀ → Set} → (t₂ : RecursorFixtures:Holder α₀) → ((t₃ : RecursorFixtures:Holder α₀) → RecursorFixtures:Holder:below {α₀} {motive₁} t₃ → motive₁ t₃) → motive₁ t₂
RecursorFixtures:Holder:brecOn {α₀} {motive₁} t₂ F1₃ = PProd.fst₂ {motive₁ t₂} {RecursorFixtures:Holder:below {α₀} {motive₁} t₂} (RecursorFixtures:Holder:brecOn:go {α₀} {motive₁} t₂ F1₃)

RecursorFixtures:Holder:casesOn : {α₀ : Set} → {motive₁ : RecursorFixtures:Holder α₀ → Set} → (t₂ : RecursorFixtures:Holder α₀) → motive₁ (RecursorFixtures:Holder:nil {α₀}) → ({n₃ : Nat} → ⦃ inst₄ : RecursorFixtures:Tag α₀ ⦄ → (rest₅ : RecursorFixtures:Holder α₀) → motive₁ (RecursorFixtures:Holder:mk {α₀} {n₃} ⦃ inst₄ ⦄ rest₅)) → motive₁ t₂
RecursorFixtures:Holder:casesOn {α₀} {motive₁} t₂ nil₃ mk₄ = RecursorFixtures:Holder:rec {α₀} {motive₁} nil₃ (λ {n₅ : Nat} → λ ⦃ inst₆ : RecursorFixtures:Tag α₀ ⦄ → λ (rest₇ : RecursorFixtures:Holder α₀) → λ (restih₈ : motive₁ rest₇) → mk₄ {n₅} ⦃ inst₆ ⦄ rest₇) t₂

-- theorem
opaque
  RecursorFixtures:Holder:brecOn:eq : {α₀ : Set} → {motive₁ : RecursorFixtures:Holder α₀ → Set} → (t₂ : RecursorFixtures:Holder α₀) → (F1₃ : (t₃ : RecursorFixtures:Holder α₀) → RecursorFixtures:Holder:below {α₀} {motive₁} t₃ → motive₁ t₃) → Eq {motive₁ t₂} (RecursorFixtures:Holder:brecOn {α₀} {motive₁} t₂ F1₃) (F1₃ t₂ (PProd.snd₃ {motive₁ t₂} {RecursorFixtures:Holder:below {α₀} {motive₁} t₂} (RecursorFixtures:Holder:brecOn:go {α₀} {motive₁} t₂ F1₃)))
  RecursorFixtures:Holder:brecOn:eq {α₀} {motive₁} t₂ F1₃ = RecursorFixtures:Holder:casesOn {α₀} {λ (x₄ : RecursorFixtures:Holder α₀) → Eq {motive₁ x₄} (RecursorFixtures:Holder:brecOn {α₀} {motive₁} x₄ F1₃) (F1₃ x₄ (PProd.snd₃ {motive₁ x₄} {RecursorFixtures:Holder:below {α₀} {motive₁} x₄} (RecursorFixtures:Holder:brecOn:go {α₀} {motive₁} x₄ F1₃)))} t₂ (Eq:refl {motive₁ (RecursorFixtures:Holder:nil {α₀})} (RecursorFixtures:Holder:brecOn {α₀} {motive₁} (RecursorFixtures:Holder:nil {α₀}) F1₃)) (λ {n₄ : Nat} → λ ⦃ inst₅ : RecursorFixtures:Tag α₀ ⦄ → λ (rest₆ : RecursorFixtures:Holder α₀) → Eq:refl {motive₁ (RecursorFixtures:Holder:mk {α₀} {n₄} ⦃ inst₅ ⦄ rest₆)} (RecursorFixtures:Holder:brecOn {α₀} {motive₁} (RecursorFixtures:Holder:mk {α₀} {n₄} ⦃ inst₅ ⦄ rest₆) F1₃))

RecursorFixtures:Holder:ctorElimType : {α₀ : Set} → {_ : RecursorFixtures:Holder α₀ → Set} → Nat → Set
RecursorFixtures:Holder:ctorElimType {α₀} {motive₁} ctorIdx₂ = cond {Set} (Nat:ble ctorIdx₂ 0) (PULift (motive₁ (RecursorFixtures:Holder:nil {α₀}))) (PULift ({n₃ : Nat} → ⦃ inst₄ : RecursorFixtures:Tag α₀ ⦄ → (rest₅ : RecursorFixtures:Holder α₀) → motive₁ (RecursorFixtures:Holder:mk {α₀} {n₃} ⦃ inst₄ ⦄ rest₅)))

RecursorFixtures:Holder:ctorIdx : {α₀ : Set} → RecursorFixtures:Holder α₀ → Nat
RecursorFixtures:Holder:ctorIdx {α₀} x₁ = RecursorFixtures:Holder:casesOn {α₀} {λ (x₂ : RecursorFixtures:Holder α₀) → Nat} x₁ 0 (λ {n₂ : Nat} → λ ⦃ inst₃ : RecursorFixtures:Tag α₀ ⦄ → λ (rest₄ : RecursorFixtures:Holder α₀) → 1)

RecursorFixtures:Holder:ctorElim : {α₀ : Set} → {motive₁ : RecursorFixtures:Holder α₀ → Set} → (ctorIdx₂ : Nat) → (t₃ : RecursorFixtures:Holder α₀) → Eq {Nat} ctorIdx₂ (RecursorFixtures:Holder:ctorIdx {α₀} t₃) → RecursorFixtures:Holder:ctorElimType {α₀} {motive₁} ctorIdx₂ → motive₁ t₃
RecursorFixtures:Holder:ctorElim {α₀} {motive₁} ctorIdx₂ t₃ h₄ k₅ = RecursorFixtures:Holder:casesOn {α₀} {λ (t₆ : RecursorFixtures:Holder α₀) → Eq {Nat} ctorIdx₂ (RecursorFixtures:Holder:ctorIdx {α₀} t₆) → motive₁ t₆} t₃ (λ (h₆ : Eq {Nat} ctorIdx₂ 0) → PULift:down {motive₁ (RecursorFixtures:Holder:nil {α₀})} (Eq:ndrec {Nat} {ctorIdx₂} {RecursorFixtures:Holder:ctorElimType {α₀} {motive₁}} k₅ {0} h₆)) (λ {n₆ : Nat} → λ ⦃ inst₇ : RecursorFixtures:Tag α₀ ⦄ → λ (rest₈ : RecursorFixtures:Holder α₀) → λ (h₉ : Eq {Nat} ctorIdx₂ 1) → PULift:down { {n₁₀ : Nat} → ⦃ inst₁₁ : RecursorFixtures:Tag α₀ ⦄ → (rest₁₂ : RecursorFixtures:Holder α₀) → motive₁ (RecursorFixtures:Holder:mk {α₀} {n₁₀} ⦃ inst₁₁ ⦄ rest₁₂) } (Eq:ndrec {Nat} {ctorIdx₂} {RecursorFixtures:Holder:ctorElimType {α₀} {motive₁}} k₅ {1} h₉) {n₆} ⦃ inst₇ ⦄ rest₈) h₄

RecursorFixtures:Holder:depth : RecursorFixtures:Holder Nat → Nat
RecursorFixtures:Holder:depth h₀ = RecursorFixtures:Holder:rec {Nat} {λ (x₁ : RecursorFixtures:Holder Nat) → Nat} (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (λ {n₁ : Nat} → λ ⦃ inst₂ : RecursorFixtures:Tag Nat ⦄ → λ (x₃ : RecursorFixtures:Holder Nat) → λ (d₄ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ d₄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) h₀

RecursorFixtures:instTagNat : RecursorFixtures:Tag Nat
RecursorFixtures:instTagNat = RecursorFixtures:Tag:mk {Nat} (OfNat:ofNat {Nat} 7 ⦃ instOfNatNat 7 ⦄)

RecursorFixtures:Holder:depth~uexample:~ushare:~n1 : Nat
RecursorFixtures:Holder:depth~uexample:~ushare:~n1 = RecursorFixtures:Holder:depth (RecursorFixtures:Holder:mk {Nat} {OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄} ⦃ RecursorFixtures:instTagNat ⦄ (RecursorFixtures:Holder:mk {Nat} {OfNat:ofNat {Nat} 2 ⦃ instOfNatNat 2 ⦄} ⦃ RecursorFixtures:instTagNat ⦄ (RecursorFixtures:Holder:nil {Nat})))

-- theorem
opaque
  RecursorFixtures:Holder:depth~uexample : Eq {Nat} RecursorFixtures:Holder:depth~uexample:~ushare:~n1 (OfNat:ofNat {Nat} 2 ⦃ instOfNatNat 2 ⦄)
  RecursorFixtures:Holder:depth~uexample = rfl {Nat} {RecursorFixtures:Holder:depth~uexample:~ushare:~n1}

RecursorFixtures:Holder:mk:elim : {α₀ : Set} → {motive₁ : RecursorFixtures:Holder α₀ → Set} → (t₂ : RecursorFixtures:Holder α₀) → Eq {Nat} (RecursorFixtures:Holder:ctorIdx {α₀} t₂) 1 → ({n₃ : Nat} → ⦃ inst₄ : RecursorFixtures:Tag α₀ ⦄ → (rest₅ : RecursorFixtures:Holder α₀) → motive₁ (RecursorFixtures:Holder:mk {α₀} {n₃} ⦃ inst₄ ⦄ rest₅)) → motive₁ t₂
RecursorFixtures:Holder:mk:elim {α₀} {motive₁} t₂ h₃ mk₄ = RecursorFixtures:Holder:ctorElim {α₀} {motive₁} 1 t₂ (Eq:symm {Nat} {RecursorFixtures:Holder:ctorIdx {α₀} t₂} {1} h₃) (PULift:up { {n₅ : Nat} → ⦃ inst₆ : RecursorFixtures:Tag α₀ ⦄ → (rest₇ : RecursorFixtures:Holder α₀) → motive₁ (RecursorFixtures:Holder:mk {α₀} {n₅} ⦃ inst₆ ⦄ rest₇) } (λ {n₅ : Nat} → λ ⦃ inst₆ : RecursorFixtures:Tag α₀ ⦄ → λ (rest₇ : RecursorFixtures:Holder α₀) → mk₄ {n₅} ⦃ inst₆ ⦄ rest₇))

RecursorFixtures:Holder:noConfusionType : Set → {α₀ : Set} → RecursorFixtures:Holder α₀ → {α₁ : Set} → RecursorFixtures:Holder α₁ → Set
RecursorFixtures:Holder:noConfusionType P₀ {α₁} t₂ {α₃} t₄ = RecursorFixtures:Holder:casesOn {α₁} {λ (t₅ : RecursorFixtures:Holder α₁) → Set} t₂ (RecursorFixtures:Holder:casesOn {α₃} {λ (t₅ : RecursorFixtures:Holder α₃) → Set} t₄ (P₀ → P₀) (λ {n₅ : Nat} → λ ⦃ inst₆ : RecursorFixtures:Tag α₃ ⦄ → λ (rest₇ : RecursorFixtures:Holder α₃) → P₀)) (λ {n₅ : Nat} → λ ⦃ inst₆ : RecursorFixtures:Tag α₁ ⦄ → λ (rest₇ : RecursorFixtures:Holder α₁) → RecursorFixtures:Holder:casesOn {α₃} {λ (t₈ : RecursorFixtures:Holder α₃) → Set} t₄ P₀ (λ {n₈ : Nat} → λ ⦃ inst₉ : RecursorFixtures:Tag α₃ ⦄ → λ (rest₁₀ : RecursorFixtures:Holder α₃) → (Eq {Nat} n₅ n₈ → HEq {RecursorFixtures:Tag α₁} inst₆ {RecursorFixtures:Tag α₃} inst₉ → HEq {RecursorFixtures:Holder α₁} rest₇ {RecursorFixtures:Holder α₃} rest₁₀ → P₀) → P₀))

RecursorFixtures:Holder:noConfusion : {P₀ : Set} → {α₁ : Set} → {t₂ : RecursorFixtures:Holder α₁} → {α₃ : Set} → {t₄ : RecursorFixtures:Holder α₃} → Eq {Set} α₁ α₃ → HEq {RecursorFixtures:Holder α₁} t₂ {RecursorFixtures:Holder α₃} t₄ → RecursorFixtures:Holder:noConfusionType P₀ {α₁} t₂ {α₃} t₄
RecursorFixtures:Holder:noConfusion {P₀} {α₁} {t₂} {α₃} {t₄} eq1₅ eq2₆ = Eq:ndrec {Set} {α₁} {λ (α₇ : Set) → {t₈ : RecursorFixtures:Holder α₇} → HEq {RecursorFixtures:Holder α₁} t₂ {RecursorFixtures:Holder α₇} t₈ → RecursorFixtures:Holder:noConfusionType P₀ {α₁} t₂ {α₇} t₈} (λ {t₇ : RecursorFixtures:Holder α₁} → λ (eq2₈ : HEq {RecursorFixtures:Holder α₁} t₂ {RecursorFixtures:Holder α₁} t₇) → Eq:ndrec {RecursorFixtures:Holder α₁} {t₂} {λ (t₉ : RecursorFixtures:Holder α₁) → RecursorFixtures:Holder:noConfusionType P₀ {α₁} t₂ {α₁} t₉} (RecursorFixtures:Holder:casesOn {α₁} {λ (t₉ : RecursorFixtures:Holder α₁) → RecursorFixtures:Holder:noConfusionType P₀ {α₁} t₉ {α₁} t₉} t₂ (λ (k₉ : P₀) → k₉) (λ {n₉ : Nat} → λ ⦃ inst₁₀ : RecursorFixtures:Tag α₁ ⦄ → λ (rest₁₁ : RecursorFixtures:Holder α₁) → λ (k₁₂ : Eq {Nat} n₉ n₉ → HEq {RecursorFixtures:Tag α₁} inst₁₀ {RecursorFixtures:Tag α₁} inst₁₀ → HEq {RecursorFixtures:Holder α₁} rest₁₁ {RecursorFixtures:Holder α₁} rest₁₁ → P₀) → k₁₂ (Eq:refl {Nat} n₉) (HEq:refl {RecursorFixtures:Tag α₁} inst₁₀) (HEq:refl {RecursorFixtures:Holder α₁} rest₁₁))) {t₇} (eq~uof~uheq {RecursorFixtures:Holder α₁} {t₂} {t₇} eq2₈)) {α₃} eq1₅ {t₄} eq2₆

-- theorem
opaque
  heq~uof~ueq : {α₀ : Set} → {a₁ : α₀} → {a₂ : α₀} → Eq {α₀} a₁ a₂ → HEq {α₀} a₁ {α₀} a₂
  heq~uof~ueq {α₀} {a₁} {a₂} h₃ = Eq:subst {α₀} {HEq {α₀} a₁ {α₀}} {a₁} {a₂} h₃ (HEq:refl {α₀} a₁)

RecursorFixtures:Holder:mk:noConfusion : {α₀ : Set} → {P₁ : Set} → {n₂ : Nat} → {inst₃ : RecursorFixtures:Tag α₀} → {rest₄ : RecursorFixtures:Holder α₀} → {n₅ : Nat} → {inst₆ : RecursorFixtures:Tag α₀} → {rest₇ : RecursorFixtures:Holder α₀} → Eq {RecursorFixtures:Holder α₀} (RecursorFixtures:Holder:mk {α₀} {n₂} ⦃ inst₃ ⦄ rest₄) (RecursorFixtures:Holder:mk {α₀} {n₅} ⦃ inst₆ ⦄ rest₇) → (Eq {Nat} n₂ n₅ → HEq {RecursorFixtures:Tag α₀} inst₃ {RecursorFixtures:Tag α₀} inst₆ → HEq {RecursorFixtures:Holder α₀} rest₄ {RecursorFixtures:Holder α₀} rest₇ → P₁) → P₁
RecursorFixtures:Holder:mk:noConfusion {α₀} {P₁} {n₂} {inst₃} {rest₄} {n₅} {inst₆} {rest₇} eq₈ k₉ = id {P₁} (RecursorFixtures:Holder:noConfusion {P₁} {α₀} {RecursorFixtures:Holder:mk {α₀} {n₂} ⦃ inst₃ ⦄ rest₄} {α₀} {RecursorFixtures:Holder:mk {α₀} {n₅} ⦃ inst₆ ⦄ rest₇} (Eq:refl {Set} α₀) (heq~uof~ueq {RecursorFixtures:Holder α₀} {RecursorFixtures:Holder:mk {α₀} {n₂} ⦃ inst₃ ⦄ rest₄} {RecursorFixtures:Holder:mk {α₀} {n₅} ⦃ inst₆ ⦄ rest₇} eq₈) k₉)

-- theorem
opaque
  RecursorFixtures:Holder:mk:inj : {α₀ : Set} → {n₁ : Nat} → {inst₂ : RecursorFixtures:Tag α₀} → {rest₃ : RecursorFixtures:Holder α₀} → {n₄ : Nat} → {inst₅ : RecursorFixtures:Tag α₀} → {rest₆ : RecursorFixtures:Holder α₀} → Eq {RecursorFixtures:Holder α₀} (RecursorFixtures:Holder:mk {α₀} {n₁} ⦃ inst₂ ⦄ rest₃) (RecursorFixtures:Holder:mk {α₀} {n₄} ⦃ inst₅ ⦄ rest₆) → And (Eq {Nat} n₁ n₄) (And (Eq {RecursorFixtures:Tag α₀} inst₂ inst₅) (Eq {RecursorFixtures:Holder α₀} rest₃ rest₆))
  RecursorFixtures:Holder:mk:inj {α₀} {n₁} {inst₂} {rest₃} {n₄} {inst₅} {rest₆} x₇ = RecursorFixtures:Holder:mk:noConfusion {α₀} {And (Eq {Nat} n₁ n₄) (And (Eq {RecursorFixtures:Tag α₀} inst₂ inst₅) (Eq {RecursorFixtures:Holder α₀} rest₃ rest₆))} {n₁} {inst₂} {rest₃} {n₄} {inst₅} {rest₆} x₇ (λ (neq₈ : Eq {Nat} n₁ n₄) → λ (insteq₉ : HEq {RecursorFixtures:Tag α₀} inst₂ {RecursorFixtures:Tag α₀} inst₅) → λ (resteq₁₀ : HEq {RecursorFixtures:Holder α₀} rest₃ {RecursorFixtures:Holder α₀} rest₆) → And:intro {Eq {Nat} n₁ n₄} {And (Eq {RecursorFixtures:Tag α₀} inst₂ inst₅) (Eq {RecursorFixtures:Holder α₀} rest₃ rest₆)} neq₈ (And:intro {Eq {RecursorFixtures:Tag α₀} inst₂ inst₅} {Eq {RecursorFixtures:Holder α₀} rest₃ rest₆} (eq~uof~uheq {RecursorFixtures:Tag α₀} {inst₂} {inst₅} insteq₉) (eq~uof~uheq {RecursorFixtures:Holder α₀} {rest₃} {rest₆} resteq₁₀)))

-- theorem
opaque
  RecursorFixtures:Holder:mk:injEq : {α₀ : Set} → {n₁ : Nat} → ⦃ inst₂ : RecursorFixtures:Tag α₀ ⦄ → (rest₃ : RecursorFixtures:Holder α₀) → (n₄ : Nat) → (inst₅ : RecursorFixtures:Tag α₀) → (rest₆ : RecursorFixtures:Holder α₀) → Eq {Set} (Eq {RecursorFixtures:Holder α₀} (RecursorFixtures:Holder:mk {α₀} {n₁} ⦃ inst₂ ⦄ rest₃) (RecursorFixtures:Holder:mk {α₀} {n₄} ⦃ inst₅ ⦄ rest₆)) (And (Eq {Nat} n₁ n₄) (And (Eq {RecursorFixtures:Tag α₀} inst₂ inst₅) (Eq {RecursorFixtures:Holder α₀} rest₃ rest₆)))
  RecursorFixtures:Holder:mk:injEq {α₀} {n₁} ⦃ inst₂ ⦄ rest₃ n₄ inst₅ rest₆ = Eq:propIntro {Eq {RecursorFixtures:Holder α₀} (RecursorFixtures:Holder:mk {α₀} {n₁} ⦃ inst₂ ⦄ rest₃) (RecursorFixtures:Holder:mk {α₀} {n₄} ⦃ inst₅ ⦄ rest₆)} {And (Eq {Nat} n₁ n₄) (And (Eq {RecursorFixtures:Tag α₀} inst₂ inst₅) (Eq {RecursorFixtures:Holder α₀} rest₃ rest₆))} (RecursorFixtures:Holder:mk:inj {α₀} {n₁} {inst₂} {rest₃} {n₄} {inst₅} {rest₆}) (Lean:injEq~uhelper {Eq {Nat} n₁ n₄} {And (Eq {RecursorFixtures:Tag α₀} inst₂ inst₅) (Eq {RecursorFixtures:Holder α₀} rest₃ rest₆)} {Eq {RecursorFixtures:Holder α₀} (RecursorFixtures:Holder:mk {α₀} {n₁} ⦃ inst₂ ⦄ rest₃) (RecursorFixtures:Holder:mk {α₀} {n₄} ⦃ inst₅ ⦄ rest₆)} (Eq:ndrec {Nat} {n₁} {λ (n₇ : Nat) → And (Eq {RecursorFixtures:Tag α₀} inst₂ inst₅) (Eq {RecursorFixtures:Holder α₀} rest₃ rest₆) → Eq {RecursorFixtures:Holder α₀} (RecursorFixtures:Holder:mk {α₀} {n₁} ⦃ inst₂ ⦄ rest₃) (RecursorFixtures:Holder:mk {α₀} {n₇} ⦃ inst₅ ⦄ rest₆)} (Lean:injEq~uhelper {Eq {RecursorFixtures:Tag α₀} inst₂ inst₅} {Eq {RecursorFixtures:Holder α₀} rest₃ rest₆} {Eq {RecursorFixtures:Holder α₀} (RecursorFixtures:Holder:mk {α₀} {n₁} ⦃ inst₂ ⦄ rest₃) (RecursorFixtures:Holder:mk {α₀} {n₁} ⦃ inst₅ ⦄ rest₆)} (Eq:ndrec {RecursorFixtures:Tag α₀} {inst₂} {λ (inst₇ : RecursorFixtures:Tag α₀) → Eq {RecursorFixtures:Holder α₀} rest₃ rest₆ → Eq {RecursorFixtures:Holder α₀} (RecursorFixtures:Holder:mk {α₀} {n₁} ⦃ inst₂ ⦄ rest₃) (RecursorFixtures:Holder:mk {α₀} {n₁} ⦃ inst₇ ⦄ rest₆)} (Eq:ndrec {RecursorFixtures:Holder α₀} {rest₃} {λ (rest₇ : RecursorFixtures:Holder α₀) → Eq {RecursorFixtures:Holder α₀} (RecursorFixtures:Holder:mk {α₀} {n₁} ⦃ inst₂ ⦄ rest₃) (RecursorFixtures:Holder:mk {α₀} {n₁} ⦃ inst₂ ⦄ rest₇)} (Eq:refl {RecursorFixtures:Holder α₀} (RecursorFixtures:Holder:mk {α₀} {n₁} ⦃ inst₂ ⦄ rest₃)) {rest₆}) {inst₅})) {n₄}))

-- theorem
opaque
  RecursorFixtures:Holder:mk:sizeOf~uspec : {α₀ : Set} → ⦃ inst₁ : SizeOf α₀ ⦄ → {n₂ : Nat} → ⦃ inst₃ : RecursorFixtures:Tag α₀ ⦄ → (rest₄ : RecursorFixtures:Holder α₀) → Eq {Nat} (SizeOf:sizeOf {RecursorFixtures:Holder α₀} ⦃ RecursorFixtures:Holder:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ ⦄ (RecursorFixtures:Holder:mk {α₀} {n₂} ⦃ inst₃ ⦄ rest₄)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {Nat} ⦃ instSizeOfNat ⦄ n₂)) (SizeOf:sizeOf {RecursorFixtures:Tag α₀} ⦃ instSizeOfDefault (RecursorFixtures:Tag α₀) ⦄ inst₃)) (SizeOf:sizeOf {RecursorFixtures:Holder α₀} ⦃ RecursorFixtures:Holder:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ ⦄ rest₄))
  RecursorFixtures:Holder:mk:sizeOf~uspec {α₀} ⦃ inst₁ ⦄ {n₂} ⦃ inst₃ ⦄ rest₄ = Eq:refl {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {Nat} ⦃ instSizeOfNat ⦄ n₂)) (SizeOf:sizeOf {RecursorFixtures:Tag α₀} ⦃ instSizeOfDefault (RecursorFixtures:Tag α₀) ⦄ inst₃)) (SizeOf:sizeOf {RecursorFixtures:Holder α₀} ⦃ RecursorFixtures:Holder:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ ⦄ rest₄))

RecursorFixtures:Holder:nil:elim : {α₀ : Set} → {motive₁ : RecursorFixtures:Holder α₀ → Set} → (t₂ : RecursorFixtures:Holder α₀) → Eq {Nat} (RecursorFixtures:Holder:ctorIdx {α₀} t₂) 0 → motive₁ (RecursorFixtures:Holder:nil {α₀}) → motive₁ t₂
RecursorFixtures:Holder:nil:elim {α₀} {motive₁} t₂ h₃ nil₄ = RecursorFixtures:Holder:ctorElim {α₀} {motive₁} 0 t₂ (Eq:symm {Nat} {RecursorFixtures:Holder:ctorIdx {α₀} t₂} {0} h₃) (PULift:up {motive₁ (RecursorFixtures:Holder:nil {α₀})} nil₄)

-- theorem
opaque
  RecursorFixtures:Holder:nil:sizeOf~uspec : {α₀ : Set} → ⦃ inst₁ : SizeOf α₀ ⦄ → Eq {Nat} (SizeOf:sizeOf {RecursorFixtures:Holder α₀} ⦃ RecursorFixtures:Holder:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ ⦄ (RecursorFixtures:Holder:nil {α₀})) (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)
  RecursorFixtures:Holder:nil:sizeOf~uspec {α₀} ⦃ inst₁ ⦄ = Eq:refl {Nat} (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)

RecursorFixtures:Holder:recOn : {α₀ : Set} → {motive₁ : RecursorFixtures:Holder α₀ → Set} → (t₂ : RecursorFixtures:Holder α₀) → motive₁ (RecursorFixtures:Holder:nil {α₀}) → ({n₃ : Nat} → ⦃ inst₄ : RecursorFixtures:Tag α₀ ⦄ → (rest₅ : RecursorFixtures:Holder α₀) → motive₁ rest₅ → motive₁ (RecursorFixtures:Holder:mk {α₀} {n₃} ⦃ inst₄ ⦄ rest₅)) → motive₁ t₂
RecursorFixtures:Holder:recOn {α₀} {motive₁} t₂ nil₃ mk₄ = RecursorFixtures:Holder:rec {α₀} {motive₁} nil₃ (λ {n₅ : Nat} → λ ⦃ inst₆ : RecursorFixtures:Tag α₀ ⦄ → λ (rest₇ : RecursorFixtures:Holder α₀) → λ (restih₈ : motive₁ rest₇) → mk₄ {n₅} ⦃ inst₆ ⦄ rest₇ restih₈) t₂

RecursorFixtures:Odd:brecOn:go : {motive1₀ : RecursorFixtures:Even → Set} → {motive2₁ : RecursorFixtures:Odd → Set} → (t₂ : RecursorFixtures:Odd) → ((t₃ : RecursorFixtures:Even) → RecursorFixtures:Even:below {motive1₀} {motive2₁} t₃ → motive1₀ t₃) → ((t₃ : RecursorFixtures:Odd) → RecursorFixtures:Odd:below {motive1₀} {motive2₁} t₃ → motive2₁ t₃) → PProd (motive2₁ t₂) (RecursorFixtures:Odd:below {motive1₀} {motive2₁} t₂)
RecursorFixtures:Odd:brecOn:go {motive1₀} {motive2₁} t₂ F1₃ F2₄ = RecursorFixtures:Odd:rec {λ (t₅ : RecursorFixtures:Even) → PProd (motive1₀ t₅) (RecursorFixtures:Even:below {motive1₀} {motive2₁} t₅)} {λ (t₅ : RecursorFixtures:Odd) → PProd (motive2₁ t₅) (RecursorFixtures:Odd:below {motive1₀} {motive2₁} t₅)} (PProd:mk {motive1₀ RecursorFixtures:Even:zero} {PUnit} (F1₃ RecursorFixtures:Even:zero PUnit:unit) PUnit:unit) (λ (o₅ : RecursorFixtures:Odd) → λ (oih₆ : PProd (motive2₁ o₅) (RecursorFixtures:Odd:below {motive1₀} {motive2₁} o₅)) → PProd:mk {motive1₀ (RecursorFixtures:Even:succ o₅)} {PProd (motive2₁ o₅) (RecursorFixtures:Odd:below {motive1₀} {motive2₁} o₅)} (F1₃ (RecursorFixtures:Even:succ o₅) oih₆) oih₆) (λ (e₅ : RecursorFixtures:Even) → λ (eih₆ : PProd (motive1₀ e₅) (RecursorFixtures:Even:below {motive1₀} {motive2₁} e₅)) → PProd:mk {motive2₁ (RecursorFixtures:Odd:succ e₅)} {PProd (motive1₀ e₅) (RecursorFixtures:Even:below {motive1₀} {motive2₁} e₅)} (F2₄ (RecursorFixtures:Odd:succ e₅) eih₆) eih₆) t₂

RecursorFixtures:Odd:brecOn : {motive1₀ : RecursorFixtures:Even → Set} → {motive2₁ : RecursorFixtures:Odd → Set} → (t₂ : RecursorFixtures:Odd) → ((t₃ : RecursorFixtures:Even) → RecursorFixtures:Even:below {motive1₀} {motive2₁} t₃ → motive1₀ t₃) → ((t₃ : RecursorFixtures:Odd) → RecursorFixtures:Odd:below {motive1₀} {motive2₁} t₃ → motive2₁ t₃) → motive2₁ t₂
RecursorFixtures:Odd:brecOn {motive1₀} {motive2₁} t₂ F1₃ F2₄ = PProd.fst₂ {motive2₁ t₂} {RecursorFixtures:Odd:below {motive1₀} {motive2₁} t₂} (RecursorFixtures:Odd:brecOn:go {motive1₀} {motive2₁} t₂ F1₃ F2₄)

RecursorFixtures:Odd:casesOn : {motive2₀ : RecursorFixtures:Odd → Set} → (t₁ : RecursorFixtures:Odd) → ((e₂ : RecursorFixtures:Even) → motive2₀ (RecursorFixtures:Odd:succ e₂)) → motive2₀ t₁
RecursorFixtures:Odd:casesOn {motive2₀} t₁ succ₂ = RecursorFixtures:Odd:rec {λ (t₃ : RecursorFixtures:Even) → PUnit} {motive2₀} PUnit:unit (λ (o₃ : RecursorFixtures:Odd) → λ (oih₄ : motive2₀ o₃) → PUnit:unit) (λ (e₃ : RecursorFixtures:Even) → λ (eih₄ : PUnit) → succ₂ e₃) t₁

-- theorem
opaque
  RecursorFixtures:Odd:brecOn:eq : {motive1₀ : RecursorFixtures:Even → Set} → {motive2₁ : RecursorFixtures:Odd → Set} → (t₂ : RecursorFixtures:Odd) → (F1₃ : (t₃ : RecursorFixtures:Even) → RecursorFixtures:Even:below {motive1₀} {motive2₁} t₃ → motive1₀ t₃) → (F2₄ : (t₄ : RecursorFixtures:Odd) → RecursorFixtures:Odd:below {motive1₀} {motive2₁} t₄ → motive2₁ t₄) → Eq {motive2₁ t₂} (RecursorFixtures:Odd:brecOn {motive1₀} {motive2₁} t₂ F1₃ F2₄) (F2₄ t₂ (PProd.snd₃ {motive2₁ t₂} {RecursorFixtures:Odd:below {motive1₀} {motive2₁} t₂} (RecursorFixtures:Odd:brecOn:go {motive1₀} {motive2₁} t₂ F1₃ F2₄)))
  RecursorFixtures:Odd:brecOn:eq {motive1₀} {motive2₁} t₂ F1₃ F2₄ = RecursorFixtures:Odd:casesOn {λ (x₅ : RecursorFixtures:Odd) → Eq {motive2₁ x₅} (RecursorFixtures:Odd:brecOn {motive1₀} {motive2₁} x₅ F1₃ F2₄) (F2₄ x₅ (PProd.snd₃ {motive2₁ x₅} {RecursorFixtures:Odd:below {motive1₀} {motive2₁} x₅} (RecursorFixtures:Odd:brecOn:go {motive1₀} {motive2₁} x₅ F1₃ F2₄)))} t₂ (λ (e₅ : RecursorFixtures:Even) → Eq:refl {motive2₁ (RecursorFixtures:Odd:succ e₅)} (RecursorFixtures:Odd:brecOn {motive1₀} {motive2₁} (RecursorFixtures:Odd:succ e₅) F1₃ F2₄))

RecursorFixtures:Odd:ctorIdx : RecursorFixtures:Odd → Nat
RecursorFixtures:Odd:ctorIdx x₀ = 0

RecursorFixtures:Odd:noConfusionType : Set → RecursorFixtures:Odd → RecursorFixtures:Odd → Set
RecursorFixtures:Odd:noConfusionType P₀ t₁ t₂ = RecursorFixtures:Odd:casesOn {λ (t₃ : RecursorFixtures:Odd) → Set} t₁ (λ (e₃ : RecursorFixtures:Even) → RecursorFixtures:Odd:casesOn {λ (t₄ : RecursorFixtures:Odd) → Set} t₂ (λ (e₄ : RecursorFixtures:Even) → (Eq {RecursorFixtures:Even} e₃ e₄ → P₀) → P₀))

RecursorFixtures:Odd:noConfusion : {P₀ : Set} → {t₁ : RecursorFixtures:Odd} → {t₂ : RecursorFixtures:Odd} → Eq {RecursorFixtures:Odd} t₁ t₂ → RecursorFixtures:Odd:noConfusionType P₀ t₁ t₂
RecursorFixtures:Odd:noConfusion {P₀} {t₁} {t₂} eq₃ = Eq:ndrec {RecursorFixtures:Odd} {t₁} {λ (t₄ : RecursorFixtures:Odd) → RecursorFixtures:Odd:noConfusionType P₀ t₁ t₄} (RecursorFixtures:Odd:casesOn {λ (t₄ : RecursorFixtures:Odd) → RecursorFixtures:Odd:noConfusionType P₀ t₄ t₄} t₁ (λ (e₄ : RecursorFixtures:Even) → λ (k₅ : Eq {RecursorFixtures:Even} e₄ e₄ → P₀) → k₅ (Eq:refl {RecursorFixtures:Even} e₄))) {t₂} eq₃

RecursorFixtures:Odd:recOn : {motive1₀ : RecursorFixtures:Even → Set} → {motive2₁ : RecursorFixtures:Odd → Set} → (t₂ : RecursorFixtures:Odd) → motive1₀ RecursorFixtures:Even:zero → ((o₃ : RecursorFixtures:Odd) → motive2₁ o₃ → motive1₀ (RecursorFixtures:Even:succ o₃)) → ((e₃ : RecursorFixtures:Even) → motive1₀ e₃ → motive2₁ (RecursorFixtures:Odd:succ e₃)) → motive2₁ t₂
RecursorFixtures:Odd:recOn {motive1₀} {motive2₁} t₂ zero₃ succ₄ succ₅ = RecursorFixtures:Odd:rec {motive1₀} {motive2₁} zero₃ succ₄ succ₅ t₂

RecursorFixtures:Odd:succ:noConfusion : {P₀ : Set} → {e₁ : RecursorFixtures:Even} → {e₂ : RecursorFixtures:Even} → Eq {RecursorFixtures:Odd} (RecursorFixtures:Odd:succ e₁) (RecursorFixtures:Odd:succ e₂) → (Eq {RecursorFixtures:Even} e₁ e₂ → P₀) → P₀
RecursorFixtures:Odd:succ:noConfusion {P₀} {e₁} {e₂} eq₃ k₄ = id {P₀} (RecursorFixtures:Odd:noConfusion {P₀} {RecursorFixtures:Odd:succ e₁} {RecursorFixtures:Odd:succ e₂} eq₃ k₄)

-- theorem
opaque
  RecursorFixtures:Odd:succ:inj : {e₀ : RecursorFixtures:Even} → {e₁ : RecursorFixtures:Even} → Eq {RecursorFixtures:Odd} (RecursorFixtures:Odd:succ e₀) (RecursorFixtures:Odd:succ e₁) → Eq {RecursorFixtures:Even} e₀ e₁
  RecursorFixtures:Odd:succ:inj {e₀} {e₁} x₂ = RecursorFixtures:Odd:succ:noConfusion {Eq {RecursorFixtures:Even} e₀ e₁} {e₀} {e₁} x₂ (λ (eeq₃ : Eq {RecursorFixtures:Even} e₀ e₁) → eeq₃)

-- theorem
opaque
  RecursorFixtures:Odd:succ:injEq : (e₀ : RecursorFixtures:Even) → (e₁ : RecursorFixtures:Even) → Eq {Set} (Eq {RecursorFixtures:Odd} (RecursorFixtures:Odd:succ e₀) (RecursorFixtures:Odd:succ e₁)) (Eq {RecursorFixtures:Even} e₀ e₁)
  RecursorFixtures:Odd:succ:injEq e₀ e₁ = Eq:propIntro {Eq {RecursorFixtures:Odd} (RecursorFixtures:Odd:succ e₀) (RecursorFixtures:Odd:succ e₁)} {Eq {RecursorFixtures:Even} e₀ e₁} (RecursorFixtures:Odd:succ:inj {e₀} {e₁}) (Eq:ndrec {RecursorFixtures:Even} {e₀} {λ (e₂ : RecursorFixtures:Even) → Eq {RecursorFixtures:Odd} (RecursorFixtures:Odd:succ e₀) (RecursorFixtures:Odd:succ e₂)} (Eq:refl {RecursorFixtures:Odd} (RecursorFixtures:Odd:succ e₀)) {e₁})

-- theorem
opaque
  RecursorFixtures:Odd:succ:sizeOf~uspec : (e₀ : RecursorFixtures:Even) → Eq {Nat} (SizeOf:sizeOf {RecursorFixtures:Odd} ⦃ RecursorFixtures:Odd:~usizeOf~uinst ⦄ (RecursorFixtures:Odd:succ e₀)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {RecursorFixtures:Even} ⦃ RecursorFixtures:Even:~usizeOf~uinst ⦄ e₀))
  RecursorFixtures:Odd:succ:sizeOf~uspec e₀ = Eq:refl {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {RecursorFixtures:Even} ⦃ RecursorFixtures:Even:~usizeOf~uinst ⦄ e₀))

data RecursorFixtures:Same {α₀ : Set} : α₀ → α₀ → Set where
  RecursorFixtures:Same:refl : (a₁ : α₀) → RecursorFixtures:Same {α₀} a₁ a₁

-- recursor
RecursorFixtures:Same:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → RecursorFixtures:Same {α₀} a₁ a₂ → Set} → motive₂ a₁ (RecursorFixtures:Same:refl {α₀} a₁) → {a₃ : α₀} → (t₄ : RecursorFixtures:Same {α₀} a₁ a₃) → motive₂ a₃ t₄
RecursorFixtures:Same:rec {α₀} {a₁} {motive₂} refl₃ {_} (RecursorFixtures:Same:refl _) = refl₃

RecursorFixtures:Same:casesOn : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → RecursorFixtures:Same {α₀} a₁ a₂ → Set} → {a₃ : α₀} → (t₄ : RecursorFixtures:Same {α₀} a₁ a₃) → motive₂ a₁ (RecursorFixtures:Same:refl {α₀} a₁) → motive₂ a₃ t₄
RecursorFixtures:Same:casesOn {α₀} {a₁} {motive₂} {a₃} t₄ refl₅ = RecursorFixtures:Same:rec {α₀} {a₁} {motive₂} refl₅ {a₃} t₄

RecursorFixtures:Same:recOn : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → RecursorFixtures:Same {α₀} a₁ a₂ → Set} → {a₃ : α₀} → (t₄ : RecursorFixtures:Same {α₀} a₁ a₃) → motive₂ a₁ (RecursorFixtures:Same:refl {α₀} a₁) → motive₂ a₃ t₄
RecursorFixtures:Same:recOn {α₀} {a₁} {motive₂} {a₃} t₄ refl₅ = RecursorFixtures:Same:rec {α₀} {a₁} {motive₂} refl₅ {a₃} t₄

RecursorFixtures:Same:transport : {a₀ : Nat} → {b₁ : Nat} → RecursorFixtures:Same {Nat} a₀ b₁ → Nat → Nat
RecursorFixtures:Same:transport {a₀} {b₁} h₂ n₃ = RecursorFixtures:Same:rec {Nat} {a₀} {λ (x₄ : Nat) → λ (x₅ : RecursorFixtures:Same {Nat} a₀ x₄) → Nat} n₃ {b₁} h₂

RecursorFixtures:Same:transport~uexample:~ushare:~n1 : Nat
RecursorFixtures:Same:transport~uexample:~ushare:~n1 = RecursorFixtures:Same:transport {OfNat:ofNat {Nat} 3 ⦃ instOfNatNat 3 ⦄} {OfNat:ofNat {Nat} 3 ⦃ instOfNatNat 3 ⦄} (RecursorFixtures:Same:refl {Nat} (OfNat:ofNat {Nat} 3 ⦃ instOfNatNat 3 ⦄)) (OfNat:ofNat {Nat} 7 ⦃ instOfNatNat 7 ⦄)

-- theorem
opaque
  RecursorFixtures:Same:transport~uexample : Eq {Nat} RecursorFixtures:Same:transport~uexample:~ushare:~n1 (OfNat:ofNat {Nat} 7 ⦃ instOfNatNat 7 ⦄)
  RecursorFixtures:Same:transport~uexample = rfl {Nat} {RecursorFixtures:Same:transport~uexample:~ushare:~n1}

RecursorFixtures:Tag:casesOn : {α₀ : Set} → {motive₁ : RecursorFixtures:Tag α₀ → Set} → (t₂ : RecursorFixtures:Tag α₀) → ((tag₃ : Nat) → motive₁ (RecursorFixtures:Tag:mk {α₀} tag₃)) → motive₁ t₂
RecursorFixtures:Tag:casesOn {α₀} {motive₁} t₂ mk₃ = RecursorFixtures:Tag:rec {α₀} {motive₁} (λ (tag₄ : Nat) → mk₃ tag₄) t₂

RecursorFixtures:Tag:ctorIdx : {α₀ : Set} → RecursorFixtures:Tag α₀ → Nat
RecursorFixtures:Tag:ctorIdx {α₀} x₁ = 0

RecursorFixtures:Tag:mk:~uflat~uctor : {α₀ : Set} → Nat → RecursorFixtures:Tag α₀
RecursorFixtures:Tag:mk:~uflat~uctor {α₀} tag₁ = RecursorFixtures:Tag:mk {α₀} tag₁

RecursorFixtures:Tag:noConfusionType : Set → {α₀ : Set} → RecursorFixtures:Tag α₀ → {α₁ : Set} → RecursorFixtures:Tag α₁ → Set
RecursorFixtures:Tag:noConfusionType P₀ {α₁} t₂ {α₃} t₄ = RecursorFixtures:Tag:casesOn {α₁} {λ (t₅ : RecursorFixtures:Tag α₁) → Set} t₂ (λ (tag₅ : Nat) → RecursorFixtures:Tag:casesOn {α₃} {λ (t₆ : RecursorFixtures:Tag α₃) → Set} t₄ (λ (tag₆ : Nat) → (Eq {Nat} tag₅ tag₆ → P₀) → P₀))

RecursorFixtures:Tag:noConfusion : {P₀ : Set} → {α₁ : Set} → {t₂ : RecursorFixtures:Tag α₁} → {α₃ : Set} → {t₄ : RecursorFixtures:Tag α₃} → Eq {Set} α₁ α₃ → HEq {RecursorFixtures:Tag α₁} t₂ {RecursorFixtures:Tag α₃} t₄ → RecursorFixtures:Tag:noConfusionType P₀ {α₁} t₂ {α₃} t₄
RecursorFixtures:Tag:noConfusion {P₀} {α₁} {t₂} {α₃} {t₄} eq1₅ eq2₆ = Eq:ndrec {Set} {α₁} {λ (α₇ : Set) → {t₈ : RecursorFixtures:Tag α₇} → HEq {RecursorFixtures:Tag α₁} t₂ {RecursorFixtures:Tag α₇} t₈ → RecursorFixtures:Tag:noConfusionType P₀ {α₁} t₂ {α₇} t₈} (λ {t₇ : RecursorFixtures:Tag α₁} → λ (eq2₈ : HEq {RecursorFixtures:Tag α₁} t₂ {RecursorFixtures:Tag α₁} t₇) → Eq:ndrec {RecursorFixtures:Tag α₁} {t₂} {λ (t₉ : RecursorFixtures:Tag α₁) → RecursorFixtures:Tag:noConfusionType P₀ {α₁} t₂ {α₁} t₉} (RecursorFixtures:Tag:casesOn {α₁} {λ (t₉ : RecursorFixtures:Tag α₁) → RecursorFixtures:Tag:noConfusionType P₀ {α₁} t₉ {α₁} t₉} t₂ (λ (tag₉ : Nat) → λ (k₁₀ : Eq {Nat} tag₉ tag₉ → P₀) → k₁₀ (Eq:refl {Nat} tag₉))) {t₇} (eq~uof~uheq {RecursorFixtures:Tag α₁} {t₂} {t₇} eq2₈)) {α₃} eq1₅ {t₄} eq2₆

RecursorFixtures:Tag:mk:noConfusion : {α₀ : Set} → {P₁ : Set} → {tag₂ : Nat} → {tag₃ : Nat} → Eq {RecursorFixtures:Tag α₀} (RecursorFixtures:Tag:mk {α₀} tag₂) (RecursorFixtures:Tag:mk {α₀} tag₃) → (Eq {Nat} tag₂ tag₃ → P₁) → P₁
RecursorFixtures:Tag:mk:noConfusion {α₀} {P₁} {tag₂} {tag₃} eq₄ k₅ = id {P₁} (RecursorFixtures:Tag:noConfusion {P₁} {α₀} {RecursorFixtures:Tag:mk {α₀} tag₂} {α₀} {RecursorFixtures:Tag:mk {α₀} tag₃} (Eq:refl {Set} α₀) (heq~uof~ueq {RecursorFixtures:Tag α₀} {RecursorFixtures:Tag:mk {α₀} tag₂} {RecursorFixtures:Tag:mk {α₀} tag₃} eq₄) k₅)

RecursorFixtures:Tag:recOn : {α₀ : Set} → {motive₁ : RecursorFixtures:Tag α₀ → Set} → (t₂ : RecursorFixtures:Tag α₀) → ((tag₃ : Nat) → motive₁ (RecursorFixtures:Tag:mk {α₀} tag₃)) → motive₁ t₂
RecursorFixtures:Tag:recOn {α₀} {motive₁} t₂ mk₃ = RecursorFixtures:Tag:rec {α₀} {motive₁} mk₃ t₂

RecursorFixtures:Tag:tag : (α₀ : Set) → ⦃ _ : RecursorFixtures:Tag α₀ ⦄ → Nat
RecursorFixtures:Tag:tag α₀ ⦃ self₁ ⦄ = RecursorFixtures:Tag.tag₁ {α₀} self₁

data RecursorFixtures:Tagged : Nat → Set where
  RecursorFixtures:Tagged:mk : (n₀ : Nat) → (k₁ : Nat) → Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) → RecursorFixtures:Tagged n₀

-- recursor
RecursorFixtures:Tagged:rec : {a₀ : Nat} → {motive₁ : RecursorFixtures:Tagged a₀ → Set} → ((k₂ : Nat) → (v₃ : Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₂ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → motive₁ (RecursorFixtures:Tagged:mk a₀ k₂ v₃)) → (t₂ : RecursorFixtures:Tagged a₀) → motive₁ t₂
RecursorFixtures:Tagged:rec {a₀} {motive₁} mk₂ (RecursorFixtures:Tagged:mk _ k₃ v₄) = mk₂ k₃ v₄

RecursorFixtures:Tagged:~usizeOf~u1 : {a₀ : Nat} → RecursorFixtures:Tagged a₀ → Nat
RecursorFixtures:Tagged:~usizeOf~u1 {a₀} t₁ = RecursorFixtures:Tagged:rec {a₀} {λ (t₂ : RecursorFixtures:Tagged a₀) → Nat} (λ (k₂ : Nat) → λ (v₃ : Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₂ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {Nat} ⦃ instSizeOfNat ⦄ k₂)) (SizeOf:sizeOf {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₂ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} ⦃ Fin:~usizeOf~uinst (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₂ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) ⦄ v₃)) t₁

RecursorFixtures:Tagged:~usizeOf~uinst : (a₀ : Nat) → SizeOf (RecursorFixtures:Tagged a₀)
RecursorFixtures:Tagged:~usizeOf~uinst a₀ = SizeOf:mk {RecursorFixtures:Tagged a₀} (λ (m₁ : RecursorFixtures:Tagged a₀) → RecursorFixtures:Tagged:~usizeOf~u1 {a₀} m₁)

RecursorFixtures:Tagged:casesOn : {a₀ : Nat} → {motive₁ : RecursorFixtures:Tagged a₀ → Set} → (t₂ : RecursorFixtures:Tagged a₀) → ((k₃ : Nat) → (v₄ : Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₃ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → motive₁ (RecursorFixtures:Tagged:mk a₀ k₃ v₄)) → motive₁ t₂
RecursorFixtures:Tagged:casesOn {a₀} {motive₁} t₂ mk₃ = RecursorFixtures:Tagged:rec {a₀} {motive₁} (λ (k₄ : Nat) → λ (v₅ : Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → mk₃ k₄ v₅) t₂

RecursorFixtures:Tagged:ctorIdx : {a₀ : Nat} → RecursorFixtures:Tagged a₀ → Nat
RecursorFixtures:Tagged:ctorIdx {a₀} x₁ = 0

RecursorFixtures:Tagged:noConfusionType : Set → {a₀ : Nat} → RecursorFixtures:Tagged a₀ → {a₁ : Nat} → RecursorFixtures:Tagged a₁ → Set
RecursorFixtures:Tagged:noConfusionType P₀ {a₁} t₂ {a₃} t₄ = RecursorFixtures:Tagged:casesOn {a₁} {λ (t₅ : RecursorFixtures:Tagged a₁) → Set} t₂ (λ (k₅ : Nat) → λ (v₆ : Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → RecursorFixtures:Tagged:casesOn {a₃} {λ (t₇ : RecursorFixtures:Tagged a₃) → Set} t₄ (λ (k₇ : Nat) → λ (v₈ : Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₇ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → (Eq {Nat} k₅ k₇ → HEq {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} v₆ {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₇ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} v₈ → P₀) → P₀))

RecursorFixtures:Tagged:noConfusion : {P₀ : Set} → {a₁ : Nat} → {t₂ : RecursorFixtures:Tagged a₁} → {a₃ : Nat} → {t₄ : RecursorFixtures:Tagged a₃} → Eq {Nat} a₁ a₃ → HEq {RecursorFixtures:Tagged a₁} t₂ {RecursorFixtures:Tagged a₃} t₄ → RecursorFixtures:Tagged:noConfusionType P₀ {a₁} t₂ {a₃} t₄
RecursorFixtures:Tagged:noConfusion {P₀} {a₁} {t₂} {a₃} {t₄} eq1₅ eq2₆ = Eq:ndrec {Nat} {a₁} {λ (a₇ : Nat) → {t₈ : RecursorFixtures:Tagged a₇} → HEq {RecursorFixtures:Tagged a₁} t₂ {RecursorFixtures:Tagged a₇} t₈ → RecursorFixtures:Tagged:noConfusionType P₀ {a₁} t₂ {a₇} t₈} (λ {t₇ : RecursorFixtures:Tagged a₁} → λ (eq2₈ : HEq {RecursorFixtures:Tagged a₁} t₂ {RecursorFixtures:Tagged a₁} t₇) → Eq:ndrec {RecursorFixtures:Tagged a₁} {t₂} {λ (t₉ : RecursorFixtures:Tagged a₁) → RecursorFixtures:Tagged:noConfusionType P₀ {a₁} t₂ {a₁} t₉} (RecursorFixtures:Tagged:casesOn {a₁} {λ (t₉ : RecursorFixtures:Tagged a₁) → RecursorFixtures:Tagged:noConfusionType P₀ {a₁} t₉ {a₁} t₉} t₂ (λ (k₉ : Nat) → λ (v₁₀ : Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₉ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → λ (k₁₁ : Eq {Nat} k₉ k₉ → HEq {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₉ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} v₁₀ {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₉ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} v₁₀ → P₀) → k₁₁ (Eq:refl {Nat} k₉) (HEq:refl {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₉ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} v₁₀))) {t₇} (eq~uof~uheq {RecursorFixtures:Tagged a₁} {t₂} {t₇} eq2₈)) {a₃} eq1₅ {t₄} eq2₆

RecursorFixtures:Tagged:mk:noConfusion : {n₀ : Nat} → {P₁ : Set} → {k₂ : Nat} → {v₃ : Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₂ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} → {k₄ : Nat} → {v₅ : Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} → Eq {RecursorFixtures:Tagged n₀} (RecursorFixtures:Tagged:mk n₀ k₂ v₃) (RecursorFixtures:Tagged:mk n₀ k₄ v₅) → (Eq {Nat} k₂ k₄ → HEq {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₂ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} v₃ {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} v₅ → P₁) → P₁
RecursorFixtures:Tagged:mk:noConfusion {n₀} {P₁} {k₂} {v₃} {k₄} {v₅} eq₆ k₇ = id {P₁} (RecursorFixtures:Tagged:noConfusion {P₁} {n₀} {RecursorFixtures:Tagged:mk n₀ k₂ v₃} {n₀} {RecursorFixtures:Tagged:mk n₀ k₄ v₅} (Eq:refl {Nat} n₀) (heq~uof~ueq {RecursorFixtures:Tagged n₀} {RecursorFixtures:Tagged:mk n₀ k₂ v₃} {RecursorFixtures:Tagged:mk n₀ k₄ v₅} eq₆) k₇)

-- theorem
opaque
  RecursorFixtures:Tagged:mk:inj : {n₀ : Nat} → {k₁ : Nat} → {v₂ : Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} → {k₃ : Nat} → {v₄ : Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₃ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} → Eq {RecursorFixtures:Tagged n₀} (RecursorFixtures:Tagged:mk n₀ k₁ v₂) (RecursorFixtures:Tagged:mk n₀ k₃ v₄) → And (Eq {Nat} k₁ k₃) (HEq {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} v₂ {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₃ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} v₄)
  RecursorFixtures:Tagged:mk:inj {n₀} {k₁} {v₂} {k₃} {v₄} x₅ = RecursorFixtures:Tagged:mk:noConfusion {n₀} {And (Eq {Nat} k₁ k₃) (HEq {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} v₂ {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₃ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} v₄)} {k₁} {v₂} {k₃} {v₄} x₅ (λ (keq₆ : Eq {Nat} k₁ k₃) → λ (veq₇ : HEq {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} v₂ {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₃ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} v₄) → And:intro {Eq {Nat} k₁ k₃} {HEq {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} v₂ {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₃ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} v₄} keq₆ veq₇)

-- theorem
opaque
  RecursorFixtures:Tagged:mk:injEq : (n₀ : Nat) → (k₁ : Nat) → (v₂ : Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → (k₃ : Nat) → (v₄ : Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₃ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → Eq {Set} (Eq {RecursorFixtures:Tagged n₀} (RecursorFixtures:Tagged:mk n₀ k₁ v₂) (RecursorFixtures:Tagged:mk n₀ k₃ v₄)) (And (Eq {Nat} k₁ k₃) (HEq {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} v₂ {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₃ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} v₄))
  RecursorFixtures:Tagged:mk:injEq n₀ k₁ v₂ k₃ v₄ = Eq:propIntro {Eq {RecursorFixtures:Tagged n₀} (RecursorFixtures:Tagged:mk n₀ k₁ v₂) (RecursorFixtures:Tagged:mk n₀ k₃ v₄)} {And (Eq {Nat} k₁ k₃) (HEq {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} v₂ {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₃ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} v₄)} (RecursorFixtures:Tagged:mk:inj {n₀} {k₁} {v₂} {k₃} {v₄}) (Lean:injEq~uhelper {Eq {Nat} k₁ k₃} {HEq {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} v₂ {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₃ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} v₄} {Eq {RecursorFixtures:Tagged n₀} (RecursorFixtures:Tagged:mk n₀ k₁ v₂) (RecursorFixtures:Tagged:mk n₀ k₃ v₄)} (λ (a₅ : Eq {Nat} k₁ k₃) → Eq:ndrec {Nat} {k₁} {λ (k₆ : Nat) → (v₇ : Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₆ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → HEq {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} v₂ {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₆ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} v₇ → Eq {RecursorFixtures:Tagged n₀} (RecursorFixtures:Tagged:mk n₀ k₁ v₂) (RecursorFixtures:Tagged:mk n₀ k₆ v₇)} (λ (v₆ : Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → HEq:homo~undrec {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} {v₂} {λ (v₇ : Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → Eq {RecursorFixtures:Tagged n₀} (RecursorFixtures:Tagged:mk n₀ k₁ v₂) (RecursorFixtures:Tagged:mk n₀ k₁ v₇)} (Eq:refl {RecursorFixtures:Tagged n₀} (RecursorFixtures:Tagged:mk n₀ k₁ v₂)) {v₆}) {k₃} a₅ v₄))

-- theorem
opaque
  RecursorFixtures:Tagged:mk:sizeOf~uspec : (n₀ : Nat) → (k₁ : Nat) → (v₂ : Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → Eq {Nat} (SizeOf:sizeOf {RecursorFixtures:Tagged n₀} ⦃ RecursorFixtures:Tagged:~usizeOf~uinst n₀ ⦄ (RecursorFixtures:Tagged:mk n₀ k₁ v₂)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {Nat} ⦃ instSizeOfNat ⦄ k₁)) (SizeOf:sizeOf {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} ⦃ Fin:~usizeOf~uinst (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) ⦄ v₂))
  RecursorFixtures:Tagged:mk:sizeOf~uspec n₀ k₁ v₂ = Eq:refl {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {Nat} ⦃ instSizeOfNat ⦄ k₁)) (SizeOf:sizeOf {Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} ⦃ Fin:~usizeOf~uinst (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) ⦄ v₂))

RecursorFixtures:Tagged:recOn : {a₀ : Nat} → {motive₁ : RecursorFixtures:Tagged a₀ → Set} → (t₂ : RecursorFixtures:Tagged a₀) → ((k₃ : Nat) → (v₄ : Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₃ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → motive₁ (RecursorFixtures:Tagged:mk a₀ k₃ v₄)) → motive₁ t₂
RecursorFixtures:Tagged:recOn {a₀} {motive₁} t₂ mk₃ = RecursorFixtures:Tagged:rec {a₀} {motive₁} mk₃ t₂

RecursorFixtures:Tagged:value : {n₀ : Nat} → (x₁ : RecursorFixtures:Tagged n₀) → Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (RecursorFixtures:Tagged:rec {n₀} {λ (self₂ : RecursorFixtures:Tagged n₀) → Nat} (λ (k₂ : Nat) → λ (v₃ : Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₂ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → k₂) x₁) (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))
RecursorFixtures:Tagged:value {n₀} x₁ = RecursorFixtures:Tagged:rec {n₀} {λ (self₂ : RecursorFixtures:Tagged n₀) → Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (RecursorFixtures:Tagged:rec {n₀} {λ (self₃ : RecursorFixtures:Tagged n₀) → Nat} (λ (k₃ : Nat) → λ (v₄ : Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₃ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → k₃) self₂) (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} (λ (k₂ : Nat) → λ (v₃ : Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₂ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → v₃) x₁

~uprivate:Init:Data:NeZero:~n0:instNeZeroNatHAdd:match~u5 : (motive₀ : (n₀ : Nat) → NeZero {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ n₀ → Nat → Set) → (n₁ : Nat) → (h₂ : NeZero {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ n₁) → (m₃ : Nat) → ((n₄ : Nat) → (x₅ : NeZero {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → motive₀ (Nat:succ n₄) x₅ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → ((n₄ : Nat) → (x₅ : NeZero {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → (n₆ : Nat) → motive₀ (Nat:succ n₄) x₅ (Nat:succ n₆)) → motive₀ n₁ h₂ m₃
~uprivate:Init:Data:NeZero:~n0:instNeZeroNatHAdd:match~u5 motive₀ n₁ h₂ m₃ h1₄ h2₅ = Nat:casesOn {λ (x₆ : Nat) → (h₇ : NeZero {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ x₆) → motive₀ x₆ h₇ m₃} n₁ (λ (h₆ : NeZero {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ Nat:zero) → False:elim {motive₀ Nat:zero h₆ m₃} (NeZero:casesOn {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ {Nat:zero} {λ (x₇ : NeZero {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ Nat:zero) → False} h₆ (λ (out₇ : Ne {Nat} Nat:zero (OfNat:ofNat {Nat} 0 ⦃ Zero:toOfNat0 {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ ⦄)) → False:elim {False} (absurd {Eq {Nat} Nat:zero Nat:zero} {False} (Eq:refl {Nat} Nat:zero) out₇)))) (λ (n₆ : Nat) → λ (h₇ : NeZero {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ (Nat:succ n₆)) → Nat:casesOn {λ (x₈ : Nat) → motive₀ (Nat:succ n₆) h₇ x₈} m₃ (h1₄ n₆ h₇) (λ (n₈ : Nat) → h2₅ n₆ h₇ n₈)) h₂

~uprivate:Init:Data:NeZero:~n0:instNeZeroNatHAdd~u1:match~u1 : (n₀ : Nat) → (motive₁ : Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) (OfNat:ofNat {Nat} 0 ⦃ Zero:toOfNat0 {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ ⦄) → Set) → (h₂ : Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) (OfNat:ofNat {Nat} 0 ⦃ Zero:toOfNat0 {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ ⦄)) → motive₁ h₂
~uprivate:Init:Data:NeZero:~n0:instNeZeroNatHAdd~u1:match~u1 n₀ motive₁ h₂ = False:elim {motive₁ h₂} (Eq:casesOn {Nat} {HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} {λ (a₃ : Nat) → λ (x₄ : Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) a₃) → Eq {Nat} (OfNat:ofNat {Nat} 0 ⦃ Zero:toOfNat0 {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ ⦄) a₃ → HEq {Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) (OfNat:ofNat {Nat} 0 ⦃ Zero:toOfNat0 {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ ⦄)} h₂ {Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) a₃} x₄ → False} {OfNat:ofNat {Nat} 0 ⦃ Zero:toOfNat0 {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ ⦄} h₂ (λ (h₃ : Eq {Nat} (OfNat:ofNat {Nat} 0 ⦃ Zero:toOfNat0 {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ ⦄) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)))) → False:elim {HEq {Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) (OfNat:ofNat {Nat} 0 ⦃ Zero:toOfNat0 {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ ⦄)} h₂ {Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)))} (Eq:refl {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)))) → False} (noConfusion~uof~uNat {Nat} Nat:ctorIdx {0} {Nat:succ (Nat:add (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) n₀)} h₃)) (Eq:refl {Nat} (OfNat:ofNat {Nat} 0 ⦃ Zero:toOfNat0 {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ ⦄)) (HEq:refl {Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) (OfNat:ofNat {Nat} 0 ⦃ Zero:toOfNat0 {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ ⦄)} h₂))

~uprivate:Init:Data:NeZero:~n0:instNeZeroNatHAdd~u1:match~u3 : (n₀ : Nat) → (n₁ : Nat) → (motive₂ : Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) (OfNat:ofNat {Nat} 0 ⦃ Zero:toOfNat0 {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ ⦄) → Set) → (h₃ : Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) (OfNat:ofNat {Nat} 0 ⦃ Zero:toOfNat0 {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ ⦄)) → motive₂ h₃
~uprivate:Init:Data:NeZero:~n0:instNeZeroNatHAdd~u1:match~u3 n₀ n₁ motive₂ h₃ = False:elim {motive₂ h₃} (Eq:casesOn {Nat} {HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} {λ (a₄ : Nat) → λ (x₅ : Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) a₄) → Eq {Nat} (OfNat:ofNat {Nat} 0 ⦃ Zero:toOfNat0 {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ ⦄) a₄ → HEq {Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) (OfNat:ofNat {Nat} 0 ⦃ Zero:toOfNat0 {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ ⦄)} h₃ {Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) a₄} x₅ → False} {OfNat:ofNat {Nat} 0 ⦃ Zero:toOfNat0 {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ ⦄} h₃ (λ (h₄ : Eq {Nat} (OfNat:ofNat {Nat} 0 ⦃ Zero:toOfNat0 {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ ⦄) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)))) → False:elim {HEq {Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) (OfNat:ofNat {Nat} 0 ⦃ Zero:toOfNat0 {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ ⦄)} h₃ {Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)))} (Eq:refl {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)))) → False} (noConfusion~uof~uNat {Nat} Nat:ctorIdx {0} {Nat:succ (Nat:add (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) n₀)} h₄)) (Eq:refl {Nat} (OfNat:ofNat {Nat} 0 ⦃ Zero:toOfNat0 {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ ⦄)) (HEq:refl {Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) (OfNat:ofNat {Nat} 0 ⦃ Zero:toOfNat0 {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ ⦄)} h₃))

-- theorem
opaque
  instNeZeroNatHAdd~u1 : {n₀ : Nat} → {m₁ : Nat} → ⦃ _ : NeZero {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ m₁ ⦄ → NeZero {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ m₁)
  instNeZeroNatHAdd~u1 {n₀} {m₁} ⦃ h₂ ⦄ = NeZero:mk {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ {HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ m₁} (~uprivate:Init:Data:NeZero:~n0:instNeZeroNatHAdd:match~u5 (λ (m₃ : Nat) → λ (h₄ : NeZero {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ m₃) → λ (n₅ : Nat) → Ne {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ m₃) (OfNat:ofNat {Nat} 0 ⦃ Zero:toOfNat0 {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ ⦄)) m₁ h₂ n₀ (λ (n₃ : Nat) → λ (x₄ : NeZero {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₃ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → λ (h₅ : Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₃ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) (OfNat:ofNat {Nat} 0 ⦃ Zero:toOfNat0 {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ ⦄)) → ~uprivate:Init:Data:NeZero:~n0:instNeZeroNatHAdd~u1:match~u1 n₃ (λ (h₆ : Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₃ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) (OfNat:ofNat {Nat} 0 ⦃ Zero:toOfNat0 {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ ⦄)) → False) h₅) (λ (n₃ : Nat) → λ (x₄ : NeZero {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₃ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → λ (n₅ : Nat) → λ (h₆ : Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₃ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) (OfNat:ofNat {Nat} 0 ⦃ Zero:toOfNat0 {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ ⦄)) → ~uprivate:Init:Data:NeZero:~n0:instNeZeroNatHAdd~u1:match~u3 n₃ n₅ (λ (h₇ : Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₃ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) (OfNat:ofNat {Nat} 0 ⦃ Zero:toOfNat0 {Nat} ⦃ Zero:ofOfNat0 {Nat} ⦃ instOfNatNat 0 ⦄ ⦄ ⦄)) → False) h₆))

RecursorFixtures:Tagged:value~uexample:~ushare:~n1 : Nat
RecursorFixtures:Tagged:value~uexample:~ushare:~n1 = HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 2 ⦃ instOfNatNat 2 ⦄) (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)

RecursorFixtures:Tagged:value~uexample:~ushare:~n2 : RecursorFixtures:Tagged (OfNat:ofNat {Nat} 4 ⦃ instOfNatNat 4 ⦄)
RecursorFixtures:Tagged:value~uexample:~ushare:~n2 = RecursorFixtures:Tagged:mk (OfNat:ofNat {Nat} 4 ⦃ instOfNatNat 4 ⦄) (OfNat:ofNat {Nat} 2 ⦃ instOfNatNat 2 ⦄) (OfNat:ofNat {Fin RecursorFixtures:Tagged:value~uexample:~ushare:~n1} 1 ⦃ Fin:instOfNat {RecursorFixtures:Tagged:value~uexample:~ushare:~n1} ⦃ instNeZeroNatHAdd~u1 {OfNat:ofNat {Nat} 2 ⦃ instOfNatNat 2 ⦄} {OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄} ⦃ Nat:instNeZeroSucc {OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄} ⦄ ⦄ {1} ⦄)

RecursorFixtures:Tagged:value~uexample:~ushare:~n3 : Nat
RecursorFixtures:Tagged:value~uexample:~ushare:~n3 = Fin:val {HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (RecursorFixtures:Tagged:rec {OfNat:ofNat {Nat} 4 ⦃ instOfNatNat 4 ⦄} {λ (self₀ : RecursorFixtures:Tagged (OfNat:ofNat {Nat} 4 ⦃ instOfNatNat 4 ⦄)) → Nat} (λ (k₀ : Nat) → λ (v₁ : Fin (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ k₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → k₀) RecursorFixtures:Tagged:value~uexample:~ushare:~n2) (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)} (RecursorFixtures:Tagged:value {OfNat:ofNat {Nat} 4 ⦃ instOfNatNat 4 ⦄} RecursorFixtures:Tagged:value~uexample:~ushare:~n2)

-- theorem
opaque
  RecursorFixtures:Tagged:value~uexample : Eq {Nat} RecursorFixtures:Tagged:value~uexample:~ushare:~n3 (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)
  RecursorFixtures:Tagged:value~uexample = rfl {Nat} {RecursorFixtures:Tagged:value~uexample:~ushare:~n3}

data RecursorFixtures:Tree : Set where
  RecursorFixtures:Tree:leaf : RecursorFixtures:Tree
  RecursorFixtures:Tree:node : RecursorFixtures:Tree → RecursorFixtures:Tree → RecursorFixtures:Tree

-- recursor
RecursorFixtures:Tree:rec : {motive₀ : RecursorFixtures:Tree → Set} → motive₀ RecursorFixtures:Tree:leaf → ((left₁ : RecursorFixtures:Tree) → (right₂ : RecursorFixtures:Tree) → motive₀ left₁ → motive₀ right₂ → motive₀ (RecursorFixtures:Tree:node left₁ right₂)) → (t₁ : RecursorFixtures:Tree) → motive₀ t₁
RecursorFixtures:Tree:rec {motive₀} leaf₁ node₂ RecursorFixtures:Tree:leaf = leaf₁
RecursorFixtures:Tree:rec {motive₀} leaf₁ node₂ (RecursorFixtures:Tree:node left₃ right₄) = node₂ left₃ right₄ (RecursorFixtures:Tree:rec {motive₀} leaf₁ node₂ left₃) (RecursorFixtures:Tree:rec {motive₀} leaf₁ node₂ right₄)

RecursorFixtures:Tree:~usizeOf~u1 : RecursorFixtures:Tree → Nat
RecursorFixtures:Tree:~usizeOf~u1 t₀ = RecursorFixtures:Tree:rec {λ (t₁ : RecursorFixtures:Tree) → Nat} (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (λ (left₁ : RecursorFixtures:Tree) → λ (right₂ : RecursorFixtures:Tree) → λ (leftih₃ : Nat) → λ (rightih₄ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) leftih₃) rightih₄) t₀

RecursorFixtures:Tree:~usizeOf~uinst : SizeOf RecursorFixtures:Tree
RecursorFixtures:Tree:~usizeOf~uinst = SizeOf:mk {RecursorFixtures:Tree} (λ (m₀ : RecursorFixtures:Tree) → RecursorFixtures:Tree:~usizeOf~u1 m₀)

RecursorFixtures:Tree:below : {_ : RecursorFixtures:Tree → Set} → RecursorFixtures:Tree → Set
RecursorFixtures:Tree:below {motive₀} t₁ = RecursorFixtures:Tree:rec {λ (t₂ : RecursorFixtures:Tree) → Set} PUnit (λ (left₂ : RecursorFixtures:Tree) → λ (right₃ : RecursorFixtures:Tree) → λ (leftih₄ : Set) → λ (rightih₅ : Set) → PProd (PProd (motive₀ left₂) leftih₄) (PProd (motive₀ right₃) rightih₅)) t₁

RecursorFixtures:Tree:brecOn:go : {motive₀ : RecursorFixtures:Tree → Set} → (t₁ : RecursorFixtures:Tree) → ((t₂ : RecursorFixtures:Tree) → RecursorFixtures:Tree:below {motive₀} t₂ → motive₀ t₂) → PProd (motive₀ t₁) (RecursorFixtures:Tree:below {motive₀} t₁)
RecursorFixtures:Tree:brecOn:go {motive₀} t₁ F1₂ = RecursorFixtures:Tree:rec {λ (t₃ : RecursorFixtures:Tree) → PProd (motive₀ t₃) (RecursorFixtures:Tree:below {motive₀} t₃)} (PProd:mk {motive₀ RecursorFixtures:Tree:leaf} {PUnit} (F1₂ RecursorFixtures:Tree:leaf PUnit:unit) PUnit:unit) (λ (left₃ : RecursorFixtures:Tree) → λ (right₄ : RecursorFixtures:Tree) → λ (leftih₅ : PProd (motive₀ left₃) (RecursorFixtures:Tree:below {motive₀} left₃)) → λ (rightih₆ : PProd (motive₀ right₄) (RecursorFixtures:Tree:below {motive₀} right₄)) → PProd:mk {motive₀ (RecursorFixtures:Tree:node left₃ right₄)} {PProd (PProd (motive₀ left₃) (RecursorFixtures:Tree:below {motive₀} left₃)) (PProd (motive₀ right₄) (RecursorFixtures:Tree:below {motive₀} right₄))} (F1₂ (RecursorFixtures:Tree:node left₃ right₄) (PProd:mk {PProd (motive₀ left₃) (RecursorFixtures:Tree:below {motive₀} left₃)} {PProd (motive₀ right₄) (RecursorFixtures:Tree:below {motive₀} right₄)} leftih₅ rightih₆)) (PProd:mk {PProd (motive₀ left₃) (RecursorFixtures:Tree:below {motive₀} left₃)} {PProd (motive₀ right₄) (RecursorFixtures:Tree:below {motive₀} right₄)} leftih₅ rightih₆)) t₁

RecursorFixtures:Tree:brecOn : {motive₀ : RecursorFixtures:Tree → Set} → (t₁ : RecursorFixtures:Tree) → ((t₂ : RecursorFixtures:Tree) → RecursorFixtures:Tree:below {motive₀} t₂ → motive₀ t₂) → motive₀ t₁
RecursorFixtures:Tree:brecOn {motive₀} t₁ F1₂ = PProd.fst₂ {motive₀ t₁} {RecursorFixtures:Tree:below {motive₀} t₁} (RecursorFixtures:Tree:brecOn:go {motive₀} t₁ F1₂)

RecursorFixtures:Tree:casesOn : {motive₀ : RecursorFixtures:Tree → Set} → (t₁ : RecursorFixtures:Tree) → motive₀ RecursorFixtures:Tree:leaf → ((left₂ : RecursorFixtures:Tree) → (right₃ : RecursorFixtures:Tree) → motive₀ (RecursorFixtures:Tree:node left₂ right₃)) → motive₀ t₁
RecursorFixtures:Tree:casesOn {motive₀} t₁ leaf₂ node₃ = RecursorFixtures:Tree:rec {motive₀} leaf₂ (λ (left₄ : RecursorFixtures:Tree) → λ (right₅ : RecursorFixtures:Tree) → λ (leftih₆ : motive₀ left₄) → λ (rightih₇ : motive₀ right₅) → node₃ left₄ right₅) t₁

-- theorem
opaque
  RecursorFixtures:Tree:brecOn:eq : {motive₀ : RecursorFixtures:Tree → Set} → (t₁ : RecursorFixtures:Tree) → (F1₂ : (t₂ : RecursorFixtures:Tree) → RecursorFixtures:Tree:below {motive₀} t₂ → motive₀ t₂) → Eq {motive₀ t₁} (RecursorFixtures:Tree:brecOn {motive₀} t₁ F1₂) (F1₂ t₁ (PProd.snd₃ {motive₀ t₁} {RecursorFixtures:Tree:below {motive₀} t₁} (RecursorFixtures:Tree:brecOn:go {motive₀} t₁ F1₂)))
  RecursorFixtures:Tree:brecOn:eq {motive₀} t₁ F1₂ = RecursorFixtures:Tree:casesOn {λ (x₃ : RecursorFixtures:Tree) → Eq {motive₀ x₃} (RecursorFixtures:Tree:brecOn {motive₀} x₃ F1₂) (F1₂ x₃ (PProd.snd₃ {motive₀ x₃} {RecursorFixtures:Tree:below {motive₀} x₃} (RecursorFixtures:Tree:brecOn:go {motive₀} x₃ F1₂)))} t₁ (Eq:refl {motive₀ RecursorFixtures:Tree:leaf} (RecursorFixtures:Tree:brecOn {motive₀} RecursorFixtures:Tree:leaf F1₂)) (λ (left₃ : RecursorFixtures:Tree) → λ (right₄ : RecursorFixtures:Tree) → Eq:refl {motive₀ (RecursorFixtures:Tree:node left₃ right₄)} (RecursorFixtures:Tree:brecOn {motive₀} (RecursorFixtures:Tree:node left₃ right₄) F1₂))

RecursorFixtures:Tree:ctorElimType : {_ : RecursorFixtures:Tree → Set} → Nat → Set
RecursorFixtures:Tree:ctorElimType {motive₀} ctorIdx₁ = cond {Set} (Nat:ble ctorIdx₁ 0) (PULift (motive₀ RecursorFixtures:Tree:leaf)) (PULift ((left₂ : RecursorFixtures:Tree) → (right₃ : RecursorFixtures:Tree) → motive₀ (RecursorFixtures:Tree:node left₂ right₃)))

RecursorFixtures:Tree:ctorIdx : RecursorFixtures:Tree → Nat
RecursorFixtures:Tree:ctorIdx x₀ = RecursorFixtures:Tree:casesOn {λ (x₁ : RecursorFixtures:Tree) → Nat} x₀ 0 (λ (left₁ : RecursorFixtures:Tree) → λ (right₂ : RecursorFixtures:Tree) → 1)

RecursorFixtures:Tree:ctorElim : {motive₀ : RecursorFixtures:Tree → Set} → (ctorIdx₁ : Nat) → (t₂ : RecursorFixtures:Tree) → Eq {Nat} ctorIdx₁ (RecursorFixtures:Tree:ctorIdx t₂) → RecursorFixtures:Tree:ctorElimType {motive₀} ctorIdx₁ → motive₀ t₂
RecursorFixtures:Tree:ctorElim {motive₀} ctorIdx₁ t₂ h₃ k₄ = RecursorFixtures:Tree:casesOn {λ (t₅ : RecursorFixtures:Tree) → Eq {Nat} ctorIdx₁ (RecursorFixtures:Tree:ctorIdx t₅) → motive₀ t₅} t₂ (λ (h₅ : Eq {Nat} ctorIdx₁ 0) → PULift:down {motive₀ RecursorFixtures:Tree:leaf} (Eq:ndrec {Nat} {ctorIdx₁} {RecursorFixtures:Tree:ctorElimType {motive₀}} k₄ {0} h₅)) (λ (left₅ : RecursorFixtures:Tree) → λ (right₆ : RecursorFixtures:Tree) → λ (h₇ : Eq {Nat} ctorIdx₁ 1) → PULift:down {(left₈ : RecursorFixtures:Tree) → (right₉ : RecursorFixtures:Tree) → motive₀ (RecursorFixtures:Tree:node left₈ right₉)} (Eq:ndrec {Nat} {ctorIdx₁} {RecursorFixtures:Tree:ctorElimType {motive₀}} k₄ {1} h₇) left₅ right₆) h₃

RecursorFixtures:Tree:leaf:elim : {motive₀ : RecursorFixtures:Tree → Set} → (t₁ : RecursorFixtures:Tree) → Eq {Nat} (RecursorFixtures:Tree:ctorIdx t₁) 0 → motive₀ RecursorFixtures:Tree:leaf → motive₀ t₁
RecursorFixtures:Tree:leaf:elim {motive₀} t₁ h₂ leaf₃ = RecursorFixtures:Tree:ctorElim {motive₀} 0 t₁ (Eq:symm {Nat} {RecursorFixtures:Tree:ctorIdx t₁} {0} h₂) (PULift:up {motive₀ RecursorFixtures:Tree:leaf} leaf₃)

-- theorem
opaque
  RecursorFixtures:Tree:leaf:sizeOf~uspec : Eq {Nat} (SizeOf:sizeOf {RecursorFixtures:Tree} ⦃ RecursorFixtures:Tree:~usizeOf~uinst ⦄ RecursorFixtures:Tree:leaf) (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)
  RecursorFixtures:Tree:leaf:sizeOf~uspec = Eq:refl {Nat} (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)

RecursorFixtures:Tree:leaves : RecursorFixtures:Tree → Nat
RecursorFixtures:Tree:leaves t₀ = RecursorFixtures:Tree:rec {λ (x₁ : RecursorFixtures:Tree) → Nat} (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (λ (x₁ : RecursorFixtures:Tree) → λ (x₂ : RecursorFixtures:Tree) → λ (l₃ : Nat) → λ (r₄ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ l₃ r₄) t₀

-- theorem
opaque
  RecursorFixtures:Tree:leaves~uexample : Eq {Nat} (RecursorFixtures:Tree:leaves (RecursorFixtures:Tree:node RecursorFixtures:Tree:leaf (RecursorFixtures:Tree:node RecursorFixtures:Tree:leaf RecursorFixtures:Tree:leaf))) (OfNat:ofNat {Nat} 3 ⦃ instOfNatNat 3 ⦄)
  RecursorFixtures:Tree:leaves~uexample = rfl {Nat} {RecursorFixtures:Tree:leaves (RecursorFixtures:Tree:node RecursorFixtures:Tree:leaf (RecursorFixtures:Tree:node RecursorFixtures:Tree:leaf RecursorFixtures:Tree:leaf))}

RecursorFixtures:Tree:noConfusionType : Set → RecursorFixtures:Tree → RecursorFixtures:Tree → Set
RecursorFixtures:Tree:noConfusionType P₀ t₁ t₂ = RecursorFixtures:Tree:casesOn {λ (t₃ : RecursorFixtures:Tree) → Set} t₁ (RecursorFixtures:Tree:casesOn {λ (t₃ : RecursorFixtures:Tree) → Set} t₂ (P₀ → P₀) (λ (left₃ : RecursorFixtures:Tree) → λ (right₄ : RecursorFixtures:Tree) → P₀)) (λ (left₃ : RecursorFixtures:Tree) → λ (right₄ : RecursorFixtures:Tree) → RecursorFixtures:Tree:casesOn {λ (t₅ : RecursorFixtures:Tree) → Set} t₂ P₀ (λ (left₅ : RecursorFixtures:Tree) → λ (right₆ : RecursorFixtures:Tree) → (Eq {RecursorFixtures:Tree} left₃ left₅ → Eq {RecursorFixtures:Tree} right₄ right₆ → P₀) → P₀))

RecursorFixtures:Tree:noConfusion : {P₀ : Set} → {t₁ : RecursorFixtures:Tree} → {t₂ : RecursorFixtures:Tree} → Eq {RecursorFixtures:Tree} t₁ t₂ → RecursorFixtures:Tree:noConfusionType P₀ t₁ t₂
RecursorFixtures:Tree:noConfusion {P₀} {t₁} {t₂} eq₃ = Eq:ndrec {RecursorFixtures:Tree} {t₁} {λ (t₄ : RecursorFixtures:Tree) → RecursorFixtures:Tree:noConfusionType P₀ t₁ t₄} (RecursorFixtures:Tree:casesOn {λ (t₄ : RecursorFixtures:Tree) → RecursorFixtures:Tree:noConfusionType P₀ t₄ t₄} t₁ (λ (k₄ : P₀) → k₄) (λ (left₄ : RecursorFixtures:Tree) → λ (right₅ : RecursorFixtures:Tree) → λ (k₆ : Eq {RecursorFixtures:Tree} left₄ left₄ → Eq {RecursorFixtures:Tree} right₅ right₅ → P₀) → k₆ (Eq:refl {RecursorFixtures:Tree} left₄) (Eq:refl {RecursorFixtures:Tree} right₅))) {t₂} eq₃

RecursorFixtures:Tree:node:elim : {motive₀ : RecursorFixtures:Tree → Set} → (t₁ : RecursorFixtures:Tree) → Eq {Nat} (RecursorFixtures:Tree:ctorIdx t₁) 1 → ((left₂ : RecursorFixtures:Tree) → (right₃ : RecursorFixtures:Tree) → motive₀ (RecursorFixtures:Tree:node left₂ right₃)) → motive₀ t₁
RecursorFixtures:Tree:node:elim {motive₀} t₁ h₂ node₃ = RecursorFixtures:Tree:ctorElim {motive₀} 1 t₁ (Eq:symm {Nat} {RecursorFixtures:Tree:ctorIdx t₁} {1} h₂) (PULift:up {(left₄ : RecursorFixtures:Tree) → (right₅ : RecursorFixtures:Tree) → motive₀ (RecursorFixtures:Tree:node left₄ right₅)} node₃)

RecursorFixtures:Tree:node:noConfusion : {P₀ : Set} → {left₁ : RecursorFixtures:Tree} → {right₂ : RecursorFixtures:Tree} → {left₃ : RecursorFixtures:Tree} → {right₄ : RecursorFixtures:Tree} → Eq {RecursorFixtures:Tree} (RecursorFixtures:Tree:node left₁ right₂) (RecursorFixtures:Tree:node left₃ right₄) → (Eq {RecursorFixtures:Tree} left₁ left₃ → Eq {RecursorFixtures:Tree} right₂ right₄ → P₀) → P₀
RecursorFixtures:Tree:node:noConfusion {P₀} {left₁} {right₂} {left₃} {right₄} eq₅ k₆ = id {P₀} (RecursorFixtures:Tree:noConfusion {P₀} {RecursorFixtures:Tree:node left₁ right₂} {RecursorFixtures:Tree:node left₃ right₄} eq₅ k₆)

-- theorem
opaque
  RecursorFixtures:Tree:node:inj : {left₀ : RecursorFixtures:Tree} → {right₁ : RecursorFixtures:Tree} → {left₂ : RecursorFixtures:Tree} → {right₃ : RecursorFixtures:Tree} → Eq {RecursorFixtures:Tree} (RecursorFixtures:Tree:node left₀ right₁) (RecursorFixtures:Tree:node left₂ right₃) → And (Eq {RecursorFixtures:Tree} left₀ left₂) (Eq {RecursorFixtures:Tree} right₁ right₃)
  RecursorFixtures:Tree:node:inj {left₀} {right₁} {left₂} {right₃} x₄ = RecursorFixtures:Tree:node:noConfusion {And (Eq {RecursorFixtures:Tree} left₀ left₂) (Eq {RecursorFixtures:Tree} right₁ right₃)} {left₀} {right₁} {left₂} {right₃} x₄ (λ (lefteq₅ : Eq {RecursorFixtures:Tree} left₀ left₂) → λ (righteq₆ : Eq {RecursorFixtures:Tree} right₁ right₃) → And:intro {Eq {RecursorFixtures:Tree} left₀ left₂} {Eq {RecursorFixtures:Tree} right₁ right₃} lefteq₅ righteq₆)

-- theorem
opaque
  RecursorFixtures:Tree:node:injEq : (left₀ : RecursorFixtures:Tree) → (right₁ : RecursorFixtures:Tree) → (left₂ : RecursorFixtures:Tree) → (right₃ : RecursorFixtures:Tree) → Eq {Set} (Eq {RecursorFixtures:Tree} (RecursorFixtures:Tree:node left₀ right₁) (RecursorFixtures:Tree:node left₂ right₃)) (And (Eq {RecursorFixtures:Tree} left₀ left₂) (Eq {RecursorFixtures:Tree} right₁ right₃))
  RecursorFixtures:Tree:node:injEq left₀ right₁ left₂ right₃ = Eq:propIntro {Eq {RecursorFixtures:Tree} (RecursorFixtures:Tree:node left₀ right₁) (RecursorFixtures:Tree:node left₂ right₃)} {And (Eq {RecursorFixtures:Tree} left₀ left₂) (Eq {RecursorFixtures:Tree} right₁ right₃)} (RecursorFixtures:Tree:node:inj {left₀} {right₁} {left₂} {right₃}) (Lean:injEq~uhelper {Eq {RecursorFixtures:Tree} left₀ left₂} {Eq {RecursorFixtures:Tree} right₁ right₃} {Eq {RecursorFixtures:Tree} (RecursorFixtures:Tree:node left₀ right₁) (RecursorFixtures:Tree:node left₂ right₃)} (Eq:ndrec {RecursorFixtures:Tree} {left₀} {λ (left₄ : RecursorFixtures:Tree) → Eq {RecursorFixtures:Tree} right₁ right₃ → Eq {RecursorFixtures:Tree} (RecursorFixtures:Tree:node left₀ right₁) (RecursorFixtures:Tree:node left₄ right₃)} (Eq:ndrec {RecursorFixtures:Tree} {right₁} {λ (right₄ : RecursorFixtures:Tree) → Eq {RecursorFixtures:Tree} (RecursorFixtures:Tree:node left₀ right₁) (RecursorFixtures:Tree:node left₀ right₄)} (Eq:refl {RecursorFixtures:Tree} (RecursorFixtures:Tree:node left₀ right₁)) {right₃}) {left₂}))

-- theorem
opaque
  RecursorFixtures:Tree:node:sizeOf~uspec : (left₀ : RecursorFixtures:Tree) → (right₁ : RecursorFixtures:Tree) → Eq {Nat} (SizeOf:sizeOf {RecursorFixtures:Tree} ⦃ RecursorFixtures:Tree:~usizeOf~uinst ⦄ (RecursorFixtures:Tree:node left₀ right₁)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {RecursorFixtures:Tree} ⦃ RecursorFixtures:Tree:~usizeOf~uinst ⦄ left₀)) (SizeOf:sizeOf {RecursorFixtures:Tree} ⦃ RecursorFixtures:Tree:~usizeOf~uinst ⦄ right₁))
  RecursorFixtures:Tree:node:sizeOf~uspec left₀ right₁ = Eq:refl {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {RecursorFixtures:Tree} ⦃ RecursorFixtures:Tree:~usizeOf~uinst ⦄ left₀)) (SizeOf:sizeOf {RecursorFixtures:Tree} ⦃ RecursorFixtures:Tree:~usizeOf~uinst ⦄ right₁))

RecursorFixtures:Tree:recOn : {motive₀ : RecursorFixtures:Tree → Set} → (t₁ : RecursorFixtures:Tree) → motive₀ RecursorFixtures:Tree:leaf → ((left₂ : RecursorFixtures:Tree) → (right₃ : RecursorFixtures:Tree) → motive₀ left₂ → motive₀ right₃ → motive₀ (RecursorFixtures:Tree:node left₂ right₃)) → motive₀ t₁
RecursorFixtures:Tree:recOn {motive₀} t₁ leaf₂ node₃ = RecursorFixtures:Tree:rec {motive₀} leaf₂ node₃ t₁

RecursorFixtures:Tree:size:match~u1 : (motive₀ : RecursorFixtures:Tree → Set) → (x₁ : RecursorFixtures:Tree) → (Unit → motive₀ RecursorFixtures:Tree:leaf) → ((l₂ : RecursorFixtures:Tree) → (r₃ : RecursorFixtures:Tree) → motive₀ (RecursorFixtures:Tree:node l₂ r₃)) → motive₀ x₁
RecursorFixtures:Tree:size:match~u1 motive₀ x₁ h1₂ h2₃ = RecursorFixtures:Tree:casesOn {λ (x₄ : RecursorFixtures:Tree) → motive₀ x₄} x₁ (h1₂ Unit:unit) (λ (left₄ : RecursorFixtures:Tree) → λ (right₅ : RecursorFixtures:Tree) → h2₃ left₄ right₅)

RecursorFixtures:Tree:size:~uf : (x₀ : RecursorFixtures:Tree) → RecursorFixtures:Tree:below {λ (x₁ : RecursorFixtures:Tree) → Nat} x₀ → Nat
RecursorFixtures:Tree:size:~uf x₀ f₁ = RecursorFixtures:Tree:size:match~u1 (λ (x₂ : RecursorFixtures:Tree) → RecursorFixtures:Tree:below {λ (x₃ : RecursorFixtures:Tree) → Nat} x₂ → Nat) x₀ (λ (x₂ : Unit) → λ (x₃ : RecursorFixtures:Tree:below {λ (x₃ : RecursorFixtures:Tree) → Nat} RecursorFixtures:Tree:leaf) → OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (λ (l₂ : RecursorFixtures:Tree) → λ (r₃ : RecursorFixtures:Tree) → λ (x₄ : RecursorFixtures:Tree:below {λ (x₄ : RecursorFixtures:Tree) → Nat} (RecursorFixtures:Tree:node l₂ r₃)) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (PProd.fst₂ {(λ (x₅ : RecursorFixtures:Tree) → Nat) l₂} {RecursorFixtures:Tree:rec {λ (t₅ : RecursorFixtures:Tree) → Set} PUnit (λ (left₅ : RecursorFixtures:Tree) → λ (right₆ : RecursorFixtures:Tree) → λ (leftih₇ : Set) → λ (rightih₈ : Set) → PProd (PProd ((λ (x₉ : RecursorFixtures:Tree) → Nat) left₅) leftih₇) (PProd ((λ (x₉ : RecursorFixtures:Tree) → Nat) right₆) rightih₈)) l₂} (PProd.fst₂ {PProd ((λ (x₅ : RecursorFixtures:Tree) → Nat) l₂) (RecursorFixtures:Tree:rec {λ (t₅ : RecursorFixtures:Tree) → Set} PUnit (λ (left₅ : RecursorFixtures:Tree) → λ (right₆ : RecursorFixtures:Tree) → λ (leftih₇ : Set) → λ (rightih₈ : Set) → PProd (PProd ((λ (x₉ : RecursorFixtures:Tree) → Nat) left₅) leftih₇) (PProd ((λ (x₉ : RecursorFixtures:Tree) → Nat) right₆) rightih₈)) l₂)} {PProd ((λ (x₅ : RecursorFixtures:Tree) → Nat) r₃) (RecursorFixtures:Tree:rec {λ (t₅ : RecursorFixtures:Tree) → Set} PUnit (λ (left₅ : RecursorFixtures:Tree) → λ (right₆ : RecursorFixtures:Tree) → λ (leftih₇ : Set) → λ (rightih₈ : Set) → PProd (PProd ((λ (x₉ : RecursorFixtures:Tree) → Nat) left₅) leftih₇) (PProd ((λ (x₉ : RecursorFixtures:Tree) → Nat) right₆) rightih₈)) r₃)} x₄)) (PProd.fst₂ {(λ (x₅ : RecursorFixtures:Tree) → Nat) r₃} {RecursorFixtures:Tree:rec {λ (t₅ : RecursorFixtures:Tree) → Set} PUnit (λ (left₅ : RecursorFixtures:Tree) → λ (right₆ : RecursorFixtures:Tree) → λ (leftih₇ : Set) → λ (rightih₈ : Set) → PProd (PProd ((λ (x₉ : RecursorFixtures:Tree) → Nat) left₅) leftih₇) (PProd ((λ (x₉ : RecursorFixtures:Tree) → Nat) right₆) rightih₈)) r₃} (PProd.snd₃ {PProd ((λ (x₅ : RecursorFixtures:Tree) → Nat) l₂) (RecursorFixtures:Tree:rec {λ (t₅ : RecursorFixtures:Tree) → Set} PUnit (λ (left₅ : RecursorFixtures:Tree) → λ (right₆ : RecursorFixtures:Tree) → λ (leftih₇ : Set) → λ (rightih₈ : Set) → PProd (PProd ((λ (x₉ : RecursorFixtures:Tree) → Nat) left₅) leftih₇) (PProd ((λ (x₉ : RecursorFixtures:Tree) → Nat) right₆) rightih₈)) l₂)} {PProd ((λ (x₅ : RecursorFixtures:Tree) → Nat) r₃) (RecursorFixtures:Tree:rec {λ (t₅ : RecursorFixtures:Tree) → Set} PUnit (λ (left₅ : RecursorFixtures:Tree) → λ (right₆ : RecursorFixtures:Tree) → λ (leftih₇ : Set) → λ (rightih₈ : Set) → PProd (PProd ((λ (x₉ : RecursorFixtures:Tree) → Nat) left₅) leftih₇) (PProd ((λ (x₉ : RecursorFixtures:Tree) → Nat) right₆) rightih₈)) r₃)} x₄))) (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) f₁

RecursorFixtures:Tree:size : RecursorFixtures:Tree → Nat
RecursorFixtures:Tree:size x₀ = RecursorFixtures:Tree:brecOn {λ (x₁ : RecursorFixtures:Tree) → Nat} x₀ RecursorFixtures:Tree:size:~uf

RecursorFixtures:Tree:size:~usunfold : RecursorFixtures:Tree → Nat
RecursorFixtures:Tree:size:~usunfold x₀ = RecursorFixtures:Tree:size:match~u1 (λ (x₁ : RecursorFixtures:Tree) → Nat) x₀ (λ (x₁ : Unit) → OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (λ (l₁ : RecursorFixtures:Tree) → λ (r₂ : RecursorFixtures:Tree) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (RecursorFixtures:Tree:size l₁) (RecursorFixtures:Tree:size r₂)) (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))

-- cyclic definition, postulated
postulate RecursorFixtures:Tree:size:~uunsafe~urec : RecursorFixtures:Tree → Nat

-- theorem
opaque
  RecursorFixtures:Tree:size~uexample : Eq {Nat} (RecursorFixtures:Tree:size (RecursorFixtures:Tree:node RecursorFixtures:Tree:leaf (RecursorFixtures:Tree:node RecursorFixtures:Tree:leaf RecursorFixtures:Tree:leaf))) (OfNat:ofNat {Nat} 5 ⦃ instOfNatNat 5 ⦄)
  RecursorFixtures:Tree:size~uexample = rfl {Nat} {RecursorFixtures:Tree:size (RecursorFixtures:Tree:node RecursorFixtures:Tree:leaf (RecursorFixtures:Tree:node RecursorFixtures:Tree:leaf RecursorFixtures:Tree:leaf))}

data RecursorFixtures:Vec (α₀ : Set) : Nat → Set where
  RecursorFixtures:Vec:nil : RecursorFixtures:Vec α₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)
  RecursorFixtures:Vec:cons : {n₁ : Nat} → α₀ → RecursorFixtures:Vec α₀ n₁ → RecursorFixtures:Vec α₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))

-- recursor
RecursorFixtures:Vec:rec : {α₀ : Set} → {motive₁ : (a₁ : Nat) → RecursorFixtures:Vec α₀ a₁ → Set} → motive₁ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (RecursorFixtures:Vec:nil {α₀}) → ({n₂ : Nat} → (head₃ : α₀) → (tail₄ : RecursorFixtures:Vec α₀ n₂) → motive₁ n₂ tail₄ → motive₁ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₂ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (RecursorFixtures:Vec:cons {α₀} {n₂} head₃ tail₄)) → {a₂ : Nat} → (t₃ : RecursorFixtures:Vec α₀ a₂) → motive₁ a₂ t₃
RecursorFixtures:Vec:rec {α₀} {motive₁} nil₂ cons₃ {_} RecursorFixtures:Vec:nil = nil₂
RecursorFixtures:Vec:rec {α₀} {motive₁} nil₂ cons₃ {_} (RecursorFixtures:Vec:cons {n₅} head₆ tail₇) = cons₃ {n₅} head₆ tail₇ (RecursorFixtures:Vec:rec {α₀} {motive₁} nil₂ cons₃ {n₅} tail₇)

RecursorFixtures:Vec:~usizeOf~u1 : {α₀ : Set} → ⦃ _ : SizeOf α₀ ⦄ → {a₁ : Nat} → RecursorFixtures:Vec α₀ a₁ → Nat
RecursorFixtures:Vec:~usizeOf~u1 {α₀} ⦃ inst₁ ⦄ {a₂} t₃ = RecursorFixtures:Vec:rec {α₀} {λ (a₄ : Nat) → λ (t₅ : RecursorFixtures:Vec α₀ a₄) → Nat} (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (λ {n₄ : Nat} → λ (head₅ : α₀) → λ (tail₆ : RecursorFixtures:Vec α₀ n₄) → λ (tailih₇ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {Nat} ⦃ instSizeOfNat ⦄ n₄)) (SizeOf:sizeOf {α₀} ⦃ inst₁ ⦄ head₅)) tailih₇) {a₂} t₃

RecursorFixtures:Vec:~usizeOf~uinst : (α₀ : Set) → (a₁ : Nat) → ⦃ _ : SizeOf α₀ ⦄ → SizeOf (RecursorFixtures:Vec α₀ a₁)
RecursorFixtures:Vec:~usizeOf~uinst α₀ a₁ ⦃ inst₂ ⦄ = SizeOf:mk {RecursorFixtures:Vec α₀ a₁} (λ (m₃ : RecursorFixtures:Vec α₀ a₁) → RecursorFixtures:Vec:~usizeOf~u1 {α₀} ⦃ inst₂ ⦄ {a₁} m₃)

RecursorFixtures:Vec:below : {α₀ : Set} → {_ : (a₁ : Nat) → RecursorFixtures:Vec α₀ a₁ → Set} → {a₁ : Nat} → RecursorFixtures:Vec α₀ a₁ → Set
RecursorFixtures:Vec:below {α₀} {motive₁} {a₂} t₃ = RecursorFixtures:Vec:rec {α₀} {λ (a₄ : Nat) → λ (t₅ : RecursorFixtures:Vec α₀ a₄) → Set} PUnit (λ {n₄ : Nat} → λ (head₅ : α₀) → λ (tail₆ : RecursorFixtures:Vec α₀ n₄) → λ (tailih₇ : Set) → PProd (motive₁ n₄ tail₆) tailih₇) {a₂} t₃

RecursorFixtures:Vec:brecOn:go : {α₀ : Set} → {motive₁ : (a₁ : Nat) → RecursorFixtures:Vec α₀ a₁ → Set} → {a₂ : Nat} → (t₃ : RecursorFixtures:Vec α₀ a₂) → ((a₄ : Nat) → (t₅ : RecursorFixtures:Vec α₀ a₄) → RecursorFixtures:Vec:below {α₀} {motive₁} {a₄} t₅ → motive₁ a₄ t₅) → PProd (motive₁ a₂ t₃) (RecursorFixtures:Vec:below {α₀} {motive₁} {a₂} t₃)
RecursorFixtures:Vec:brecOn:go {α₀} {motive₁} {a₂} t₃ F1₄ = RecursorFixtures:Vec:rec {α₀} {λ (a₅ : Nat) → λ (t₆ : RecursorFixtures:Vec α₀ a₅) → PProd (motive₁ a₅ t₆) (RecursorFixtures:Vec:below {α₀} {motive₁} {a₅} t₆)} (PProd:mk {motive₁ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (RecursorFixtures:Vec:nil {α₀})} {PUnit} (F1₄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (RecursorFixtures:Vec:nil {α₀}) PUnit:unit) PUnit:unit) (λ {n₅ : Nat} → λ (head₆ : α₀) → λ (tail₇ : RecursorFixtures:Vec α₀ n₅) → λ (tailih₈ : PProd (motive₁ n₅ tail₇) (RecursorFixtures:Vec:below {α₀} {motive₁} {n₅} tail₇)) → PProd:mk {motive₁ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (RecursorFixtures:Vec:cons {α₀} {n₅} head₆ tail₇)} {PProd (motive₁ n₅ tail₇) (RecursorFixtures:Vec:below {α₀} {motive₁} {n₅} tail₇)} (F1₄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (RecursorFixtures:Vec:cons {α₀} {n₅} head₆ tail₇) tailih₈) tailih₈) {a₂} t₃

RecursorFixtures:Vec:brecOn : {α₀ : Set} → {motive₁ : (a₁ : Nat) → RecursorFixtures:Vec α₀ a₁ → Set} → {a₂ : Nat} → (t₃ : RecursorFixtures:Vec α₀ a₂) → ((a₄ : Nat) → (t₅ : RecursorFixtures:Vec α₀ a₄) → RecursorFixtures:Vec:below {α₀} {motive₁} {a₄} t₅ → motive₁ a₄ t₅) → motive₁ a₂ t₃
RecursorFixtures:Vec:brecOn {α₀} {motive₁} {a₂} t₃ F1₄ = PProd.fst₂ {motive₁ a₂ t₃} {RecursorFixtures:Vec:below {α₀} {motive₁} {a₂} t₃} (RecursorFixtures:Vec:brecOn:go {α₀} {motive₁} {a₂} t₃ F1₄)

RecursorFixtures:Vec:casesOn : {α₀ : Set} → {motive₁ : (a₁ : Nat) → RecursorFixtures:Vec α₀ a₁ → Set} → {a₂ : Nat} → (t₃ : RecursorFixtures:Vec α₀ a₂) → motive₁ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (RecursorFixtures:Vec:nil {α₀}) → ({n₄ : Nat} → (head₅ : α₀) → (tail₆ : RecursorFixtures:Vec α₀ n₄) → motive₁ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (RecursorFixtures:Vec:cons {α₀} {n₄} head₅ tail₆)) → motive₁ a₂ t₃
RecursorFixtures:Vec:casesOn {α₀} {motive₁} {a₂} t₃ nil₄ cons₅ = RecursorFixtures:Vec:rec {α₀} {motive₁} nil₄ (λ {n₆ : Nat} → λ (head₇ : α₀) → λ (tail₈ : RecursorFixtures:Vec α₀ n₆) → λ (tailih₉ : motive₁ n₆ tail₈) → cons₅ {n₆} head₇ tail₈) {a₂} t₃

-- theorem
opaque
  RecursorFixtures:Vec:brecOn:eq : {α₀ : Set} → {motive₁ : (a₁ : Nat) → RecursorFixtures:Vec α₀ a₁ → Set} → {a₂ : Nat} → (t₃ : RecursorFixtures:Vec α₀ a₂) → (F1₄ : (a₄ : Nat) → (t₅ : RecursorFixtures:Vec α₀ a₄) → RecursorFixtures:Vec:below {α₀} {motive₁} {a₄} t₅ → motive₁ a₄ t₅) → Eq {motive₁ a₂ t₃} (RecursorFixtures:Vec:brecOn {α₀} {motive₁} {a₂} t₃ F1₄) (F1₄ a₂ t₃ (PProd.snd₃ {motive₁ a₂ t₃} {RecursorFixtures:Vec:below {α₀} {motive₁} {a₂} t₃} (RecursorFixtures:Vec:brecOn:go {α₀} {motive₁} {a₂} t₃ F1₄)))
  RecursorFixtures:Vec:brecOn:eq {α₀} {motive₁} {a₂} t₃ F1₄ = RecursorFixtures:Vec:casesOn {α₀} {λ (a₅ : Nat) → λ (x₆ : RecursorFixtures:Vec α₀ a₅) → Eq {Nat} a₂ a₅ → HEq {RecursorFixtures:Vec α₀ a₂} t₃ {RecursorFixtures:Vec α₀ a₅} x₆ → Eq {motive₁ a₂ t₃} (RecursorFixtures:Vec:brecOn {α₀} {motive₁} {a₂} t₃ F1₄) (F1₄ a₂ t₃ (PProd.snd₃ {motive₁ a₂ t₃} {RecursorFixtures:Vec:below {α₀} {motive₁} {a₂} t₃} (RecursorFixtures:Vec:brecOn:go {α₀} {motive₁} {a₂} t₃ F1₄)))} {a₂} t₃ (λ (h₅ : Eq {Nat} a₂ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → Eq:ndrec {Nat} {OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄} {λ (a₆ : Nat) → (t₇ : RecursorFixtures:Vec α₀ a₆) → HEq {RecursorFixtures:Vec α₀ a₆} t₇ {RecursorFixtures:Vec α₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)} (RecursorFixtures:Vec:nil {α₀}) → Eq {motive₁ a₆ t₇} (RecursorFixtures:Vec:brecOn {α₀} {motive₁} {a₆} t₇ F1₄) (F1₄ a₆ t₇ (PProd.snd₃ {motive₁ a₆ t₇} {RecursorFixtures:Vec:below {α₀} {motive₁} {a₆} t₇} (RecursorFixtures:Vec:brecOn:go {α₀} {motive₁} {a₆} t₇ F1₄)))} (λ (t₆ : RecursorFixtures:Vec α₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → λ (h₇ : HEq {RecursorFixtures:Vec α₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)} t₆ {RecursorFixtures:Vec α₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)} (RecursorFixtures:Vec:nil {α₀})) → Eq:ndrec {RecursorFixtures:Vec α₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)} {RecursorFixtures:Vec:nil {α₀}} {λ (t₈ : RecursorFixtures:Vec α₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → Eq {motive₁ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) t₈} (RecursorFixtures:Vec:brecOn {α₀} {motive₁} {OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄} t₈ F1₄) (F1₄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) t₈ (PProd.snd₃ {motive₁ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) t₈} {RecursorFixtures:Vec:below {α₀} {motive₁} {OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄} t₈} (RecursorFixtures:Vec:brecOn:go {α₀} {motive₁} {OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄} t₈ F1₄)))} (Eq:refl {motive₁ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (RecursorFixtures:Vec:nil {α₀})} (RecursorFixtures:Vec:brecOn {α₀} {motive₁} {OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄} (RecursorFixtures:Vec:nil {α₀}) F1₄)) {t₆} (Eq:symm {RecursorFixtures:Vec α₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)} {t₆} {RecursorFixtures:Vec:nil {α₀}} (eq~uof~uheq {RecursorFixtures:Vec α₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)} {t₆} {RecursorFixtures:Vec:nil {α₀}} h₇))) {a₂} (Eq:symm {Nat} {a₂} {OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄} h₅) t₃) (λ {n₅ : Nat} → λ (head₆ : α₀) → λ (tail₇ : RecursorFixtures:Vec α₀ n₅) → λ (h₈ : Eq {Nat} a₂ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → Eq:ndrec {Nat} {HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)} {λ (a₉ : Nat) → (t₁₀ : RecursorFixtures:Vec α₀ a₉) → HEq {RecursorFixtures:Vec α₀ a₉} t₁₀ {RecursorFixtures:Vec α₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} (RecursorFixtures:Vec:cons {α₀} {n₅} head₆ tail₇) → Eq {motive₁ a₉ t₁₀} (RecursorFixtures:Vec:brecOn {α₀} {motive₁} {a₉} t₁₀ F1₄) (F1₄ a₉ t₁₀ (PProd.snd₃ {motive₁ a₉ t₁₀} {RecursorFixtures:Vec:below {α₀} {motive₁} {a₉} t₁₀} (RecursorFixtures:Vec:brecOn:go {α₀} {motive₁} {a₉} t₁₀ F1₄)))} (λ (t₉ : RecursorFixtures:Vec α₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → λ (h₁₀ : HEq {RecursorFixtures:Vec α₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} t₉ {RecursorFixtures:Vec α₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} (RecursorFixtures:Vec:cons {α₀} {n₅} head₆ tail₇)) → Eq:ndrec {RecursorFixtures:Vec α₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} {RecursorFixtures:Vec:cons {α₀} {n₅} head₆ tail₇} {λ (t₁₁ : RecursorFixtures:Vec α₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → Eq {motive₁ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) t₁₁} (RecursorFixtures:Vec:brecOn {α₀} {motive₁} {HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)} t₁₁ F1₄) (F1₄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) t₁₁ (PProd.snd₃ {motive₁ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) t₁₁} {RecursorFixtures:Vec:below {α₀} {motive₁} {HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)} t₁₁} (RecursorFixtures:Vec:brecOn:go {α₀} {motive₁} {HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)} t₁₁ F1₄)))} (Eq:refl {motive₁ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (RecursorFixtures:Vec:cons {α₀} {n₅} head₆ tail₇)} (RecursorFixtures:Vec:brecOn {α₀} {motive₁} {HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)} (RecursorFixtures:Vec:cons {α₀} {n₅} head₆ tail₇) F1₄)) {t₉} (Eq:symm {RecursorFixtures:Vec α₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} {t₉} {RecursorFixtures:Vec:cons {α₀} {n₅} head₆ tail₇} (eq~uof~uheq {RecursorFixtures:Vec α₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} {t₉} {RecursorFixtures:Vec:cons {α₀} {n₅} head₆ tail₇} h₁₀))) {a₂} (Eq:symm {Nat} {a₂} {HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)} h₈) t₃) (Eq:refl {Nat} a₂) (HEq:refl {RecursorFixtures:Vec α₀ a₂} t₃)

RecursorFixtures:Vec:ctorElimType : {α₀ : Set} → {_ : (a₁ : Nat) → RecursorFixtures:Vec α₀ a₁ → Set} → Nat → Set
RecursorFixtures:Vec:ctorElimType {α₀} {motive₁} ctorIdx₂ = cond {Set} (Nat:ble ctorIdx₂ 0) (PULift (motive₁ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (RecursorFixtures:Vec:nil {α₀}))) (PULift ({n₃ : Nat} → (head₄ : α₀) → (tail₅ : RecursorFixtures:Vec α₀ n₃) → motive₁ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₃ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (RecursorFixtures:Vec:cons {α₀} {n₃} head₄ tail₅)))

RecursorFixtures:Vec:ctorIdx : {α₀ : Set} → {a₁ : Nat} → RecursorFixtures:Vec α₀ a₁ → Nat
RecursorFixtures:Vec:ctorIdx {α₀} {a₁} x₂ = RecursorFixtures:Vec:casesOn {α₀} {λ (a₃ : Nat) → λ (x₄ : RecursorFixtures:Vec α₀ a₃) → Nat} {a₁} x₂ 0 (λ {n₃ : Nat} → λ (head₄ : α₀) → λ (tail₅ : RecursorFixtures:Vec α₀ n₃) → 1)

RecursorFixtures:Vec:ctorElim : {α₀ : Set} → {motive₁ : (a₁ : Nat) → RecursorFixtures:Vec α₀ a₁ → Set} → (ctorIdx₂ : Nat) → {a₃ : Nat} → (t₄ : RecursorFixtures:Vec α₀ a₃) → Eq {Nat} ctorIdx₂ (RecursorFixtures:Vec:ctorIdx {α₀} {a₃} t₄) → RecursorFixtures:Vec:ctorElimType {α₀} {motive₁} ctorIdx₂ → motive₁ a₃ t₄
RecursorFixtures:Vec:ctorElim {α₀} {motive₁} ctorIdx₂ {a₃} t₄ h₅ k₆ = RecursorFixtures:Vec:casesOn {α₀} {λ (a₇ : Nat) → λ (t₈ : RecursorFixtures:Vec α₀ a₇) → Eq {Nat} ctorIdx₂ (RecursorFixtures:Vec:ctorIdx {α₀} {a₇} t₈) → motive₁ a₇ t₈} {a₃} t₄ (λ (h₇ : Eq {Nat} ctorIdx₂ 0) → PULift:down {motive₁ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (RecursorFixtures:Vec:nil {α₀})} (Eq:ndrec {Nat} {ctorIdx₂} {RecursorFixtures:Vec:ctorElimType {α₀} {motive₁}} k₆ {0} h₇)) (λ {n₇ : Nat} → λ (head₈ : α₀) → λ (tail₉ : RecursorFixtures:Vec α₀ n₇) → λ (h₁₀ : Eq {Nat} ctorIdx₂ 1) → PULift:down { {n₁₁ : Nat} → (head₁₂ : α₀) → (tail₁₃ : RecursorFixtures:Vec α₀ n₁₁) → motive₁ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (RecursorFixtures:Vec:cons {α₀} {n₁₁} head₁₂ tail₁₃) } (Eq:ndrec {Nat} {ctorIdx₂} {RecursorFixtures:Vec:ctorElimType {α₀} {motive₁}} k₆ {1} h₁₀) {n₇} head₈ tail₉) h₅

RecursorFixtures:Vec:cons:elim : {α₀ : Set} → {motive₁ : (a₁ : Nat) → RecursorFixtures:Vec α₀ a₁ → Set} → {a₂ : Nat} → (t₃ : RecursorFixtures:Vec α₀ a₂) → Eq {Nat} (RecursorFixtures:Vec:ctorIdx {α₀} {a₂} t₃) 1 → ({n₄ : Nat} → (head₅ : α₀) → (tail₆ : RecursorFixtures:Vec α₀ n₄) → motive₁ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (RecursorFixtures:Vec:cons {α₀} {n₄} head₅ tail₆)) → motive₁ a₂ t₃
RecursorFixtures:Vec:cons:elim {α₀} {motive₁} {a₂} t₃ h₄ cons₅ = RecursorFixtures:Vec:ctorElim {α₀} {motive₁} 1 {a₂} t₃ (Eq:symm {Nat} {RecursorFixtures:Vec:ctorIdx {α₀} {a₂} t₃} {1} h₄) (PULift:up { {n₆ : Nat} → (head₇ : α₀) → (tail₈ : RecursorFixtures:Vec α₀ n₆) → motive₁ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₆ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (RecursorFixtures:Vec:cons {α₀} {n₆} head₇ tail₈) } cons₅)

RecursorFixtures:Vec:noConfusionType : Set → {α₀ : Set} → {a₁ : Nat} → RecursorFixtures:Vec α₀ a₁ → {α₂ : Set} → {a₃ : Nat} → RecursorFixtures:Vec α₂ a₃ → Set
RecursorFixtures:Vec:noConfusionType P₀ {α₁} {a₂} t₃ {α₄} {a₅} t₆ = RecursorFixtures:Vec:casesOn {α₁} {λ (a₇ : Nat) → λ (t₈ : RecursorFixtures:Vec α₁ a₇) → Set} {a₂} t₃ (RecursorFixtures:Vec:casesOn {α₄} {λ (a₇ : Nat) → λ (t₈ : RecursorFixtures:Vec α₄ a₇) → Set} {a₅} t₆ (P₀ → P₀) (λ {n₇ : Nat} → λ (head₈ : α₄) → λ (tail₉ : RecursorFixtures:Vec α₄ n₇) → P₀)) (λ {n₇ : Nat} → λ (head₈ : α₁) → λ (tail₉ : RecursorFixtures:Vec α₁ n₇) → RecursorFixtures:Vec:casesOn {α₄} {λ (a₁₀ : Nat) → λ (t₁₁ : RecursorFixtures:Vec α₄ a₁₀) → Set} {a₅} t₆ P₀ (λ {n₁₀ : Nat} → λ (head₁₁ : α₄) → λ (tail₁₂ : RecursorFixtures:Vec α₄ n₁₀) → (Eq {Nat} n₇ n₁₀ → HEq {α₁} head₈ {α₄} head₁₁ → HEq {RecursorFixtures:Vec α₁ n₇} tail₉ {RecursorFixtures:Vec α₄ n₁₀} tail₁₂ → P₀) → P₀))

RecursorFixtures:Vec:noConfusion : {P₀ : Set} → {α₁ : Set} → {a₂ : Nat} → {t₃ : RecursorFixtures:Vec α₁ a₂} → {α₄ : Set} → {a₅ : Nat} → {t₆ : RecursorFixtures:Vec α₄ a₅} → Eq {Set} α₁ α₄ → Eq {Nat} a₂ a₅ → HEq {RecursorFixtures:Vec α₁ a₂} t₃ {RecursorFixtures:Vec α₄ a₅} t₆ → RecursorFixtures:Vec:noConfusionType P₀ {α₁} {a₂} t₃ {α₄} {a₅} t₆
RecursorFixtures:Vec:noConfusion {P₀} {α₁} {a₂} {t₃} {α₄} {a₅} {t₆} eq1₇ eq2₈ eq3₉ = Eq:ndrec {Set} {α₁} {λ (α₁₀ : Set) → {t₁₁ : RecursorFixtures:Vec α₁₀ a₅} → HEq {RecursorFixtures:Vec α₁ a₂} t₃ {RecursorFixtures:Vec α₁₀ a₅} t₁₁ → RecursorFixtures:Vec:noConfusionType P₀ {α₁} {a₂} t₃ {α₁₀} {a₅} t₁₁} (λ {t₁₀ : RecursorFixtures:Vec α₁ a₅} → λ (eq3₁₁ : HEq {RecursorFixtures:Vec α₁ a₂} t₃ {RecursorFixtures:Vec α₁ a₅} t₁₀) → Eq:ndrec {Nat} {a₂} {λ (a₁₂ : Nat) → {t₁₃ : RecursorFixtures:Vec α₁ a₁₂} → HEq {RecursorFixtures:Vec α₁ a₂} t₃ {RecursorFixtures:Vec α₁ a₁₂} t₁₃ → RecursorFixtures:Vec:noConfusionType P₀ {α₁} {a₂} t₃ {α₁} {a₁₂} t₁₃} (λ {t₁₂ : RecursorFixtures:Vec α₁ a₂} → λ (eq3₁₃ : HEq {RecursorFixtures:Vec α₁ a₂} t₃ {RecursorFixtures:Vec α₁ a₂} t₁₂) → Eq:ndrec {RecursorFixtures:Vec α₁ a₂} {t₃} {λ (t₁₄ : RecursorFixtures:Vec α₁ a₂) → RecursorFixtures:Vec:noConfusionType P₀ {α₁} {a₂} t₃ {α₁} {a₂} t₁₄} (RecursorFixtures:Vec:casesOn {α₁} {λ (a₁₄ : Nat) → λ (t₁₅ : RecursorFixtures:Vec α₁ a₁₄) → RecursorFixtures:Vec:noConfusionType P₀ {α₁} {a₁₄} t₁₅ {α₁} {a₁₄} t₁₅} {a₂} t₃ (λ (k₁₄ : P₀) → k₁₄) (λ {n₁₄ : Nat} → λ (head₁₅ : α₁) → λ (tail₁₆ : RecursorFixtures:Vec α₁ n₁₄) → λ (k₁₇ : Eq {Nat} n₁₄ n₁₄ → HEq {α₁} head₁₅ {α₁} head₁₅ → HEq {RecursorFixtures:Vec α₁ n₁₄} tail₁₆ {RecursorFixtures:Vec α₁ n₁₄} tail₁₆ → P₀) → k₁₇ (Eq:refl {Nat} n₁₄) (HEq:refl {α₁} head₁₅) (HEq:refl {RecursorFixtures:Vec α₁ n₁₄} tail₁₆))) {t₁₂} (eq~uof~uheq {RecursorFixtures:Vec α₁ a₂} {t₃} {t₁₂} eq3₁₃)) {a₅} eq2₈ {t₁₀} eq3₁₁) {α₄} eq1₇ {t₆} eq3₉

RecursorFixtures:Vec:cons:noConfusion : {α₀ : Set} → {P₁ : Set} → {n₂ : Nat} → {head₃ : α₀} → {tail₄ : RecursorFixtures:Vec α₀ n₂} → {n₅ : Nat} → {head₆ : α₀} → {tail₇ : RecursorFixtures:Vec α₀ n₅} → Eq {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₂ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) → HEq {RecursorFixtures:Vec α₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₂ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} (RecursorFixtures:Vec:cons {α₀} {n₂} head₃ tail₄) {RecursorFixtures:Vec α₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} (RecursorFixtures:Vec:cons {α₀} {n₅} head₆ tail₇) → (Eq {Nat} n₂ n₅ → HEq {α₀} head₃ {α₀} head₆ → HEq {RecursorFixtures:Vec α₀ n₂} tail₄ {RecursorFixtures:Vec α₀ n₅} tail₇ → P₁) → P₁
RecursorFixtures:Vec:cons:noConfusion {α₀} {P₁} {n₂} {head₃} {tail₄} {n₅} {head₆} {tail₇} eq1₈ eq2₉ k₁₀ = id {P₁} (RecursorFixtures:Vec:noConfusion {P₁} {α₀} {HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₂ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)} {RecursorFixtures:Vec:cons {α₀} {n₂} head₃ tail₄} {α₀} {HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₅ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)} {RecursorFixtures:Vec:cons {α₀} {n₅} head₆ tail₇} (Eq:refl {Set} α₀) eq1₈ eq2₉ k₁₀)

-- theorem
opaque
  RecursorFixtures:Vec:cons:inj : {α₀ : Set} → {n₁ : Nat} → {head₂ : α₀} → {tail₃ : RecursorFixtures:Vec α₀ n₁} → {head₄ : α₀} → {tail₅ : RecursorFixtures:Vec α₀ n₁} → Eq {RecursorFixtures:Vec α₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} (RecursorFixtures:Vec:cons {α₀} {n₁} head₂ tail₃) (RecursorFixtures:Vec:cons {α₀} {n₁} head₄ tail₅) → And (Eq {α₀} head₂ head₄) (Eq {RecursorFixtures:Vec α₀ n₁} tail₃ tail₅)
  RecursorFixtures:Vec:cons:inj {α₀} {n₁} {head₂} {tail₃} {head₄} {tail₅} x₆ = RecursorFixtures:Vec:cons:noConfusion {α₀} {And (Eq {α₀} head₂ head₄) (Eq {RecursorFixtures:Vec α₀ n₁} tail₃ tail₅)} {n₁} {head₂} {tail₃} {n₁} {head₄} {tail₅} (Eq:refl {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) (heq~uof~ueq {RecursorFixtures:Vec α₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} {RecursorFixtures:Vec:cons {α₀} {n₁} head₂ tail₃} {RecursorFixtures:Vec:cons {α₀} {n₁} head₄ tail₅} x₆) (λ (neq₇ : Eq {Nat} n₁ n₁) → λ (headeq₈ : HEq {α₀} head₂ {α₀} head₄) → λ (taileq₉ : HEq {RecursorFixtures:Vec α₀ n₁} tail₃ {RecursorFixtures:Vec α₀ n₁} tail₅) → And:intro {Eq {α₀} head₂ head₄} {Eq {RecursorFixtures:Vec α₀ n₁} tail₃ tail₅} (eq~uof~uheq {α₀} {head₂} {head₄} headeq₈) (eq~uof~uheq {RecursorFixtures:Vec α₀ n₁} {tail₃} {tail₅} taileq₉))

-- theorem
opaque
  RecursorFixtures:Vec:cons:injEq : {α₀ : Set} → {n₁ : Nat} → (head₂ : α₀) → (tail₃ : RecursorFixtures:Vec α₀ n₁) → (head₄ : α₀) → (tail₅ : RecursorFixtures:Vec α₀ n₁) → Eq {Set} (Eq {RecursorFixtures:Vec α₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} (RecursorFixtures:Vec:cons {α₀} {n₁} head₂ tail₃) (RecursorFixtures:Vec:cons {α₀} {n₁} head₄ tail₅)) (And (Eq {α₀} head₂ head₄) (Eq {RecursorFixtures:Vec α₀ n₁} tail₃ tail₅))
  RecursorFixtures:Vec:cons:injEq {α₀} {n₁} head₂ tail₃ head₄ tail₅ = Eq:propIntro {Eq {RecursorFixtures:Vec α₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} (RecursorFixtures:Vec:cons {α₀} {n₁} head₂ tail₃) (RecursorFixtures:Vec:cons {α₀} {n₁} head₄ tail₅)} {And (Eq {α₀} head₂ head₄) (Eq {RecursorFixtures:Vec α₀ n₁} tail₃ tail₅)} (RecursorFixtures:Vec:cons:inj {α₀} {n₁} {head₂} {tail₃} {head₄} {tail₅}) (Lean:injEq~uhelper {Eq {α₀} head₂ head₄} {Eq {RecursorFixtures:Vec α₀ n₁} tail₃ tail₅} {Eq {RecursorFixtures:Vec α₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} (RecursorFixtures:Vec:cons {α₀} {n₁} head₂ tail₃) (RecursorFixtures:Vec:cons {α₀} {n₁} head₄ tail₅)} (Eq:ndrec {α₀} {head₂} {λ (head₆ : α₀) → Eq {RecursorFixtures:Vec α₀ n₁} tail₃ tail₅ → Eq {RecursorFixtures:Vec α₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} (RecursorFixtures:Vec:cons {α₀} {n₁} head₂ tail₃) (RecursorFixtures:Vec:cons {α₀} {n₁} head₆ tail₅)} (Eq:ndrec {RecursorFixtures:Vec α₀ n₁} {tail₃} {λ (tail₆ : RecursorFixtures:Vec α₀ n₁) → Eq {RecursorFixtures:Vec α₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} (RecursorFixtures:Vec:cons {α₀} {n₁} head₂ tail₃) (RecursorFixtures:Vec:cons {α₀} {n₁} head₂ tail₆)} (Eq:refl {RecursorFixtures:Vec α₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} (RecursorFixtures:Vec:cons {α₀} {n₁} head₂ tail₃)) {tail₅}) {head₄}))

-- theorem
opaque
  RecursorFixtures:Vec:cons:sizeOf~uspec : {α₀ : Set} → ⦃ inst₁ : SizeOf α₀ ⦄ → {n₂ : Nat} → (head₃ : α₀) → (tail₄ : RecursorFixtures:Vec α₀ n₂) → Eq {Nat} (SizeOf:sizeOf {RecursorFixtures:Vec α₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₂ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))} ⦃ RecursorFixtures:Vec:~usizeOf~uinst α₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₂ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) ⦃ inst₁ ⦄ ⦄ (RecursorFixtures:Vec:cons {α₀} {n₂} head₃ tail₄)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {Nat} ⦃ instSizeOfNat ⦄ n₂)) (SizeOf:sizeOf {α₀} ⦃ inst₁ ⦄ head₃)) (SizeOf:sizeOf {RecursorFixtures:Vec α₀ n₂} ⦃ RecursorFixtures:Vec:~usizeOf~uinst α₀ n₂ ⦃ inst₁ ⦄ ⦄ tail₄))
  RecursorFixtures:Vec:cons:sizeOf~uspec {α₀} ⦃ inst₁ ⦄ {n₂} head₃ tail₄ = Eq:refl {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (SizeOf:sizeOf {Nat} ⦃ instSizeOfNat ⦄ n₂)) (SizeOf:sizeOf {α₀} ⦃ inst₁ ⦄ head₃)) (SizeOf:sizeOf {RecursorFixtures:Vec α₀ n₂} ⦃ RecursorFixtures:Vec:~usizeOf~uinst α₀ n₂ ⦃ inst₁ ⦄ ⦄ tail₄))

RecursorFixtures:Vec:nil:elim : {α₀ : Set} → {motive₁ : (a₁ : Nat) → RecursorFixtures:Vec α₀ a₁ → Set} → {a₂ : Nat} → (t₃ : RecursorFixtures:Vec α₀ a₂) → Eq {Nat} (RecursorFixtures:Vec:ctorIdx {α₀} {a₂} t₃) 0 → motive₁ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (RecursorFixtures:Vec:nil {α₀}) → motive₁ a₂ t₃
RecursorFixtures:Vec:nil:elim {α₀} {motive₁} {a₂} t₃ h₄ nil₅ = RecursorFixtures:Vec:ctorElim {α₀} {motive₁} 0 {a₂} t₃ (Eq:symm {Nat} {RecursorFixtures:Vec:ctorIdx {α₀} {a₂} t₃} {0} h₄) (PULift:up {motive₁ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (RecursorFixtures:Vec:nil {α₀})} nil₅)

-- theorem
opaque
  RecursorFixtures:Vec:nil:sizeOf~uspec : {α₀ : Set} → ⦃ inst₁ : SizeOf α₀ ⦄ → Eq {Nat} (SizeOf:sizeOf {RecursorFixtures:Vec α₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)} ⦃ RecursorFixtures:Vec:~usizeOf~uinst α₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) ⦃ inst₁ ⦄ ⦄ (RecursorFixtures:Vec:nil {α₀})) (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)
  RecursorFixtures:Vec:nil:sizeOf~uspec {α₀} ⦃ inst₁ ⦄ = Eq:refl {Nat} (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)

RecursorFixtures:Vec:recOn : {α₀ : Set} → {motive₁ : (a₁ : Nat) → RecursorFixtures:Vec α₀ a₁ → Set} → {a₂ : Nat} → (t₃ : RecursorFixtures:Vec α₀ a₂) → motive₁ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (RecursorFixtures:Vec:nil {α₀}) → ({n₄ : Nat} → (head₅ : α₀) → (tail₆ : RecursorFixtures:Vec α₀ n₄) → motive₁ n₄ tail₆ → motive₁ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (RecursorFixtures:Vec:cons {α₀} {n₄} head₅ tail₆)) → motive₁ a₂ t₃
RecursorFixtures:Vec:recOn {α₀} {motive₁} {a₂} t₃ nil₄ cons₅ = RecursorFixtures:Vec:rec {α₀} {motive₁} nil₄ cons₅ {a₂} t₃

RecursorFixtures:Vec:sum : {n₀ : Nat} → RecursorFixtures:Vec Nat n₀ → Nat
RecursorFixtures:Vec:sum {n₀} v₁ = RecursorFixtures:Vec:rec {Nat} {λ (x₂ : Nat) → λ (x₃ : RecursorFixtures:Vec Nat x₂) → Nat} (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (λ {n₂ : Nat} → λ (h₃ : Nat) → λ (x₄ : RecursorFixtures:Vec Nat n₂) → λ (s₅ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ h₃ s₅) {n₀} v₁

RecursorFixtures:Vec:sum~uexample:~ushare:~n1 : Nat
RecursorFixtures:Vec:sum~uexample:~ushare:~n1 = HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)

RecursorFixtures:Vec:sum~uexample:~ushare:~n2 : Nat
RecursorFixtures:Vec:sum~uexample:~ushare:~n2 = RecursorFixtures:Vec:sum {HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ RecursorFixtures:Vec:sum~uexample:~ushare:~n1 (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)} (RecursorFixtures:Vec:cons {Nat} {RecursorFixtures:Vec:sum~uexample:~ushare:~n1} (OfNat:ofNat {Nat} 2 ⦃ instOfNatNat 2 ⦄) (RecursorFixtures:Vec:cons {Nat} {OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄} (OfNat:ofNat {Nat} 3 ⦃ instOfNatNat 3 ⦄) (RecursorFixtures:Vec:nil {Nat})))

-- theorem
opaque
  RecursorFixtures:Vec:sum~uexample : Eq {Nat} RecursorFixtures:Vec:sum~uexample:~ushare:~n2 (OfNat:ofNat {Nat} 5 ⦃ instOfNatNat 5 ⦄)
  RecursorFixtures:Vec:sum~uexample = rfl {Nat} {RecursorFixtures:Vec:sum~uexample:~ushare:~n2}

data RecursorFixtures:Void : Set where

-- recursor
RecursorFixtures:Void:rec : (motive₀ : RecursorFixtures:Void → Set) → (t₁ : RecursorFixtures:Void) → motive₀ t₁
RecursorFixtures:Void:rec motive₀ ()

RecursorFixtures:Void:~usizeOf~u1 : RecursorFixtures:Void → Nat
RecursorFixtures:Void:~usizeOf~u1 t₀ = RecursorFixtures:Void:rec (λ (t₁ : RecursorFixtures:Void) → Nat) t₀

RecursorFixtures:Void:~usizeOf~uinst : SizeOf RecursorFixtures:Void
RecursorFixtures:Void:~usizeOf~uinst = SizeOf:mk {RecursorFixtures:Void} (λ (m₀ : RecursorFixtures:Void) → RecursorFixtures:Void:~usizeOf~u1 m₀)

RecursorFixtures:Void:casesOn : (motive₀ : RecursorFixtures:Void → Set) → (t₁ : RecursorFixtures:Void) → motive₀ t₁
RecursorFixtures:Void:casesOn motive₀ t₁ = RecursorFixtures:Void:rec motive₀ t₁

RecursorFixtures:Void:ctorIdx : RecursorFixtures:Void → Nat
RecursorFixtures:Void:ctorIdx x₀ = RecursorFixtures:Void:casesOn (λ (x₁ : RecursorFixtures:Void) → Nat) x₀

RecursorFixtures:Void:elim : RecursorFixtures:Void → Nat
RecursorFixtures:Void:elim v₀ = RecursorFixtures:Void:rec (λ (x₁ : RecursorFixtures:Void) → Nat) v₀

RecursorFixtures:Void:noConfusionType : Set → RecursorFixtures:Void → RecursorFixtures:Void → Set
RecursorFixtures:Void:noConfusionType P₀ t₁ t₂ = RecursorFixtures:Void:casesOn (λ (t₃ : RecursorFixtures:Void) → Set) t₁

RecursorFixtures:Void:noConfusion : {P₀ : Set} → {t₁ : RecursorFixtures:Void} → {t₂ : RecursorFixtures:Void} → Eq {RecursorFixtures:Void} t₁ t₂ → RecursorFixtures:Void:noConfusionType P₀ t₁ t₂
RecursorFixtures:Void:noConfusion {P₀} {t₁} {t₂} eq₃ = Eq:ndrec {RecursorFixtures:Void} {t₁} {λ (t₄ : RecursorFixtures:Void) → RecursorFixtures:Void:noConfusionType P₀ t₁ t₄} (RecursorFixtures:Void:casesOn (λ (t₄ : RecursorFixtures:Void) → RecursorFixtures:Void:noConfusionType P₀ t₄ t₄) t₁) {t₂} eq₃

RecursorFixtures:Void:recOn : (motive₀ : RecursorFixtures:Void → Set) → (t₁ : RecursorFixtures:Void) → motive₀ t₁
RecursorFixtures:Void:recOn motive₀ t₁ = RecursorFixtures:Void:rec motive₀ t₁

RecursorFixtures:Wide:rec~u2:~ushare:~n1 : Set
RecursorFixtures:Wide:rec~u2:~ushare:~n1 = Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat

RecursorFixtures:Wide:rec~u1:~ushare:~n1 : Set
RecursorFixtures:Wide:rec~u1:~ushare:~n1 = Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat

RecursorFixtures:Wide:rec:~ushare:~n1 : Set
RecursorFixtures:Wide:rec:~ushare:~n1 = Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat

data RecursorFixtures:Wide : Set where
  RecursorFixtures:Wide:leaf : RecursorFixtures:Wide
  RecursorFixtures:Wide:node : List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide) → RecursorFixtures:Wide

RecursorFixtures:Wide:rec:~ushare:~n2 : Set
RecursorFixtures:Wide:rec:~ushare:~n2 = Prod RecursorFixtures:Wide:rec:~ushare:~n1 RecursorFixtures:Wide

RecursorFixtures:Wide:rec:~ushare:~n3 : Set
RecursorFixtures:Wide:rec:~ushare:~n3 = List RecursorFixtures:Wide:rec:~ushare:~n2

RecursorFixtures:Wide:rec~u1:~ushare:~n2 : Set
RecursorFixtures:Wide:rec~u1:~ushare:~n2 = Prod RecursorFixtures:Wide:rec~u1:~ushare:~n1 RecursorFixtures:Wide

RecursorFixtures:Wide:rec~u1:~ushare:~n3 : Set
RecursorFixtures:Wide:rec~u1:~ushare:~n3 = List RecursorFixtures:Wide:rec~u1:~ushare:~n2

RecursorFixtures:Wide:rec~u2:~ushare:~n2 : Set
RecursorFixtures:Wide:rec~u2:~ushare:~n2 = Prod RecursorFixtures:Wide:rec~u2:~ushare:~n1 RecursorFixtures:Wide

RecursorFixtures:Wide:rec~u2:~ushare:~n3 : Set
RecursorFixtures:Wide:rec~u2:~ushare:~n3 = List RecursorFixtures:Wide:rec~u2:~ushare:~n2

-- recursor
mutual
  RecursorFixtures:Wide:rec : {motive1₀ : RecursorFixtures:Wide → Set} → {motive2₁ : RecursorFixtures:Wide:rec:~ushare:~n3 → Set} → {motive3₂ : RecursorFixtures:Wide:rec:~ushare:~n2 → Set} → motive1₀ RecursorFixtures:Wide:leaf → ((xs₃ : RecursorFixtures:Wide:rec:~ushare:~n3) → motive2₁ xs₃ → motive1₀ (RecursorFixtures:Wide:node xs₃)) → motive2₁ (List:nil {RecursorFixtures:Wide:rec:~ushare:~n2}) → ((head₃ : RecursorFixtures:Wide:rec:~ushare:~n2) → (tail₄ : RecursorFixtures:Wide:rec:~ushare:~n3) → motive3₂ head₃ → motive2₁ tail₄ → motive2₁ (List:cons {RecursorFixtures:Wide:rec:~ushare:~n2} head₃ tail₄)) → ((fst₃ : RecursorFixtures:Wide:rec:~ushare:~n1) → (snd₄ : RecursorFixtures:Wide) → motive1₀ snd₄ → motive3₂ (Prod:mk {RecursorFixtures:Wide:rec:~ushare:~n1} {RecursorFixtures:Wide} fst₃ snd₄)) → (t₃ : RecursorFixtures:Wide) → motive1₀ t₃
  RecursorFixtures:Wide:rec~u1 : {motive1₀ : RecursorFixtures:Wide → Set} → {motive2₁ : RecursorFixtures:Wide:rec~u1:~ushare:~n3 → Set} → {motive3₂ : RecursorFixtures:Wide:rec~u1:~ushare:~n2 → Set} → motive1₀ RecursorFixtures:Wide:leaf → ((xs₃ : RecursorFixtures:Wide:rec~u1:~ushare:~n3) → motive2₁ xs₃ → motive1₀ (RecursorFixtures:Wide:node xs₃)) → motive2₁ (List:nil {RecursorFixtures:Wide:rec~u1:~ushare:~n2}) → ((head₃ : RecursorFixtures:Wide:rec~u1:~ushare:~n2) → (tail₄ : RecursorFixtures:Wide:rec~u1:~ushare:~n3) → motive3₂ head₃ → motive2₁ tail₄ → motive2₁ (List:cons {RecursorFixtures:Wide:rec~u1:~ushare:~n2} head₃ tail₄)) → ((fst₃ : RecursorFixtures:Wide:rec~u1:~ushare:~n1) → (snd₄ : RecursorFixtures:Wide) → motive1₀ snd₄ → motive3₂ (Prod:mk {RecursorFixtures:Wide:rec~u1:~ushare:~n1} {RecursorFixtures:Wide} fst₃ snd₄)) → (t₃ : RecursorFixtures:Wide:rec~u1:~ushare:~n3) → motive2₁ t₃
  RecursorFixtures:Wide:rec~u2 : {motive1₀ : RecursorFixtures:Wide → Set} → {motive2₁ : RecursorFixtures:Wide:rec~u2:~ushare:~n3 → Set} → {motive3₂ : RecursorFixtures:Wide:rec~u2:~ushare:~n2 → Set} → motive1₀ RecursorFixtures:Wide:leaf → ((xs₃ : RecursorFixtures:Wide:rec~u2:~ushare:~n3) → motive2₁ xs₃ → motive1₀ (RecursorFixtures:Wide:node xs₃)) → motive2₁ (List:nil {RecursorFixtures:Wide:rec~u2:~ushare:~n2}) → ((head₃ : RecursorFixtures:Wide:rec~u2:~ushare:~n2) → (tail₄ : RecursorFixtures:Wide:rec~u2:~ushare:~n3) → motive3₂ head₃ → motive2₁ tail₄ → motive2₁ (List:cons {RecursorFixtures:Wide:rec~u2:~ushare:~n2} head₃ tail₄)) → ((fst₃ : RecursorFixtures:Wide:rec~u2:~ushare:~n1) → (snd₄ : RecursorFixtures:Wide) → motive1₀ snd₄ → motive3₂ (Prod:mk {RecursorFixtures:Wide:rec~u2:~ushare:~n1} {RecursorFixtures:Wide} fst₃ snd₄)) → (t₃ : RecursorFixtures:Wide:rec~u2:~ushare:~n2) → motive3₂ t₃
  RecursorFixtures:Wide:rec {motive1₀} {motive2₁} {motive3₂} leaf₃ node₄ nil₅ cons₆ mk₇ RecursorFixtures:Wide:leaf = leaf₃
  RecursorFixtures:Wide:rec {motive1₀} {motive2₁} {motive3₂} leaf₃ node₄ nil₅ cons₆ mk₇ (RecursorFixtures:Wide:node xs₈) = node₄ xs₈ (RecursorFixtures:Wide:rec~u1 {motive1₀} {motive2₁} {motive3₂} leaf₃ node₄ nil₅ cons₆ mk₇ xs₈)
  RecursorFixtures:Wide:rec~u1 {motive1₀} {motive2₁} {motive3₂} leaf₃ node₄ nil₅ cons₆ mk₇ List:nil = nil₅
  RecursorFixtures:Wide:rec~u1 {motive1₀} {motive2₁} {motive3₂} leaf₃ node₄ nil₅ cons₆ mk₇ (List:cons head₈ tail₉) = cons₆ head₈ tail₉ (RecursorFixtures:Wide:rec~u2 {motive1₀} {motive2₁} {motive3₂} leaf₃ node₄ nil₅ cons₆ mk₇ head₈) (RecursorFixtures:Wide:rec~u1 {motive1₀} {motive2₁} {motive3₂} leaf₃ node₄ nil₅ cons₆ mk₇ tail₉)
  RecursorFixtures:Wide:rec~u2 {motive1₀} {motive2₁} {motive3₂} leaf₃ node₄ nil₅ cons₆ mk₇ (Prod:mk fst₈ snd₉) = mk₇ fst₈ snd₉ (RecursorFixtures:Wide:rec {motive1₀} {motive2₁} {motive3₂} leaf₃ node₄ nil₅ cons₆ mk₇ snd₉)

RecursorFixtures:Wide:~usizeOf~u1:~ushare:~n1 : Set
RecursorFixtures:Wide:~usizeOf~u1:~ushare:~n1 = Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat

RecursorFixtures:Wide:~usizeOf~u1:~ushare:~n2 : Set
RecursorFixtures:Wide:~usizeOf~u1:~ushare:~n2 = Prod RecursorFixtures:Wide:~usizeOf~u1:~ushare:~n1 RecursorFixtures:Wide

RecursorFixtures:Wide:~usizeOf~u1:~ushare:~n3 : Set
RecursorFixtures:Wide:~usizeOf~u1:~ushare:~n3 = List RecursorFixtures:Wide:~usizeOf~u1:~ushare:~n2

RecursorFixtures:Wide:~usizeOf~u1 : RecursorFixtures:Wide → Nat
RecursorFixtures:Wide:~usizeOf~u1 t₀ = RecursorFixtures:Wide:rec {λ (t₁ : RecursorFixtures:Wide) → Nat} {λ (t₁ : RecursorFixtures:Wide:~usizeOf~u1:~ushare:~n3) → Nat} {λ (t₁ : RecursorFixtures:Wide:~usizeOf~u1:~ushare:~n2) → Nat} (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (λ (xs₁ : RecursorFixtures:Wide:~usizeOf~u1:~ushare:~n3) → λ (xsih₂ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) xsih₂) (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (λ (head₁ : RecursorFixtures:Wide:~usizeOf~u1:~ushare:~n2) → λ (tail₂ : RecursorFixtures:Wide:~usizeOf~u1:~ushare:~n3) → λ (headih₃ : Nat) → λ (tailih₄ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) headih₃) tailih₄) (λ (fst₁ : RecursorFixtures:Wide:~usizeOf~u1:~ushare:~n1) → λ (snd₂ : RecursorFixtures:Wide) → λ (sndih₃ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) sndih₃) t₀

RecursorFixtures:Wide:~usizeOf~u2:~ushare:~n1 : Set
RecursorFixtures:Wide:~usizeOf~u2:~ushare:~n1 = Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat

RecursorFixtures:Wide:~usizeOf~u2:~ushare:~n2 : Set
RecursorFixtures:Wide:~usizeOf~u2:~ushare:~n2 = Prod RecursorFixtures:Wide:~usizeOf~u2:~ushare:~n1 RecursorFixtures:Wide

RecursorFixtures:Wide:~usizeOf~u2:~ushare:~n3 : Set
RecursorFixtures:Wide:~usizeOf~u2:~ushare:~n3 = List RecursorFixtures:Wide:~usizeOf~u2:~ushare:~n2

RecursorFixtures:Wide:~usizeOf~u2 : RecursorFixtures:Wide:~usizeOf~u2:~ushare:~n3 → Nat
RecursorFixtures:Wide:~usizeOf~u2 t₀ = RecursorFixtures:Wide:rec~u1 {λ (t₁ : RecursorFixtures:Wide) → Nat} {λ (t₁ : RecursorFixtures:Wide:~usizeOf~u2:~ushare:~n3) → Nat} {λ (t₁ : RecursorFixtures:Wide:~usizeOf~u2:~ushare:~n2) → Nat} (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (λ (xs₁ : RecursorFixtures:Wide:~usizeOf~u2:~ushare:~n3) → λ (xsih₂ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) xsih₂) (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (λ (head₁ : RecursorFixtures:Wide:~usizeOf~u2:~ushare:~n2) → λ (tail₂ : RecursorFixtures:Wide:~usizeOf~u2:~ushare:~n3) → λ (headih₃ : Nat) → λ (tailih₄ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) headih₃) tailih₄) (λ (fst₁ : RecursorFixtures:Wide:~usizeOf~u2:~ushare:~n1) → λ (snd₂ : RecursorFixtures:Wide) → λ (sndih₃ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) sndih₃) t₀

RecursorFixtures:Wide:~usizeOf~uinst : SizeOf RecursorFixtures:Wide
RecursorFixtures:Wide:~usizeOf~uinst = SizeOf:mk {RecursorFixtures:Wide} (λ (m₀ : RecursorFixtures:Wide) → RecursorFixtures:Wide:~usizeOf~u1 m₀)

RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n1 : Set
RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n1 = Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat

RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n2 : Set
RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n2 = Prod RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n1 RecursorFixtures:Wide

RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n3 : Set
RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n3 = List RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n2

RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n4 : SizeOf (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide)
RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n4 = Prod:~usizeOf~uinst RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n1 RecursorFixtures:Wide ⦃ instSizeOfDefault RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n1 ⦄ ⦃ RecursorFixtures:Wide:~usizeOf~uinst ⦄

RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n5 : List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide) → Nat
RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n5 = SizeOf:sizeOf {RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n3} ⦃ List:~usizeOf~uinst RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n2 ⦃ RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n4 ⦄ ⦄

RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n6 : Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide → Nat
RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n6 = SizeOf:sizeOf {RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n2} ⦃ RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n4 ⦄

RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n7 : Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide → List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide) → List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide)
RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n7 = List:cons {RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n2}

-- theorem
opaque
  RecursorFixtures:Wide:~usizeOf~u2~ueq : (x₀ : RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n3) → Eq {Nat} (RecursorFixtures:Wide:~usizeOf~u2 x₀) (RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n5 x₀)
  RecursorFixtures:Wide:~usizeOf~u2~ueq x₀ = List:rec {RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n2} {λ (t₁ : RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n3) → Eq {Nat} (RecursorFixtures:Wide:~usizeOf~u2 t₁) (RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n5 t₁)} (Eq:refl {Nat} (RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n5 (List:nil {RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n2}))) (λ (head₁ : RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n2) → λ (tail₂ : RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n3) → λ (tailih₃ : Eq {Nat} (RecursorFixtures:Wide:~usizeOf~u2 tail₂) (RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n5 tail₂)) → Eq:trans {Nat} {Nat:add (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n6 head₁)) (RecursorFixtures:Wide:~usizeOf~u2 tail₂)} {Nat:add (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n6 head₁)) (RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n5 tail₂)} {RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n5 (RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n7 head₁ tail₂)} (congrArg {Nat} {Nat} {RecursorFixtures:Wide:~usizeOf~u2 tail₂} {RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n5 tail₂} (Nat:add (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n6 head₁))) tailih₃) (Eq:symm {Nat} {RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n5 (RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n7 head₁ tail₂)} {HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n6 head₁)) (RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n5 tail₂)} (List:cons:sizeOf~uspec {RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n2} ⦃ RecursorFixtures:Wide:~usizeOf~u2~ueq:~ushare:~n4 ⦄ head₁ tail₂))) x₀

RecursorFixtures:Wide:~usizeOf~u3:~ushare:~n1 : Set
RecursorFixtures:Wide:~usizeOf~u3:~ushare:~n1 = Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat

RecursorFixtures:Wide:~usizeOf~u3:~ushare:~n2 : Set
RecursorFixtures:Wide:~usizeOf~u3:~ushare:~n2 = Prod RecursorFixtures:Wide:~usizeOf~u3:~ushare:~n1 RecursorFixtures:Wide

RecursorFixtures:Wide:~usizeOf~u3:~ushare:~n3 : Set
RecursorFixtures:Wide:~usizeOf~u3:~ushare:~n3 = List RecursorFixtures:Wide:~usizeOf~u3:~ushare:~n2

RecursorFixtures:Wide:~usizeOf~u3 : RecursorFixtures:Wide:~usizeOf~u3:~ushare:~n2 → Nat
RecursorFixtures:Wide:~usizeOf~u3 t₀ = RecursorFixtures:Wide:rec~u2 {λ (t₁ : RecursorFixtures:Wide) → Nat} {λ (t₁ : RecursorFixtures:Wide:~usizeOf~u3:~ushare:~n3) → Nat} {λ (t₁ : RecursorFixtures:Wide:~usizeOf~u3:~ushare:~n2) → Nat} (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (λ (xs₁ : RecursorFixtures:Wide:~usizeOf~u3:~ushare:~n3) → λ (xsih₂ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) xsih₂) (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (λ (head₁ : RecursorFixtures:Wide:~usizeOf~u3:~ushare:~n2) → λ (tail₂ : RecursorFixtures:Wide:~usizeOf~u3:~ushare:~n3) → λ (headih₃ : Nat) → λ (tailih₄ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) headih₃) tailih₄) (λ (fst₁ : RecursorFixtures:Wide:~usizeOf~u3:~ushare:~n1) → λ (snd₂ : RecursorFixtures:Wide) → λ (sndih₃ : Nat) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) sndih₃) t₀

RecursorFixtures:Wide:below:~ushare:~n1 : Set
RecursorFixtures:Wide:below:~ushare:~n1 = Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat

RecursorFixtures:Wide:below:~ushare:~n2 : Set
RecursorFixtures:Wide:below:~ushare:~n2 = Prod RecursorFixtures:Wide:below:~ushare:~n1 RecursorFixtures:Wide

RecursorFixtures:Wide:below:~ushare:~n3 : Set
RecursorFixtures:Wide:below:~ushare:~n3 = List RecursorFixtures:Wide:below:~ushare:~n2

RecursorFixtures:Wide:below:~ushare:~n4 : Set
RecursorFixtures:Wide:below:~ushare:~n4 = RecursorFixtures:Wide:below:~ushare:~n3 → Set

RecursorFixtures:Wide:below:~ushare:~n5 : Set
RecursorFixtures:Wide:below:~ushare:~n5 = RecursorFixtures:Wide:below:~ushare:~n2 → Set

RecursorFixtures:Wide:below : {_ : RecursorFixtures:Wide → Set} → {_ : RecursorFixtures:Wide:below:~ushare:~n4} → {_ : RecursorFixtures:Wide:below:~ushare:~n5} → RecursorFixtures:Wide → Set
RecursorFixtures:Wide:below {motive1₀} {motive2₁} {motive3₂} t₃ = RecursorFixtures:Wide:rec {λ (t₄ : RecursorFixtures:Wide) → Set} {λ (t₄ : RecursorFixtures:Wide:below:~ushare:~n3) → Set} {λ (t₄ : RecursorFixtures:Wide:below:~ushare:~n2) → Set} PUnit (λ (xs₄ : RecursorFixtures:Wide:below:~ushare:~n3) → λ (xsih₅ : Set) → PProd (motive2₁ xs₄) xsih₅) PUnit (λ (head₄ : RecursorFixtures:Wide:below:~ushare:~n2) → λ (tail₅ : RecursorFixtures:Wide:below:~ushare:~n3) → λ (headih₆ : Set) → λ (tailih₇ : Set) → PProd (PProd (motive3₂ head₄) headih₆) (PProd (motive2₁ tail₅) tailih₇)) (λ (fst₄ : RecursorFixtures:Wide:below:~ushare:~n1) → λ (snd₅ : RecursorFixtures:Wide) → λ (sndih₆ : Set) → PProd (motive1₀ snd₅) sndih₆) t₃

RecursorFixtures:Wide:below~u1:~ushare:~n1 : Set
RecursorFixtures:Wide:below~u1:~ushare:~n1 = Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat

RecursorFixtures:Wide:below~u1:~ushare:~n2 : Set
RecursorFixtures:Wide:below~u1:~ushare:~n2 = Prod RecursorFixtures:Wide:below~u1:~ushare:~n1 RecursorFixtures:Wide

RecursorFixtures:Wide:below~u1:~ushare:~n3 : Set
RecursorFixtures:Wide:below~u1:~ushare:~n3 = List RecursorFixtures:Wide:below~u1:~ushare:~n2

RecursorFixtures:Wide:below~u1:~ushare:~n4 : Set
RecursorFixtures:Wide:below~u1:~ushare:~n4 = RecursorFixtures:Wide:below~u1:~ushare:~n3 → Set

RecursorFixtures:Wide:below~u1:~ushare:~n5 : Set
RecursorFixtures:Wide:below~u1:~ushare:~n5 = RecursorFixtures:Wide:below~u1:~ushare:~n2 → Set

RecursorFixtures:Wide:below~u1 : {_ : RecursorFixtures:Wide → Set} → {_ : RecursorFixtures:Wide:below~u1:~ushare:~n4} → {_ : RecursorFixtures:Wide:below~u1:~ushare:~n5} → RecursorFixtures:Wide:below~u1:~ushare:~n3 → Set
RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} t₃ = RecursorFixtures:Wide:rec~u1 {λ (t₄ : RecursorFixtures:Wide) → Set} {λ (t₄ : RecursorFixtures:Wide:below~u1:~ushare:~n3) → Set} {λ (t₄ : RecursorFixtures:Wide:below~u1:~ushare:~n2) → Set} PUnit (λ (xs₄ : RecursorFixtures:Wide:below~u1:~ushare:~n3) → λ (xsih₅ : Set) → PProd (motive2₁ xs₄) xsih₅) PUnit (λ (head₄ : RecursorFixtures:Wide:below~u1:~ushare:~n2) → λ (tail₅ : RecursorFixtures:Wide:below~u1:~ushare:~n3) → λ (headih₆ : Set) → λ (tailih₇ : Set) → PProd (PProd (motive3₂ head₄) headih₆) (PProd (motive2₁ tail₅) tailih₇)) (λ (fst₄ : RecursorFixtures:Wide:below~u1:~ushare:~n1) → λ (snd₅ : RecursorFixtures:Wide) → λ (sndih₆ : Set) → PProd (motive1₀ snd₅) sndih₆) t₃

RecursorFixtures:Wide:below~u2:~ushare:~n1 : Set
RecursorFixtures:Wide:below~u2:~ushare:~n1 = Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat

RecursorFixtures:Wide:below~u2:~ushare:~n2 : Set
RecursorFixtures:Wide:below~u2:~ushare:~n2 = Prod RecursorFixtures:Wide:below~u2:~ushare:~n1 RecursorFixtures:Wide

RecursorFixtures:Wide:below~u2:~ushare:~n3 : Set
RecursorFixtures:Wide:below~u2:~ushare:~n3 = List RecursorFixtures:Wide:below~u2:~ushare:~n2

RecursorFixtures:Wide:below~u2:~ushare:~n4 : Set
RecursorFixtures:Wide:below~u2:~ushare:~n4 = RecursorFixtures:Wide:below~u2:~ushare:~n3 → Set

RecursorFixtures:Wide:below~u2:~ushare:~n5 : Set
RecursorFixtures:Wide:below~u2:~ushare:~n5 = RecursorFixtures:Wide:below~u2:~ushare:~n2 → Set

RecursorFixtures:Wide:below~u2 : {_ : RecursorFixtures:Wide → Set} → {_ : RecursorFixtures:Wide:below~u2:~ushare:~n4} → {_ : RecursorFixtures:Wide:below~u2:~ushare:~n5} → RecursorFixtures:Wide:below~u2:~ushare:~n2 → Set
RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} t₃ = RecursorFixtures:Wide:rec~u2 {λ (t₄ : RecursorFixtures:Wide) → Set} {λ (t₄ : RecursorFixtures:Wide:below~u2:~ushare:~n3) → Set} {λ (t₄ : RecursorFixtures:Wide:below~u2:~ushare:~n2) → Set} PUnit (λ (xs₄ : RecursorFixtures:Wide:below~u2:~ushare:~n3) → λ (xsih₅ : Set) → PProd (motive2₁ xs₄) xsih₅) PUnit (λ (head₄ : RecursorFixtures:Wide:below~u2:~ushare:~n2) → λ (tail₅ : RecursorFixtures:Wide:below~u2:~ushare:~n3) → λ (headih₆ : Set) → λ (tailih₇ : Set) → PProd (PProd (motive3₂ head₄) headih₆) (PProd (motive2₁ tail₅) tailih₇)) (λ (fst₄ : RecursorFixtures:Wide:below~u2:~ushare:~n1) → λ (snd₅ : RecursorFixtures:Wide) → λ (sndih₆ : Set) → PProd (motive1₀ snd₅) sndih₆) t₃

RecursorFixtures:Wide:brecOn:go:~ushare:~n1 : Set
RecursorFixtures:Wide:brecOn:go:~ushare:~n1 = Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat

RecursorFixtures:Wide:brecOn:go:~ushare:~n2 : Set
RecursorFixtures:Wide:brecOn:go:~ushare:~n2 = Prod RecursorFixtures:Wide:brecOn:go:~ushare:~n1 RecursorFixtures:Wide

RecursorFixtures:Wide:brecOn:go:~ushare:~n3 : Set
RecursorFixtures:Wide:brecOn:go:~ushare:~n3 = List RecursorFixtures:Wide:brecOn:go:~ushare:~n2

RecursorFixtures:Wide:brecOn:go:~ushare:~n4 : Set
RecursorFixtures:Wide:brecOn:go:~ushare:~n4 = RecursorFixtures:Wide:brecOn:go:~ushare:~n3 → Set

RecursorFixtures:Wide:brecOn:go:~ushare:~n5 : Set
RecursorFixtures:Wide:brecOn:go:~ushare:~n5 = RecursorFixtures:Wide:brecOn:go:~ushare:~n2 → Set

RecursorFixtures:Wide:brecOn:go:~ushare:~n6 : List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide)
RecursorFixtures:Wide:brecOn:go:~ushare:~n6 = List:nil {RecursorFixtures:Wide:brecOn:go:~ushare:~n2}

RecursorFixtures:Wide:brecOn:go:~ushare:~n7 : Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide → List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide) → List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide)
RecursorFixtures:Wide:brecOn:go:~ushare:~n7 = List:cons {RecursorFixtures:Wide:brecOn:go:~ushare:~n2}

RecursorFixtures:Wide:brecOn:go:~ushare:~n8 : (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) → RecursorFixtures:Wide → Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide
RecursorFixtures:Wide:brecOn:go:~ushare:~n8 = Prod:mk {RecursorFixtures:Wide:brecOn:go:~ushare:~n1} {RecursorFixtures:Wide}

RecursorFixtures:Wide:brecOn:go : {motive1₀ : RecursorFixtures:Wide → Set} → {motive2₁ : RecursorFixtures:Wide:brecOn:go:~ushare:~n4} → {motive3₂ : RecursorFixtures:Wide:brecOn:go:~ushare:~n5} → (t₃ : RecursorFixtures:Wide) → ((t₄ : RecursorFixtures:Wide) → RecursorFixtures:Wide:below {motive1₀} {motive2₁} {motive3₂} t₄ → motive1₀ t₄) → ((t₄ : RecursorFixtures:Wide:brecOn:go:~ushare:~n3) → RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} t₄ → motive2₁ t₄) → ((t₄ : RecursorFixtures:Wide:brecOn:go:~ushare:~n2) → RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} t₄ → motive3₂ t₄) → PProd (motive1₀ t₃) (RecursorFixtures:Wide:below {motive1₀} {motive2₁} {motive3₂} t₃)
RecursorFixtures:Wide:brecOn:go {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆ = RecursorFixtures:Wide:rec {λ (t₇ : RecursorFixtures:Wide) → PProd (motive1₀ t₇) (RecursorFixtures:Wide:below {motive1₀} {motive2₁} {motive3₂} t₇)} {λ (t₇ : RecursorFixtures:Wide:brecOn:go:~ushare:~n3) → PProd (motive2₁ t₇) (RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} t₇)} {λ (t₇ : RecursorFixtures:Wide:brecOn:go:~ushare:~n2) → PProd (motive3₂ t₇) (RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} t₇)} (PProd:mk {motive1₀ RecursorFixtures:Wide:leaf} {PUnit} (F1₄ RecursorFixtures:Wide:leaf PUnit:unit) PUnit:unit) (λ (xs₇ : RecursorFixtures:Wide:brecOn:go:~ushare:~n3) → λ (xsih₈ : PProd (motive2₁ xs₇) (RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} xs₇)) → PProd:mk {motive1₀ (RecursorFixtures:Wide:node xs₇)} {PProd (motive2₁ xs₇) (RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} xs₇)} (F1₄ (RecursorFixtures:Wide:node xs₇) xsih₈) xsih₈) (PProd:mk {motive2₁ RecursorFixtures:Wide:brecOn:go:~ushare:~n6} {PUnit} (F2₅ RecursorFixtures:Wide:brecOn:go:~ushare:~n6 PUnit:unit) PUnit:unit) (λ (head₇ : RecursorFixtures:Wide:brecOn:go:~ushare:~n2) → λ (tail₈ : RecursorFixtures:Wide:brecOn:go:~ushare:~n3) → λ (headih₉ : PProd (motive3₂ head₇) (RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} head₇)) → λ (tailih₁₀ : PProd (motive2₁ tail₈) (RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} tail₈)) → PProd:mk {motive2₁ (RecursorFixtures:Wide:brecOn:go:~ushare:~n7 head₇ tail₈)} {PProd (PProd (motive3₂ head₇) (RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} head₇)) (PProd (motive2₁ tail₈) (RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} tail₈))} (F2₅ (RecursorFixtures:Wide:brecOn:go:~ushare:~n7 head₇ tail₈) (PProd:mk {PProd (motive3₂ head₇) (RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} head₇)} {PProd (motive2₁ tail₈) (RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} tail₈)} headih₉ tailih₁₀)) (PProd:mk {PProd (motive3₂ head₇) (RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} head₇)} {PProd (motive2₁ tail₈) (RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} tail₈)} headih₉ tailih₁₀)) (λ (fst₇ : RecursorFixtures:Wide:brecOn:go:~ushare:~n1) → λ (snd₈ : RecursorFixtures:Wide) → λ (sndih₉ : PProd (motive1₀ snd₈) (RecursorFixtures:Wide:below {motive1₀} {motive2₁} {motive3₂} snd₈)) → PProd:mk {motive3₂ (RecursorFixtures:Wide:brecOn:go:~ushare:~n8 fst₇ snd₈)} {PProd (motive1₀ snd₈) (RecursorFixtures:Wide:below {motive1₀} {motive2₁} {motive3₂} snd₈)} (F3₆ (RecursorFixtures:Wide:brecOn:go:~ushare:~n8 fst₇ snd₈) sndih₉) sndih₉) t₃

RecursorFixtures:Wide:brecOn:~ushare:~n1 : Set
RecursorFixtures:Wide:brecOn:~ushare:~n1 = Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide

RecursorFixtures:Wide:brecOn:~ushare:~n2 : Set
RecursorFixtures:Wide:brecOn:~ushare:~n2 = List RecursorFixtures:Wide:brecOn:~ushare:~n1

RecursorFixtures:Wide:brecOn:~ushare:~n3 : Set
RecursorFixtures:Wide:brecOn:~ushare:~n3 = RecursorFixtures:Wide:brecOn:~ushare:~n2 → Set

RecursorFixtures:Wide:brecOn:~ushare:~n4 : Set
RecursorFixtures:Wide:brecOn:~ushare:~n4 = RecursorFixtures:Wide:brecOn:~ushare:~n1 → Set

RecursorFixtures:Wide:brecOn : {motive1₀ : RecursorFixtures:Wide → Set} → {motive2₁ : RecursorFixtures:Wide:brecOn:~ushare:~n3} → {motive3₂ : RecursorFixtures:Wide:brecOn:~ushare:~n4} → (t₃ : RecursorFixtures:Wide) → ((t₄ : RecursorFixtures:Wide) → RecursorFixtures:Wide:below {motive1₀} {motive2₁} {motive3₂} t₄ → motive1₀ t₄) → ((t₄ : RecursorFixtures:Wide:brecOn:~ushare:~n2) → RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} t₄ → motive2₁ t₄) → ((t₄ : RecursorFixtures:Wide:brecOn:~ushare:~n1) → RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} t₄ → motive3₂ t₄) → motive1₀ t₃
RecursorFixtures:Wide:brecOn {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆ = PProd.fst₂ {motive1₀ t₃} {RecursorFixtures:Wide:below {motive1₀} {motive2₁} {motive3₂} t₃} (RecursorFixtures:Wide:brecOn:go {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆)

RecursorFixtures:Wide:casesOn:~ushare:~n1 : Set
RecursorFixtures:Wide:casesOn:~ushare:~n1 = Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat

RecursorFixtures:Wide:casesOn:~ushare:~n2 : Set
RecursorFixtures:Wide:casesOn:~ushare:~n2 = Prod RecursorFixtures:Wide:casesOn:~ushare:~n1 RecursorFixtures:Wide

RecursorFixtures:Wide:casesOn:~ushare:~n3 : Set
RecursorFixtures:Wide:casesOn:~ushare:~n3 = List RecursorFixtures:Wide:casesOn:~ushare:~n2

RecursorFixtures:Wide:casesOn : {motive1₀ : RecursorFixtures:Wide → Set} → (t₁ : RecursorFixtures:Wide) → motive1₀ RecursorFixtures:Wide:leaf → ((xs₂ : RecursorFixtures:Wide:casesOn:~ushare:~n3) → motive1₀ (RecursorFixtures:Wide:node xs₂)) → motive1₀ t₁
RecursorFixtures:Wide:casesOn {motive1₀} t₁ leaf₂ node₃ = RecursorFixtures:Wide:rec {motive1₀} {λ (t₄ : RecursorFixtures:Wide:casesOn:~ushare:~n3) → PUnit} {λ (t₄ : RecursorFixtures:Wide:casesOn:~ushare:~n2) → PUnit} leaf₂ (λ (xs₄ : RecursorFixtures:Wide:casesOn:~ushare:~n3) → λ (xsih₅ : PUnit) → node₃ xs₄) PUnit:unit (λ (head₄ : RecursorFixtures:Wide:casesOn:~ushare:~n2) → λ (tail₅ : RecursorFixtures:Wide:casesOn:~ushare:~n3) → λ (headih₆ : PUnit) → λ (tailih₇ : PUnit) → PUnit:unit) (λ (fst₄ : RecursorFixtures:Wide:casesOn:~ushare:~n1) → λ (snd₅ : RecursorFixtures:Wide) → λ (sndih₆ : motive1₀ snd₅) → PUnit:unit) t₁

RecursorFixtures:Wide:brecOn:eq:~ushare:~n1 : Set
RecursorFixtures:Wide:brecOn:eq:~ushare:~n1 = Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide

RecursorFixtures:Wide:brecOn:eq:~ushare:~n2 : Set
RecursorFixtures:Wide:brecOn:eq:~ushare:~n2 = List RecursorFixtures:Wide:brecOn:eq:~ushare:~n1

RecursorFixtures:Wide:brecOn:eq:~ushare:~n3 : Set
RecursorFixtures:Wide:brecOn:eq:~ushare:~n3 = RecursorFixtures:Wide:brecOn:eq:~ushare:~n2 → Set

RecursorFixtures:Wide:brecOn:eq:~ushare:~n4 : Set
RecursorFixtures:Wide:brecOn:eq:~ushare:~n4 = RecursorFixtures:Wide:brecOn:eq:~ushare:~n1 → Set

-- theorem
opaque
  RecursorFixtures:Wide:brecOn:eq : {motive1₀ : RecursorFixtures:Wide → Set} → {motive2₁ : RecursorFixtures:Wide:brecOn:eq:~ushare:~n3} → {motive3₂ : RecursorFixtures:Wide:brecOn:eq:~ushare:~n4} → (t₃ : RecursorFixtures:Wide) → (F1₄ : (t₄ : RecursorFixtures:Wide) → RecursorFixtures:Wide:below {motive1₀} {motive2₁} {motive3₂} t₄ → motive1₀ t₄) → (F2₅ : (t₅ : RecursorFixtures:Wide:brecOn:eq:~ushare:~n2) → RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} t₅ → motive2₁ t₅) → (F3₆ : (t₆ : RecursorFixtures:Wide:brecOn:eq:~ushare:~n1) → RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} t₆ → motive3₂ t₆) → Eq {motive1₀ t₃} (RecursorFixtures:Wide:brecOn {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆) (F1₄ t₃ (PProd.snd₃ {motive1₀ t₃} {RecursorFixtures:Wide:below {motive1₀} {motive2₁} {motive3₂} t₃} (RecursorFixtures:Wide:brecOn:go {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆)))
  RecursorFixtures:Wide:brecOn:eq {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆ = RecursorFixtures:Wide:casesOn {λ (x₇ : RecursorFixtures:Wide) → Eq {motive1₀ x₇} (RecursorFixtures:Wide:brecOn {motive1₀} {motive2₁} {motive3₂} x₇ F1₄ F2₅ F3₆) (F1₄ x₇ (PProd.snd₃ {motive1₀ x₇} {RecursorFixtures:Wide:below {motive1₀} {motive2₁} {motive3₂} x₇} (RecursorFixtures:Wide:brecOn:go {motive1₀} {motive2₁} {motive3₂} x₇ F1₄ F2₅ F3₆)))} t₃ (Eq:refl {motive1₀ RecursorFixtures:Wide:leaf} (RecursorFixtures:Wide:brecOn {motive1₀} {motive2₁} {motive3₂} RecursorFixtures:Wide:leaf F1₄ F2₅ F3₆)) (λ (xs₇ : RecursorFixtures:Wide:brecOn:eq:~ushare:~n2) → Eq:refl {motive1₀ (RecursorFixtures:Wide:node xs₇)} (RecursorFixtures:Wide:brecOn {motive1₀} {motive2₁} {motive3₂} (RecursorFixtures:Wide:node xs₇) F1₄ F2₅ F3₆))

RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n1 : Set
RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n1 = Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat

RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n2 : Set
RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n2 = Prod RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n1 RecursorFixtures:Wide

RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n3 : Set
RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n3 = List RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n2

RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n4 : Set
RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n4 = RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n3 → Set

RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n5 : Set
RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n5 = RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n2 → Set

RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n6 : List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide)
RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n6 = List:nil {RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n2}

RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n7 : Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide → List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide) → List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide)
RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n7 = List:cons {RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n2}

RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n8 : (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) → RecursorFixtures:Wide → Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide
RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n8 = Prod:mk {RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n1} {RecursorFixtures:Wide}

RecursorFixtures:Wide:brecOn~u1:go : {motive1₀ : RecursorFixtures:Wide → Set} → {motive2₁ : RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n4} → {motive3₂ : RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n5} → (t₃ : RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n3) → ((t₄ : RecursorFixtures:Wide) → RecursorFixtures:Wide:below {motive1₀} {motive2₁} {motive3₂} t₄ → motive1₀ t₄) → ((t₄ : RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n3) → RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} t₄ → motive2₁ t₄) → ((t₄ : RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n2) → RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} t₄ → motive3₂ t₄) → PProd (motive2₁ t₃) (RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} t₃)
RecursorFixtures:Wide:brecOn~u1:go {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆ = RecursorFixtures:Wide:rec~u1 {λ (t₇ : RecursorFixtures:Wide) → PProd (motive1₀ t₇) (RecursorFixtures:Wide:below {motive1₀} {motive2₁} {motive3₂} t₇)} {λ (t₇ : RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n3) → PProd (motive2₁ t₇) (RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} t₇)} {λ (t₇ : RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n2) → PProd (motive3₂ t₇) (RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} t₇)} (PProd:mk {motive1₀ RecursorFixtures:Wide:leaf} {PUnit} (F1₄ RecursorFixtures:Wide:leaf PUnit:unit) PUnit:unit) (λ (xs₇ : RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n3) → λ (xsih₈ : PProd (motive2₁ xs₇) (RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} xs₇)) → PProd:mk {motive1₀ (RecursorFixtures:Wide:node xs₇)} {PProd (motive2₁ xs₇) (RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} xs₇)} (F1₄ (RecursorFixtures:Wide:node xs₇) xsih₈) xsih₈) (PProd:mk {motive2₁ RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n6} {PUnit} (F2₅ RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n6 PUnit:unit) PUnit:unit) (λ (head₇ : RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n2) → λ (tail₈ : RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n3) → λ (headih₉ : PProd (motive3₂ head₇) (RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} head₇)) → λ (tailih₁₀ : PProd (motive2₁ tail₈) (RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} tail₈)) → PProd:mk {motive2₁ (RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n7 head₇ tail₈)} {PProd (PProd (motive3₂ head₇) (RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} head₇)) (PProd (motive2₁ tail₈) (RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} tail₈))} (F2₅ (RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n7 head₇ tail₈) (PProd:mk {PProd (motive3₂ head₇) (RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} head₇)} {PProd (motive2₁ tail₈) (RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} tail₈)} headih₉ tailih₁₀)) (PProd:mk {PProd (motive3₂ head₇) (RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} head₇)} {PProd (motive2₁ tail₈) (RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} tail₈)} headih₉ tailih₁₀)) (λ (fst₇ : RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n1) → λ (snd₈ : RecursorFixtures:Wide) → λ (sndih₉ : PProd (motive1₀ snd₈) (RecursorFixtures:Wide:below {motive1₀} {motive2₁} {motive3₂} snd₈)) → PProd:mk {motive3₂ (RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n8 fst₇ snd₈)} {PProd (motive1₀ snd₈) (RecursorFixtures:Wide:below {motive1₀} {motive2₁} {motive3₂} snd₈)} (F3₆ (RecursorFixtures:Wide:brecOn~u1:go:~ushare:~n8 fst₇ snd₈) sndih₉) sndih₉) t₃

RecursorFixtures:Wide:brecOn~u1:~ushare:~n1 : Set
RecursorFixtures:Wide:brecOn~u1:~ushare:~n1 = Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide

RecursorFixtures:Wide:brecOn~u1:~ushare:~n2 : Set
RecursorFixtures:Wide:brecOn~u1:~ushare:~n2 = List RecursorFixtures:Wide:brecOn~u1:~ushare:~n1

RecursorFixtures:Wide:brecOn~u1:~ushare:~n3 : Set
RecursorFixtures:Wide:brecOn~u1:~ushare:~n3 = RecursorFixtures:Wide:brecOn~u1:~ushare:~n2 → Set

RecursorFixtures:Wide:brecOn~u1:~ushare:~n4 : Set
RecursorFixtures:Wide:brecOn~u1:~ushare:~n4 = RecursorFixtures:Wide:brecOn~u1:~ushare:~n1 → Set

RecursorFixtures:Wide:brecOn~u1 : {motive1₀ : RecursorFixtures:Wide → Set} → {motive2₁ : RecursorFixtures:Wide:brecOn~u1:~ushare:~n3} → {motive3₂ : RecursorFixtures:Wide:brecOn~u1:~ushare:~n4} → (t₃ : RecursorFixtures:Wide:brecOn~u1:~ushare:~n2) → ((t₄ : RecursorFixtures:Wide) → RecursorFixtures:Wide:below {motive1₀} {motive2₁} {motive3₂} t₄ → motive1₀ t₄) → ((t₄ : RecursorFixtures:Wide:brecOn~u1:~ushare:~n2) → RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} t₄ → motive2₁ t₄) → ((t₄ : RecursorFixtures:Wide:brecOn~u1:~ushare:~n1) → RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} t₄ → motive3₂ t₄) → motive2₁ t₃
RecursorFixtures:Wide:brecOn~u1 {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆ = PProd.fst₂ {motive2₁ t₃} {RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} t₃} (RecursorFixtures:Wide:brecOn~u1:go {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆)

RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n1 : Set
RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n1 = Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide

RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n2 : Set
RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n2 = List RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n1

RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n3 : Set
RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n3 = RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n2 → Set

RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n4 : Set
RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n4 = RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n1 → Set

RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n5 : List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide)
RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n5 = List:nil {RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n1}

RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n6 : Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide → List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide) → List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide)
RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n6 = List:cons {RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n1}

-- theorem
opaque
  RecursorFixtures:Wide:brecOn~u1:eq : {motive1₀ : RecursorFixtures:Wide → Set} → {motive2₁ : RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n3} → {motive3₂ : RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n4} → (t₃ : RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n2) → (F1₄ : (t₄ : RecursorFixtures:Wide) → RecursorFixtures:Wide:below {motive1₀} {motive2₁} {motive3₂} t₄ → motive1₀ t₄) → (F2₅ : (t₅ : RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n2) → RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} t₅ → motive2₁ t₅) → (F3₆ : (t₆ : RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n1) → RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} t₆ → motive3₂ t₆) → Eq {motive2₁ t₃} (RecursorFixtures:Wide:brecOn~u1 {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆) (F2₅ t₃ (PProd.snd₃ {motive2₁ t₃} {RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} t₃} (RecursorFixtures:Wide:brecOn~u1:go {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆)))
  RecursorFixtures:Wide:brecOn~u1:eq {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆ = List:casesOn {RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n1} {λ (x₇ : RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n2) → Eq {motive2₁ x₇} (RecursorFixtures:Wide:brecOn~u1 {motive1₀} {motive2₁} {motive3₂} x₇ F1₄ F2₅ F3₆) (F2₅ x₇ (PProd.snd₃ {motive2₁ x₇} {RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} x₇} (RecursorFixtures:Wide:brecOn~u1:go {motive1₀} {motive2₁} {motive3₂} x₇ F1₄ F2₅ F3₆)))} t₃ (Eq:refl {motive2₁ RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n5} (RecursorFixtures:Wide:brecOn~u1 {motive1₀} {motive2₁} {motive3₂} RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n5 F1₄ F2₅ F3₆)) (λ (head₇ : RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n1) → λ (tail₈ : RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n2) → Eq:refl {motive2₁ (RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n6 head₇ tail₈)} (RecursorFixtures:Wide:brecOn~u1 {motive1₀} {motive2₁} {motive3₂} (RecursorFixtures:Wide:brecOn~u1:eq:~ushare:~n6 head₇ tail₈) F1₄ F2₅ F3₆))

RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n1 : Set
RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n1 = Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat

RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n2 : Set
RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n2 = Prod RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n1 RecursorFixtures:Wide

RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n3 : Set
RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n3 = List RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n2

RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n4 : Set
RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n4 = RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n3 → Set

RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n5 : Set
RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n5 = RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n2 → Set

RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n6 : List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide)
RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n6 = List:nil {RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n2}

RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n7 : Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide → List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide) → List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide)
RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n7 = List:cons {RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n2}

RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n8 : (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) → RecursorFixtures:Wide → Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide
RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n8 = Prod:mk {RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n1} {RecursorFixtures:Wide}

RecursorFixtures:Wide:brecOn~u2:go : {motive1₀ : RecursorFixtures:Wide → Set} → {motive2₁ : RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n4} → {motive3₂ : RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n5} → (t₃ : RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n2) → ((t₄ : RecursorFixtures:Wide) → RecursorFixtures:Wide:below {motive1₀} {motive2₁} {motive3₂} t₄ → motive1₀ t₄) → ((t₄ : RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n3) → RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} t₄ → motive2₁ t₄) → ((t₄ : RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n2) → RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} t₄ → motive3₂ t₄) → PProd (motive3₂ t₃) (RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} t₃)
RecursorFixtures:Wide:brecOn~u2:go {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆ = RecursorFixtures:Wide:rec~u2 {λ (t₇ : RecursorFixtures:Wide) → PProd (motive1₀ t₇) (RecursorFixtures:Wide:below {motive1₀} {motive2₁} {motive3₂} t₇)} {λ (t₇ : RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n3) → PProd (motive2₁ t₇) (RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} t₇)} {λ (t₇ : RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n2) → PProd (motive3₂ t₇) (RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} t₇)} (PProd:mk {motive1₀ RecursorFixtures:Wide:leaf} {PUnit} (F1₄ RecursorFixtures:Wide:leaf PUnit:unit) PUnit:unit) (λ (xs₇ : RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n3) → λ (xsih₈ : PProd (motive2₁ xs₇) (RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} xs₇)) → PProd:mk {motive1₀ (RecursorFixtures:Wide:node xs₇)} {PProd (motive2₁ xs₇) (RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} xs₇)} (F1₄ (RecursorFixtures:Wide:node xs₇) xsih₈) xsih₈) (PProd:mk {motive2₁ RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n6} {PUnit} (F2₅ RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n6 PUnit:unit) PUnit:unit) (λ (head₇ : RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n2) → λ (tail₈ : RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n3) → λ (headih₉ : PProd (motive3₂ head₇) (RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} head₇)) → λ (tailih₁₀ : PProd (motive2₁ tail₈) (RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} tail₈)) → PProd:mk {motive2₁ (RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n7 head₇ tail₈)} {PProd (PProd (motive3₂ head₇) (RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} head₇)) (PProd (motive2₁ tail₈) (RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} tail₈))} (F2₅ (RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n7 head₇ tail₈) (PProd:mk {PProd (motive3₂ head₇) (RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} head₇)} {PProd (motive2₁ tail₈) (RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} tail₈)} headih₉ tailih₁₀)) (PProd:mk {PProd (motive3₂ head₇) (RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} head₇)} {PProd (motive2₁ tail₈) (RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} tail₈)} headih₉ tailih₁₀)) (λ (fst₇ : RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n1) → λ (snd₈ : RecursorFixtures:Wide) → λ (sndih₉ : PProd (motive1₀ snd₈) (RecursorFixtures:Wide:below {motive1₀} {motive2₁} {motive3₂} snd₈)) → PProd:mk {motive3₂ (RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n8 fst₇ snd₈)} {PProd (motive1₀ snd₈) (RecursorFixtures:Wide:below {motive1₀} {motive2₁} {motive3₂} snd₈)} (F3₆ (RecursorFixtures:Wide:brecOn~u2:go:~ushare:~n8 fst₇ snd₈) sndih₉) sndih₉) t₃

RecursorFixtures:Wide:brecOn~u2:~ushare:~n1 : Set
RecursorFixtures:Wide:brecOn~u2:~ushare:~n1 = Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide

RecursorFixtures:Wide:brecOn~u2:~ushare:~n2 : Set
RecursorFixtures:Wide:brecOn~u2:~ushare:~n2 = List RecursorFixtures:Wide:brecOn~u2:~ushare:~n1

RecursorFixtures:Wide:brecOn~u2:~ushare:~n3 : Set
RecursorFixtures:Wide:brecOn~u2:~ushare:~n3 = RecursorFixtures:Wide:brecOn~u2:~ushare:~n2 → Set

RecursorFixtures:Wide:brecOn~u2:~ushare:~n4 : Set
RecursorFixtures:Wide:brecOn~u2:~ushare:~n4 = RecursorFixtures:Wide:brecOn~u2:~ushare:~n1 → Set

RecursorFixtures:Wide:brecOn~u2 : {motive1₀ : RecursorFixtures:Wide → Set} → {motive2₁ : RecursorFixtures:Wide:brecOn~u2:~ushare:~n3} → {motive3₂ : RecursorFixtures:Wide:brecOn~u2:~ushare:~n4} → (t₃ : RecursorFixtures:Wide:brecOn~u2:~ushare:~n1) → ((t₄ : RecursorFixtures:Wide) → RecursorFixtures:Wide:below {motive1₀} {motive2₁} {motive3₂} t₄ → motive1₀ t₄) → ((t₄ : RecursorFixtures:Wide:brecOn~u2:~ushare:~n2) → RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} t₄ → motive2₁ t₄) → ((t₄ : RecursorFixtures:Wide:brecOn~u2:~ushare:~n1) → RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} t₄ → motive3₂ t₄) → motive3₂ t₃
RecursorFixtures:Wide:brecOn~u2 {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆ = PProd.fst₂ {motive3₂ t₃} {RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} t₃} (RecursorFixtures:Wide:brecOn~u2:go {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆)

RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n1 : Set
RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n1 = Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat

RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n2 : Set
RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n2 = Prod RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n1 RecursorFixtures:Wide

RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n3 : Set
RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n3 = List RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n2

RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n4 : Set
RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n4 = RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n3 → Set

RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n5 : Set
RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n5 = RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n2 → Set

RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n6 : (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) → RecursorFixtures:Wide → Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide
RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n6 = Prod:mk {RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n1} {RecursorFixtures:Wide}

-- theorem
opaque
  RecursorFixtures:Wide:brecOn~u2:eq : {motive1₀ : RecursorFixtures:Wide → Set} → {motive2₁ : RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n4} → {motive3₂ : RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n5} → (t₃ : RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n2) → (F1₄ : (t₄ : RecursorFixtures:Wide) → RecursorFixtures:Wide:below {motive1₀} {motive2₁} {motive3₂} t₄ → motive1₀ t₄) → (F2₅ : (t₅ : RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n3) → RecursorFixtures:Wide:below~u1 {motive1₀} {motive2₁} {motive3₂} t₅ → motive2₁ t₅) → (F3₆ : (t₆ : RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n2) → RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} t₆ → motive3₂ t₆) → Eq {motive3₂ t₃} (RecursorFixtures:Wide:brecOn~u2 {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆) (F3₆ t₃ (PProd.snd₃ {motive3₂ t₃} {RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} t₃} (RecursorFixtures:Wide:brecOn~u2:go {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆)))
  RecursorFixtures:Wide:brecOn~u2:eq {motive1₀} {motive2₁} {motive3₂} t₃ F1₄ F2₅ F3₆ = Prod:casesOn {RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n1} {RecursorFixtures:Wide} {λ (x₇ : RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n2) → Eq {motive3₂ x₇} (RecursorFixtures:Wide:brecOn~u2 {motive1₀} {motive2₁} {motive3₂} x₇ F1₄ F2₅ F3₆) (F3₆ x₇ (PProd.snd₃ {motive3₂ x₇} {RecursorFixtures:Wide:below~u2 {motive1₀} {motive2₁} {motive3₂} x₇} (RecursorFixtures:Wide:brecOn~u2:go {motive1₀} {motive2₁} {motive3₂} x₇ F1₄ F2₅ F3₆)))} t₃ (λ (fst₇ : RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n1) → λ (snd₈ : RecursorFixtures:Wide) → Eq:refl {motive3₂ (RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n6 fst₇ snd₈)} (RecursorFixtures:Wide:brecOn~u2 {motive1₀} {motive2₁} {motive3₂} (RecursorFixtures:Wide:brecOn~u2:eq:~ushare:~n6 fst₇ snd₈) F1₄ F2₅ F3₆))

RecursorFixtures:Wide:ctorElimType : {_ : RecursorFixtures:Wide → Set} → Nat → Set
RecursorFixtures:Wide:ctorElimType {motive1₀} ctorIdx₁ = cond {Set} (Nat:ble ctorIdx₁ 0) (PULift (motive1₀ RecursorFixtures:Wide:leaf)) (PULift ((xs₂ : List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide)) → motive1₀ (RecursorFixtures:Wide:node xs₂)))

RecursorFixtures:Wide:ctorIdx : RecursorFixtures:Wide → Nat
RecursorFixtures:Wide:ctorIdx x₀ = RecursorFixtures:Wide:casesOn {λ (x₁ : RecursorFixtures:Wide) → Nat} x₀ 0 (λ (xs₁ : List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide)) → 1)

RecursorFixtures:Wide:ctorElim:~ushare:~n1 : Set
RecursorFixtures:Wide:ctorElim:~ushare:~n1 = List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide)

RecursorFixtures:Wide:ctorElim : {motive1₀ : RecursorFixtures:Wide → Set} → (ctorIdx₁ : Nat) → (t₂ : RecursorFixtures:Wide) → Eq {Nat} ctorIdx₁ (RecursorFixtures:Wide:ctorIdx t₂) → RecursorFixtures:Wide:ctorElimType {motive1₀} ctorIdx₁ → motive1₀ t₂
RecursorFixtures:Wide:ctorElim {motive1₀} ctorIdx₁ t₂ h₃ k₄ = RecursorFixtures:Wide:casesOn {λ (t₅ : RecursorFixtures:Wide) → Eq {Nat} ctorIdx₁ (RecursorFixtures:Wide:ctorIdx t₅) → motive1₀ t₅} t₂ (λ (h₅ : Eq {Nat} ctorIdx₁ 0) → PULift:down {motive1₀ RecursorFixtures:Wide:leaf} (Eq:ndrec {Nat} {ctorIdx₁} {RecursorFixtures:Wide:ctorElimType {motive1₀}} k₄ {0} h₅)) (λ (xs₅ : RecursorFixtures:Wide:ctorElim:~ushare:~n1) → λ (h₆ : Eq {Nat} ctorIdx₁ 1) → PULift:down {(xs₇ : RecursorFixtures:Wide:ctorElim:~ushare:~n1) → motive1₀ (RecursorFixtures:Wide:node xs₇)} (Eq:ndrec {Nat} {ctorIdx₁} {RecursorFixtures:Wide:ctorElimType {motive1₀}} k₄ {1} h₆) xs₅) h₃

RecursorFixtures:Wide:isLeaf:match~u1:~ushare:~n1 : Set
RecursorFixtures:Wide:isLeaf:match~u1:~ushare:~n1 = List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide)

RecursorFixtures:Wide:isLeaf:match~u1 : (motive₀ : RecursorFixtures:Wide → Set) → (x₁ : RecursorFixtures:Wide) → (Unit → motive₀ RecursorFixtures:Wide:leaf) → ((xs₂ : RecursorFixtures:Wide:isLeaf:match~u1:~ushare:~n1) → motive₀ (RecursorFixtures:Wide:node xs₂)) → motive₀ x₁
RecursorFixtures:Wide:isLeaf:match~u1 motive₀ x₁ h1₂ h2₃ = RecursorFixtures:Wide:casesOn {λ (x₄ : RecursorFixtures:Wide) → motive₀ x₄} x₁ (h1₂ Unit:unit) (λ (xs₄ : RecursorFixtures:Wide:isLeaf:match~u1:~ushare:~n1) → h2₃ xs₄)

RecursorFixtures:Wide:isLeaf : RecursorFixtures:Wide → Bool
RecursorFixtures:Wide:isLeaf x₀ = RecursorFixtures:Wide:isLeaf:match~u1 (λ (x₁ : RecursorFixtures:Wide) → Bool) x₀ (λ (x₁ : Unit) → Bool:true) (λ (xs₁ : List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide)) → Bool:false)

RecursorFixtures:Wide:isLeaf~uexample:~ushare:~n1 : Set
RecursorFixtures:Wide:isLeaf~uexample:~ushare:~n1 = Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat

RecursorFixtures:Wide:isLeaf~uexample:~ushare:~n2 : Set
RecursorFixtures:Wide:isLeaf~uexample:~ushare:~n2 = Prod RecursorFixtures:Wide:isLeaf~uexample:~ushare:~n1 RecursorFixtures:Wide

RecursorFixtures:Wide:isLeaf~uexample:~ushare:~n3 : Bool
RecursorFixtures:Wide:isLeaf~uexample:~ushare:~n3 = RecursorFixtures:Wide:isLeaf (RecursorFixtures:Wide:node (List:cons {RecursorFixtures:Wide:isLeaf~uexample:~ushare:~n2} (Prod:mk {RecursorFixtures:Wide:isLeaf~uexample:~ushare:~n1} {RecursorFixtures:Wide} (λ (x₀ : Nat) → λ (x₁ : Nat) → λ (x₂ : Nat) → λ (x₃ : Nat) → λ (x₄ : Nat) → λ (x₅ : Nat) → λ (x₆ : Nat) → λ (x₇ : Nat) → λ (x₈ : Nat) → λ (x₉ : Nat) → λ (x₁₀ : Nat) → λ (x₁₁ : Nat) → λ (x₁₂ : Nat) → λ (x₁₃ : Nat) → λ (x₁₄ : Nat) → λ (x₁₅ : Nat) → OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) RecursorFixtures:Wide:leaf) (List:nil {RecursorFixtures:Wide:isLeaf~uexample:~ushare:~n2})))

-- theorem
opaque
  RecursorFixtures:Wide:isLeaf~uexample : Eq {Bool} RecursorFixtures:Wide:isLeaf~uexample:~ushare:~n3 Bool:false
  RecursorFixtures:Wide:isLeaf~uexample = rfl {Bool} {RecursorFixtures:Wide:isLeaf~uexample:~ushare:~n3}

RecursorFixtures:Wide:leaf:elim : {motive1₀ : RecursorFixtures:Wide → Set} → (t₁ : RecursorFixtures:Wide) → Eq {Nat} (RecursorFixtures:Wide:ctorIdx t₁) 0 → motive1₀ RecursorFixtures:Wide:leaf → motive1₀ t₁
RecursorFixtures:Wide:leaf:elim {motive1₀} t₁ h₂ leaf₃ = RecursorFixtures:Wide:ctorElim {motive1₀} 0 t₁ (Eq:symm {Nat} {RecursorFixtures:Wide:ctorIdx t₁} {0} h₂) (PULift:up {motive1₀ RecursorFixtures:Wide:leaf} leaf₃)

-- theorem
opaque
  RecursorFixtures:Wide:leaf:sizeOf~uspec : Eq {Nat} (SizeOf:sizeOf {RecursorFixtures:Wide} ⦃ RecursorFixtures:Wide:~usizeOf~uinst ⦄ RecursorFixtures:Wide:leaf) (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)
  RecursorFixtures:Wide:leaf:sizeOf~uspec = Eq:refl {Nat} (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)

RecursorFixtures:Wide:noConfusionType:~ushare:~n1 : Set
RecursorFixtures:Wide:noConfusionType:~ushare:~n1 = List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide)

RecursorFixtures:Wide:noConfusionType : Set → RecursorFixtures:Wide → RecursorFixtures:Wide → Set
RecursorFixtures:Wide:noConfusionType P₀ t₁ t₂ = RecursorFixtures:Wide:casesOn {λ (t₃ : RecursorFixtures:Wide) → Set} t₁ (RecursorFixtures:Wide:casesOn {λ (t₃ : RecursorFixtures:Wide) → Set} t₂ (P₀ → P₀) (λ (xs₃ : RecursorFixtures:Wide:noConfusionType:~ushare:~n1) → P₀)) (λ (xs₃ : RecursorFixtures:Wide:noConfusionType:~ushare:~n1) → RecursorFixtures:Wide:casesOn {λ (t₄ : RecursorFixtures:Wide) → Set} t₂ P₀ (λ (xs₄ : RecursorFixtures:Wide:noConfusionType:~ushare:~n1) → (Eq {RecursorFixtures:Wide:noConfusionType:~ushare:~n1} xs₃ xs₄ → P₀) → P₀))

RecursorFixtures:Wide:noConfusion:~ushare:~n1 : Set
RecursorFixtures:Wide:noConfusion:~ushare:~n1 = List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide)

RecursorFixtures:Wide:noConfusion : {P₀ : Set} → {t₁ : RecursorFixtures:Wide} → {t₂ : RecursorFixtures:Wide} → Eq {RecursorFixtures:Wide} t₁ t₂ → RecursorFixtures:Wide:noConfusionType P₀ t₁ t₂
RecursorFixtures:Wide:noConfusion {P₀} {t₁} {t₂} eq₃ = Eq:ndrec {RecursorFixtures:Wide} {t₁} {λ (t₄ : RecursorFixtures:Wide) → RecursorFixtures:Wide:noConfusionType P₀ t₁ t₄} (RecursorFixtures:Wide:casesOn {λ (t₄ : RecursorFixtures:Wide) → RecursorFixtures:Wide:noConfusionType P₀ t₄ t₄} t₁ (λ (k₄ : P₀) → k₄) (λ (xs₄ : RecursorFixtures:Wide:noConfusion:~ushare:~n1) → λ (k₅ : Eq {RecursorFixtures:Wide:noConfusion:~ushare:~n1} xs₄ xs₄ → P₀) → k₅ (Eq:refl {RecursorFixtures:Wide:noConfusion:~ushare:~n1} xs₄))) {t₂} eq₃

RecursorFixtures:Wide:node:elim:~ushare:~n1 : Set
RecursorFixtures:Wide:node:elim:~ushare:~n1 = List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide)

RecursorFixtures:Wide:node:elim : {motive1₀ : RecursorFixtures:Wide → Set} → (t₁ : RecursorFixtures:Wide) → Eq {Nat} (RecursorFixtures:Wide:ctorIdx t₁) 1 → ((xs₂ : RecursorFixtures:Wide:node:elim:~ushare:~n1) → motive1₀ (RecursorFixtures:Wide:node xs₂)) → motive1₀ t₁
RecursorFixtures:Wide:node:elim {motive1₀} t₁ h₂ node₃ = RecursorFixtures:Wide:ctorElim {motive1₀} 1 t₁ (Eq:symm {Nat} {RecursorFixtures:Wide:ctorIdx t₁} {1} h₂) (PULift:up {(xs₄ : RecursorFixtures:Wide:node:elim:~ushare:~n1) → motive1₀ (RecursorFixtures:Wide:node xs₄)} node₃)

RecursorFixtures:Wide:node:noConfusion:~ushare:~n1 : Set
RecursorFixtures:Wide:node:noConfusion:~ushare:~n1 = List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide)

RecursorFixtures:Wide:node:noConfusion:~ushare:~n2 : List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide) → List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide) → Set
RecursorFixtures:Wide:node:noConfusion:~ushare:~n2 = Eq {RecursorFixtures:Wide:node:noConfusion:~ushare:~n1}

RecursorFixtures:Wide:node:noConfusion : {P₀ : Set} → {xs₁ : RecursorFixtures:Wide:node:noConfusion:~ushare:~n1} → {xs₂ : RecursorFixtures:Wide:node:noConfusion:~ushare:~n1} → Eq {RecursorFixtures:Wide} (RecursorFixtures:Wide:node xs₁) (RecursorFixtures:Wide:node xs₂) → (RecursorFixtures:Wide:node:noConfusion:~ushare:~n2 xs₁ xs₂ → P₀) → P₀
RecursorFixtures:Wide:node:noConfusion {P₀} {xs₁} {xs₂} eq₃ k₄ = id {P₀} (RecursorFixtures:Wide:noConfusion {P₀} {RecursorFixtures:Wide:node xs₁} {RecursorFixtures:Wide:node xs₂} eq₃ k₄)

RecursorFixtures:Wide:node:inj:~ushare:~n1 : Set
RecursorFixtures:Wide:node:inj:~ushare:~n1 = List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide)

RecursorFixtures:Wide:node:inj:~ushare:~n2 : List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide) → List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide) → Set
RecursorFixtures:Wide:node:inj:~ushare:~n2 = Eq {RecursorFixtures:Wide:node:inj:~ushare:~n1}

-- theorem
opaque
  RecursorFixtures:Wide:node:inj : {xs₀ : RecursorFixtures:Wide:node:inj:~ushare:~n1} → {xs₁ : RecursorFixtures:Wide:node:inj:~ushare:~n1} → Eq {RecursorFixtures:Wide} (RecursorFixtures:Wide:node xs₀) (RecursorFixtures:Wide:node xs₁) → RecursorFixtures:Wide:node:inj:~ushare:~n2 xs₀ xs₁
  RecursorFixtures:Wide:node:inj {xs₀} {xs₁} x₂ = RecursorFixtures:Wide:node:noConfusion {RecursorFixtures:Wide:node:inj:~ushare:~n2 xs₀ xs₁} {xs₀} {xs₁} x₂ (λ (xseq₃ : RecursorFixtures:Wide:node:inj:~ushare:~n2 xs₀ xs₁) → xseq₃)

RecursorFixtures:Wide:node:injEq:~ushare:~n1 : Set
RecursorFixtures:Wide:node:injEq:~ushare:~n1 = List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide)

RecursorFixtures:Wide:node:injEq:~ushare:~n2 : List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide) → List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide) → Set
RecursorFixtures:Wide:node:injEq:~ushare:~n2 = Eq {RecursorFixtures:Wide:node:injEq:~ushare:~n1}

-- theorem
opaque
  RecursorFixtures:Wide:node:injEq : (xs₀ : RecursorFixtures:Wide:node:injEq:~ushare:~n1) → (xs₁ : RecursorFixtures:Wide:node:injEq:~ushare:~n1) → Eq {Set} (Eq {RecursorFixtures:Wide} (RecursorFixtures:Wide:node xs₀) (RecursorFixtures:Wide:node xs₁)) (RecursorFixtures:Wide:node:injEq:~ushare:~n2 xs₀ xs₁)
  RecursorFixtures:Wide:node:injEq xs₀ xs₁ = Eq:propIntro {Eq {RecursorFixtures:Wide} (RecursorFixtures:Wide:node xs₀) (RecursorFixtures:Wide:node xs₁)} {RecursorFixtures:Wide:node:injEq:~ushare:~n2 xs₀ xs₁} (RecursorFixtures:Wide:node:inj {xs₀} {xs₁}) (Eq:ndrec {RecursorFixtures:Wide:node:injEq:~ushare:~n1} {xs₀} {λ (xs₂ : RecursorFixtures:Wide:node:injEq:~ushare:~n1) → Eq {RecursorFixtures:Wide} (RecursorFixtures:Wide:node xs₀) (RecursorFixtures:Wide:node xs₂)} (Eq:refl {RecursorFixtures:Wide} (RecursorFixtures:Wide:node xs₀)) {xs₁})

RecursorFixtures:Wide:node:sizeOf~uspec:~ushare:~n1 : Set
RecursorFixtures:Wide:node:sizeOf~uspec:~ushare:~n1 = Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat

RecursorFixtures:Wide:node:sizeOf~uspec:~ushare:~n2 : Set
RecursorFixtures:Wide:node:sizeOf~uspec:~ushare:~n2 = Prod RecursorFixtures:Wide:node:sizeOf~uspec:~ushare:~n1 RecursorFixtures:Wide

RecursorFixtures:Wide:node:sizeOf~uspec:~ushare:~n3 : Set
RecursorFixtures:Wide:node:sizeOf~uspec:~ushare:~n3 = List RecursorFixtures:Wide:node:sizeOf~uspec:~ushare:~n2

RecursorFixtures:Wide:node:sizeOf~uspec:~ushare:~n4 : List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide) → Nat
RecursorFixtures:Wide:node:sizeOf~uspec:~ushare:~n4 = SizeOf:sizeOf {RecursorFixtures:Wide:node:sizeOf~uspec:~ushare:~n3} ⦃ List:~usizeOf~uinst RecursorFixtures:Wide:node:sizeOf~uspec:~ushare:~n2 ⦃ Prod:~usizeOf~uinst RecursorFixtures:Wide:node:sizeOf~uspec:~ushare:~n1 RecursorFixtures:Wide ⦃ instSizeOfDefault RecursorFixtures:Wide:node:sizeOf~uspec:~ushare:~n1 ⦄ ⦃ RecursorFixtures:Wide:~usizeOf~uinst ⦄ ⦄ ⦄

-- theorem
opaque
  RecursorFixtures:Wide:node:sizeOf~uspec : (xs₀ : RecursorFixtures:Wide:node:sizeOf~uspec:~ushare:~n3) → Eq {Nat} (SizeOf:sizeOf {RecursorFixtures:Wide} ⦃ RecursorFixtures:Wide:~usizeOf~uinst ⦄ (RecursorFixtures:Wide:node xs₀)) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (RecursorFixtures:Wide:node:sizeOf~uspec:~ushare:~n4 xs₀))
  RecursorFixtures:Wide:node:sizeOf~uspec xs₀ = congrArg {Nat} {Nat} {RecursorFixtures:Wide:~usizeOf~u2 xs₀} {RecursorFixtures:Wide:node:sizeOf~uspec:~ushare:~n4 xs₀} (Nat:add (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (RecursorFixtures:Wide:~usizeOf~u2~ueq xs₀)

RecursorFixtures:Wide:recOn:~ushare:~n1 : Set
RecursorFixtures:Wide:recOn:~ushare:~n1 = Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat

RecursorFixtures:Wide:recOn:~ushare:~n2 : Set
RecursorFixtures:Wide:recOn:~ushare:~n2 = Prod RecursorFixtures:Wide:recOn:~ushare:~n1 RecursorFixtures:Wide

RecursorFixtures:Wide:recOn:~ushare:~n3 : Set
RecursorFixtures:Wide:recOn:~ushare:~n3 = List RecursorFixtures:Wide:recOn:~ushare:~n2

RecursorFixtures:Wide:recOn:~ushare:~n4 : Set
RecursorFixtures:Wide:recOn:~ushare:~n4 = RecursorFixtures:Wide:recOn:~ushare:~n3 → Set

RecursorFixtures:Wide:recOn:~ushare:~n5 : Set
RecursorFixtures:Wide:recOn:~ushare:~n5 = RecursorFixtures:Wide:recOn:~ushare:~n2 → Set

RecursorFixtures:Wide:recOn:~ushare:~n6 : List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide)
RecursorFixtures:Wide:recOn:~ushare:~n6 = List:nil {RecursorFixtures:Wide:recOn:~ushare:~n2}

RecursorFixtures:Wide:recOn:~ushare:~n7 : Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide → List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide) → List (Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide)
RecursorFixtures:Wide:recOn:~ushare:~n7 = List:cons {RecursorFixtures:Wide:recOn:~ushare:~n2}

RecursorFixtures:Wide:recOn:~ushare:~n8 : (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) → RecursorFixtures:Wide → Prod (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) RecursorFixtures:Wide
RecursorFixtures:Wide:recOn:~ushare:~n8 = Prod:mk {RecursorFixtures:Wide:recOn:~ushare:~n1} {RecursorFixtures:Wide}

RecursorFixtures:Wide:recOn : {motive1₀ : RecursorFixtures:Wide → Set} → {motive2₁ : RecursorFixtures:Wide:recOn:~ushare:~n4} → {motive3₂ : RecursorFixtures:Wide:recOn:~ushare:~n5} → (t₃ : RecursorFixtures:Wide) → motive1₀ RecursorFixtures:Wide:leaf → ((xs₄ : RecursorFixtures:Wide:recOn:~ushare:~n3) → motive2₁ xs₄ → motive1₀ (RecursorFixtures:Wide:node xs₄)) → motive2₁ RecursorFixtures:Wide:recOn:~ushare:~n6 → ((head₄ : RecursorFixtures:Wide:recOn:~ushare:~n2) → (tail₅ : RecursorFixtures:Wide:recOn:~ushare:~n3) → motive3₂ head₄ → motive2₁ tail₅ → motive2₁ (RecursorFixtures:Wide:recOn:~ushare:~n7 head₄ tail₅)) → ((fst₄ : RecursorFixtures:Wide:recOn:~ushare:~n1) → (snd₅ : RecursorFixtures:Wide) → motive1₀ snd₅ → motive3₂ (RecursorFixtures:Wide:recOn:~ushare:~n8 fst₄ snd₅)) → motive1₀ t₃
RecursorFixtures:Wide:recOn {motive1₀} {motive2₁} {motive3₂} t₃ leaf₄ node₅ nil₆ cons₇ mk₈ = RecursorFixtures:Wide:rec {motive1₀} {motive2₁} {motive3₂} leaf₄ node₅ nil₆ cons₇ mk₈ t₃
