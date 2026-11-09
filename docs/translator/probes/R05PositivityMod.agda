-- Outcome on 2026-11-09 with Agda 2.8.0: heap exhausted under +RTS -M2G (exit 251, about 30 s), in the positivity check of Probe
{-# OPTIONS --type-in-type #-}
module R05PositivityMod where

-- Lean's `Nat.mod` and `Eq` as the nat-gcd-self golden prints them,
-- with the declarations they use and every theorem postulated, and one
-- record whose field mentions `v % 16`.  Agda's positivity check
-- normalizes the field's type, and the normal form of `Nat.mod` on a
-- variable and a literal, through `Nat.modCore` and `Nat.ble`, which
-- Lean compiles through `brecOn`, grows exponentially with the literal:
-- with 8 in place of 16 the file checks at a peak of 98 MB, with 12 at
-- 699 MB.  It is the smallest form of `ByteArray.IsValidUTF8`'s refusal
-- (recursors.md, Agda's positivity check), for issue M3-6's table of
-- Agda-native definitions of the operations Lean's kernel accelerates.

record Add (α₀ : Set) : Set where
  constructor Add:mk
  field
    add₁ : α₀ → α₀ → α₀

Add:add : {α₀ : Set} → ⦃ _ : Add α₀ ⦄ → α₀ → α₀ → α₀
Add:add {α₀} ⦃ self₁ ⦄ = Add.add₁ {α₀} self₁

data Bool : Set where
  Bool:false : Bool
  Bool:true : Bool

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

record PUnit : Set where
  constructor PUnit:unit

Unit : Set
Unit = PUnit

Unit:unit : Unit
Unit:unit = PUnit:unit

Bool:decEq:match~u1 : (motive₀ : Bool → Bool → Set) → (a₁ : Bool) → (b₂ : Bool) → (Unit → motive₀ Bool:false Bool:false) → (Unit → motive₀ Bool:false Bool:true) → (Unit → motive₀ Bool:true Bool:false) → (Unit → motive₀ Bool:true Bool:true) → motive₀ a₁ b₂
Bool:decEq:match~u1 motive₀ a₁ b₂ h1₃ h2₄ h3₅ h4₆ = Bool:casesOn {λ (x₇ : Bool) → motive₀ x₇ b₂} a₁ (Bool:casesOn {λ (x₇ : Bool) → motive₀ Bool:false x₇} b₂ (h1₃ Unit:unit) (h2₄ Unit:unit)) (Bool:casesOn {λ (x₇ : Bool) → motive₀ Bool:true x₇} b₂ (h3₅ Unit:unit) (h4₆ Unit:unit))

Bool:noConfusionType : Set → Bool → Bool → Set
Bool:noConfusionType P₀ t₁ t₂ = Bool:casesOn {λ (t₃ : Bool) → Set} t₁ (Bool:casesOn {λ (t₃ : Bool) → Set} t₂ (P₀ → P₀) P₀) (Bool:casesOn {λ (t₃ : Bool) → Set} t₂ P₀ (P₀ → P₀))

data Eq {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl : (a₁ : α₀) → Eq {α₀} a₁ a₁

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

rfl : {α₀ : Set} → {a₁ : α₀} → Eq {α₀} a₁ a₁
rfl {α₀} {a₁} = Eq:refl {α₀} a₁

Bool:decEq : (a₀ : Bool) → (b₁ : Bool) → Decidable (Eq {Bool} a₀ b₁)
Bool:decEq a₀ b₁ = Bool:decEq:match~u1 (λ (a₂ : Bool) → λ (b₃ : Bool) → Decidable (Eq {Bool} a₂ b₃)) a₀ b₁ (λ (x₂ : Unit) → Decidable:isTrue {Eq {Bool} Bool:false Bool:false} (rfl {Bool} {Bool:false})) (λ (x₂ : Unit) → Decidable:isFalse {Eq {Bool} Bool:false Bool:true} (λ (h₃ : Eq {Bool} Bool:false Bool:true) → Bool:noConfusion {False} {Bool:false} {Bool:true} h₃)) (λ (x₂ : Unit) → Decidable:isFalse {Eq {Bool} Bool:true Bool:false} (λ (h₃ : Eq {Bool} Bool:true Bool:false) → Bool:noConfusion {False} {Bool:true} {Bool:false} h₃)) (λ (x₂ : Unit) → Decidable:isTrue {Eq {Bool} Bool:true Bool:true} (rfl {Bool} {Bool:true}))

Decidable:casesOn : {p₀ : Set} → {motive₁ : Decidable p₀ → Set} → (t₂ : Decidable p₀) → ((h₃ : Not p₀) → motive₁ (Decidable:isFalse {p₀} h₃)) → ((h₃ : p₀) → motive₁ (Decidable:isTrue {p₀} h₃)) → motive₁ t₂
Decidable:casesOn {p₀} {motive₁} t₂ isFalse₃ isTrue₄ = Decidable:rec {p₀} {motive₁} (λ (h₅ : Not p₀) → isFalse₃ h₅) (λ (h₅ : p₀) → isTrue₄ h₅) t₂

DecidableEq : Set → Set
DecidableEq α₀ = (a₁ : α₀) → (b₂ : α₀) → Decidable (Eq {α₀} a₁ b₂)

False:elim : {C₀ : Set} → False → C₀
False:elim {C₀} h₁ = False:rec (λ (x₂ : False) → C₀) h₁

record LE (α₀ : Set) : Set where
  constructor LE:mk
  field
    le₁ : α₀ → α₀ → Set

LE:le : {α₀ : Set} → ⦃ _ : LE α₀ ⦄ → α₀ → α₀ → Set
LE:le {α₀} ⦃ self₁ ⦄ = LE.le₁ {α₀} self₁

record LT (α₀ : Set) : Set where
  constructor LT:mk
  field
    lt₁ : α₀ → α₀ → Set

LT:lt : {α₀ : Set} → ⦃ _ : LT α₀ ⦄ → α₀ → α₀ → Set
LT:lt {α₀} ⦃ self₁ ⦄ = LT.lt₁ {α₀} self₁

outParam : Set → Set
outParam α₀ = α₀

record HAdd (α₀ : Set) (β₁ : Set) (γ₂ : outParam Set) : Set where
  constructor HAdd:mk
  field
    hAdd₃ : α₀ → β₁ → γ₂

HAdd:hAdd : {α₀ : Set} → {β₁ : Set} → {γ₂ : outParam Set} → ⦃ _ : HAdd α₀ β₁ γ₂ ⦄ → α₀ → β₁ → γ₂
HAdd:hAdd {α₀} {β₁} {γ₂} ⦃ self₃ ⦄ = HAdd.hAdd₃ {α₀} {β₁} {γ₂} self₃

data HEq {α₀ : Set} : α₀ → {β₁ : Set} → β₁ → Set where
  HEq:refl : (a₁ : α₀) → HEq {α₀} a₁ {α₀} a₁

record HMod (α₀ : Set) (β₁ : Set) (γ₂ : outParam Set) : Set where
  constructor HMod:mk
  field
    hMod₃ : α₀ → β₁ → γ₂

HMod:hMod : {α₀ : Set} → {β₁ : Set} → {γ₂ : outParam Set} → ⦃ _ : HMod α₀ β₁ γ₂ ⦄ → α₀ → β₁ → γ₂
HMod:hMod {α₀} {β₁} {γ₂} ⦃ self₃ ⦄ = HMod.hMod₃ {α₀} {β₁} {γ₂} self₃

record HSub (α₀ : Set) (β₁ : Set) (γ₂ : outParam Set) : Set where
  constructor HSub:mk
  field
    hSub₃ : α₀ → β₁ → γ₂

HSub:hSub : {α₀ : Set} → {β₁ : Set} → {γ₂ : outParam Set} → ⦃ _ : HSub α₀ β₁ γ₂ ⦄ → α₀ → β₁ → γ₂
HSub:hSub {α₀} {β₁} {γ₂} ⦃ self₃ ⦄ = HSub.hSub₃ {α₀} {β₁} {γ₂} self₃

record Mod (α₀ : Set) : Set where
  constructor Mod:mk
  field
    mod₁ : α₀ → α₀ → α₀

Mod:mod : {α₀ : Set} → ⦃ _ : Mod α₀ ⦄ → α₀ → α₀ → α₀
Mod:mod {α₀} ⦃ self₁ ⦄ = Mod.mod₁ {α₀} self₁

Nat:casesOn : {motive₀ : Nat → Set} → (t₁ : Nat) → motive₀ Nat:zero → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ t₁
Nat:casesOn {motive₀} t₁ zero₂ succ₃ = Nat:rec {motive₀} zero₂ (λ (n₄ : Nat) → λ (nih₅ : motive₀ n₄) → succ₃ n₄) t₁

Nat:add:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → ((a₃ : Nat) → motive₀ a₃ Nat:zero) → ((a₃ : Nat) → (b₄ : Nat) → motive₀ a₃ (Nat:succ b₄)) → motive₀ x₁ x₂
Nat:add:match~u1 motive₀ x₁ x₂ h1₃ h2₄ = Nat:casesOn {λ (x₅ : Nat) → motive₀ x₁ x₅} x₂ (h1₃ x₁) (λ (n₅ : Nat) → h2₄ x₁ n₅)

record PProd (α₀ : Set) (β₁ : Set) : Set where
  constructor PProd:mk
  field
    fst₂ : α₀
    snd₃ : β₁

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

Nat:beq:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → (Unit → motive₀ Nat:zero Nat:zero) → ((n₃ : Nat) → motive₀ Nat:zero (Nat:succ n₃)) → ((n₃ : Nat) → motive₀ (Nat:succ n₃) Nat:zero) → ((n₃ : Nat) → (m₄ : Nat) → motive₀ (Nat:succ n₃) (Nat:succ m₄)) → motive₀ x₁ x₂
Nat:beq:match~u1 motive₀ x₁ x₂ h1₃ h2₄ h3₅ h4₆ = Nat:casesOn {λ (x₇ : Nat) → motive₀ x₇ x₂} x₁ (Nat:casesOn {λ (x₇ : Nat) → motive₀ Nat:zero x₇} x₂ (h1₃ Unit:unit) (λ (n₇ : Nat) → h2₄ n₇)) (λ (n₇ : Nat) → Nat:casesOn {λ (x₈ : Nat) → motive₀ (Nat:succ n₇) x₈} x₂ (h3₅ n₇) (λ (n₈ : Nat) → h4₆ n₇ n₈))

Nat:beq:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Nat → Bool} x₀ → Nat → Bool
Nat:beq:~uf x₀ f₁ x₂ = Nat:beq:match~u1 (λ (x₃ : Nat) → λ (x₄ : Nat) → Nat:below {λ (x₅ : Nat) → Nat → Bool} x₃ → Bool) x₀ x₂ (λ (x₃ : Unit) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Bool} Nat:zero) → Bool:true) (λ (n₃ : Nat) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Bool} Nat:zero) → Bool:false) (λ (n₃ : Nat) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Bool} (Nat:succ n₃)) → Bool:false) (λ (n₃ : Nat) → λ (m₄ : Nat) → λ (x₅ : Nat:below {λ (x₅ : Nat) → Nat → Bool} (Nat:succ n₃)) → PProd.fst₂ {(λ (x₆ : Nat) → Nat → Bool) n₃} {Nat:rec {λ (t₆ : Nat) → Set} PUnit (λ (n₆ : Nat) → λ (nih₇ : Set) → PProd ((λ (x₈ : Nat) → Nat → Bool) n₆) nih₇) n₃} x₅ m₄) f₁

Nat:beq : Nat → Nat → Bool
Nat:beq x₀ x₁ = Nat:brecOn {λ (x₂ : Nat) → Nat → Bool} x₀ Nat:beq:~uf x₁

Nat:ble:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → ((x₃ : Nat) → motive₀ Nat:zero x₃) → ((n₃ : Nat) → motive₀ (Nat:succ n₃) Nat:zero) → ((n₃ : Nat) → (m₄ : Nat) → motive₀ (Nat:succ n₃) (Nat:succ m₄)) → motive₀ x₁ x₂
Nat:ble:match~u1 motive₀ x₁ x₂ h1₃ h2₄ h3₅ = Nat:casesOn {λ (x₆ : Nat) → motive₀ x₆ x₂} x₁ (h1₃ x₂) (λ (n₆ : Nat) → Nat:casesOn {λ (x₇ : Nat) → motive₀ (Nat:succ n₆) x₇} x₂ (h2₄ n₆) (λ (n₇ : Nat) → h3₅ n₆ n₇))

Nat:ble:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Nat → Bool} x₀ → Nat → Bool
Nat:ble:~uf x₀ f₁ x₂ = Nat:ble:match~u1 (λ (x₃ : Nat) → λ (x₄ : Nat) → Nat:below {λ (x₅ : Nat) → Nat → Bool} x₃ → Bool) x₀ x₂ (λ (x₃ : Nat) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Bool} Nat:zero) → Bool:true) (λ (n₃ : Nat) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Bool} (Nat:succ n₃)) → Bool:false) (λ (n₃ : Nat) → λ (m₄ : Nat) → λ (x₅ : Nat:below {λ (x₅ : Nat) → Nat → Bool} (Nat:succ n₃)) → PProd.fst₂ {(λ (x₆ : Nat) → Nat → Bool) n₃} {Nat:rec {λ (t₆ : Nat) → Set} PUnit (λ (n₆ : Nat) → λ (nih₇ : Set) → PProd ((λ (x₈ : Nat) → Nat → Bool) n₆) nih₇) n₃} x₅ m₄) f₁

Nat:ble : Nat → Nat → Bool
Nat:ble x₀ x₁ = Nat:brecOn {λ (x₂ : Nat) → Nat → Bool} x₀ Nat:ble:~uf x₁

record OfNat (α₀ : Set) (x₁ : Nat) : Set where
  constructor OfNat:mk
  field
    ofNat₂ : α₀

OfNat:ofNat : {α₀ : Set} → (x₁ : Nat) → ⦃ _ : OfNat α₀ x₁ ⦄ → α₀
OfNat:ofNat {α₀} x₁ ⦃ self₂ ⦄ = OfNat.ofNat₂ {α₀} {x₁} self₂

instOfNatNat : (n₀ : Nat) → OfNat Nat n₀
instOfNatNat n₀ = OfNat:mk {Nat} {n₀} n₀

record True : Set where
  constructor True:intro

-- theorem
postulate noConfusion~uof~uNat : {α₀ : Set} → (f₁ : α₀ → Nat) → {a₂ : α₀} → {b₃ : α₀} → Eq {α₀} a₂ b₃ → Bool:rec {λ (x₄ : Bool) → Set} False True (Nat:beq (f₁ a₂) (f₁ b₃))

data Nat:le (n₀ : Nat) : Nat → Set where
  Nat:le:refl : Nat:le n₀ n₀
  Nat:le:step : {m₁ : Nat} → Nat:le n₀ m₁ → Nat:le n₀ (Nat:succ m₁)

-- recursor
Nat:le:rec : {n₀ : Nat} → {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} → motive₁ n₀ (Nat:le:refl {n₀}) → ({m₂ : Nat} → (a₃ : Nat:le n₀ m₂) → motive₁ m₂ a₃ → motive₁ (Nat:succ m₂) (Nat:le:step {n₀} {m₂} a₃)) → {a₂ : Nat} → (t₃ : Nat:le n₀ a₂) → motive₁ a₂ t₃
Nat:le:rec {n₀} {motive₁} refl₂ step₃ {_} Nat:le:refl = refl₂
Nat:le:rec {n₀} {motive₁} refl₂ step₃ {_} (Nat:le:step {m₅} a₆) = step₃ {m₅} a₆ (Nat:le:rec {n₀} {motive₁} refl₂ step₃ {m₅} a₆)

instLENat : LE Nat
instLENat = LE:mk {Nat} Nat:le

instAddNat : Add Nat
instAddNat = Add:mk {Nat} Nat:add

instHAdd : {α₀ : Set} → ⦃ _ : Add α₀ ⦄ → HAdd α₀ α₀ α₀
instHAdd {α₀} ⦃ inst₁ ⦄ = HAdd:mk {α₀} {α₀} {α₀} (λ (a₂ : α₀) → λ (b₃ : α₀) → Add:add {α₀} ⦃ inst₁ ⦄ a₂ b₃)

Nat:ctorIdx : Nat → Nat
Nat:ctorIdx x₀ = Nat:casesOn {λ (x₁ : Nat) → Nat} x₀ 0 (λ (n₁ : Nat) → 1)

-- theorem
postulate Nat:le~uof~uble~ueq~utrue : {n₀ : Nat} → {m₁ : Nat} → Eq {Bool} (Nat:ble n₀ m₁) Bool:true → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁

-- theorem
postulate Nat:not~ule~uof~unot~uble~ueq~utrue : {n₀ : Nat} → {m₁ : Nat} → Not (Eq {Bool} (Nat:ble n₀ m₁) Bool:true) → Not (LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁)

dite : {α₀ : Set} → (c₁ : Set) → ⦃ _ : Decidable c₁ ⦄ → (c₁ → α₀) → (Not c₁ → α₀) → α₀
dite {α₀} c₁ ⦃ h₂ ⦄ t₃ e₄ = Decidable:casesOn {c₁} {λ (x₅ : Decidable c₁) → α₀} h₂ e₄ t₃

instDecidableEqBool : DecidableEq Bool
instDecidableEqBool = Bool:decEq

Nat:decLe : (n₀ : Nat) → (m₁ : Nat) → Decidable (LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁)
Nat:decLe n₀ m₁ = dite {Decidable (LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁)} (Eq {Bool} (Nat:ble n₀ m₁) Bool:true) ⦃ instDecidableEqBool (Nat:ble n₀ m₁) Bool:true ⦄ (λ (h₂ : Eq {Bool} (Nat:ble n₀ m₁) Bool:true) → Decidable:isTrue {LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁} (Nat:le~uof~uble~ueq~utrue {n₀} {m₁} h₂)) (λ (h₂ : Not (Eq {Bool} (Nat:ble n₀ m₁) Bool:true)) → Decidable:isFalse {LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁} (Nat:not~ule~uof~unot~uble~ueq~utrue {n₀} {m₁} h₂))

Nat:lt : Nat → Nat → Set
Nat:lt n₀ m₁ = Nat:le (Nat:succ n₀) m₁

instLTNat : LT Nat
instLTNat = LT:mk {Nat} Nat:lt

Nat:decLt : (n₀ : Nat) → (m₁ : Nat) → Decidable (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁)
Nat:decLt n₀ m₁ = Nat:decLe (Nat:succ n₀) m₁

Nat:le:casesOn : {n₀ : Nat} → {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} → {a₂ : Nat} → (t₃ : Nat:le n₀ a₂) → motive₁ n₀ (Nat:le:refl {n₀}) → ({m₄ : Nat} → (a₅ : Nat:le n₀ m₄) → motive₁ (Nat:succ m₄) (Nat:le:step {n₀} {m₄} a₅)) → motive₁ a₂ t₃
Nat:le:casesOn {n₀} {motive₁} {a₂} t₃ refl₄ step₅ = Nat:le:rec {n₀} {motive₁} refl₄ (λ {m₆ : Nat} → λ (a₇ : Nat:le n₀ m₆) → λ (aih₈ : motive₁ m₆ a₇) → step₅ {m₆} a₇) {a₂} t₃

Nat:div:go:match~u1 : (x₀ : Nat) → (motive₁ : (fuel₁ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₀ fuel₁ → Set) → (fuel₂ : Nat) → (hfuel₃ : LT:lt {Nat} ⦃ instLTNat ⦄ x₀ fuel₂) → ((fuel₄ : Nat) → (hfuel₅ : LT:lt {Nat} ⦃ instLTNat ⦄ x₀ (Nat:succ fuel₄)) → motive₁ (Nat:succ fuel₄) hfuel₅) → motive₁ fuel₂ hfuel₃
Nat:div:go:match~u1 x₀ motive₁ fuel₂ hfuel₃ h1₄ = Nat:casesOn {λ (x₅ : Nat) → (hfuel₆ : LT:lt {Nat} ⦃ instLTNat ⦄ x₀ x₅) → motive₁ x₅ hfuel₆} fuel₂ (λ (hfuel₅ : LT:lt {Nat} ⦃ instLTNat ⦄ x₀ Nat:zero) → False:elim {motive₁ Nat:zero hfuel₅} (Nat:le:casesOn {Nat:succ x₀} {λ (a₆ : Nat) → λ (x₇ : Nat:le (Nat:succ x₀) a₆) → Eq {Nat} Nat:zero a₆ → HEq {LT:lt {Nat} ⦃ instLTNat ⦄ x₀ Nat:zero} hfuel₅ {Nat:le (Nat:succ x₀) a₆} x₇ → False} {Nat:zero} hfuel₅ (λ (h₆ : Eq {Nat} Nat:zero (Nat:succ x₀)) → False:elim {HEq {LT:lt {Nat} ⦃ instLTNat ⦄ x₀ Nat:zero} hfuel₅ {Nat:le (Nat:succ x₀) (Nat:succ x₀)} (Nat:le:refl {Nat:succ x₀}) → False} (noConfusion~uof~uNat {Nat} Nat:ctorIdx {Nat:zero} {Nat:succ x₀} h₆)) (λ {m₆ : Nat} → λ (a₇ : Nat:le (Nat:succ x₀) m₆) → λ (h₈ : Eq {Nat} Nat:zero (Nat:succ m₆)) → False:elim {HEq {LT:lt {Nat} ⦃ instLTNat ⦄ x₀ Nat:zero} hfuel₅ {Nat:le (Nat:succ x₀) (Nat:succ m₆)} (Nat:le:step {Nat:succ x₀} {m₆} a₇) → False} (noConfusion~uof~uNat {Nat} Nat:ctorIdx {Nat:zero} {Nat:succ m₆} h₈)) (Eq:refl {Nat} Nat:zero) (HEq:refl {LT:lt {Nat} ⦃ instLTNat ⦄ x₀ Nat:zero} hfuel₅))) (λ (n₅ : Nat) → λ (hfuel₆ : LT:lt {Nat} ⦃ instLTNat ⦄ x₀ (Nat:succ n₅)) → h1₄ n₅ hfuel₆) hfuel₃

Nat:pow:match~u1 : (motive₀ : Nat → Set) → (x₁ : Nat) → (Unit → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ x₁
Nat:pow:match~u1 motive₀ x₁ h1₂ h2₃ = Nat:casesOn {λ (x₄ : Nat) → motive₀ x₄} x₁ (h1₂ Unit:unit) (λ (n₄ : Nat) → h2₃ n₄)

Nat:pred : Nat → Nat
Nat:pred x₀ = Nat:pow:match~u1 (λ (x₁ : Nat) → Nat) x₀ (λ (x₁ : Unit) → OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (λ (a₁ : Nat) → a₁)

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

Sub:sub : {α₀ : Set} → ⦃ _ : Sub α₀ ⦄ → α₀ → α₀ → α₀
Sub:sub {α₀} ⦃ self₁ ⦄ = Sub.sub₁ {α₀} self₁

instHSub : {α₀ : Set} → ⦃ _ : Sub α₀ ⦄ → HSub α₀ α₀ α₀
instHSub {α₀} ⦃ inst₁ ⦄ = HSub:mk {α₀} {α₀} {α₀} (λ (a₂ : α₀) → λ (b₃ : α₀) → Sub:sub {α₀} ⦃ inst₁ ⦄ a₂ b₃)

instSubNat : Sub Nat
instSubNat = Sub:mk {Nat} Nat:sub

-- theorem
postulate Nat:div~urec~ufuel~ulemma : {x₀ : Nat} → {y₁ : Nat} → {fuel₂ : Nat} → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁ → LE:le {Nat} ⦃ instLENat ⦄ y₁ x₀ → LT:lt {Nat} ⦃ instLTNat ⦄ x₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ fuel₂ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) → LT:lt {Nat} ⦃ instLTNat ⦄ (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ x₀ y₁) fuel₂

namedPattern : {α₀ : Set} → (x₁ : α₀) → (a₂ : α₀) → Eq {α₀} x₁ a₂ → α₀
namedPattern {α₀} x₁ a₂ h₃ = a₂

Nat:mod:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → ((x₃ : Nat) → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₃) → ((n₃ : Nat) → (n₄ : Nat) → (h₅ : Eq {Nat} n₃ (Nat:succ n₄)) → (m₆ : Nat) → motive₀ (namedPattern {Nat} n₃ (Nat:succ n₄) h₅) m₆) → motive₀ x₁ x₂
Nat:mod:match~u1 motive₀ x₁ x₂ h1₃ h2₄ = Nat:casesOn {λ (x₅ : Nat) → motive₀ x₅ x₂} x₁ (h1₃ x₂) (λ (n₅ : Nat) → h2₄ (Nat:succ n₅) n₅ (Eq:refl {Nat} (Nat:succ n₅)) x₂)

-- theorem
postulate Nat:lt~usucc~uself : (n₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ n₀ (Nat:succ n₀)

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

instHMod : {α₀ : Set} → ⦃ _ : Mod α₀ ⦄ → HMod α₀ α₀ α₀
instHMod {α₀} ⦃ inst₁ ⦄ = HMod:mk {α₀} {α₀} {α₀} (λ (a₂ : α₀) → λ (b₃ : α₀) → Mod:mod {α₀} ⦃ inst₁ ⦄ a₂ b₃)

record Probe (v₀ : Nat) : Set where
  constructor Probe:mk
  field
    x₁ : Eq {Nat} (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ v₀ 16) 0
