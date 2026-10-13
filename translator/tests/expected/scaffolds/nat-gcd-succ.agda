-- File: translator/tests/expected/scaffolds/nat-gcd-succ.agda
{-# OPTIONS --type-in-type #-}
-- lean2agda, profile U: the scaffold of the closure of Nat:gcd~usucc
module U.Init.Data.Nat.Gcd where

record Add (α₀ : Set) : Set where
  constructor Add:mk
  field
    add₁ : α₀ → α₀ → α₀

postulate Add:rec : {α₀ : Set} → {motive₁ : Add α₀ → Set} → ((add₂ : α₀ → α₀ → α₀) → motive₁ (Add:mk {α₀} add₂)) → (t₂ : Add α₀) → motive₁ t₂

Add:add : {α₀ : Set} → ⦃ _ : Add α₀ ⦄ → α₀ → α₀ → α₀
Add:add {α₀} ⦃ self₁ ⦄ = Add.add₁ {α₀} self₁

record And (a₀ : Set) (b₁ : Set) : Set where
  constructor And:intro
  field
    left₂ : a₀
    right₃ : b₁

postulate And:rec : {a₀ : Set} → {b₁ : Set} → {motive₂ : And a₀ b₁ → Set} → ((left₃ : a₀) → (right₄ : b₁) → motive₂ (And:intro {a₀} {b₁} left₃ right₄)) → (t₃ : And a₀ b₁) → motive₂ t₃

postulate And:casesOn : {a₀ : Set} → {b₁ : Set} → {motive₂ : And a₀ b₁ → Set} → (t₃ : And a₀ b₁) → ((left₄ : a₀) → (right₅ : b₁) → motive₂ (And:intro {a₀} {b₁} left₄ right₅)) → motive₂ t₃

data Bool : Set where
  Bool:false : Bool
  Bool:true : Bool

postulate Bool:rec : {motive₀ : Bool → Set} → motive₀ Bool:false → motive₀ Bool:true → (t₁ : Bool) → motive₀ t₁

postulate Bool:casesOn : {motive₀ : Bool → Set} → (t₁ : Bool) → motive₀ Bool:false → motive₀ Bool:true → motive₀ t₁

data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

postulate Nat:rec : {motive₀ : Nat → Set} → motive₀ Nat:zero → ((n₁ : Nat) → motive₀ n₁ → motive₀ (Nat:succ n₁)) → (t₁ : Nat) → motive₀ t₁

postulate Bool:ctorIdx : Bool → Nat

record PUnit : Set where
  constructor PUnit:unit

postulate PUnit:rec : {motive₀ : PUnit → Set} → motive₀ PUnit:unit → (t₁ : PUnit) → motive₀ t₁

postulate Unit : Set

postulate Unit:unit : Unit

postulate Bool:decEq:match~u1 : (motive₀ : Bool → Bool → Set) → (a₁ : Bool) → (b₂ : Bool) → (Unit → motive₀ Bool:false Bool:false) → (Unit → motive₀ Bool:false Bool:true) → (Unit → motive₀ Bool:true Bool:false) → (Unit → motive₀ Bool:true Bool:true) → motive₀ a₁ b₂

postulate Bool:noConfusionType : Set → Bool → Bool → Set

data Eq {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl : (a₁ : α₀) → Eq {α₀} a₁ a₁

postulate Eq:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → Eq {α₀} a₁ a₂ → Set} → motive₂ a₁ (Eq:refl {α₀} a₁) → {a₃ : α₀} → (t₄ : Eq {α₀} a₁ a₃) → motive₂ a₃ t₄

postulate Eq:ndrec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : α₀ → Set} → motive₂ a₁ → {b₃ : α₀} → Eq {α₀} a₁ b₃ → motive₂ b₃

postulate Bool:noConfusion : {P₀ : Set} → {t₁ : Bool} → {t₂ : Bool} → Eq {Bool} t₁ t₂ → Bool:noConfusionType P₀ t₁ t₂

data False : Set where

postulate False:rec : (motive₀ : False → Set) → (t₁ : False) → motive₀ t₁

Not : Set → Set
Not a₀ = a₀ → False

data Decidable (p₀ : Set) : Set where
  Decidable:isFalse : Not p₀ → Decidable p₀
  Decidable:isTrue : p₀ → Decidable p₀

postulate Decidable:rec : {p₀ : Set} → {motive₁ : Decidable p₀ → Set} → ((h₂ : Not p₀) → motive₁ (Decidable:isFalse {p₀} h₂)) → ((h₂ : p₀) → motive₁ (Decidable:isTrue {p₀} h₂)) → (t₂ : Decidable p₀) → motive₁ t₂

postulate rfl : {α₀ : Set} → {a₁ : α₀} → Eq {α₀} a₁ a₁

postulate Bool:decEq : (a₀ : Bool) → (b₁ : Bool) → Decidable (Eq {Bool} a₀ b₁)

postulate Decidable:casesOn : {p₀ : Set} → {motive₁ : Decidable p₀ → Set} → (t₂ : Decidable p₀) → ((h₃ : Not p₀) → motive₁ (Decidable:isFalse {p₀} h₃)) → ((h₃ : p₀) → motive₁ (Decidable:isTrue {p₀} h₃)) → motive₁ t₂

DecidableEq : Set → Set
DecidableEq α₀ = (a₁ : α₀) → (b₂ : α₀) → Decidable (Eq {α₀} a₁ b₂)

postulate Eq:casesOn : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → Eq {α₀} a₁ a₂ → Set} → {a₃ : α₀} → (t₄ : Eq {α₀} a₁ a₃) → motive₂ a₁ (Eq:refl {α₀} a₁) → motive₂ a₃ t₄

postulate Eq:symm : {α₀ : Set} → {a₁ : α₀} → {b₂ : α₀} → Eq {α₀} a₁ b₂ → Eq {α₀} b₂ a₁

postulate Eq:mpr : {α₀ : Set} → {β₁ : Set} → Eq {Set} α₀ β₁ → β₁ → α₀

postulate Eq:trans : {α₀ : Set} → {a₁ : α₀} → {b₂ : α₀} → {c₃ : α₀} → Eq {α₀} a₁ b₂ → Eq {α₀} b₂ c₃ → Eq {α₀} a₁ c₃

postulate False:elim : {C₀ : Set} → False → C₀

record LE (α₀ : Set) : Set where
  constructor LE:mk
  field
    le₁ : α₀ → α₀ → Set

postulate LE:rec : {α₀ : Set} → {motive₁ : LE α₀ → Set} → ((le₂ : α₀ → α₀ → Set) → motive₁ (LE:mk {α₀} le₂)) → (t₂ : LE α₀) → motive₁ t₂

LE:le : {α₀ : Set} → ⦃ _ : LE α₀ ⦄ → α₀ → α₀ → Set
LE:le {α₀} ⦃ self₁ ⦄ = LE.le₁ {α₀} self₁

postulate GE:ge : {α₀ : Set} → ⦃ _ : LE α₀ ⦄ → α₀ → α₀ → Set

outParam : Set → Set
outParam α₀ = α₀

record HAdd (α₀ : Set) (β₁ : Set) (γ₂ : outParam Set) : Set where
  constructor HAdd:mk
  field
    hAdd₃ : α₀ → β₁ → γ₂

postulate HAdd:rec : {α₀ : Set} → {β₁ : Set} → {γ₂ : Set} → {motive₃ : HAdd α₀ β₁ γ₂ → Set} → ((hAdd₄ : α₀ → β₁ → γ₂) → motive₃ (HAdd:mk {α₀} {β₁} {γ₂} hAdd₄)) → (t₄ : HAdd α₀ β₁ γ₂) → motive₃ t₄

HAdd:hAdd : {α₀ : Set} → {β₁ : Set} → {γ₂ : outParam Set} → ⦃ _ : HAdd α₀ β₁ γ₂ ⦄ → α₀ → β₁ → γ₂
HAdd:hAdd {α₀} {β₁} {γ₂} ⦃ self₃ ⦄ = HAdd.hAdd₃ {α₀} {β₁} {γ₂} self₃

data HEq {α₀ : Set} : α₀ → {β₁ : Set} → β₁ → Set where
  HEq:refl : (a₁ : α₀) → HEq {α₀} a₁ {α₀} a₁

postulate HEq:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : {β₂ : Set} → (a₃ : β₂) → HEq {α₀} a₁ {β₂} a₃ → Set} → motive₂ {α₀} a₁ (HEq:refl {α₀} a₁) → {β₃ : Set} → {a₄ : β₃} → (t₅ : HEq {α₀} a₁ {β₃} a₄) → motive₂ {β₃} a₄ t₅

record HMod (α₀ : Set) (β₁ : Set) (γ₂ : outParam Set) : Set where
  constructor HMod:mk
  field
    hMod₃ : α₀ → β₁ → γ₂

postulate HMod:rec : {α₀ : Set} → {β₁ : Set} → {γ₂ : Set} → {motive₃ : HMod α₀ β₁ γ₂ → Set} → ((hMod₄ : α₀ → β₁ → γ₂) → motive₃ (HMod:mk {α₀} {β₁} {γ₂} hMod₄)) → (t₄ : HMod α₀ β₁ γ₂) → motive₃ t₄

HMod:hMod : {α₀ : Set} → {β₁ : Set} → {γ₂ : outParam Set} → ⦃ _ : HMod α₀ β₁ γ₂ ⦄ → α₀ → β₁ → γ₂
HMod:hMod {α₀} {β₁} {γ₂} ⦃ self₃ ⦄ = HMod.hMod₃ {α₀} {β₁} {γ₂} self₃

record HSub (α₀ : Set) (β₁ : Set) (γ₂ : outParam Set) : Set where
  constructor HSub:mk
  field
    hSub₃ : α₀ → β₁ → γ₂

postulate HSub:rec : {α₀ : Set} → {β₁ : Set} → {γ₂ : Set} → {motive₃ : HSub α₀ β₁ γ₂ → Set} → ((hSub₄ : α₀ → β₁ → γ₂) → motive₃ (HSub:mk {α₀} {β₁} {γ₂} hSub₄)) → (t₄ : HSub α₀ β₁ γ₂) → motive₃ t₄

HSub:hSub : {α₀ : Set} → {β₁ : Set} → {γ₂ : outParam Set} → ⦃ _ : HSub α₀ β₁ γ₂ ⦄ → α₀ → β₁ → γ₂
HSub:hSub {α₀} {β₁} {γ₂} ⦃ self₃ ⦄ = HSub.hSub₃ {α₀} {β₁} {γ₂} self₃

postulate InvImage : {α₀ : Set} → {β₁ : Set} → (β₁ → β₁ → Set) → (α₀ → β₁) → α₀ → α₀ → Set

record LT (α₀ : Set) : Set where
  constructor LT:mk
  field
    lt₁ : α₀ → α₀ → Set

postulate LT:rec : {α₀ : Set} → {motive₁ : LT α₀ → Set} → ((lt₂ : α₀ → α₀ → Set) → motive₁ (LT:mk {α₀} lt₂)) → (t₂ : LT α₀) → motive₁ t₂

LT:lt : {α₀ : Set} → ⦃ _ : LT α₀ ⦄ → α₀ → α₀ → Set
LT:lt {α₀} ⦃ self₁ ⦄ = LT.lt₁ {α₀} self₁

record Mod (α₀ : Set) : Set where
  constructor Mod:mk
  field
    mod₁ : α₀ → α₀ → α₀

postulate Mod:rec : {α₀ : Set} → {motive₁ : Mod α₀ → Set} → ((mod₂ : α₀ → α₀ → α₀) → motive₁ (Mod:mk {α₀} mod₂)) → (t₂ : Mod α₀) → motive₁ t₂

Mod:mod : {α₀ : Set} → ⦃ _ : Mod α₀ ⦄ → α₀ → α₀ → α₀
Mod:mod {α₀} ⦃ self₁ ⦄ = Mod.mod₁ {α₀} self₁

postulate Nat:casesOn : {motive₀ : Nat → Set} → (t₁ : Nat) → motive₀ Nat:zero → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ t₁

postulate Nat:add:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → ((a₃ : Nat) → motive₀ a₃ Nat:zero) → ((a₃ : Nat) → (b₄ : Nat) → motive₀ a₃ (Nat:succ b₄)) → motive₀ x₁ x₂

record PProd (α₀ : Set) (β₁ : Set) : Set where
  constructor PProd:mk
  field
    fst₂ : α₀
    snd₃ : β₁

postulate PProd:rec : {α₀ : Set} → {β₁ : Set} → {motive₂ : PProd α₀ β₁ → Set} → ((fst₃ : α₀) → (snd₄ : β₁) → motive₂ (PProd:mk {α₀} {β₁} fst₃ snd₄)) → (t₃ : PProd α₀ β₁) → motive₂ t₃

postulate Nat:below : {_ : Nat → Set} → Nat → Set

postulate Nat:add:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Nat → Nat} x₀ → Nat → Nat

postulate Nat:brecOn:go : {motive₀ : Nat → Set} → (t₁ : Nat) → ((t₂ : Nat) → Nat:below {motive₀} t₂ → motive₀ t₂) → PProd (motive₀ t₁) (Nat:below {motive₀} t₁)

postulate Nat:brecOn : {motive₀ : Nat → Set} → (t₁ : Nat) → ((t₂ : Nat) → Nat:below {motive₀} t₂ → motive₀ t₂) → motive₀ t₁

postulate Nat:add : Nat → Nat → Nat

postulate Nat:beq:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → (Unit → motive₀ Nat:zero Nat:zero) → ((n₃ : Nat) → motive₀ Nat:zero (Nat:succ n₃)) → ((n₃ : Nat) → motive₀ (Nat:succ n₃) Nat:zero) → ((n₃ : Nat) → (m₄ : Nat) → motive₀ (Nat:succ n₃) (Nat:succ m₄)) → motive₀ x₁ x₂

postulate Nat:beq:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Nat → Bool} x₀ → Nat → Bool

postulate Nat:beq : Nat → Nat → Bool

postulate Nat:ble:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → ((x₃ : Nat) → motive₀ Nat:zero x₃) → ((n₃ : Nat) → motive₀ (Nat:succ n₃) Nat:zero) → ((n₃ : Nat) → (m₄ : Nat) → motive₀ (Nat:succ n₃) (Nat:succ m₄)) → motive₀ x₁ x₂

postulate Nat:ble:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Nat → Bool} x₀ → Nat → Bool

postulate Nat:ble : Nat → Nat → Bool

record OfNat (α₀ : Set) (x₁ : Nat) : Set where
  constructor OfNat:mk
  field
    ofNat₂ : α₀

postulate OfNat:rec : {α₀ : Set} → {x₁ : Nat} → {motive₂ : OfNat α₀ x₁ → Set} → ((ofNat₃ : α₀) → motive₂ (OfNat:mk {α₀} {x₁} ofNat₃)) → (t₃ : OfNat α₀ x₁) → motive₂ t₃

OfNat:ofNat : {α₀ : Set} → (x₁ : Nat) → ⦃ _ : OfNat α₀ x₁ ⦄ → α₀
OfNat:ofNat {α₀} x₁ ⦃ self₂ ⦄ = OfNat.ofNat₂ {α₀} {x₁} self₂

postulate instOfNatNat : (n₀ : Nat) → OfNat Nat n₀

postulate ~uprivate:Init:Prelude:~n0:Nat:ble~uself~ueq~utrue:match~u1~u1 : (motive₀ : Nat → Set) → (x₁ : Nat) → (Unit → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ x₁

postulate Nat:ble~uself~ueq~utrue:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Eq {Bool} (Nat:ble x₁ x₁) Bool:true} x₀ → Eq {Bool} (Nat:ble x₀ x₀) Bool:true

postulate Nat:ble~uself~ueq~utrue : (n₀ : Nat) → Eq {Bool} (Nat:ble n₀ n₀) Bool:true

record True : Set where
  constructor True:intro

postulate True:rec : {motive₀ : True → Set} → motive₀ True:intro → (t₁ : True) → motive₀ t₁

postulate ~uprivate:Init:Prelude:~n0:noConfusion~uof~uNat:aux:match~u1~u1 : (motive₀ : Nat → Set) → (x₁ : Nat) → (Unit → motive₀ Nat:zero) → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ x₁

postulate ~uprivate:Init:Prelude:~n0:noConfusion~uof~uNat:aux:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Bool:rec {λ (x₂ : Bool) → Set} False True (Nat:beq x₁ x₁)} x₀ → Bool:rec {λ (x₁ : Bool) → Set} False True (Nat:beq x₀ x₀)

postulate ~uprivate:Init:Prelude:~n0:noConfusion~uof~uNat:aux : (a₀ : Nat) → Bool:rec {λ (x₁ : Bool) → Set} False True (Nat:beq a₀ a₀)

postulate congrArg : {α₀ : Set} → {β₁ : Set} → {a₂ : α₀} → {a₃ : α₀} → (f₄ : α₀ → β₁) → Eq {α₀} a₂ a₃ → Eq {β₁} (f₄ a₂) (f₄ a₃)

postulate noConfusion~uof~uNat : {α₀ : Set} → (f₁ : α₀ → Nat) → {a₂ : α₀} → {b₃ : α₀} → Eq {α₀} a₂ b₃ → Bool:rec {λ (x₄ : Bool) → Set} False True (Nat:beq (f₁ a₂) (f₁ b₃))

postulate ~uprivate:Init:Prelude:~n0:Nat:ble~usucc~ueq~utrue:match~u1~u1 : (motive₀ : (x₀ : Nat) → (x₁ : Nat) → Eq {Bool} (Nat:ble x₀ x₁) Bool:true → Set) → (x₁ : Nat) → (x₂ : Nat) → (x₃ : Eq {Bool} (Nat:ble x₁ x₂) Bool:true) → ((x₄ : Nat) → (x₅ : Eq {Bool} (Nat:ble (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₄) Bool:true) → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₄ x₅) → ((n₄ : Nat) → (n₅ : Nat) → (h₆ : Eq {Bool} (Nat:ble (Nat:succ n₄) (Nat:succ n₅)) Bool:true) → motive₀ (Nat:succ n₄) (Nat:succ n₅) h₆) → motive₀ x₁ x₂ x₃

postulate Nat:ble~usucc~ueq~utrue:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → (x₂ : Nat) → Eq {Bool} (Nat:ble x₁ x₂) Bool:true → Eq {Bool} (Nat:ble x₁ (Nat:succ x₂)) Bool:true} x₀ → (x₁ : Nat) → Eq {Bool} (Nat:ble x₀ x₁) Bool:true → Eq {Bool} (Nat:ble x₀ (Nat:succ x₁)) Bool:true

postulate Nat:ble~usucc~ueq~utrue : {n₀ : Nat} → {m₁ : Nat} → Eq {Bool} (Nat:ble n₀ m₁) Bool:true → Eq {Bool} (Nat:ble n₀ (Nat:succ m₁)) Bool:true

data Nat:le (n₀ : Nat) : Nat → Set where
  Nat:le:refl : Nat:le n₀ n₀
  Nat:le:step : {m₁ : Nat} → Nat:le n₀ m₁ → Nat:le n₀ (Nat:succ m₁)

postulate Nat:le:rec : {n₀ : Nat} → {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} → motive₁ n₀ (Nat:le:refl {n₀}) → ({m₂ : Nat} → (a₃ : Nat:le n₀ m₂) → motive₁ m₂ a₃ → motive₁ (Nat:succ m₂) (Nat:le:step {n₀} {m₂} a₃)) → {a₂ : Nat} → (t₃ : Nat:le n₀ a₂) → motive₁ a₂ t₃

data Nat:le:below {n₀ : Nat} {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} : {a₂ : Nat} → Nat:le n₀ a₂ → Set where
  Nat:le:below:refl : Nat:le:below {n₀} {motive₁} {n₀} (Nat:le:refl {n₀})
  Nat:le:below:step : {m₂ : Nat} → (a₃ : Nat:le n₀ m₂) → Nat:le:below {n₀} {motive₁} {m₂} a₃ → motive₁ m₂ a₃ → Nat:le:below {n₀} {motive₁} {Nat:succ m₂} (Nat:le:step {n₀} {m₂} a₃)

postulate Nat:le:below:rec : {n₀ : Nat} → {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} → {motive₂ : {a₂ : Nat} → (t₃ : Nat:le n₀ a₂) → Nat:le:below {n₀} {motive₁} {a₂} t₃ → Set} → motive₂ {n₀} (Nat:le:refl {n₀}) (Nat:le:below:refl {n₀} {motive₁}) → ({m₃ : Nat} → (a₄ : Nat:le n₀ m₃) → (ih₅ : Nat:le:below {n₀} {motive₁} {m₃} a₄) → (aih₆ : motive₁ m₃ a₄) → motive₂ {m₃} a₄ ih₅ → motive₂ {Nat:succ m₃} (Nat:le:step {n₀} {m₃} a₄) (Nat:le:below:step {n₀} {motive₁} {m₃} a₄ ih₅ aih₆)) → {a₃ : Nat} → {t₄ : Nat:le n₀ a₃} → (t₅ : Nat:le:below {n₀} {motive₁} {a₃} t₄) → motive₂ {a₃} t₄ t₅

postulate Nat:le:brecOn : {n₀ : Nat} → {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} → {a₂ : Nat} → (t₃ : Nat:le n₀ a₂) → ((a₄ : Nat) → (t₅ : Nat:le n₀ a₄) → Nat:le:below {n₀} {motive₁} {a₄} t₅ → motive₁ a₄ t₅) → motive₁ a₂ t₃

postulate Nat:le:below:casesOn : {n₀ : Nat} → {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} → {motive₂ : {a₂ : Nat} → (t₃ : Nat:le n₀ a₂) → Nat:le:below {n₀} {motive₁} {a₂} t₃ → Set} → {a₃ : Nat} → {t₄ : Nat:le n₀ a₃} → (t₅ : Nat:le:below {n₀} {motive₁} {a₃} t₄) → motive₂ {n₀} (Nat:le:refl {n₀}) (Nat:le:below:refl {n₀} {motive₁}) → ({m₆ : Nat} → (a₇ : Nat:le n₀ m₆) → (ih₈ : Nat:le:below {n₀} {motive₁} {m₆} a₇) → (aih₉ : motive₁ m₆ a₇) → motive₂ {Nat:succ m₆} (Nat:le:step {n₀} {m₆} a₇) (Nat:le:below:step {n₀} {motive₁} {m₆} a₇ ih₈ aih₉)) → motive₂ {a₃} t₄ t₅

postulate cast : {α₀ : Set} → {β₁ : Set} → Eq {Set} α₀ β₁ → α₀ → β₁

postulate eq~uof~uheq : {α₀ : Set} → {a₁ : α₀} → {a₂ : α₀} → HEq {α₀} a₁ {α₀} a₂ → Eq {α₀} a₁ a₂

postulate instLENat : LE Nat

postulate ~uprivate:Init:Prelude:~n0:Nat:ble~ueq~utrue~uof~ule:match~u1~u7 : {n₀ : Nat} → (funType1₁ : {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → Set) → (motive₂ : (m₂ : Nat) → (h₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₂) → Nat:le:below {n₀} {λ (m₄ : Nat) → λ (h₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₄) → funType1₁ {m₄} h₅} {m₂} h₃ → Set) → (m₃ : Nat) → (h₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₃) → (below₅ : Nat:le:below {n₀} {λ (m₅ : Nat) → λ (h₆ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₅) → funType1₁ {m₅} h₆} {m₃} h₄) → (Unit → motive₂ n₀ (Nat:le:refl {n₀}) (Nat:le:below:refl {n₀} {λ (m₆ : Nat) → λ (h₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₆) → funType1₁ {m₆} h₇})) → ((m₆ : Nat) → (h₇ : Nat:le n₀ m₆) → (ih₈ : Nat:le:below {n₀} {λ (m₈ : Nat) → λ (h₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₈) → funType1₁ {m₈} h₉} {m₆} h₇) → (aih₉ : funType1₁ {m₆} h₇) → motive₂ (Nat:succ m₆) (Nat:le:step {n₀} {m₆} h₇) (Nat:le:below:step {n₀} {λ (m₁₀ : Nat) → λ (h₁₁ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₀) → funType1₁ {m₁₀} h₁₁} {m₆} h₇ ih₈ aih₉)) → motive₂ m₃ h₄ below₅

postulate Nat:ble~ueq~utrue~uof~ule : {n₀ : Nat} → {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → Eq {Bool} (Nat:ble n₀ m₁) Bool:true

postulate instAddNat : Add Nat

postulate instHAdd : {α₀ : Set} → ⦃ _ : Add α₀ ⦄ → HAdd α₀ α₀ α₀

postulate Nat:casesAuxOn : {motive₀ : Nat → Set} → (t₁ : Nat) → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) → ((n₂ : Nat) → motive₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₂ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → motive₀ t₁

postulate Nat:ctorIdx : Nat → Nat

postulate Nat:decEq:match~u1 : (motive₀ : Bool → Set) → (x₁ : Bool) → (Eq {Bool} x₁ Bool:true → motive₀ Bool:true) → (Eq {Bool} x₁ Bool:false → motive₀ Bool:false) → motive₀ x₁

postulate ~uprivate:Init:Prelude:~n0:Nat:eq~uof~ubeq~ueq~utrue:match~u1~u1 : (motive₀ : (x₀ : Nat) → (x₁ : Nat) → Eq {Bool} (Nat:beq x₀ x₁) Bool:true → Set) → (x₁ : Nat) → (x₂ : Nat) → (x₃ : Eq {Bool} (Nat:beq x₁ x₂) Bool:true) → ((x₄ : Eq {Bool} (Nat:beq Nat:zero Nat:zero) Bool:true) → motive₀ Nat:zero Nat:zero x₄) → ((n₄ : Nat) → (h₅ : Eq {Bool} (Nat:beq Nat:zero (Nat:succ n₄)) Bool:true) → motive₀ Nat:zero (Nat:succ n₄) h₅) → ((n₄ : Nat) → (h₅ : Eq {Bool} (Nat:beq (Nat:succ n₄) Nat:zero) Bool:true) → motive₀ (Nat:succ n₄) Nat:zero h₅) → ((n₄ : Nat) → (m₅ : Nat) → (h₆ : Eq {Bool} (Nat:beq (Nat:succ n₄) (Nat:succ m₅)) Bool:true) → motive₀ (Nat:succ n₄) (Nat:succ m₅) h₆) → motive₀ x₁ x₂ x₃

postulate Nat:eq~uof~ubeq~ueq~utrue:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → (x₂ : Nat) → Eq {Bool} (Nat:beq x₁ x₂) Bool:true → Eq {Nat} x₁ x₂} x₀ → (x₁ : Nat) → Eq {Bool} (Nat:beq x₀ x₁) Bool:true → Eq {Nat} x₀ x₁

postulate Nat:eq~uof~ubeq~ueq~utrue : {n₀ : Nat} → {m₁ : Nat} → Eq {Bool} (Nat:beq n₀ m₁) Bool:true → Eq {Nat} n₀ m₁

postulate Nat:noConfusionType : Set → Nat → Nat → Set

postulate Nat:noConfusion : {P₀ : Set} → {t₁ : Nat} → {t₂ : Nat} → Eq {Nat} t₁ t₂ → Nat:noConfusionType P₀ t₁ t₂

postulate ~uprivate:Init:Prelude:~n0:Nat:ne~uof~ubeq~ueq~ufalse:match~u1~u1 : (motive₀ : (x₀ : Nat) → (x₁ : Nat) → Eq {Bool} (Nat:beq x₀ x₁) Bool:false → Eq {Nat} x₀ x₁ → Set) → (x₁ : Nat) → (x₂ : Nat) → (x₃ : Eq {Bool} (Nat:beq x₁ x₂) Bool:false) → (x₄ : Eq {Nat} x₁ x₂) → ((h₅ : Eq {Bool} (Nat:beq Nat:zero Nat:zero) Bool:false) → (x₆ : Eq {Nat} Nat:zero Nat:zero) → motive₀ Nat:zero Nat:zero h₅ x₆) → ((n₅ : Nat) → (x₆ : Eq {Bool} (Nat:beq Nat:zero (Nat:succ n₅)) Bool:false) → (h₇ : Eq {Nat} Nat:zero (Nat:succ n₅)) → motive₀ Nat:zero (Nat:succ n₅) x₆ h₇) → ((n₅ : Nat) → (x₆ : Eq {Bool} (Nat:beq (Nat:succ n₅) Nat:zero) Bool:false) → (h₇ : Eq {Nat} (Nat:succ n₅) Nat:zero) → motive₀ (Nat:succ n₅) Nat:zero x₆ h₇) → ((n₅ : Nat) → (m₆ : Nat) → (h₇ : Eq {Bool} (Nat:beq (Nat:succ n₅) (Nat:succ m₆)) Bool:false) → (h₈ : Eq {Nat} (Nat:succ n₅) (Nat:succ m₆)) → motive₀ (Nat:succ n₅) (Nat:succ m₆) h₇ h₈) → motive₀ x₁ x₂ x₃ x₄

postulate absurd : {a₀ : Set} → {b₁ : Set} → a₀ → Not a₀ → b₁

postulate Nat:ne~uof~ubeq~ueq~ufalse:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → (x₂ : Nat) → Eq {Bool} (Nat:beq x₁ x₂) Bool:false → Eq {Nat} x₁ x₂ → False} x₀ → (x₁ : Nat) → Eq {Bool} (Nat:beq x₀ x₁) Bool:false → Eq {Nat} x₀ x₁ → False

postulate Nat:ne~uof~ubeq~ueq~ufalse : {n₀ : Nat} → {m₁ : Nat} → Eq {Bool} (Nat:beq n₀ m₁) Bool:false → Not (Eq {Nat} n₀ m₁)

postulate Nat:decEq : (n₀ : Nat) → (m₁ : Nat) → Decidable (Eq {Nat} n₀ m₁)

postulate ~uprivate:Init:Prelude:~n0:Nat:succ~ule~usucc:match~u1~u7 : {n₀ : Nat} → (funType1₁ : {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → Set) → (motive₂ : (m₂ : Nat) → (x₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₂) → Nat:le:below {n₀} {λ (m₄ : Nat) → λ (x₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₄) → funType1₁ {m₄} x₅} {m₂} x₃ → Set) → (m₃ : Nat) → (x₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₃) → (below₅ : Nat:le:below {n₀} {λ (m₅ : Nat) → λ (x₆ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₅) → funType1₁ {m₅} x₆} {m₃} x₄) → (Unit → motive₂ n₀ (Nat:le:refl {n₀}) (Nat:le:below:refl {n₀} {λ (m₆ : Nat) → λ (x₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₆) → funType1₁ {m₆} x₇})) → ((m₆ : Nat) → (h₇ : Nat:le n₀ m₆) → (ih₈ : Nat:le:below {n₀} {λ (m₈ : Nat) → λ (x₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₈) → funType1₁ {m₈} x₉} {m₆} h₇) → (aih₉ : funType1₁ {m₆} h₇) → motive₂ (Nat:succ m₆) (Nat:le:step {n₀} {m₆} h₇) (Nat:le:below:step {n₀} {λ (m₁₀ : Nat) → λ (x₁₁ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₀) → funType1₁ {m₁₀} x₁₁} {m₆} h₇ ih₈ aih₉)) → motive₂ m₃ x₄ below₅

postulate Nat:succ~ule~usucc : {n₀ : Nat} → {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₀) (Nat:succ m₁)

postulate ~uprivate:Init:Prelude:~n0:Nat:zero~ule:match~u1~u1 : (motive₀ : Nat → Set) → (x₁ : Nat) → (Unit → motive₀ Nat:zero) → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ x₁

postulate Nat:zero~ule:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₁} x₀ → LE:le {Nat} ⦃ instLENat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₀

postulate Nat:zero~ule : (n₀ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) n₀

postulate ~uprivate:Init:Prelude:~n0:Nat:le~uof~uble~ueq~utrue:match~u1~u1 : (motive₀ : (n₀ : Nat) → (m₁ : Nat) → Eq {Bool} (Nat:ble n₀ m₁) Bool:true → Set) → (n₁ : Nat) → (m₂ : Nat) → (h₃ : Eq {Bool} (Nat:ble n₁ m₂) Bool:true) → ((x₄ : Nat) → (h₅ : Eq {Bool} (Nat:ble (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₄) Bool:true) → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₄ h₅) → ((n₄ : Nat) → (n₅ : Nat) → (h₆ : Eq {Bool} (Nat:ble (Nat:succ n₄) (Nat:succ n₅)) Bool:true) → motive₀ (Nat:succ n₄) (Nat:succ n₅) h₆) → motive₀ n₁ m₂ h₃

postulate Nat:le~uof~uble~ueq~utrue:~uf : {n₀ : Nat} → Nat:below {λ (n₁ : Nat) → {m₂ : Nat} → Eq {Bool} (Nat:ble n₁ m₂) Bool:true → LE:le {Nat} ⦃ instLENat ⦄ n₁ m₂} n₀ → {m₁ : Nat} → Eq {Bool} (Nat:ble n₀ m₁) Bool:true → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁

postulate Nat:le~uof~uble~ueq~utrue : {n₀ : Nat} → {m₁ : Nat} → Eq {Bool} (Nat:ble n₀ m₁) Bool:true → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁

postulate Nat:not~ule~uof~unot~uble~ueq~utrue : {n₀ : Nat} → {m₁ : Nat} → Not (Eq {Bool} (Nat:ble n₀ m₁) Bool:true) → Not (LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁)

postulate dite : {α₀ : Set} → (c₁ : Set) → ⦃ _ : Decidable c₁ ⦄ → (c₁ → α₀) → (Not c₁ → α₀) → α₀

postulate instDecidableEqBool : DecidableEq Bool

postulate Nat:decLe : (n₀ : Nat) → (m₁ : Nat) → Decidable (LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁)

postulate Nat:lt : Nat → Nat → Set

postulate instLTNat : LT Nat

postulate Nat:decLt : (n₀ : Nat) → (m₁ : Nat) → Decidable (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁)

postulate Nat:le:casesOn : {n₀ : Nat} → {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} → {a₂ : Nat} → (t₃ : Nat:le n₀ a₂) → motive₁ n₀ (Nat:le:refl {n₀}) → ({m₄ : Nat} → (a₅ : Nat:le n₀ m₄) → motive₁ (Nat:succ m₄) (Nat:le:step {n₀} {m₄} a₅)) → motive₁ a₂ t₃

postulate Nat:div:go:match~u1 : (x₀ : Nat) → (motive₁ : (fuel₁ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₀ fuel₁ → Set) → (fuel₂ : Nat) → (hfuel₃ : LT:lt {Nat} ⦃ instLTNat ⦄ x₀ fuel₂) → ((fuel₄ : Nat) → (hfuel₅ : LT:lt {Nat} ⦃ instLTNat ⦄ x₀ (Nat:succ fuel₄)) → motive₁ (Nat:succ fuel₄) hfuel₅) → motive₁ fuel₂ hfuel₃

postulate ~uprivate:Init:Prelude:~n0:Nat:le~utrans:match~u1~u10 : {n₀ : Nat} → {m₁ : Nat} → (funType1₂ : {k₂ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → LE:le {Nat} ⦃ instLENat ⦄ m₁ k₂ → Set) → (motive₃ : (k₃ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → (x₄ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₃) → Nat:le:below {m₁} {λ (k₅ : Nat) → λ (x₆ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₅) → (x₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₅} x₇ x₆} {k₃} x₄ → Set) → (k₄ : Nat) → (x₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → (x₆ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₄) → (below₇ : Nat:le:below {m₁} {λ (k₇ : Nat) → λ (x₈ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₇) → (x₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₇} x₉ x₈} {k₄} x₆) → ((h₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → motive₃ m₁ h₈ (Nat:le:refl {m₁}) (Nat:le:below:refl {m₁} {λ (k₉ : Nat) → λ (x₁₀ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₉) → (x₁₁ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₉} x₁₁ x₁₀})) → ((h₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → (m₉ : Nat) → (h₁₀ : Nat:le m₁ m₉) → (ih₁₁ : Nat:le:below {m₁} {λ (k₁₁ : Nat) → λ (x₁₂ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₁) → (x₁₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₁} x₁₃ x₁₂} {m₉} h₁₀) → (aih₁₂ : (x₁₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {m₉} x₁₂ h₁₀) → motive₃ (Nat:succ m₉) h₈ (Nat:le:step {m₁} {m₉} h₁₀) (Nat:le:below:step {m₁} {λ (k₁₃ : Nat) → λ (x₁₄ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₃) → (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₃} x₁₅ x₁₄} {m₉} h₁₀ ih₁₁ aih₁₂)) → motive₃ k₄ x₅ x₆ below₇

postulate Nat:le~utrans : {n₀ : Nat} → {m₁ : Nat} → {k₂ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → LE:le {Nat} ⦃ instLENat ⦄ m₁ k₂ → LE:le {Nat} ⦃ instLENat ⦄ n₀ k₂

postulate Nat:lt~uof~ult~uof~ule : {n₀ : Nat} → {m₁ : Nat} → {k₂ : Nat} → LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁ → LE:le {Nat} ⦃ instLENat ⦄ m₁ k₂ → LT:lt {Nat} ⦃ instLTNat ⦄ n₀ k₂

postulate Nat:le~usucc : (n₀ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ n₀)

postulate Nat:pow:match~u1 : (motive₀ : Nat → Set) → (x₁ : Nat) → (Unit → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ x₁

postulate Nat:pred : Nat → Nat

postulate ~uprivate:Init:Prelude:~n0:Nat:pred~ule~upred:match~u1~u1 : (motive₀ : (x₀ : Nat) → (x₁ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ x₀ x₁ → Set) → (x₁ : Nat) → (x₂ : Nat) → (x₃ : LE:le {Nat} ⦃ instLENat ⦄ x₁ x₂) → ((n₄ : Nat) → motive₀ n₄ n₄ (Nat:le:refl {n₄})) → ((n₄ : Nat) → (h₅ : Nat:le (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) n₄) → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₄) (Nat:le:step {OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄} {n₄} h₅)) → ((n₄ : Nat) → (n₅ : Nat) → (h₆ : Nat:le (Nat:succ n₄) n₅) → motive₀ (Nat:succ n₄) (Nat:succ n₅) (Nat:le:step {Nat:succ n₄} {n₅} h₆)) → motive₀ x₁ x₂ x₃

postulate Nat:pred~ule~upred : {n₀ : Nat} → {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → LE:le {Nat} ⦃ instLENat ⦄ (Nat:pred n₀) (Nat:pred m₁)

postulate Nat:le~uof~usucc~ule~usucc : {n₀ : Nat} → {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₀) (Nat:succ m₁) → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁

postulate Nat:not~usucc~ule~uzero : (n₀ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₀) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) → False

postulate ~uprivate:Init:Prelude:~n0:Nat:not~usucc~ule~uself:match~u1~u1 : (motive₀ : Nat → Set) → (x₁ : Nat) → (Unit → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ x₁

postulate Nat:not~usucc~ule~uself:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Not (LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ x₁) x₁)} x₀ → Not (LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ x₀) x₀)

postulate Nat:not~usucc~ule~uself : (n₀ : Nat) → Not (LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₀) n₀)

postulate Nat:lt~uirrefl : (n₀ : Nat) → Not (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ n₀)

postulate Nat:lt~usucc~uof~ule : {n₀ : Nat} → {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → LT:lt {Nat} ⦃ instLTNat ⦄ n₀ (Nat:succ m₁)

postulate Nat:le~urefl : (n₀ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ n₀ n₀

postulate ~uprivate:Init:Prelude:~n0:Nat:pred~ule:match~u1~u1 : (motive₀ : Nat → Set) → (x₁ : Nat) → (Unit → motive₀ Nat:zero) → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ x₁

postulate Nat:pred~ule : (n₀ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ (Nat:pred n₀) n₀

postulate Nat:mul:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → ((x₃ : Nat) → motive₀ x₃ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → ((a₃ : Nat) → (b₄ : Nat) → motive₀ a₃ (Nat:succ b₄)) → motive₀ x₁ x₂

postulate Nat:sub:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Nat → Nat} x₀ → Nat → Nat

postulate Nat:sub : Nat → Nat → Nat

record Sub (α₀ : Set) : Set where
  constructor Sub:mk
  field
    sub₁ : α₀ → α₀ → α₀

postulate Sub:rec : {α₀ : Set} → {motive₁ : Sub α₀ → Set} → ((sub₂ : α₀ → α₀ → α₀) → motive₁ (Sub:mk {α₀} sub₂)) → (t₂ : Sub α₀) → motive₁ t₂

Sub:sub : {α₀ : Set} → ⦃ _ : Sub α₀ ⦄ → α₀ → α₀ → α₀
Sub:sub {α₀} ⦃ self₁ ⦄ = Sub.sub₁ {α₀} self₁

postulate instHSub : {α₀ : Set} → ⦃ _ : Sub α₀ ⦄ → HSub α₀ α₀ α₀

postulate instSubNat : Sub Nat

postulate Nat:sub~ule : (n₀ : Nat) → (m₁ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ n₀ m₁) n₀

postulate Nat:succ~usub~usucc~ueq~usub : (n₀ : Nat) → (m₁ : Nat) → Eq {Nat} (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ (Nat:succ n₀) (Nat:succ m₁)) (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ n₀ m₁)

~uprivate:Init:Prelude:~n0:Nat:sub~ult:match~u1~u1:~ushare:~n1 : Set
~uprivate:Init:Prelude:~n0:Nat:sub~ult:match~u1~u1:~ushare:~n1 = (x₀ : Nat) → (x₁ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₀ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₁ → Set

postulate ~uprivate:Init:Prelude:~n0:Nat:sub~ult:match~u1~u1 : (motive₀ : ~uprivate:Init:Prelude:~n0:Nat:sub~ult:match~u1~u1:~ushare:~n1) → (x₁ : Nat) → (x₂ : Nat) → (x₃ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₁) → (x₄ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₂) → ((x₅ : Nat) → (h1₆ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → (x₇ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₅) → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₅ h1₆ x₇) → ((n₅ : Nat) → (x₆ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₅)) → (h2₇ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → motive₀ (Nat:succ n₅) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₆ h2₇) → ((n₅ : Nat) → (m₆ : Nat) → (x₇ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₅)) → (x₈ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ m₆)) → motive₀ (Nat:succ n₅) (Nat:succ m₆) x₇ x₈) → motive₀ x₁ x₂ x₃ x₄

postulate Nat:sub~ult : {n₀ : Nat} → {m₁ : Nat} → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) n₀ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) m₁ → LT:lt {Nat} ⦃ instLTNat ⦄ (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ n₀ m₁) n₀

postulate ~uprivate:Init:Prelude:~n0:Nat:div~urec~ulemma:match~u1~u1 : {x₀ : Nat} → {y₁ : Nat} → (motive₂ : And (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) (LE:le {Nat} ⦃ instLENat ⦄ y₁ x₀) → Set) → (x₃ : And (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) (LE:le {Nat} ⦃ instLENat ⦄ y₁ x₀)) → ((ypos₄ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) → (ylex₅ : LE:le {Nat} ⦃ instLENat ⦄ y₁ x₀) → motive₂ (And:intro {LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁} {LE:le {Nat} ⦃ instLENat ⦄ y₁ x₀} ypos₄ ylex₅)) → motive₂ x₃

postulate Nat:div~urec~ulemma : {x₀ : Nat} → {y₁ : Nat} → And (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) (LE:le {Nat} ⦃ instLENat ⦄ y₁ x₀) → LT:lt {Nat} ⦃ instLTNat ⦄ (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ x₀ y₁) x₀

postulate Nat:le~uof~ult~usucc : {m₀ : Nat} → {n₁ : Nat} → LT:lt {Nat} ⦃ instLTNat ⦄ m₀ (Nat:succ n₁) → LE:le {Nat} ⦃ instLENat ⦄ m₀ n₁

postulate Nat:div~urec~ufuel~ulemma : {x₀ : Nat} → {y₁ : Nat} → {fuel₂ : Nat} → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁ → LE:le {Nat} ⦃ instLENat ⦄ y₁ x₀ → LT:lt {Nat} ⦃ instLTNat ⦄ x₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ fuel₂ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) → LT:lt {Nat} ⦃ instLTNat ⦄ (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ x₀ y₁) fuel₂

data Or (a₀ : Set) (b₁ : Set) : Set where
  Or:inl : a₀ → Or a₀ b₁
  Or:inr : b₁ → Or a₀ b₁

postulate Or:rec : {a₀ : Set} → {b₁ : Set} → {motive₂ : Or a₀ b₁ → Set} → ((h₃ : a₀) → motive₂ (Or:inl {a₀} {b₁} h₃)) → ((h₃ : b₁) → motive₂ (Or:inr {a₀} {b₁} h₃)) → (t₃ : Or a₀ b₁) → motive₂ t₃

postulate Or:casesOn : {a₀ : Set} → {b₁ : Set} → {motive₂ : Or a₀ b₁ → Set} → (t₃ : Or a₀ b₁) → ((h₄ : a₀) → motive₂ (Or:inl {a₀} {b₁} h₄)) → ((h₄ : b₁) → motive₂ (Or:inr {a₀} {b₁} h₄)) → motive₂ t₃

postulate ~uprivate:Init:Prelude:~n0:Nat:eq~uor~ult~uof~ule:match~u1~u1 : (n₀ : Nat) → (m₁ : Nat) → (motive₂ : Or (Eq {Nat} n₀ m₁) (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁) → Set) → (x₃ : Or (Eq {Nat} n₀ m₁) (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁)) → ((h₄ : Eq {Nat} n₀ m₁) → motive₂ (Or:inl {Eq {Nat} n₀ m₁} {LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁} h₄)) → ((h₄ : LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁) → motive₂ (Or:inr {Eq {Nat} n₀ m₁} {LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁} h₄)) → motive₂ x₃

postulate ~uprivate:Init:Prelude:~n0:Nat:eq~uor~ult~uof~ule:match~u1~u3 : (motive₀ : (x₀ : Nat) → (x₁ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ x₀ x₁ → Set) → (x₁ : Nat) → (x₂ : Nat) → (x₃ : LE:le {Nat} ⦃ instLENat ⦄ x₁ x₂) → ((x₄ : LE:le {Nat} ⦃ instLENat ⦄ Nat:zero Nat:zero) → motive₀ Nat:zero Nat:zero x₄) → ((n₄ : Nat) → (x₅ : LE:le {Nat} ⦃ instLENat ⦄ Nat:zero (Nat:succ n₄)) → motive₀ Nat:zero (Nat:succ n₄) x₅) → ((n₄ : Nat) → (h₅ : LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₄) Nat:zero) → motive₀ (Nat:succ n₄) Nat:zero h₅) → ((n₄ : Nat) → (m₅ : Nat) → (h₆ : LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₄) (Nat:succ m₅)) → motive₀ (Nat:succ n₄) (Nat:succ m₅) h₆) → motive₀ x₁ x₂ x₃

Nat:eq~uor~ult~uof~ule:~uf:~ushare:~n1 : Nat → Set
Nat:eq~uor~ult~uof~ule:~uf:~ushare:~n1 = Nat:below {λ (x₀ : Nat) → (x₁ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ x₀ x₁ → Or (Eq {Nat} x₀ x₁) (LT:lt {Nat} ⦃ instLTNat ⦄ x₀ x₁)}

postulate Nat:eq~uor~ult~uof~ule:~uf : (x₀ : Nat) → Nat:eq~uor~ult~uof~ule:~uf:~ushare:~n1 x₀ → (x₁ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ x₀ x₁ → Or (Eq {Nat} x₀ x₁) (LT:lt {Nat} ⦃ instLTNat ⦄ x₀ x₁)

postulate Nat:eq~uor~ult~uof~ule : {n₀ : Nat} → {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → Or (Eq {Nat} n₀ m₁) (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁)

postulate namedPattern : {α₀ : Set} → (x₁ : α₀) → (a₂ : α₀) → Eq {α₀} x₁ a₂ → α₀

postulate Nat:mod:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → ((x₃ : Nat) → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₃) → ((n₃ : Nat) → (n₄ : Nat) → (h₅ : Eq {Nat} n₃ (Nat:succ n₄)) → (m₆ : Nat) → motive₀ (namedPattern {Nat} n₃ (Nat:succ n₄) h₅) m₆) → motive₀ x₁ x₂

postulate Nat:lt~uadd~uone : (n₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ n₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))

postulate Nat:lt~usucc~uself : (n₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ n₀ (Nat:succ n₀)

postulate Nat:modCore:go:~uf : (y₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀ → (fuel₁ : Nat) → Nat:below {λ (fuel₂ : Nat) → (x₃ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₃ fuel₂ → Nat} fuel₁ → (x₂ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₂ fuel₁ → Nat

postulate Nat:modCore:go : (y₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀ → (fuel₁ : Nat) → (x₂ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₂ fuel₁ → Nat

postulate Nat:modCore : Nat → Nat → Nat

postulate ite : {α₀ : Set} → (c₁ : Set) → ⦃ _ : Decidable c₁ ⦄ → α₀ → α₀ → α₀

postulate Nat:mod : Nat → Nat → Nat

postulate Nat:instMod : Mod Nat

record PSigma {α₀ : Set} (β₁ : α₀ → Set) : Set where
  constructor PSigma:mk
  field
    fst₂ : α₀
    snd₃ : β₁ fst₂

postulate PSigma:rec : {α₀ : Set} → {β₁ : α₀ → Set} → {motive₂ : PSigma {α₀} β₁ → Set} → ((fst₃ : α₀) → (snd₄ : β₁ fst₃) → motive₂ (PSigma:mk {α₀} {β₁} fst₃ snd₄)) → (t₃ : PSigma {α₀} β₁) → motive₂ t₃

postulate PSigma:casesOn : {α₀ : Set} → {β₁ : α₀ → Set} → {motive₂ : PSigma {α₀} β₁ → Set} → (t₃ : PSigma {α₀} β₁) → ((fst₄ : α₀) → (snd₅ : β₁ fst₄) → motive₂ (PSigma:mk {α₀} {β₁} fst₄ snd₅)) → motive₂ t₃

postulate WellFounded:Nat:eager : Nat → Nat

postulate ite~uself : {α₀ : Set} → {c₁ : Set} → {d₂ : Decidable c₁} → (a₃ : α₀) → Eq {α₀} (ite {α₀} c₁ ⦃ d₂ ⦄ a₃ a₃) a₃

postulate WellFounded:Nat:eager~ueq : (n₀ : Nat) → Eq {Nat} (WellFounded:Nat:eager n₀) n₀

postulate WellFounded:Nat:fix:~uproof~u2 : {α₀ : Set} → (h₁ : α₀ → Nat) → (x₂ : α₀) → LT:lt {Nat} ⦃ instLTNat ⦄ (h₁ x₂) (WellFounded:Nat:eager (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (h₁ x₂) (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)))

postulate Nat:le~uof~ult~uadd~uone : {n₀ : Nat} → {m₁ : Nat} → LT:lt {Nat} ⦃ instLTNat ⦄ n₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ m₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁

postulate WellFounded:Nat:fix:~uproof~u1 : {α₀ : Set} → (h₁ : α₀ → Nat) → (x₂ : Nat) → (x₃ : α₀) → LT:lt {Nat} ⦃ instLTNat ⦄ (h₁ x₃) (Nat:succ x₂) → (y₄ : α₀) → InvImage {α₀} {Nat} (λ (x1₅ : Nat) → λ (x2₆ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x1₅ x2₆) h₁ y₄ x₃ → LT:lt {Nat} ⦃ instLTNat ⦄ (h₁ y₄) x₂

postulate WellFounded:Nat:fix:go:~uproof~u1 : {α₀ : Set} → (h₁ : α₀ → Nat) → (x₂ : α₀) → LT:lt {Nat} ⦃ instLTNat ⦄ (h₁ x₂) Nat:zero → False

postulate WellFounded:Nat:fix:go : {α₀ : Set} → {motive₁ : α₀ → Set} → (h₂ : α₀ → Nat) → ((x₃ : α₀) → ((y₄ : α₀) → InvImage {α₀} {Nat} (λ (x1₅ : Nat) → λ (x2₆ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x1₅ x2₆) h₂ y₄ x₃ → motive₁ y₄) → motive₁ x₃) → (fuel₃ : Nat) → (x₄ : α₀) → LT:lt {Nat} ⦃ instLTNat ⦄ (h₂ x₄) fuel₃ → motive₁ x₄

postulate WellFounded:Nat:fix : {α₀ : Set} → {motive₁ : α₀ → Set} → (h₂ : α₀ → Nat) → ((x₃ : α₀) → ((y₄ : α₀) → InvImage {α₀} {Nat} (λ (x1₅ : Nat) → λ (x2₆ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x1₅ x2₆) h₂ y₄ x₃ → motive₁ y₄) → motive₁ x₃) → (x₃ : α₀) → motive₁ x₃

postulate Nat:le~usucc~uof~ule : {n₀ : Nat} → {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → LE:le {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₁)

postulate ~uprivate:Init:Prelude:~n0:Nat:lt~uor~uge:match~u1~u1 : (n₀ : Nat) → (m₁ : Nat) → (motive₂ : Or (Eq {Nat} m₁ n₀) (LT:lt {Nat} ⦃ instLTNat ⦄ m₁ n₀) → Set) → (x₃ : Or (Eq {Nat} m₁ n₀) (LT:lt {Nat} ⦃ instLTNat ⦄ m₁ n₀)) → ((h1₄ : Eq {Nat} m₁ n₀) → motive₂ (Or:inl {Eq {Nat} m₁ n₀} {LT:lt {Nat} ⦃ instLTNat ⦄ m₁ n₀} h1₄)) → ((h1₄ : LT:lt {Nat} ⦃ instLTNat ⦄ m₁ n₀) → motive₂ (Or:inr {Eq {Nat} m₁ n₀} {LT:lt {Nat} ⦃ instLTNat ⦄ m₁ n₀} h1₄)) → motive₂ x₃

postulate ~uprivate:Init:Prelude:~n0:Nat:lt~uor~uge:match~u1~u3 : (n₀ : Nat) → (m₁ : Nat) → (motive₂ : Or (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁) (GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₁) → Set) → (x₃ : Or (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁) (GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₁)) → ((h₄ : LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁) → motive₂ (Or:inl {LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁} {GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₁} h₄)) → ((h₄ : GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₁) → motive₂ (Or:inr {LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁} {GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₁} h₄)) → motive₂ x₃

postulate ~uprivate:Init:Prelude:~n0:Nat:lt~uor~uge:match~u1~u5 : (motive₀ : Nat → Set) → (m₁ : Nat) → (Unit → motive₀ Nat:zero) → ((m₂ : Nat) → motive₀ (Nat:succ m₂)) → motive₀ m₁

postulate Nat:lt~uor~uge:~uf : (n₀ : Nat) → (m₁ : Nat) → Nat:below {λ (m₂ : Nat) → Or (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₂) (GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₂)} m₁ → Or (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁) (GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₁)

postulate Nat:lt~uor~uge : (n₀ : Nat) → (m₁ : Nat) → Or (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁) (GE:ge {Nat} ⦃ instLENat ⦄ n₀ m₁)

postulate ~uprivate:Init:Prelude:~n0:Or:elim:match~u1~u1 : {a₀ : Set} → {b₁ : Set} → (motive₂ : Or a₀ b₁ → Set) → (h₃ : Or a₀ b₁) → ((h₄ : a₀) → motive₂ (Or:inl {a₀} {b₁} h₄)) → ((h₄ : b₁) → motive₂ (Or:inr {a₀} {b₁} h₄)) → motive₂ h₃

postulate Or:elim : {a₀ : Set} → {b₁ : Set} → {c₂ : Set} → Or a₀ b₁ → (a₀ → c₂) → (b₁ → c₂) → c₂

postulate id : {α₀ : Set} → α₀ → α₀

postulate Or:resolve~uright : {a₀ : Set} → {b₁ : Set} → Or a₀ b₁ → Not b₁ → a₀

postulate Nat:lt~uof~unot~ule : {a₀ : Nat} → {b₁ : Nat} → Not (LE:le {Nat} ⦃ instLENat ⦄ a₀ b₁) → LT:lt {Nat} ⦃ instLTNat ⦄ b₁ a₀

postulate Nat:not~ult~uzero : (n₀ : Nat) → Not (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄))

postulate ~uprivate:Init:Prelude:~n0:Nat:modCoreGo~ult:match~u1~u1 : {y₀ : Nat} → (x₁ : Nat) → (motive₂ : Decidable (LE:le {Nat} ⦃ instLENat ⦄ y₀ x₁) → Set) → (x₃ : Decidable (LE:le {Nat} ⦃ instLENat ⦄ y₀ x₁)) → ((h₄ : LE:le {Nat} ⦃ instLENat ⦄ y₀ x₁) → motive₂ (Decidable:isTrue {LE:le {Nat} ⦃ instLENat ⦄ y₀ x₁} h₄)) → ((h₄ : Not (LE:le {Nat} ⦃ instLENat ⦄ y₀ x₁)) → motive₂ (Decidable:isFalse {LE:le {Nat} ⦃ instLENat ⦄ y₀ x₁} h₄)) → motive₂ x₃

postulate Nat:modCoreGo~ult : {fuel₀ : Nat} → {y₁ : Nat} → (hy₂ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) → (x₃ : Nat) → (hfuel₄ : LT:lt {Nat} ⦃ instLTNat ⦄ x₃ fuel₀) → LT:lt {Nat} ⦃ instLTNat ⦄ (Nat:modCore:go y₁ hy₂ fuel₀ x₃ hfuel₄) y₁

postulate ~uprivate:Init:Prelude:~n0:Nat:modCore~ult:match~u1~u1 : {y₀ : Nat} → (motive₁ : Decidable (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀) → Set) → (x₂ : Decidable (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀)) → ((h₃ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀) → motive₁ (Decidable:isTrue {LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀} h₃)) → ((h₃ : Not (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀)) → motive₁ (Decidable:isFalse {LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀} h₃)) → motive₁ x₂

postulate Nat:modCore~ult : {x₀ : Nat} → {y₁ : Nat} → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁ → LT:lt {Nat} ⦃ instLTNat ⦄ (Nat:modCore x₀ y₁) y₁

postulate Nat:zero~ult~usucc : (n₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₀)

postulate ~uprivate:Init:Prelude:~n0:Nat:mod~ult:match~u1~u1 : (n₀ : Nat) → (m₁ : Nat) → (motive₂ : Decidable (LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ n₀)) → Set) → (x₃ : Decidable (LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ n₀))) → ((h₄ : LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ n₀)) → motive₂ (Decidable:isTrue {LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ n₀)} h₄)) → ((h₄ : Not (LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ n₀))) → motive₂ (Decidable:isFalse {LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ n₀)} h₄)) → motive₂ x₃

postulate ~uprivate:Init:Prelude:~n0:Nat:mod~ult:match~u1~u3 : (motive₀ : Nat → (x₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₀ → Set) → (x₁ : Nat) → (x₂ : Nat) → (x₃ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₂) → ((n₄ : Nat) → (x₅ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₄)) → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₄) x₅) → ((n₄ : Nat) → (m₅ : Nat) → (hm₆ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) m₅) → motive₀ (Nat:succ n₄) m₅ hm₆) → motive₀ x₁ x₂ x₃

postulate instHMod : {α₀ : Set} → ⦃ _ : Mod α₀ ⦄ → HMod α₀ α₀ α₀

postulate Nat:mod~ult : (x₀ : Nat) → {y₁ : Nat} → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁ → LT:lt {Nat} ⦃ instLTNat ⦄ (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ x₀ y₁) y₁

postulate Ne : {α₀ : Set} → α₀ → α₀ → Set

postulate ~uprivate:Init:Data:Nat:Basic:~n0:Nat:zero~ult~uof~une~uzero:match~u1~u1 : (motive₀ : (a₀ : Nat) → Ne {Nat} a₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) → Set) → (a₁ : Nat) → (h₂ : Ne {Nat} a₁ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → ((h₃ : Ne {Nat} (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) h₃) → ((a₃ : Nat) → (h₄ : Ne {Nat} (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ a₃ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → motive₀ (Nat:succ a₃) h₄) → motive₀ a₁ h₂

postulate Nat:zero~ult~uof~une~uzero : {a₀ : Nat} → Ne {Nat} a₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) a₀

~uprivate:Init:Data:Nat:Gcd:~n0:Nat:gcd:~uunary:~uproof~u1:~ushare:~n1 : PSigma {Nat} (λ (m₀ : Nat) → Nat) → PSigma {Nat} (λ (m₀ : Nat) → Nat) → Set
~uprivate:Init:Data:Nat:Gcd:~n0:Nat:gcd:~uunary:~uproof~u1:~ushare:~n1 = InvImage {PSigma {Nat} (λ (m₀ : Nat) → Nat)} {Nat} (λ (x1₀ : Nat) → λ (x2₁ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x1₀ x2₁) (λ (x₀ : PSigma {Nat} (λ (m₀ : Nat) → Nat)) → PSigma:casesOn {Nat} {λ (m₁ : Nat) → Nat} {λ (x₁ : PSigma {Nat} (λ (m₁ : Nat) → Nat)) → Nat} x₀ (λ (m₁ : Nat) → λ (n₂ : Nat) → m₁))

postulate ~uprivate:Init:Data:Nat:Gcd:~n0:Nat:gcd:~uunary:~uproof~u1 : (m₀ : Nat) → (n₁ : Nat) → Not (Eq {Nat} m₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → ~uprivate:Init:Data:Nat:Gcd:~n0:Nat:gcd:~uunary:~uproof~u1:~ushare:~n1 (PSigma:mk {Nat} {λ (m₂ : Nat) → Nat} (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ n₁ m₀) m₀) (PSigma:mk {Nat} {λ (m₂ : Nat) → Nat} m₀ n₁)

postulate instDecidableEqNat : DecidableEq Nat

postulate Nat:gcd:~uunary : PSigma {Nat} (λ (m₀ : Nat) → Nat) → Nat

postulate Nat:gcd : Nat → Nat → Nat

postulate WellFounded:Nat:fix:go:congr~usimp : {α₀ : Set} → {motive₁ : α₀ → Set} → (h₂ : α₀ → Nat) → (F₃ : (x₃ : α₀) → ((y₄ : α₀) → InvImage {α₀} {Nat} (λ (x1₅ : Nat) → λ (x2₆ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x1₅ x2₆) h₂ y₄ x₃ → motive₁ y₄) → motive₁ x₃) → (F₄ : (x₄ : α₀) → ((y₅ : α₀) → InvImage {α₀} {Nat} (λ (x1₆ : Nat) → λ (x2₇ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x1₆ x2₇) h₂ y₅ x₄ → motive₁ y₅) → motive₁ x₄) → Eq {(x₅ : α₀) → ((y₆ : α₀) → InvImage {α₀} {Nat} (λ (x1₇ : Nat) → λ (x2₈ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x1₇ x2₈) h₂ y₆ x₅ → motive₁ y₆) → motive₁ x₅} F₃ F₄ → (fuel₅ : Nat) → (fuel₆ : Nat) → (efuel₇ : Eq {Nat} fuel₅ fuel₆) → (x₈ : α₀) → (a₉ : LT:lt {Nat} ⦃ instLTNat ⦄ (h₂ x₈) fuel₅) → Eq {motive₁ x₈} (WellFounded:Nat:fix:go {α₀} {motive₁} h₂ F₃ fuel₅ x₈ a₉) (WellFounded:Nat:fix:go {α₀} {motive₁} h₂ F₄ fuel₆ x₈ (Eq:ndrec {Nat} {fuel₅} {λ (fuel₁₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (h₂ x₈) fuel₁₀} a₉ {fuel₆} efuel₇))

postulate Nat:recAux : {motive₀ : Nat → Set} → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) → ((n₁ : Nat) → motive₀ n₁ → motive₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))) → (t₁ : Nat) → motive₀ t₁

postulate Quot : {α₀ : Set} → (α₀ → α₀ → Set) → Set

postulate Quot:mk : {α₀ : Set} → (r₁ : α₀ → α₀ → Set) → α₀ → Quot {α₀} r₁

postulate Quot:ind : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {β₂ : Quot {α₀} r₁ → Set} → ((a₃ : α₀) → β₂ (Quot:mk {α₀} r₁ a₃)) → (q₃ : Quot {α₀} r₁) → β₂ q₃

postulate Quot:lift : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {β₂ : Set} → (f₃ : α₀ → β₂) → ((a₄ : α₀) → (b₅ : α₀) → r₁ a₄ b₅ → Eq {β₂} (f₃ a₄) (f₃ b₅)) → Quot {α₀} r₁ → β₂

postulate Quot:liftOn : {α₀ : Set} → {β₁ : Set} → {r₂ : α₀ → α₀ → Set} → Quot {α₀} r₂ → (f₃ : α₀ → β₁) → ((a₄ : α₀) → (b₅ : α₀) → r₂ a₄ b₅ → Eq {β₁} (f₃ a₄) (f₃ b₅)) → β₁

postulate Quot:sound : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {a₂ : α₀} → {b₃ : α₀} → r₁ a₂ b₃ → Eq {Quot {α₀} r₁} (Quot:mk {α₀} r₁ a₂) (Quot:mk {α₀} r₁ b₃)

postulate funext : {α₀ : Set} → {β₁ : α₀ → Set} → {f₂ : (x₂ : α₀) → β₁ x₂} → {g₃ : (x₃ : α₀) → β₁ x₃} → ((x₄ : α₀) → Eq {β₁ x₄} (f₂ x₄) (g₃ x₄)) → Eq {(x₄ : α₀) → β₁ x₄} f₂ g₃

postulate WellFounded:Nat:fix:go~ucongr : {α₀ : Set} → {motive₁ : α₀ → Set} → (h₂ : α₀ → Nat) → (F₃ : (x₃ : α₀) → ((y₄ : α₀) → InvImage {α₀} {Nat} (λ (x1₅ : Nat) → λ (x2₆ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x1₅ x2₆) h₂ y₄ x₃ → motive₁ y₄) → motive₁ x₃) → (x₄ : α₀) → (fuel₅ : Nat) → (fuel₆ : Nat) → (h₇ : LT:lt {Nat} ⦃ instLTNat ⦄ (h₂ x₄) fuel₅) → (h₈ : LT:lt {Nat} ⦃ instLTNat ⦄ (h₂ x₄) fuel₆) → Eq {motive₁ x₄} (WellFounded:Nat:fix:go {α₀} {motive₁} h₂ F₃ fuel₅ x₄ h₇) (WellFounded:Nat:fix:go {α₀} {motive₁} h₂ F₃ fuel₆ x₄ h₈)

postulate congr : {α₀ : Set} → {β₁ : Set} → {f₂ : α₀ → β₁} → {f₃ : α₀ → β₁} → {a₄ : α₀} → {a₅ : α₀} → Eq {α₀ → β₁} f₂ f₃ → Eq {α₀} a₄ a₅ → Eq {β₁} (f₂ a₄) (f₃ a₅)

postulate WellFounded:Nat:fix~ueq : {α₀ : Set} → {motive₁ : α₀ → Set} → (h₂ : α₀ → Nat) → (F₃ : (x₃ : α₀) → ((y₄ : α₀) → InvImage {α₀} {Nat} (λ (x1₅ : Nat) → λ (x2₆ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x1₅ x2₆) h₂ y₄ x₃ → motive₁ y₄) → motive₁ x₃) → (x₄ : α₀) → Eq {motive₁ x₄} (WellFounded:Nat:fix {α₀} {motive₁} h₂ F₃ x₄) (F₃ x₄ (λ (y₅ : α₀) → λ (x₆ : InvImage {α₀} {Nat} (λ (x1₆ : Nat) → λ (x2₇ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x1₆ x2₇) h₂ y₅ x₄) → WellFounded:Nat:fix {α₀} {motive₁} h₂ F₃ y₅))

postulate ~uprivate:Init:Data:Nat:Gcd:~n0:PSigma:casesOn:~uarg~upusher : {α₀ : Set} → {β₁ : α₀ → Set} → {motive₂ : PSigma {α₀} β₁ → Set} → (α₃ : Set) → (β₄ : α₃ → Set) → (f₅ : (x₅ : α₃) → β₄ x₅) → (rel₆ : PSigma {α₀} β₁ → α₃ → Set) → (t₇ : PSigma {α₀} β₁) → (mk₈ : (fst₈ : α₀) → (snd₉ : β₁ fst₈) → ((y₁₀ : α₃) → rel₆ (PSigma:mk {α₀} {β₁} fst₈ snd₉) y₁₀ → β₄ y₁₀) → motive₂ (PSigma:mk {α₀} {β₁} fst₈ snd₉)) → Eq {motive₂ t₇} (PSigma:casesOn {α₀} {β₁} {λ (t₉ : PSigma {α₀} β₁) → ((y₁₀ : α₃) → rel₆ t₉ y₁₀ → β₄ y₁₀) → motive₂ t₉} t₇ mk₈ (λ (y₉ : α₃) → λ (h₁₀ : rel₆ t₇ y₉) → f₅ y₉)) (PSigma:casesOn {α₀} {β₁} {motive₂} t₇ (λ (fst₉ : α₀) → λ (snd₁₀ : β₁ fst₉) → mk₈ fst₉ snd₁₀ (λ (y₁₁ : α₃) → λ (h₁₂ : rel₆ (PSigma:mk {α₀} {β₁} fst₉ snd₁₀) y₁₁) → f₅ y₁₁)))

postulate congrFun~x27~ : {α₀ : Set} → {β₁ : Set} → {f₂ : α₀ → β₁} → {g₃ : α₀ → β₁} → Eq {α₀ → β₁} f₂ g₃ → (a₄ : α₀) → Eq {β₁} (f₂ a₄) (g₃ a₄)

postulate ~uprivate:Init:Data:Nat:Gcd:~n0:Nat:gcd:~uunary:eq~udef : (x₀ : PSigma {Nat} (λ (m₀ : Nat) → Nat)) → Eq {Nat} (Nat:gcd:~uunary x₀) (PSigma:casesOn {Nat} {λ (m₁ : Nat) → Nat} {λ (x₁ : PSigma {Nat} (λ (m₁ : Nat) → Nat)) → Nat} x₀ (λ (m₁ : Nat) → λ (n₂ : Nat) → ite {Nat} (Eq {Nat} m₁ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) ⦃ instDecidableEqNat m₁ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) ⦄ n₂ (Nat:gcd:~uunary (PSigma:mk {Nat} {λ (m₃ : Nat) → Nat} (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ n₂ m₁) m₁))))

postulate ~uprivate:Init:Data:Nat:Gcd:~n0:Nat:gcd:eq~udef : (m₀ : Nat) → (n₁ : Nat) → Eq {Nat} (Nat:gcd m₀ n₁) (ite {Nat} (Eq {Nat} m₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) ⦃ instDecidableEqNat m₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) ⦄ n₁ (Nat:gcd (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ n₁ m₀) m₀))

postulate ~uprivate:Init:Data:Nat:Gcd:~n0:Nat:gcd:eq~u1 : (m₀ : Nat) → (n₁ : Nat) → Eq {Nat} (Nat:gcd m₀ n₁) (ite {Nat} (Eq {Nat} m₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) ⦃ instDecidableEqNat m₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) ⦄ n₁ (Nat:gcd (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ n₁ m₀) m₀))

Nat:gcd~usucc : (x₀ : Nat) → (y₁ : Nat) → Eq {Nat} (Nat:gcd (Nat:succ x₀) y₁) (Nat:gcd (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ y₁ (Nat:succ x₀)) (Nat:succ x₀))
Nat:gcd~usucc x₀ y₁ = Eq:mpr {Eq {Nat} (Nat:gcd (Nat:succ x₀) y₁) (Nat:gcd (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ y₁ (Nat:succ x₀)) (Nat:succ x₀))} {Eq {Nat} (ite {Nat} (Eq {Nat} (Nat:succ x₀) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) ⦃ instDecidableEqNat (Nat:succ x₀) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) ⦄ y₁ (Nat:gcd (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ y₁ (Nat:succ x₀)) (Nat:succ x₀))) (Nat:gcd (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ y₁ (Nat:succ x₀)) (Nat:succ x₀))} (id {Eq {Set} (Eq {Nat} (Nat:gcd (Nat:succ x₀) y₁) (Nat:gcd (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ y₁ (Nat:succ x₀)) (Nat:succ x₀))) (Eq {Nat} (ite {Nat} (Eq {Nat} (Nat:succ x₀) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) ⦃ instDecidableEqNat (Nat:succ x₀) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) ⦄ y₁ (Nat:gcd (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ y₁ (Nat:succ x₀)) (Nat:succ x₀))) (Nat:gcd (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ y₁ (Nat:succ x₀)) (Nat:succ x₀)))} (congrArg {Nat} {Set} {Nat:gcd (Nat:succ x₀) y₁} {ite {Nat} (Eq {Nat} (Nat:succ x₀) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) ⦃ instDecidableEqNat (Nat:succ x₀) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) ⦄ y₁ (Nat:gcd (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ y₁ (Nat:succ x₀)) (Nat:succ x₀))} (λ (a₂ : Nat) → Eq {Nat} a₂ (Nat:gcd (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ y₁ (Nat:succ x₀)) (Nat:succ x₀))) (~uprivate:Init:Data:Nat:Gcd:~n0:Nat:gcd:eq~u1 (Nat:succ x₀) y₁))) (Eq:refl {Nat} (ite {Nat} (Eq {Nat} (Nat:succ x₀) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) ⦃ instDecidableEqNat (Nat:succ x₀) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) ⦄ y₁ (Nat:gcd (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ y₁ (Nat:succ x₀)) (Nat:succ x₀))))
