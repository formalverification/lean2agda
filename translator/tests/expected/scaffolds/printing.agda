-- File: translator/tests/expected/scaffolds/printing.agda
{-# OPTIONS --type-in-type #-}
-- lean2agda, profile U: the scaffold of the closure of PrintFixtures:Dependent:value PrintFixtures:Pair:first PrintFixtures:alignedDeep PrintFixtures:alignedTop PrintFixtures:doubling and 8 more
module U.TranslatorTests.Input.Printing where

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

data List (α₀ : Set) : Set where
  List:nil : List α₀
  List:cons : α₀ → List α₀ → List α₀

postulate List:rec : {α₀ : Set} → {motive₁ : List α₀ → Set} → motive₁ (List:nil {α₀}) → ((head₂ : α₀) → (tail₃ : List α₀) → motive₁ tail₃ → motive₁ (List:cons {α₀} head₂ tail₃)) → (t₂ : List α₀) → motive₁ t₂

record Array (α₀ : Set) : Set where
  constructor Array:mk
  field
    toList₁ : List α₀

postulate Array:rec : {α₀ : Set} → {motive₁ : Array α₀ → Set} → ((toList₂ : List α₀) → motive₁ (Array:mk {α₀} toList₂)) → (t₂ : Array α₀) → motive₁ t₂

data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

postulate Nat:rec : {motive₀ : Nat → Set} → motive₀ Nat:zero → ((n₁ : Nat) → motive₀ n₁ → motive₀ (Nat:succ n₁)) → (t₁ : Nat) → motive₀ t₁

postulate Array:emptyWithCapacity : {α₀ : Set} → Nat → Array α₀

record OfNat (α₀ : Set) (x₁ : Nat) : Set where
  constructor OfNat:mk
  field
    ofNat₂ : α₀

postulate OfNat:rec : {α₀ : Set} → {x₁ : Nat} → {motive₂ : OfNat α₀ x₁ → Set} → ((ofNat₃ : α₀) → motive₂ (OfNat:mk {α₀} {x₁} ofNat₃)) → (t₃ : OfNat α₀ x₁) → motive₂ t₃

OfNat:ofNat : {α₀ : Set} → (x₁ : Nat) → ⦃ _ : OfNat α₀ x₁ ⦄ → α₀
OfNat:ofNat {α₀} x₁ ⦃ self₂ ⦄ = OfNat.ofNat₂ {α₀} {x₁} self₂

postulate instOfNatNat : (n₀ : Nat) → OfNat Nat n₀

postulate Array:empty : {α₀ : Set} → Array α₀

Array:toList : {α₀ : Set} → Array α₀ → List α₀
Array:toList {α₀} self₁ = Array.toList₁ {α₀} self₁

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

postulate List:concat:match~u1 : {α₀ : Set} → (motive₁ : List α₀ → α₀ → Set) → (x₂ : List α₀) → (x₃ : α₀) → ((b₄ : α₀) → motive₁ (List:nil {α₀}) b₄) → ((a₄ : α₀) → (as₅ : List α₀) → (b₆ : α₀) → motive₁ (List:cons {α₀} a₄ as₅) b₆) → motive₁ x₂ x₃

postulate List:concat:~uf : {α₀ : Set} → (x₁ : List α₀) → List:below {α₀} {λ (x₂ : List α₀) → α₀ → List α₀} x₁ → α₀ → List α₀

postulate List:concat : {α₀ : Set} → List α₀ → α₀ → List α₀

postulate Array:push : {α₀ : Set} → Array α₀ → α₀ → Array α₀

record LT (α₀ : Set) : Set where
  constructor LT:mk
  field
    lt₁ : α₀ → α₀ → Set

postulate LT:rec : {α₀ : Set} → {motive₁ : LT α₀ → Set} → ((lt₂ : α₀ → α₀ → Set) → motive₁ (LT:mk {α₀} lt₂)) → (t₂ : LT α₀) → motive₁ t₂

LT:lt : {α₀ : Set} → ⦃ _ : LT α₀ ⦄ → α₀ → α₀ → Set
LT:lt {α₀} ⦃ self₁ ⦄ = LT.lt₁ {α₀} self₁

data Nat:le (n₀ : Nat) : Nat → Set where
  Nat:le:refl : Nat:le n₀ n₀
  Nat:le:step : {m₁ : Nat} → Nat:le n₀ m₁ → Nat:le n₀ (Nat:succ m₁)

postulate Nat:le:rec : {n₀ : Nat} → {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} → motive₁ n₀ (Nat:le:refl {n₀}) → ({m₂ : Nat} → (a₃ : Nat:le n₀ m₂) → motive₁ m₂ a₃ → motive₁ (Nat:succ m₂) (Nat:le:step {n₀} {m₂} a₃)) → {a₂ : Nat} → (t₃ : Nat:le n₀ a₂) → motive₁ a₂ t₃

postulate Nat:lt : Nat → Nat → Set

postulate instLTNat : LT Nat

record Fin (n₀ : Nat) : Set where
  constructor Fin:mk
  field
    val₁ : Nat
    isLt₂ : LT:lt {Nat} ⦃ instLTNat ⦄ val₁ n₀

postulate Fin:rec : {n₀ : Nat} → {motive₁ : Fin n₀ → Set} → ((val₂ : Nat) → (isLt₃ : LT:lt {Nat} ⦃ instLTNat ⦄ val₂ n₀) → motive₁ (Fin:mk {n₀} val₂ isLt₃)) → (t₂ : Fin n₀) → motive₁ t₂

outParam : Set → Set
outParam α₀ = α₀

record HPow (α₀ : Set) (β₁ : Set) (γ₂ : outParam Set) : Set where
  constructor HPow:mk
  field
    hPow₃ : α₀ → β₁ → γ₂

postulate HPow:rec : {α₀ : Set} → {β₁ : Set} → {γ₂ : Set} → {motive₃ : HPow α₀ β₁ γ₂ → Set} → ((hPow₄ : α₀ → β₁ → γ₂) → motive₃ (HPow:mk {α₀} {β₁} {γ₂} hPow₄)) → (t₄ : HPow α₀ β₁ γ₂) → motive₃ t₄

HPow:hPow : {α₀ : Set} → {β₁ : Set} → {γ₂ : outParam Set} → ⦃ _ : HPow α₀ β₁ γ₂ ⦄ → α₀ → β₁ → γ₂
HPow:hPow {α₀} {β₁} {γ₂} ⦃ self₃ ⦄ = HPow.hPow₃ {α₀} {β₁} {γ₂} self₃

record Pow (α₀ : Set) (β₁ : Set) : Set where
  constructor Pow:mk
  field
    pow₂ : α₀ → β₁ → α₀

postulate Pow:rec : {α₀ : Set} → {β₁ : Set} → {motive₂ : Pow α₀ β₁ → Set} → ((pow₃ : α₀ → β₁ → α₀) → motive₂ (Pow:mk {α₀} {β₁} pow₃)) → (t₃ : Pow α₀ β₁) → motive₂ t₃

Pow:pow : {α₀ : Set} → {β₁ : Set} → ⦃ _ : Pow α₀ β₁ ⦄ → α₀ → β₁ → α₀
Pow:pow {α₀} {β₁} ⦃ self₂ ⦄ = Pow.pow₂ {α₀} {β₁} self₂

postulate instHPow : {α₀ : Set} → {β₁ : Set} → ⦃ _ : Pow α₀ β₁ ⦄ → HPow α₀ β₁ α₀

postulate Nat:below : {_ : Nat → Set} → Nat → Set

postulate Nat:brecOn:go : {motive₀ : Nat → Set} → (t₁ : Nat) → ((t₂ : Nat) → Nat:below {motive₀} t₂ → motive₀ t₂) → PProd (motive₀ t₁) (Nat:below {motive₀} t₁)

postulate Nat:brecOn : {motive₀ : Nat → Set} → (t₁ : Nat) → ((t₂ : Nat) → Nat:below {motive₀} t₂ → motive₀ t₂) → motive₀ t₁

postulate Nat:casesOn : {motive₀ : Nat → Set} → (t₁ : Nat) → motive₀ Nat:zero → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ t₁

postulate Nat:add:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → ((a₃ : Nat) → motive₀ a₃ Nat:zero) → ((a₃ : Nat) → (b₄ : Nat) → motive₀ a₃ (Nat:succ b₄)) → motive₀ x₁ x₂

postulate Nat:add:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Nat → Nat} x₀ → Nat → Nat

postulate Nat:add : Nat → Nat → Nat

postulate Nat:mul:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → ((x₃ : Nat) → motive₀ x₃ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → ((a₃ : Nat) → (b₄ : Nat) → motive₀ a₃ (Nat:succ b₄)) → motive₀ x₁ x₂

postulate Nat:mul:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Nat → Nat} x₀ → Nat → Nat

postulate Nat:mul : Nat → Nat → Nat

postulate Unit : Set

postulate Unit:unit : Unit

postulate Nat:pow:match~u1 : (motive₀ : Nat → Set) → (x₁ : Nat) → (Unit → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ x₁

postulate Nat:pow:~uf : Nat → (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Nat} x₀ → Nat

postulate Nat:pow : Nat → Nat → Nat

record NatPow (α₀ : Set) : Set where
  constructor NatPow:mk
  field
    pow₁ : α₀ → Nat → α₀

postulate NatPow:rec : {α₀ : Set} → {motive₁ : NatPow α₀ → Set} → ((pow₂ : α₀ → Nat → α₀) → motive₁ (NatPow:mk {α₀} pow₂)) → (t₂ : NatPow α₀) → motive₁ t₂

postulate instNatPowNat : NatPow Nat

NatPow:pow : {α₀ : Set} → ⦃ _ : NatPow α₀ ⦄ → α₀ → Nat → α₀
NatPow:pow {α₀} ⦃ self₁ ⦄ = NatPow.pow₁ {α₀} self₁

postulate instPowNat : {α₀ : Set} → ⦃ _ : NatPow α₀ ⦄ → Pow α₀ Nat

record BitVec (w₀ : Nat) : Set where
  constructor BitVec:ofFin
  field
    toFin₁ : Fin (HPow:hPow {Nat} {Nat} {Nat} ⦃ instHPow {Nat} {Nat} ⦃ instPowNat {Nat} ⦃ instNatPowNat ⦄ ⦄ ⦄ (OfNat:ofNat {Nat} 2 ⦃ instOfNatNat 2 ⦄) w₀)

postulate BitVec:rec : {w₀ : Nat} → {motive₁ : BitVec w₀ → Set} → ((toFin₂ : Fin (HPow:hPow {Nat} {Nat} {Nat} ⦃ instHPow {Nat} {Nat} ⦃ instPowNat {Nat} ⦃ instNatPowNat ⦄ ⦄ ⦄ (OfNat:ofNat {Nat} 2 ⦃ instOfNatNat 2 ⦄) w₀)) → motive₁ (BitVec:ofFin {w₀} toFin₂)) → (t₂ : BitVec w₀) → motive₁ t₂

data False : Set where

postulate False:rec : (motive₀ : False → Set) → (t₁ : False) → motive₀ t₁

postulate False:elim : {C₀ : Set} → False → C₀

record HMul (α₀ : Set) (β₁ : Set) (γ₂ : outParam Set) : Set where
  constructor HMul:mk
  field
    hMul₃ : α₀ → β₁ → γ₂

postulate HMul:rec : {α₀ : Set} → {β₁ : Set} → {γ₂ : Set} → {motive₃ : HMul α₀ β₁ γ₂ → Set} → ((hMul₄ : α₀ → β₁ → γ₂) → motive₃ (HMul:mk {α₀} {β₁} {γ₂} hMul₄)) → (t₄ : HMul α₀ β₁ γ₂) → motive₃ t₄

HMul:hMul : {α₀ : Set} → {β₁ : Set} → {γ₂ : outParam Set} → ⦃ _ : HMul α₀ β₁ γ₂ ⦄ → α₀ → β₁ → γ₂
HMul:hMul {α₀} {β₁} {γ₂} ⦃ self₃ ⦄ = HMul.hMul₃ {α₀} {β₁} {γ₂} self₃

record HAdd (α₀ : Set) (β₁ : Set) (γ₂ : outParam Set) : Set where
  constructor HAdd:mk
  field
    hAdd₃ : α₀ → β₁ → γ₂

postulate HAdd:rec : {α₀ : Set} → {β₁ : Set} → {γ₂ : Set} → {motive₃ : HAdd α₀ β₁ γ₂ → Set} → ((hAdd₄ : α₀ → β₁ → γ₂) → motive₃ (HAdd:mk {α₀} {β₁} {γ₂} hAdd₄)) → (t₄ : HAdd α₀ β₁ γ₂) → motive₃ t₄

HAdd:hAdd : {α₀ : Set} → {β₁ : Set} → {γ₂ : outParam Set} → ⦃ _ : HAdd α₀ β₁ γ₂ ⦄ → α₀ → β₁ → γ₂
HAdd:hAdd {α₀} {β₁} {γ₂} ⦃ self₃ ⦄ = HAdd.hAdd₃ {α₀} {β₁} {γ₂} self₃

data Eq {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl : (a₁ : α₀) → Eq {α₀} a₁ a₁

postulate Eq:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → Eq {α₀} a₁ a₂ → Set} → motive₂ a₁ (Eq:refl {α₀} a₁) → {a₃ : α₀} → (t₄ : Eq {α₀} a₁ a₃) → motive₂ a₃ t₄

record LE (α₀ : Set) : Set where
  constructor LE:mk
  field
    le₁ : α₀ → α₀ → Set

postulate LE:rec : {α₀ : Set} → {motive₁ : LE α₀ → Set} → ((le₂ : α₀ → α₀ → Set) → motive₁ (LE:mk {α₀} le₂)) → (t₂ : LE α₀) → motive₁ t₂

LE:le : {α₀ : Set} → ⦃ _ : LE α₀ ⦄ → α₀ → α₀ → Set
LE:le {α₀} ⦃ self₁ ⦄ = LE.le₁ {α₀} self₁

postulate Nat:le:casesOn : {n₀ : Nat} → {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} → {a₂ : Nat} → (t₃ : Nat:le n₀ a₂) → motive₁ n₀ (Nat:le:refl {n₀}) → ({m₄ : Nat} → (a₅ : Nat:le n₀ m₄) → motive₁ (Nat:succ m₄) (Nat:le:step {n₀} {m₄} a₅)) → motive₁ a₂ t₃

postulate Eq:ndrec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : α₀ → Set} → motive₂ a₁ → {b₃ : α₀} → Eq {α₀} a₁ b₃ → motive₂ b₃

postulate Nat:noConfusionType : Set → Nat → Nat → Set

postulate Nat:noConfusion : {P₀ : Set} → {t₁ : Nat} → {t₂ : Nat} → Eq {Nat} t₁ t₂ → Nat:noConfusionType P₀ t₁ t₂

postulate instLENat : LE Nat

postulate rfl : {α₀ : Set} → {a₁ : α₀} → Eq {α₀} a₁ a₁

postulate Nat:not~usucc~ule~uzero : (n₀ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₀) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) → False

data Nat:le:below {n₀ : Nat} {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} : {a₂ : Nat} → Nat:le n₀ a₂ → Set where
  Nat:le:below:refl : Nat:le:below {n₀} {motive₁} {n₀} (Nat:le:refl {n₀})
  Nat:le:below:step : {m₂ : Nat} → (a₃ : Nat:le n₀ m₂) → Nat:le:below {n₀} {motive₁} {m₂} a₃ → motive₁ m₂ a₃ → Nat:le:below {n₀} {motive₁} {Nat:succ m₂} (Nat:le:step {n₀} {m₂} a₃)

postulate Nat:le:below:rec : {n₀ : Nat} → {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} → {motive₂ : {a₂ : Nat} → (t₃ : Nat:le n₀ a₂) → Nat:le:below {n₀} {motive₁} {a₂} t₃ → Set} → motive₂ {n₀} (Nat:le:refl {n₀}) (Nat:le:below:refl {n₀} {motive₁}) → ({m₃ : Nat} → (a₄ : Nat:le n₀ m₃) → (ih₅ : Nat:le:below {n₀} {motive₁} {m₃} a₄) → (aih₆ : motive₁ m₃ a₄) → motive₂ {m₃} a₄ ih₅ → motive₂ {Nat:succ m₃} (Nat:le:step {n₀} {m₃} a₄) (Nat:le:below:step {n₀} {motive₁} {m₃} a₄ ih₅ aih₆)) → {a₃ : Nat} → {t₄ : Nat:le n₀ a₃} → (t₅ : Nat:le:below {n₀} {motive₁} {a₃} t₄) → motive₂ {a₃} t₄ t₅

postulate Nat:le:brecOn : {n₀ : Nat} → {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} → {a₂ : Nat} → (t₃ : Nat:le n₀ a₂) → ((a₄ : Nat) → (t₅ : Nat:le n₀ a₄) → Nat:le:below {n₀} {motive₁} {a₄} t₅ → motive₁ a₄ t₅) → motive₁ a₂ t₃

postulate Eq:symm : {α₀ : Set} → {a₁ : α₀} → {b₂ : α₀} → Eq {α₀} a₁ b₂ → Eq {α₀} b₂ a₁

data HEq {α₀ : Set} : α₀ → {β₁ : Set} → β₁ → Set where
  HEq:refl : (a₁ : α₀) → HEq {α₀} a₁ {α₀} a₁

postulate HEq:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : {β₂ : Set} → (a₃ : β₂) → HEq {α₀} a₁ {β₂} a₃ → Set} → motive₂ {α₀} a₁ (HEq:refl {α₀} a₁) → {β₃ : Set} → {a₄ : β₃} → (t₅ : HEq {α₀} a₁ {β₃} a₄) → motive₂ {β₃} a₄ t₅

postulate Nat:le:below:casesOn : {n₀ : Nat} → {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} → {motive₂ : {a₂ : Nat} → (t₃ : Nat:le n₀ a₂) → Nat:le:below {n₀} {motive₁} {a₂} t₃ → Set} → {a₃ : Nat} → {t₄ : Nat:le n₀ a₃} → (t₅ : Nat:le:below {n₀} {motive₁} {a₃} t₄) → motive₂ {n₀} (Nat:le:refl {n₀}) (Nat:le:below:refl {n₀} {motive₁}) → ({m₆ : Nat} → (a₇ : Nat:le n₀ m₆) → (ih₈ : Nat:le:below {n₀} {motive₁} {m₆} a₇) → (aih₉ : motive₁ m₆ a₇) → motive₂ {Nat:succ m₆} (Nat:le:step {n₀} {m₆} a₇) (Nat:le:below:step {n₀} {motive₁} {m₆} a₇ ih₈ aih₉)) → motive₂ {a₃} t₄ t₅

postulate cast : {α₀ : Set} → {β₁ : Set} → Eq {Set} α₀ β₁ → α₀ → β₁

postulate eq~uof~uheq : {α₀ : Set} → {a₁ : α₀} → {a₂ : α₀} → HEq {α₀} a₁ {α₀} a₂ → Eq {α₀} a₁ a₂

postulate ~uprivate:Init:Prelude:~n0:Nat:succ~ule~usucc:match~u1~u7 : {n₀ : Nat} → (funType1₁ : {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → Set) → (motive₂ : (m₂ : Nat) → (x₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₂) → Nat:le:below {n₀} {λ (m₄ : Nat) → λ (x₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₄) → funType1₁ {m₄} x₅} {m₂} x₃ → Set) → (m₃ : Nat) → (x₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₃) → (below₅ : Nat:le:below {n₀} {λ (m₅ : Nat) → λ (x₆ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₅) → funType1₁ {m₅} x₆} {m₃} x₄) → (Unit → motive₂ n₀ (Nat:le:refl {n₀}) (Nat:le:below:refl {n₀} {λ (m₆ : Nat) → λ (x₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₆) → funType1₁ {m₆} x₇})) → ((m₆ : Nat) → (h₇ : Nat:le n₀ m₆) → (ih₈ : Nat:le:below {n₀} {λ (m₈ : Nat) → λ (x₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₈) → funType1₁ {m₈} x₉} {m₆} h₇) → (aih₉ : funType1₁ {m₆} h₇) → motive₂ (Nat:succ m₆) (Nat:le:step {n₀} {m₆} h₇) (Nat:le:below:step {n₀} {λ (m₁₀ : Nat) → λ (x₁₁ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₀) → funType1₁ {m₁₀} x₁₁} {m₆} h₇ ih₈ aih₉)) → motive₂ m₃ x₄ below₅

postulate instAddNat : Add Nat

postulate instHAdd : {α₀ : Set} → ⦃ _ : Add α₀ ⦄ → HAdd α₀ α₀ α₀

postulate Nat:succ~ule~usucc : {n₀ : Nat} → {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₀) (Nat:succ m₁)

postulate ~uprivate:Init:Prelude:~n0:Nat:zero~ule:match~u1~u1 : (motive₀ : Nat → Set) → (x₁ : Nat) → (Unit → motive₀ Nat:zero) → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ x₁

postulate Nat:zero~ule:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₁} x₀ → LE:le {Nat} ⦃ instLENat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₀

postulate Nat:zero~ule : (n₀ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) n₀

postulate Nat:zero~ult~usucc : (n₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₀)

postulate ~uprivate:Init:Prelude:~n0:Nat:add~upos~uright:match~u1~u1 : (motive₀ : (x₀ : Nat) → Nat → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₀ → Set) → (x₁ : Nat) → (x₂ : Nat) → (x₃ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₁) → ((x₄ : Nat) → (h₅ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) Nat:zero) → motive₀ Nat:zero x₄ h₅) → ((n₄ : Nat) → (x₅ : Nat) → (x₆ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₄)) → motive₀ (Nat:succ n₄) x₅ x₆) → motive₀ x₁ x₂ x₃

postulate Nat:add~upos~uright : {b₀ : Nat} → (a₁ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) b₀ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ a₁ b₀)

~uprivate:Init:Prelude:~n0:Nat:mul~upos:match~u1~u1:~ushare:~n1 : Set
~uprivate:Init:Prelude:~n0:Nat:mul~upos:match~u1~u1:~ushare:~n1 = (x₀ : Nat) → (x₁ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₀ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₁ → Set

postulate ~uprivate:Init:Prelude:~n0:Nat:mul~upos:match~u1~u1 : (motive₀ : ~uprivate:Init:Prelude:~n0:Nat:mul~upos:match~u1~u1:~ushare:~n1) → (x₁ : Nat) → (x₂ : Nat) → (x₃ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₁) → (x₄ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₂) → ((x₅ : Nat) → (x₆ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₅) → (hb₇ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) Nat:zero) → motive₀ x₅ Nat:zero x₆ hb₇) → ((x₅ : Nat) → (n₆ : Nat) → (ha₇ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₅) → (x₈ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₆)) → motive₀ x₅ (Nat:succ n₆) ha₇ x₈) → motive₀ x₁ x₂ x₃ x₄

record Mul (α₀ : Set) : Set where
  constructor Mul:mk
  field
    mul₁ : α₀ → α₀ → α₀

postulate Mul:rec : {α₀ : Set} → {motive₁ : Mul α₀ → Set} → ((mul₂ : α₀ → α₀ → α₀) → motive₁ (Mul:mk {α₀} mul₂)) → (t₂ : Mul α₀) → motive₁ t₂

Mul:mul : {α₀ : Set} → ⦃ _ : Mul α₀ ⦄ → α₀ → α₀ → α₀
Mul:mul {α₀} ⦃ self₁ ⦄ = Mul.mul₁ {α₀} self₁

postulate instHMul : {α₀ : Set} → ⦃ _ : Mul α₀ ⦄ → HMul α₀ α₀ α₀

postulate instMulNat : Mul Nat

postulate Nat:mul~upos : {n₀ : Nat} → {m₁ : Nat} → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) n₀ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) m₁ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HMul:hMul {Nat} {Nat} {Nat} ⦃ instHMul {Nat} ⦃ instMulNat ⦄ ⦄ n₀ m₁)

postulate ~uprivate:Init:Prelude:~n0:Nat:pow~upos:match~u1~u1 : {a₀ : Nat} → (motive₁ : Nat → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) a₀ → Set) → (x₂ : Nat) → (x₃ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) a₀) → ((x₄ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) a₀) → motive₁ Nat:zero x₄) → ((n₄ : Nat) → (h₅ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) a₀) → motive₁ (Nat:succ n₄) h₅) → motive₁ x₂ x₃

postulate Nat:pow~upos:~uf : {a₀ : Nat} → (x₁ : Nat) → Nat:below {λ (x₂ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) a₀ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HPow:hPow {Nat} {Nat} {Nat} ⦃ instHPow {Nat} {Nat} ⦃ instPowNat {Nat} ⦃ instNatPowNat ⦄ ⦄ ⦄ a₀ x₂)} x₁ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) a₀ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HPow:hPow {Nat} {Nat} {Nat} ⦃ instHPow {Nat} {Nat} ⦃ instPowNat {Nat} ⦃ instNatPowNat ⦄ ⦄ ⦄ a₀ x₁)

postulate Nat:pow~upos : {a₀ : Nat} → {n₁ : Nat} → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) a₀ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HPow:hPow {Nat} {Nat} {Nat} ⦃ instHPow {Nat} {Nat} ⦃ instPowNat {Nat} ⦃ instNatPowNat ⦄ ⦄ ⦄ a₀ n₁)

postulate BitVec:ofNat:~uproof~u1 : (n₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HPow:hPow {Nat} {Nat} {Nat} ⦃ instHPow {Nat} {Nat} ⦃ instPowNat {Nat} ⦃ instNatPowNat ⦄ ⦄ ⦄ (OfNat:ofNat {Nat} 2 ⦃ instOfNatNat 2 ⦄) n₀)

record HMod (α₀ : Set) (β₁ : Set) (γ₂ : outParam Set) : Set where
  constructor HMod:mk
  field
    hMod₃ : α₀ → β₁ → γ₂

postulate HMod:rec : {α₀ : Set} → {β₁ : Set} → {γ₂ : Set} → {motive₃ : HMod α₀ β₁ γ₂ → Set} → ((hMod₄ : α₀ → β₁ → γ₂) → motive₃ (HMod:mk {α₀} {β₁} {γ₂} hMod₄)) → (t₄ : HMod α₀ β₁ γ₂) → motive₃ t₄

HMod:hMod : {α₀ : Set} → {β₁ : Set} → {γ₂ : outParam Set} → ⦃ _ : HMod α₀ β₁ γ₂ ⦄ → α₀ → β₁ → γ₂
HMod:hMod {α₀} {β₁} {γ₂} ⦃ self₃ ⦄ = HMod.hMod₃ {α₀} {β₁} {γ₂} self₃

record Mod (α₀ : Set) : Set where
  constructor Mod:mk
  field
    mod₁ : α₀ → α₀ → α₀

postulate Mod:rec : {α₀ : Set} → {motive₁ : Mod α₀ → Set} → ((mod₂ : α₀ → α₀ → α₀) → motive₁ (Mod:mk {α₀} mod₂)) → (t₂ : Mod α₀) → motive₁ t₂

data Bool : Set where
  Bool:false : Bool
  Bool:true : Bool

postulate Bool:rec : {motive₀ : Bool → Set} → motive₀ Bool:false → motive₀ Bool:true → (t₁ : Bool) → motive₀ t₁

Not : Set → Set
Not a₀ = a₀ → False

data Decidable (p₀ : Set) : Set where
  Decidable:isFalse : Not p₀ → Decidable p₀
  Decidable:isTrue : p₀ → Decidable p₀

postulate Decidable:rec : {p₀ : Set} → {motive₁ : Decidable p₀ → Set} → ((h₂ : Not p₀) → motive₁ (Decidable:isFalse {p₀} h₂)) → ((h₂ : p₀) → motive₁ (Decidable:isTrue {p₀} h₂)) → (t₂ : Decidable p₀) → motive₁ t₂

postulate Nat:ble:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → ((x₃ : Nat) → motive₀ Nat:zero x₃) → ((n₃ : Nat) → motive₀ (Nat:succ n₃) Nat:zero) → ((n₃ : Nat) → (m₄ : Nat) → motive₀ (Nat:succ n₃) (Nat:succ m₄)) → motive₀ x₁ x₂

postulate Nat:ble:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Nat → Bool} x₀ → Nat → Bool

postulate Nat:ble : Nat → Nat → Bool

postulate Bool:casesOn : {motive₀ : Bool → Set} → (t₁ : Bool) → motive₀ Bool:false → motive₀ Bool:true → motive₀ t₁

postulate Bool:ctorIdx : Bool → Nat

postulate Eq:casesOn : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → Eq {α₀} a₁ a₂ → Set} → {a₃ : α₀} → (t₄ : Eq {α₀} a₁ a₃) → motive₂ a₁ (Eq:refl {α₀} a₁) → motive₂ a₃ t₄

postulate Nat:beq:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → (Unit → motive₀ Nat:zero Nat:zero) → ((n₃ : Nat) → motive₀ Nat:zero (Nat:succ n₃)) → ((n₃ : Nat) → motive₀ (Nat:succ n₃) Nat:zero) → ((n₃ : Nat) → (m₄ : Nat) → motive₀ (Nat:succ n₃) (Nat:succ m₄)) → motive₀ x₁ x₂

postulate Nat:beq:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Nat → Bool} x₀ → Nat → Bool

postulate Nat:beq : Nat → Nat → Bool

record True : Set where
  constructor True:intro

postulate True:rec : {motive₀ : True → Set} → motive₀ True:intro → (t₁ : True) → motive₀ t₁

postulate ~uprivate:Init:Prelude:~n0:noConfusion~uof~uNat:aux:match~u1~u1 : (motive₀ : Nat → Set) → (x₁ : Nat) → (Unit → motive₀ Nat:zero) → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ x₁

postulate ~uprivate:Init:Prelude:~n0:noConfusion~uof~uNat:aux:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Bool:rec {λ (x₂ : Bool) → Set} False True (Nat:beq x₁ x₁)} x₀ → Bool:rec {λ (x₁ : Bool) → Set} False True (Nat:beq x₀ x₀)

postulate ~uprivate:Init:Prelude:~n0:noConfusion~uof~uNat:aux : (a₀ : Nat) → Bool:rec {λ (x₁ : Bool) → Set} False True (Nat:beq a₀ a₀)

postulate congrArg : {α₀ : Set} → {β₁ : Set} → {a₂ : α₀} → {a₃ : α₀} → (f₄ : α₀ → β₁) → Eq {α₀} a₂ a₃ → Eq {β₁} (f₄ a₂) (f₄ a₃)

postulate noConfusion~uof~uNat : {α₀ : Set} → (f₁ : α₀ → Nat) → {a₂ : α₀} → {b₃ : α₀} → Eq {α₀} a₂ b₃ → Bool:rec {λ (x₄ : Bool) → Set} False True (Nat:beq (f₁ a₂) (f₁ b₃))

postulate ~uprivate:Init:Prelude:~n0:Nat:le~uof~uble~ueq~utrue:match~u1~u1 : (motive₀ : (n₀ : Nat) → (m₁ : Nat) → Eq {Bool} (Nat:ble n₀ m₁) Bool:true → Set) → (n₁ : Nat) → (m₂ : Nat) → (h₃ : Eq {Bool} (Nat:ble n₁ m₂) Bool:true) → ((x₄ : Nat) → (h₅ : Eq {Bool} (Nat:ble (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₄) Bool:true) → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₄ h₅) → ((n₄ : Nat) → (n₅ : Nat) → (h₆ : Eq {Bool} (Nat:ble (Nat:succ n₄) (Nat:succ n₅)) Bool:true) → motive₀ (Nat:succ n₄) (Nat:succ n₅) h₆) → motive₀ n₁ m₂ h₃

postulate Nat:le~uof~uble~ueq~utrue:~uf : {n₀ : Nat} → Nat:below {λ (n₁ : Nat) → {m₂ : Nat} → Eq {Bool} (Nat:ble n₁ m₂) Bool:true → LE:le {Nat} ⦃ instLENat ⦄ n₁ m₂} n₀ → {m₁ : Nat} → Eq {Bool} (Nat:ble n₀ m₁) Bool:true → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁

postulate Nat:le~uof~uble~ueq~utrue : {n₀ : Nat} → {m₁ : Nat} → Eq {Bool} (Nat:ble n₀ m₁) Bool:true → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁

postulate ~uprivate:Init:Prelude:~n0:Nat:ble~uself~ueq~utrue:match~u1~u1 : (motive₀ : Nat → Set) → (x₁ : Nat) → (Unit → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ x₁

postulate Nat:ble~uself~ueq~utrue:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Eq {Bool} (Nat:ble x₁ x₁) Bool:true} x₀ → Eq {Bool} (Nat:ble x₀ x₀) Bool:true

postulate Nat:ble~uself~ueq~utrue : (n₀ : Nat) → Eq {Bool} (Nat:ble n₀ n₀) Bool:true

postulate ~uprivate:Init:Prelude:~n0:Nat:ble~usucc~ueq~utrue:match~u1~u1 : (motive₀ : (x₀ : Nat) → (x₁ : Nat) → Eq {Bool} (Nat:ble x₀ x₁) Bool:true → Set) → (x₁ : Nat) → (x₂ : Nat) → (x₃ : Eq {Bool} (Nat:ble x₁ x₂) Bool:true) → ((x₄ : Nat) → (x₅ : Eq {Bool} (Nat:ble (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₄) Bool:true) → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₄ x₅) → ((n₄ : Nat) → (n₅ : Nat) → (h₆ : Eq {Bool} (Nat:ble (Nat:succ n₄) (Nat:succ n₅)) Bool:true) → motive₀ (Nat:succ n₄) (Nat:succ n₅) h₆) → motive₀ x₁ x₂ x₃

postulate Nat:ble~usucc~ueq~utrue:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → (x₂ : Nat) → Eq {Bool} (Nat:ble x₁ x₂) Bool:true → Eq {Bool} (Nat:ble x₁ (Nat:succ x₂)) Bool:true} x₀ → (x₁ : Nat) → Eq {Bool} (Nat:ble x₀ x₁) Bool:true → Eq {Bool} (Nat:ble x₀ (Nat:succ x₁)) Bool:true

postulate Nat:ble~usucc~ueq~utrue : {n₀ : Nat} → {m₁ : Nat} → Eq {Bool} (Nat:ble n₀ m₁) Bool:true → Eq {Bool} (Nat:ble n₀ (Nat:succ m₁)) Bool:true

postulate ~uprivate:Init:Prelude:~n0:Nat:ble~ueq~utrue~uof~ule:match~u1~u7 : {n₀ : Nat} → (funType1₁ : {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → Set) → (motive₂ : (m₂ : Nat) → (h₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₂) → Nat:le:below {n₀} {λ (m₄ : Nat) → λ (h₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₄) → funType1₁ {m₄} h₅} {m₂} h₃ → Set) → (m₃ : Nat) → (h₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₃) → (below₅ : Nat:le:below {n₀} {λ (m₅ : Nat) → λ (h₆ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₅) → funType1₁ {m₅} h₆} {m₃} h₄) → (Unit → motive₂ n₀ (Nat:le:refl {n₀}) (Nat:le:below:refl {n₀} {λ (m₆ : Nat) → λ (h₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₆) → funType1₁ {m₆} h₇})) → ((m₆ : Nat) → (h₇ : Nat:le n₀ m₆) → (ih₈ : Nat:le:below {n₀} {λ (m₈ : Nat) → λ (h₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₈) → funType1₁ {m₈} h₉} {m₆} h₇) → (aih₉ : funType1₁ {m₆} h₇) → motive₂ (Nat:succ m₆) (Nat:le:step {n₀} {m₆} h₇) (Nat:le:below:step {n₀} {λ (m₁₀ : Nat) → λ (h₁₁ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₀) → funType1₁ {m₁₀} h₁₁} {m₆} h₇ ih₈ aih₉)) → motive₂ m₃ h₄ below₅

postulate Nat:ble~ueq~utrue~uof~ule : {n₀ : Nat} → {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → Eq {Bool} (Nat:ble n₀ m₁) Bool:true

postulate absurd : {a₀ : Set} → {b₁ : Set} → a₀ → Not a₀ → b₁

postulate Nat:not~ule~uof~unot~uble~ueq~utrue : {n₀ : Nat} → {m₁ : Nat} → Not (Eq {Bool} (Nat:ble n₀ m₁) Bool:true) → Not (LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁)

postulate Decidable:casesOn : {p₀ : Set} → {motive₁ : Decidable p₀ → Set} → (t₂ : Decidable p₀) → ((h₃ : Not p₀) → motive₁ (Decidable:isFalse {p₀} h₃)) → ((h₃ : p₀) → motive₁ (Decidable:isTrue {p₀} h₃)) → motive₁ t₂

postulate dite : {α₀ : Set} → (c₁ : Set) → ⦃ _ : Decidable c₁ ⦄ → (c₁ → α₀) → (Not c₁ → α₀) → α₀

postulate Bool:decEq:match~u1 : (motive₀ : Bool → Bool → Set) → (a₁ : Bool) → (b₂ : Bool) → (Unit → motive₀ Bool:false Bool:false) → (Unit → motive₀ Bool:false Bool:true) → (Unit → motive₀ Bool:true Bool:false) → (Unit → motive₀ Bool:true Bool:true) → motive₀ a₁ b₂

postulate Bool:noConfusionType : Set → Bool → Bool → Set

postulate Bool:noConfusion : {P₀ : Set} → {t₁ : Bool} → {t₂ : Bool} → Eq {Bool} t₁ t₂ → Bool:noConfusionType P₀ t₁ t₂

postulate Bool:decEq : (a₀ : Bool) → (b₁ : Bool) → Decidable (Eq {Bool} a₀ b₁)

DecidableEq : Set → Set
DecidableEq α₀ = (a₁ : α₀) → (b₂ : α₀) → Decidable (Eq {α₀} a₁ b₂)

postulate instDecidableEqBool : DecidableEq Bool

postulate Nat:decLe : (n₀ : Nat) → (m₁ : Nat) → Decidable (LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁)

postulate namedPattern : {α₀ : Set} → (x₁ : α₀) → (a₂ : α₀) → Eq {α₀} x₁ a₂ → α₀

postulate Nat:mod:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → ((x₃ : Nat) → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₃) → ((n₃ : Nat) → (n₄ : Nat) → (h₅ : Eq {Nat} n₃ (Nat:succ n₄)) → (m₆ : Nat) → motive₀ (namedPattern {Nat} n₃ (Nat:succ n₄) h₅) m₆) → motive₀ x₁ x₂

postulate Nat:decLt : (n₀ : Nat) → (m₁ : Nat) → Decidable (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁)

postulate Nat:le~urefl : (n₀ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ n₀ n₀

postulate Nat:lt~uadd~uone : (n₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ n₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₀ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))

postulate Nat:lt~usucc~uself : (n₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ n₀ (Nat:succ n₀)

record HSub (α₀ : Set) (β₁ : Set) (γ₂ : outParam Set) : Set where
  constructor HSub:mk
  field
    hSub₃ : α₀ → β₁ → γ₂

postulate HSub:rec : {α₀ : Set} → {β₁ : Set} → {γ₂ : Set} → {motive₃ : HSub α₀ β₁ γ₂ → Set} → ((hSub₄ : α₀ → β₁ → γ₂) → motive₃ (HSub:mk {α₀} {β₁} {γ₂} hSub₄)) → (t₄ : HSub α₀ β₁ γ₂) → motive₃ t₄

HSub:hSub : {α₀ : Set} → {β₁ : Set} → {γ₂ : outParam Set} → ⦃ _ : HSub α₀ β₁ γ₂ ⦄ → α₀ → β₁ → γ₂
HSub:hSub {α₀} {β₁} {γ₂} ⦃ self₃ ⦄ = HSub.hSub₃ {α₀} {β₁} {γ₂} self₃

postulate Nat:ctorIdx : Nat → Nat

postulate Nat:div:go:match~u1 : (x₀ : Nat) → (motive₁ : (fuel₁ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₀ fuel₁ → Set) → (fuel₂ : Nat) → (hfuel₃ : LT:lt {Nat} ⦃ instLTNat ⦄ x₀ fuel₂) → ((fuel₄ : Nat) → (hfuel₅ : LT:lt {Nat} ⦃ instLTNat ⦄ x₀ (Nat:succ fuel₄)) → motive₁ (Nat:succ fuel₄) hfuel₅) → motive₁ fuel₂ hfuel₃

postulate ~uprivate:Init:Prelude:~n0:Nat:le~utrans:match~u1~u10 : {n₀ : Nat} → {m₁ : Nat} → (funType1₂ : {k₂ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → LE:le {Nat} ⦃ instLENat ⦄ m₁ k₂ → Set) → (motive₃ : (k₃ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → (x₄ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₃) → Nat:le:below {m₁} {λ (k₅ : Nat) → λ (x₆ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₅) → (x₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₅} x₇ x₆} {k₃} x₄ → Set) → (k₄ : Nat) → (x₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → (x₆ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₄) → (below₇ : Nat:le:below {m₁} {λ (k₇ : Nat) → λ (x₈ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₇) → (x₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₇} x₉ x₈} {k₄} x₆) → ((h₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → motive₃ m₁ h₈ (Nat:le:refl {m₁}) (Nat:le:below:refl {m₁} {λ (k₉ : Nat) → λ (x₁₀ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₉) → (x₁₁ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₉} x₁₁ x₁₀})) → ((h₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → (m₉ : Nat) → (h₁₀ : Nat:le m₁ m₉) → (ih₁₁ : Nat:le:below {m₁} {λ (k₁₁ : Nat) → λ (x₁₂ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₁) → (x₁₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₁} x₁₃ x₁₂} {m₉} h₁₀) → (aih₁₂ : (x₁₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {m₉} x₁₂ h₁₀) → motive₃ (Nat:succ m₉) h₈ (Nat:le:step {m₁} {m₉} h₁₀) (Nat:le:below:step {m₁} {λ (k₁₃ : Nat) → λ (x₁₄ : LE:le {Nat} ⦃ instLENat ⦄ m₁ k₁₃) → (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁) → funType1₂ {k₁₃} x₁₅ x₁₄} {m₉} h₁₀ ih₁₁ aih₁₂)) → motive₃ k₄ x₅ x₆ below₇

postulate Nat:le~utrans : {n₀ : Nat} → {m₁ : Nat} → {k₂ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → LE:le {Nat} ⦃ instLENat ⦄ m₁ k₂ → LE:le {Nat} ⦃ instLENat ⦄ n₀ k₂

postulate Nat:lt~uof~ult~uof~ule : {n₀ : Nat} → {m₁ : Nat} → {k₂ : Nat} → LT:lt {Nat} ⦃ instLTNat ⦄ n₀ m₁ → LE:le {Nat} ⦃ instLENat ⦄ m₁ k₂ → LT:lt {Nat} ⦃ instLTNat ⦄ n₀ k₂

postulate Nat:le~usucc : (n₀ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ n₀)

postulate Nat:pred : Nat → Nat

postulate ~uprivate:Init:Prelude:~n0:Nat:pred~ule~upred:match~u1~u1 : (motive₀ : (x₀ : Nat) → (x₁ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ x₀ x₁ → Set) → (x₁ : Nat) → (x₂ : Nat) → (x₃ : LE:le {Nat} ⦃ instLENat ⦄ x₁ x₂) → ((n₄ : Nat) → motive₀ n₄ n₄ (Nat:le:refl {n₄})) → ((n₄ : Nat) → (h₅ : Nat:le (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) n₄) → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₄) (Nat:le:step {OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄} {n₄} h₅)) → ((n₄ : Nat) → (n₅ : Nat) → (h₆ : Nat:le (Nat:succ n₄) n₅) → motive₀ (Nat:succ n₄) (Nat:succ n₅) (Nat:le:step {Nat:succ n₄} {n₅} h₆)) → motive₀ x₁ x₂ x₃

postulate Nat:pred~ule~upred : {n₀ : Nat} → {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → LE:le {Nat} ⦃ instLENat ⦄ (Nat:pred n₀) (Nat:pred m₁)

postulate Nat:le~uof~usucc~ule~usucc : {n₀ : Nat} → {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₀) (Nat:succ m₁) → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁

postulate ~uprivate:Init:Prelude:~n0:Nat:not~usucc~ule~uself:match~u1~u1 : (motive₀ : Nat → Set) → (x₁ : Nat) → (Unit → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ x₁

postulate Nat:not~usucc~ule~uself:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Not (LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ x₁) x₁)} x₀ → Not (LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ x₀) x₀)

postulate Nat:not~usucc~ule~uself : (n₀ : Nat) → Not (LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₀) n₀)

postulate Nat:lt~uirrefl : (n₀ : Nat) → Not (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ n₀)

postulate Nat:lt~usucc~uof~ule : {n₀ : Nat} → {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → LT:lt {Nat} ⦃ instLTNat ⦄ n₀ (Nat:succ m₁)

postulate ~uprivate:Init:Prelude:~n0:Nat:pred~ule:match~u1~u1 : (motive₀ : Nat → Set) → (x₁ : Nat) → (Unit → motive₀ Nat:zero) → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ x₁

postulate Nat:pred~ule : (n₀ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ (Nat:pred n₀) n₀

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

postulate Nat:modCore:go:~uf : (y₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀ → (fuel₁ : Nat) → Nat:below {λ (fuel₂ : Nat) → (x₃ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₃ fuel₂ → Nat} fuel₁ → (x₂ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₂ fuel₁ → Nat

postulate Nat:modCore:go : (y₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀ → (fuel₁ : Nat) → (x₂ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₂ fuel₁ → Nat

postulate Nat:modCore : Nat → Nat → Nat

postulate ite : {α₀ : Set} → (c₁ : Set) → ⦃ _ : Decidable c₁ ⦄ → α₀ → α₀ → α₀

postulate Nat:mod : Nat → Nat → Nat

postulate Nat:instMod : Mod Nat

postulate GE:ge : {α₀ : Set} → ⦃ _ : LE α₀ ⦄ → α₀ → α₀ → Set

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

postulate ~uprivate:Init:Prelude:~n0:Nat:mod~ult:match~u1~u1 : (n₀ : Nat) → (m₁ : Nat) → (motive₂ : Decidable (LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ n₀)) → Set) → (x₃ : Decidable (LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ n₀))) → ((h₄ : LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ n₀)) → motive₂ (Decidable:isTrue {LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ n₀)} h₄)) → ((h₄ : Not (LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ n₀))) → motive₂ (Decidable:isFalse {LE:le {Nat} ⦃ instLENat ⦄ m₁ (Nat:succ n₀)} h₄)) → motive₂ x₃

postulate ~uprivate:Init:Prelude:~n0:Nat:mod~ult:match~u1~u3 : (motive₀ : Nat → (x₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₀ → Set) → (x₁ : Nat) → (x₂ : Nat) → (x₃ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₂) → ((n₄ : Nat) → (x₅ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₄)) → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₄) x₅) → ((n₄ : Nat) → (m₅ : Nat) → (hm₆ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) m₅) → motive₀ (Nat:succ n₄) m₅ hm₆) → motive₀ x₁ x₂ x₃

Mod:mod : {α₀ : Set} → ⦃ _ : Mod α₀ ⦄ → α₀ → α₀ → α₀
Mod:mod {α₀} ⦃ self₁ ⦄ = Mod.mod₁ {α₀} self₁

postulate instHMod : {α₀ : Set} → ⦃ _ : Mod α₀ ⦄ → HMod α₀ α₀ α₀

postulate Nat:mod~ult : (x₀ : Nat) → {y₁ : Nat} → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁ → LT:lt {Nat} ⦃ instLTNat ⦄ (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ x₀ y₁) y₁

postulate Fin:Internal:ofNat : (n₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) n₀ → Nat → Fin n₀

postulate BitVec:ofNat : (n₀ : Nat) → Nat → BitVec n₀

BitVec:toFin : {w₀ : Nat} → BitVec w₀ → Fin (HPow:hPow {Nat} {Nat} {Nat} ⦃ instHPow {Nat} {Nat} ⦃ instPowNat {Nat} ⦃ instNatPowNat ⦄ ⦄ ⦄ (OfNat:ofNat {Nat} 2 ⦃ instOfNatNat 2 ⦄) w₀)
BitVec:toFin {w₀} self₁ = BitVec.toFin₁ {w₀} self₁

Fin:val : {n₀ : Nat} → Fin n₀ → Nat
Fin:val {n₀} self₁ = Fin.val₁ {n₀} self₁

postulate BitVec:toNat : {w₀ : Nat} → BitVec w₀ → Nat

record UInt8 : Set where
  constructor UInt8:ofBitVec
  field
    toBitVec₀ : BitVec (OfNat:ofNat {Nat} 8 ⦃ instOfNatNat 8 ⦄)

postulate UInt8:rec : {motive₀ : UInt8 → Set} → ((toBitVec₁ : BitVec (OfNat:ofNat {Nat} 8 ⦃ instOfNatNat 8 ⦄)) → motive₀ (UInt8:ofBitVec toBitVec₁)) → (t₁ : UInt8) → motive₀ t₁

record ByteArray : Set where
  constructor ByteArray:mk
  field
    data₀ : Array UInt8

postulate ByteArray:rec : {motive₀ : ByteArray → Set} → ((data₁ : Array UInt8) → motive₀ (ByteArray:mk data₁)) → (t₁ : ByteArray) → motive₀ t₁

record UInt32 : Set where
  constructor UInt32:ofBitVec
  field
    toBitVec₀ : BitVec (OfNat:ofNat {Nat} 32 ⦃ instOfNatNat 32 ⦄)

postulate UInt32:rec : {motive₀ : UInt32 → Set} → ((toBitVec₁ : BitVec (OfNat:ofNat {Nat} 32 ⦃ instOfNatNat 32 ⦄)) → motive₀ (UInt32:ofBitVec toBitVec₁)) → (t₁ : UInt32) → motive₀ t₁

postulate Nat:isValidChar : Nat → Set

UInt32:toBitVec : UInt32 → BitVec (OfNat:ofNat {Nat} 32 ⦃ instOfNatNat 32 ⦄)
UInt32:toBitVec self₀ = UInt32.toBitVec₀ self₀

postulate UInt32:toNat : UInt32 → Nat

postulate UInt32:isValidChar : UInt32 → Set

record Char : Set where
  constructor Char:mk
  field
    val₀ : UInt32
    valid₁ : UInt32:isValidChar val₀

postulate Char:rec : {motive₀ : Char → Set} → ((val₁ : UInt32) → (valid₂ : UInt32:isValidChar val₁) → motive₀ (Char:mk val₁ valid₂)) → (t₁ : Char) → motive₀ t₁

postulate List:append:match~u1 : {α₀ : Set} → (motive₁ : List α₀ → List α₀ → Set) → (x₂ : List α₀) → (x₃ : List α₀) → ((bs₄ : List α₀) → motive₁ (List:nil {α₀}) bs₄) → ((a₄ : α₀) → (as₅ : List α₀) → (bs₆ : List α₀) → motive₁ (List:cons {α₀} a₄ as₅) bs₆) → motive₁ x₂ x₃

postulate List:append:~uf : {α₀ : Set} → (x₁ : List α₀) → List:below {α₀} {λ (x₂ : List α₀) → List α₀ → List α₀} x₁ → List α₀ → List α₀

postulate List:append : {α₀ : Set} → List α₀ → List α₀ → List α₀

postulate List:flatten:match~u1 : {α₀ : Set} → (motive₁ : List (List α₀) → Set) → (x₂ : List (List α₀)) → (Unit → motive₁ (List:nil {List α₀})) → ((l₃ : List α₀) → (L₄ : List (List α₀)) → motive₁ (List:cons {List α₀} l₃ L₄)) → motive₁ x₂

postulate List:flatten:~uf : {α₀ : Set} → (x₁ : List (List α₀)) → List:below {List α₀} {λ (x₂ : List (List α₀)) → List α₀} x₁ → List α₀

postulate List:flatten : {α₀ : Set} → List (List α₀) → List α₀

postulate instDecidableEqList:match~u1 : {α₀ : Set} → (motive₁ : List α₀ → Set) → (ys₂ : List α₀) → (Unit → motive₁ (List:nil {α₀})) → ((head₃ : α₀) → (tail₄ : List α₀) → motive₁ (List:cons {α₀} head₃ tail₄)) → motive₁ ys₂

postulate List:map:~uf : {α₀ : Set} → {β₁ : Set} → (α₀ → β₁) → (x₂ : List α₀) → List:below {α₀} {λ (x₃ : List α₀) → List β₁} x₂ → List β₁

postulate List:map : {α₀ : Set} → {β₁ : Set} → (α₀ → β₁) → List α₀ → List β₁

postulate List:flatMap : {α₀ : Set} → {β₁ : Set} → (α₀ → List β₁) → List α₀ → List β₁

postulate ByteArray:emptyWithCapacity : Nat → ByteArray

postulate ByteArray:empty : ByteArray

postulate ByteArray:casesOn : {motive₀ : ByteArray → Set} → (t₁ : ByteArray) → ((data₂ : Array UInt8) → motive₀ (ByteArray:mk data₂)) → motive₀ t₁

postulate ByteArray:push:match~u1 : (motive₀ : ByteArray → UInt8 → Set) → (x₁ : ByteArray) → (x₂ : UInt8) → ((bs₃ : Array UInt8) → (b₄ : UInt8) → motive₀ (ByteArray:mk bs₃) b₄) → motive₀ x₁ x₂

postulate ByteArray:push : ByteArray → UInt8 → ByteArray

postulate List:toByteArray:match~u1 : (motive₀ : List UInt8 → ByteArray → Set) → (x₁ : List UInt8) → (x₂ : ByteArray) → ((r₃ : ByteArray) → motive₀ (List:nil {UInt8}) r₃) → ((b₃ : UInt8) → (bs₄ : List UInt8) → (r₅ : ByteArray) → motive₀ (List:cons {UInt8} b₃ bs₄) r₅) → motive₀ x₁ x₂

postulate List:toByteArray:loop:~uf : (x₀ : List UInt8) → List:below {UInt8} {λ (x₁ : List UInt8) → ByteArray → ByteArray} x₀ → ByteArray → ByteArray

postulate List:toByteArray:loop : List UInt8 → ByteArray → ByteArray

postulate List:toByteArray : List UInt8 → ByteArray

Char:val : Char → UInt32
Char:val self₀ = Char.val₀ self₀

record HDiv (α₀ : Set) (β₁ : Set) (γ₂ : outParam Set) : Set where
  constructor HDiv:mk
  field
    hDiv₃ : α₀ → β₁ → γ₂

postulate HDiv:rec : {α₀ : Set} → {β₁ : Set} → {γ₂ : Set} → {motive₃ : HDiv α₀ β₁ γ₂ → Set} → ((hDiv₄ : α₀ → β₁ → γ₂) → motive₃ (HDiv:mk {α₀} {β₁} {γ₂} hDiv₄)) → (t₄ : HDiv α₀ β₁ γ₂) → motive₃ t₄

HDiv:hDiv : {α₀ : Set} → {β₁ : Set} → {γ₂ : outParam Set} → ⦃ _ : HDiv α₀ β₁ γ₂ ⦄ → α₀ → β₁ → γ₂
HDiv:hDiv {α₀} {β₁} {γ₂} ⦃ self₃ ⦄ = HDiv.hDiv₃ {α₀} {β₁} {γ₂} self₃

record Div (α₀ : Set) : Set where
  constructor Div:mk
  field
    div₁ : α₀ → α₀ → α₀

postulate Div:rec : {α₀ : Set} → {motive₁ : Div α₀ → Set} → ((div₂ : α₀ → α₀ → α₀) → motive₁ (Div:mk {α₀} div₂)) → (t₂ : Div α₀) → motive₁ t₂

postulate Nat:div:go:~uf : (y₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀ → (fuel₁ : Nat) → Nat:below {λ (fuel₂ : Nat) → (x₃ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₃ fuel₂ → Nat} fuel₁ → (x₂ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₂ fuel₁ → Nat

postulate Nat:div:go : (y₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀ → (fuel₁ : Nat) → (x₂ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₂ fuel₁ → Nat

postulate Nat:div : Nat → Nat → Nat

postulate Nat:instDiv : Div Nat

postulate UInt8:ofNat : Nat → UInt8

Div:div : {α₀ : Set} → ⦃ _ : Div α₀ ⦄ → α₀ → α₀ → α₀
Div:div {α₀} ⦃ self₁ ⦄ = Div.div₁ {α₀} self₁

postulate instHDiv : {α₀ : Set} → ⦃ _ : Div α₀ ⦄ → HDiv α₀ α₀ α₀

postulate String:utf8EncodeChar : Char → List UInt8

postulate List:utf8Encode : List Char → ByteArray

record ByteArray:IsValidUTF8 (b₀ : ByteArray) : Set where
  constructor ByteArray:IsValidUTF8:intro
  field
    m₁ : List Char
    hm₂ : Eq {ByteArray} b₀ (List:utf8Encode m₁)

postulate ByteArray:IsValidUTF8:rec : {b₀ : ByteArray} → {motive₁ : ByteArray:IsValidUTF8 b₀ → Set} → ((m₂ : List Char) → (hm₃ : Eq {ByteArray} b₀ (List:utf8Encode m₂)) → motive₁ (ByteArray:IsValidUTF8:intro {b₀} m₂ hm₃)) → (t₂ : ByteArray:IsValidUTF8 b₀) → motive₁ t₂

record Inhabited (α₀ : Set) : Set where
  constructor Inhabited:mk
  field
    default₁ : α₀

postulate Inhabited:rec : {α₀ : Set} → {motive₁ : Inhabited α₀ → Set} → ((default₂ : α₀) → motive₁ (Inhabited:mk {α₀} default₂)) → (t₂ : Inhabited α₀) → motive₁ t₂

Inhabited:default : {α₀ : Set} → ⦃ _ : Inhabited α₀ ⦄ → α₀
Inhabited:default {α₀} ⦃ self₁ ⦄ = Inhabited.default₁ {α₀} self₁

record PrintFixtures:Dependent : Set where
  constructor PrintFixtures:Dependent:mk
  field
    size₀ : Nat
    value₁ : Fin size₀

postulate PrintFixtures:Dependent:rec : {motive₀ : PrintFixtures:Dependent → Set} → ((size₁ : Nat) → (value₂ : Fin size₁) → motive₀ (PrintFixtures:Dependent:mk size₁ value₂)) → (t₁ : PrintFixtures:Dependent) → motive₀ t₁

PrintFixtures:Dependent:size : PrintFixtures:Dependent → Nat
PrintFixtures:Dependent:size self₀ = PrintFixtures:Dependent.size₀ self₀

PrintFixtures:Dependent:value : (self₀ : PrintFixtures:Dependent) → Fin (PrintFixtures:Dependent:size self₀)
PrintFixtures:Dependent:value self₀ = PrintFixtures:Dependent.value₁ self₀

record PrintFixtures:Pair : Set where
  constructor PrintFixtures:Pair:mk
  field
    first₀ : Nat
    second₁ : Nat

postulate PrintFixtures:Pair:rec : {motive₀ : PrintFixtures:Pair → Set} → ((first₁ : Nat) → (second₂ : Nat) → motive₀ (PrintFixtures:Pair:mk first₁ second₂)) → (t₁ : PrintFixtures:Pair) → motive₀ t₁

PrintFixtures:Pair:first : PrintFixtures:Pair → Nat
PrintFixtures:Pair:first self₀ = PrintFixtures:Pair.first₀ self₀

postulate PrintFixtures:applyImplicit : ({α₀ : Set} → α₀ → α₀) → Nat

PrintFixtures:alignedDeep : Nat
PrintFixtures:alignedDeep = PrintFixtures:applyImplicit (λ {α₀ : Set} → λ (a₁ : α₀) → a₁)

PrintFixtures:alignedTop : {α₀ : Set} → α₀ → α₀
PrintFixtures:alignedTop {α₀} a₁ = a₁

PrintFixtures:doubling:~ushare:~n1 : Nat
PrintFixtures:doubling:~ushare:~n1 = Nat:add (Nat:add (Nat:add (Nat:add Nat:zero Nat:zero) (Nat:add Nat:zero Nat:zero)) (Nat:add (Nat:add Nat:zero Nat:zero) (Nat:add Nat:zero Nat:zero))) (Nat:add (Nat:add (Nat:add Nat:zero Nat:zero) (Nat:add Nat:zero Nat:zero)) (Nat:add (Nat:add Nat:zero Nat:zero) (Nat:add Nat:zero Nat:zero)))

PrintFixtures:doubling:~ushare:~n2 : Nat
PrintFixtures:doubling:~ushare:~n2 = Nat:add PrintFixtures:doubling:~ushare:~n1 PrintFixtures:doubling:~ushare:~n1

PrintFixtures:doubling:~ushare:~n3 : Nat
PrintFixtures:doubling:~ushare:~n3 = Nat:add PrintFixtures:doubling:~ushare:~n2 PrintFixtures:doubling:~ushare:~n2

PrintFixtures:doubling:~ushare:~n4 : Nat
PrintFixtures:doubling:~ushare:~n4 = Nat:add PrintFixtures:doubling:~ushare:~n3 PrintFixtures:doubling:~ushare:~n3

PrintFixtures:doubling:~ushare:~n5 : Nat
PrintFixtures:doubling:~ushare:~n5 = Nat:add PrintFixtures:doubling:~ushare:~n4 PrintFixtures:doubling:~ushare:~n4

PrintFixtures:doubling:~ushare:~n6 : Nat
PrintFixtures:doubling:~ushare:~n6 = Nat:add PrintFixtures:doubling:~ushare:~n5 PrintFixtures:doubling:~ushare:~n5

PrintFixtures:doubling : Nat
PrintFixtures:doubling = Nat:add PrintFixtures:doubling:~ushare:~n6 PrintFixtures:doubling:~ushare:~n6

postulate String : Set
{-# BUILTIN STRING String #-}

postulate String:ofByteArray : (toByteArray₀ : ByteArray) → ByteArray:IsValidUTF8 toByteArray₀ → String

postulate String:rec : {motive₀ : String → Set} → ((toByteArray₁ : ByteArray) → (isValidUTF8₂ : ByteArray:IsValidUTF8 toByteArray₁) → motive₀ (String:ofByteArray toByteArray₁ isValidUTF8₂)) → (t₁ : String) → motive₀ t₁

PrintFixtures:greeting : String
PrintFixtures:greeting = "a\"b\\c\10\&\955\&\10013\&"

PrintFixtures:higher : (Nat → Nat) → ((Nat → Nat) → Nat) → Nat
PrintFixtures:higher f₀ g₁ = g₁ f₀

PrintFixtures:large : Nat
PrintFixtures:large = OfNat:ofNat {Nat} 18446744073709551616 ⦃ instOfNatNat 18446744073709551616 ⦄

PrintFixtures:pick : (α₀ : Set) → ⦃ _ : Inhabited α₀ ⦄ → α₀
PrintFixtures:pick α₀ ⦃ inst₁ ⦄ = Inhabited:default {α₀} ⦃ inst₁ ⦄

PrintFixtures:redex : Nat
PrintFixtures:redex = (λ (x₀ : Nat) → Nat:succ x₀) (OfNat:ofNat {Nat} 3 ⦃ instOfNatNat 3 ⦄)

PrintFixtures:sorts : Set → Set → Set
PrintFixtures:sorts α₀ x₁ = α₀

PrintFixtures:strict : {n₀ : Nat} → Eq {Nat} n₀ n₀ → Nat
PrintFixtures:strict {n₀} x₁ = n₀

PrintFixtures:withLet : Nat → Nat
PrintFixtures:withLet n₀ = let m₁ : Nat; m₁ = Nat:add n₀ n₀ in Nat:add m₁ m₁
