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

And:casesOn : {a₀ : Set} → {b₁ : Set} → {motive₂ : And a₀ b₁ → Set} → (t₃ : And a₀ b₁) → ((left₄ : a₀) → (right₅ : b₁) → motive₂ (And:intro {a₀} {b₁} left₄ right₅)) → motive₂ t₃
And:casesOn {a₀} {b₁} {motive₂} t₃ intro₄ = And:rec {a₀} {b₁} {motive₂} (λ (left₅ : a₀) → λ (right₆ : b₁) → intro₄ left₅ right₆) t₃

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

Array:emptyWithCapacity : {α₀ : Set} → Nat → Array α₀
Array:emptyWithCapacity {α₀} c₁ = Array:mk {α₀} (List:nil {α₀})

record OfNat (α₀ : Set) (x₁ : Nat) : Set where
  constructor OfNat:mk
  field
    ofNat₂ : α₀

postulate OfNat:rec : {α₀ : Set} → {x₁ : Nat} → {motive₂ : OfNat α₀ x₁ → Set} → ((ofNat₃ : α₀) → motive₂ (OfNat:mk {α₀} {x₁} ofNat₃)) → (t₃ : OfNat α₀ x₁) → motive₂ t₃

OfNat:ofNat : {α₀ : Set} → (x₁ : Nat) → ⦃ _ : OfNat α₀ x₁ ⦄ → α₀
OfNat:ofNat {α₀} x₁ ⦃ self₂ ⦄ = OfNat.ofNat₂ {α₀} {x₁} self₂

instOfNatNat : (n₀ : Nat) → OfNat Nat n₀
instOfNatNat n₀ = OfNat:mk {Nat} {n₀} n₀

Array:empty : {α₀ : Set} → Array α₀
Array:empty {α₀} = Array:emptyWithCapacity {α₀} (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)

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

List:below : {α₀ : Set} → {_ : List α₀ → Set} → List α₀ → Set
List:below {α₀} {motive₁} t₂ = List:rec {α₀} {λ (t₃ : List α₀) → Set} PUnit (λ (head₃ : α₀) → λ (tail₄ : List α₀) → λ (tailih₅ : Set) → PProd (motive₁ tail₄) tailih₅) t₂

List:brecOn:go : {α₀ : Set} → {motive₁ : List α₀ → Set} → (t₂ : List α₀) → ((t₃ : List α₀) → List:below {α₀} {motive₁} t₃ → motive₁ t₃) → PProd (motive₁ t₂) (List:below {α₀} {motive₁} t₂)
List:brecOn:go {α₀} {motive₁} t₂ F1₃ = List:rec {α₀} {λ (t₄ : List α₀) → PProd (motive₁ t₄) (List:below {α₀} {motive₁} t₄)} (PProd:mk {motive₁ (List:nil {α₀})} {PUnit} (F1₃ (List:nil {α₀}) PUnit:unit) PUnit:unit) (λ (head₄ : α₀) → λ (tail₅ : List α₀) → λ (tailih₆ : PProd (motive₁ tail₅) (List:below {α₀} {motive₁} tail₅)) → PProd:mk {motive₁ (List:cons {α₀} head₄ tail₅)} {PProd (motive₁ tail₅) (List:below {α₀} {motive₁} tail₅)} (F1₃ (List:cons {α₀} head₄ tail₅) tailih₆) tailih₆) t₂

List:brecOn : {α₀ : Set} → {motive₁ : List α₀ → Set} → (t₂ : List α₀) → ((t₃ : List α₀) → List:below {α₀} {motive₁} t₃ → motive₁ t₃) → motive₁ t₂
List:brecOn {α₀} {motive₁} t₂ F1₃ = PProd.fst₂ {motive₁ t₂} {List:below {α₀} {motive₁} t₂} (List:brecOn:go {α₀} {motive₁} t₂ F1₃)

List:casesOn : {α₀ : Set} → {motive₁ : List α₀ → Set} → (t₂ : List α₀) → motive₁ (List:nil {α₀}) → ((head₃ : α₀) → (tail₄ : List α₀) → motive₁ (List:cons {α₀} head₃ tail₄)) → motive₁ t₂
List:casesOn {α₀} {motive₁} t₂ nil₃ cons₄ = List:rec {α₀} {motive₁} nil₃ (λ (head₅ : α₀) → λ (tail₆ : List α₀) → λ (tailih₇ : motive₁ tail₆) → cons₄ head₅ tail₆) t₂

List:concat:match~u1 : {α₀ : Set} → (motive₁ : List α₀ → α₀ → Set) → (x₂ : List α₀) → (x₃ : α₀) → ((b₄ : α₀) → motive₁ (List:nil {α₀}) b₄) → ((a₄ : α₀) → (as₅ : List α₀) → (b₆ : α₀) → motive₁ (List:cons {α₀} a₄ as₅) b₆) → motive₁ x₂ x₃
List:concat:match~u1 {α₀} motive₁ x₂ x₃ h1₄ h2₅ = List:casesOn {α₀} {λ (x₆ : List α₀) → motive₁ x₆ x₃} x₂ (h1₄ x₃) (λ (head₆ : α₀) → λ (tail₇ : List α₀) → h2₅ head₆ tail₇ x₃)

List:concat:~uf : {α₀ : Set} → (x₁ : List α₀) → List:below {α₀} {λ (x₂ : List α₀) → α₀ → List α₀} x₁ → α₀ → List α₀
List:concat:~uf {α₀} x₁ f₂ x₃ = List:concat:match~u1 {α₀} (λ (x₄ : List α₀) → λ (x₅ : α₀) → List:below {α₀} {λ (x₆ : List α₀) → α₀ → List α₀} x₄ → List α₀) x₁ x₃ (λ (b₄ : α₀) → λ (x₅ : List:below {α₀} {λ (x₅ : List α₀) → α₀ → List α₀} (List:nil {α₀})) → List:cons {α₀} b₄ (List:nil {α₀})) (λ (a₄ : α₀) → λ (as₅ : List α₀) → λ (b₆ : α₀) → λ (x₇ : List:below {α₀} {λ (x₇ : List α₀) → α₀ → List α₀} (List:cons {α₀} a₄ as₅)) → List:cons {α₀} a₄ (PProd.fst₂ {(λ (x₈ : List α₀) → α₀ → List α₀) as₅} {List:rec {α₀} {λ (t₈ : List α₀) → Set} PUnit (λ (head₈ : α₀) → λ (tail₉ : List α₀) → λ (tailih₁₀ : Set) → PProd ((λ (x₁₁ : List α₀) → α₀ → List α₀) tail₉) tailih₁₀) as₅} x₇ b₆)) f₂

List:concat : {α₀ : Set} → List α₀ → α₀ → List α₀
List:concat {α₀} x₁ x₂ = List:brecOn {α₀} {λ (x₃ : List α₀) → α₀ → List α₀} x₁ (List:concat:~uf {α₀}) x₂

Array:push : {α₀ : Set} → Array α₀ → α₀ → Array α₀
Array:push {α₀} a₁ v₂ = Array:mk {α₀} (List:concat {α₀} (Array:toList {α₀} a₁) v₂)

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

Nat:lt : Nat → Nat → Set
Nat:lt n₀ m₁ = Nat:le (Nat:succ n₀) m₁

instLTNat : LT Nat
instLTNat = LT:mk {Nat} Nat:lt

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

instHPow : {α₀ : Set} → {β₁ : Set} → ⦃ _ : Pow α₀ β₁ ⦄ → HPow α₀ β₁ α₀
instHPow {α₀} {β₁} ⦃ inst₂ ⦄ = HPow:mk {α₀} {β₁} {α₀} (λ (a₃ : α₀) → λ (b₄ : β₁) → Pow:pow {α₀} {β₁} ⦃ inst₂ ⦄ a₃ b₄)

Nat:below : {_ : Nat → Set} → Nat → Set
Nat:below {motive₀} t₁ = Nat:rec {λ (t₂ : Nat) → Set} PUnit (λ (n₂ : Nat) → λ (nih₃ : Set) → PProd (motive₀ n₂) nih₃) t₁

Nat:brecOn:go : {motive₀ : Nat → Set} → (t₁ : Nat) → ((t₂ : Nat) → Nat:below {motive₀} t₂ → motive₀ t₂) → PProd (motive₀ t₁) (Nat:below {motive₀} t₁)
Nat:brecOn:go {motive₀} t₁ F1₂ = Nat:rec {λ (t₃ : Nat) → PProd (motive₀ t₃) (Nat:below {motive₀} t₃)} (PProd:mk {motive₀ Nat:zero} {PUnit} (F1₂ Nat:zero PUnit:unit) PUnit:unit) (λ (n₃ : Nat) → λ (nih₄ : PProd (motive₀ n₃) (Nat:below {motive₀} n₃)) → PProd:mk {motive₀ (Nat:succ n₃)} {PProd (motive₀ n₃) (Nat:below {motive₀} n₃)} (F1₂ (Nat:succ n₃) nih₄) nih₄) t₁

Nat:brecOn : {motive₀ : Nat → Set} → (t₁ : Nat) → ((t₂ : Nat) → Nat:below {motive₀} t₂ → motive₀ t₂) → motive₀ t₁
Nat:brecOn {motive₀} t₁ F1₂ = PProd.fst₂ {motive₀ t₁} {Nat:below {motive₀} t₁} (Nat:brecOn:go {motive₀} t₁ F1₂)

Nat:casesOn : {motive₀ : Nat → Set} → (t₁ : Nat) → motive₀ Nat:zero → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ t₁
Nat:casesOn {motive₀} t₁ zero₂ succ₃ = Nat:rec {motive₀} zero₂ (λ (n₄ : Nat) → λ (nih₅ : motive₀ n₄) → succ₃ n₄) t₁

Nat:add:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → ((a₃ : Nat) → motive₀ a₃ Nat:zero) → ((a₃ : Nat) → (b₄ : Nat) → motive₀ a₃ (Nat:succ b₄)) → motive₀ x₁ x₂
Nat:add:match~u1 motive₀ x₁ x₂ h1₃ h2₄ = Nat:casesOn {λ (x₅ : Nat) → motive₀ x₁ x₅} x₂ (h1₃ x₁) (λ (n₅ : Nat) → h2₄ x₁ n₅)

Nat:add:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Nat → Nat} x₀ → Nat → Nat
Nat:add:~uf x₀ f₁ x₂ = Nat:add:match~u1 (λ (x₃ : Nat) → λ (x₄ : Nat) → Nat:below {λ (x₅ : Nat) → Nat → Nat} x₄ → Nat) x₂ x₀ (λ (a₃ : Nat) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Nat} Nat:zero) → a₃) (λ (a₃ : Nat) → λ (b₄ : Nat) → λ (x₅ : Nat:below {λ (x₅ : Nat) → Nat → Nat} (Nat:succ b₄)) → Nat:succ (PProd.fst₂ {(λ (x₆ : Nat) → Nat → Nat) b₄} {Nat:rec {λ (t₆ : Nat) → Set} PUnit (λ (n₆ : Nat) → λ (nih₇ : Set) → PProd ((λ (x₈ : Nat) → Nat → Nat) n₆) nih₇) b₄} x₅ a₃)) f₁

Nat:add : Nat → Nat → Nat
Nat:add x₀ x₁ = Nat:brecOn {λ (x₂ : Nat) → Nat → Nat} x₁ Nat:add:~uf x₀

Nat:mul:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → ((x₃ : Nat) → motive₀ x₃ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → ((a₃ : Nat) → (b₄ : Nat) → motive₀ a₃ (Nat:succ b₄)) → motive₀ x₁ x₂
Nat:mul:match~u1 motive₀ x₁ x₂ h1₃ h2₄ = Nat:casesOn {λ (x₅ : Nat) → motive₀ x₁ x₅} x₂ (h1₃ x₁) (λ (n₅ : Nat) → h2₄ x₁ n₅)

Nat:mul:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Nat → Nat} x₀ → Nat → Nat
Nat:mul:~uf x₀ f₁ x₂ = Nat:mul:match~u1 (λ (x₃ : Nat) → λ (x₄ : Nat) → Nat:below {λ (x₅ : Nat) → Nat → Nat} x₄ → Nat) x₂ x₀ (λ (x₃ : Nat) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Nat} (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (λ (a₃ : Nat) → λ (b₄ : Nat) → λ (x₅ : Nat:below {λ (x₅ : Nat) → Nat → Nat} (Nat:succ b₄)) → Nat:add (PProd.fst₂ {(λ (x₆ : Nat) → Nat → Nat) b₄} {Nat:rec {λ (t₆ : Nat) → Set} PUnit (λ (n₆ : Nat) → λ (nih₇ : Set) → PProd ((λ (x₈ : Nat) → Nat → Nat) n₆) nih₇) b₄} x₅ a₃) a₃) f₁

Nat:mul : Nat → Nat → Nat
Nat:mul x₀ x₁ = Nat:brecOn {λ (x₂ : Nat) → Nat → Nat} x₁ Nat:mul:~uf x₀

Unit : Set
Unit = PUnit

Unit:unit : Unit
Unit:unit = PUnit:unit

Nat:pow:match~u1 : (motive₀ : Nat → Set) → (x₁ : Nat) → (Unit → motive₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ x₁
Nat:pow:match~u1 motive₀ x₁ h1₂ h2₃ = Nat:casesOn {λ (x₄ : Nat) → motive₀ x₄} x₁ (h1₂ Unit:unit) (λ (n₄ : Nat) → h2₃ n₄)

Nat:pow:~uf : Nat → (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Nat} x₀ → Nat
Nat:pow:~uf m₀ x₁ f₂ = Nat:pow:match~u1 (λ (x₃ : Nat) → Nat:below {λ (x₄ : Nat) → Nat} x₃ → Nat) x₁ (λ (x₃ : Unit) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat} (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄) (λ (n₃ : Nat) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat} (Nat:succ n₃)) → Nat:mul (PProd.fst₂ {(λ (x₅ : Nat) → Nat) n₃} {Nat:rec {λ (t₅ : Nat) → Set} PUnit (λ (n₅ : Nat) → λ (nih₆ : Set) → PProd ((λ (x₇ : Nat) → Nat) n₅) nih₆) n₃} x₄) m₀) f₂

Nat:pow : Nat → Nat → Nat
Nat:pow m₀ x₁ = Nat:brecOn {λ (x₂ : Nat) → Nat} x₁ (Nat:pow:~uf m₀)

record NatPow (α₀ : Set) : Set where
  constructor NatPow:mk
  field
    pow₁ : α₀ → Nat → α₀

postulate NatPow:rec : {α₀ : Set} → {motive₁ : NatPow α₀ → Set} → ((pow₂ : α₀ → Nat → α₀) → motive₁ (NatPow:mk {α₀} pow₂)) → (t₂ : NatPow α₀) → motive₁ t₂

instNatPowNat : NatPow Nat
instNatPowNat = NatPow:mk {Nat} Nat:pow

NatPow:pow : {α₀ : Set} → ⦃ _ : NatPow α₀ ⦄ → α₀ → Nat → α₀
NatPow:pow {α₀} ⦃ self₁ ⦄ = NatPow.pow₁ {α₀} self₁

instPowNat : {α₀ : Set} → ⦃ _ : NatPow α₀ ⦄ → Pow α₀ Nat
instPowNat {α₀} ⦃ inst₁ ⦄ = Pow:mk {α₀} {Nat} (λ (a₂ : α₀) → λ (n₃ : Nat) → NatPow:pow {α₀} ⦃ inst₁ ⦄ a₂ n₃)

record BitVec (w₀ : Nat) : Set where
  constructor BitVec:ofFin
  field
    toFin₁ : Fin (HPow:hPow {Nat} {Nat} {Nat} ⦃ instHPow {Nat} {Nat} ⦃ instPowNat {Nat} ⦃ instNatPowNat ⦄ ⦄ ⦄ (OfNat:ofNat {Nat} 2 ⦃ instOfNatNat 2 ⦄) w₀)

postulate BitVec:rec : {w₀ : Nat} → {motive₁ : BitVec w₀ → Set} → ((toFin₂ : Fin (HPow:hPow {Nat} {Nat} {Nat} ⦃ instHPow {Nat} {Nat} ⦃ instPowNat {Nat} ⦃ instNatPowNat ⦄ ⦄ ⦄ (OfNat:ofNat {Nat} 2 ⦃ instOfNatNat 2 ⦄) w₀)) → motive₁ (BitVec:ofFin {w₀} toFin₂)) → (t₂ : BitVec w₀) → motive₁ t₂

data False : Set where

postulate False:rec : (motive₀ : False → Set) → (t₁ : False) → motive₀ t₁

False:elim : {C₀ : Set} → False → C₀
False:elim {C₀} h₁ = False:rec (λ (x₂ : False) → C₀) h₁

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

Nat:le:casesOn : {n₀ : Nat} → {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} → {a₂ : Nat} → (t₃ : Nat:le n₀ a₂) → motive₁ n₀ (Nat:le:refl {n₀}) → ({m₄ : Nat} → (a₅ : Nat:le n₀ m₄) → motive₁ (Nat:succ m₄) (Nat:le:step {n₀} {m₄} a₅)) → motive₁ a₂ t₃
Nat:le:casesOn {n₀} {motive₁} {a₂} t₃ refl₄ step₅ = Nat:le:rec {n₀} {motive₁} refl₄ (λ {m₆ : Nat} → λ (a₇ : Nat:le n₀ m₆) → λ (aih₈ : motive₁ m₆ a₇) → step₅ {m₆} a₇) {a₂} t₃

Eq:ndrec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : α₀ → Set} → motive₂ a₁ → {b₃ : α₀} → Eq {α₀} a₁ b₃ → motive₂ b₃
Eq:ndrec {α₀} {a₁} {motive₂} m₃ {b₄} h₅ = Eq:rec {α₀} {a₁} {λ (x₆ : α₀) → λ (x₇ : Eq {α₀} a₁ x₆) → motive₂ x₆} m₃ {b₄} h₅

Nat:noConfusionType : Set → Nat → Nat → Set
Nat:noConfusionType P₀ t₁ t₂ = Nat:casesOn {λ (t₃ : Nat) → Set} t₁ (Nat:casesOn {λ (t₃ : Nat) → Set} t₂ (P₀ → P₀) (λ (n₃ : Nat) → P₀)) (λ (n₃ : Nat) → Nat:casesOn {λ (t₄ : Nat) → Set} t₂ P₀ (λ (n₄ : Nat) → (Eq {Nat} n₃ n₄ → P₀) → P₀))

Nat:noConfusion : {P₀ : Set} → {t₁ : Nat} → {t₂ : Nat} → Eq {Nat} t₁ t₂ → Nat:noConfusionType P₀ t₁ t₂
Nat:noConfusion {P₀} {t₁} {t₂} eq₃ = Eq:ndrec {Nat} {t₁} {λ (t₄ : Nat) → Nat:noConfusionType P₀ t₁ t₄} (Nat:casesOn {λ (t₄ : Nat) → Nat:noConfusionType P₀ t₄ t₄} t₁ (λ (k₄ : P₀) → k₄) (λ (n₄ : Nat) → λ (k₅ : Eq {Nat} n₄ n₄ → P₀) → k₅ (Eq:refl {Nat} n₄))) {t₂} eq₃

instLENat : LE Nat
instLENat = LE:mk {Nat} Nat:le

rfl : {α₀ : Set} → {a₁ : α₀} → Eq {α₀} a₁ a₁
rfl {α₀} {a₁} = Eq:refl {α₀} a₁

-- theorem
opaque
  Nat:not~usucc~ule~uzero : (n₀ : Nat) → LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₀) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) → False
  Nat:not~usucc~ule~uzero n₀ = let this₁ : (m₁ : Nat) → Eq {Nat} m₁ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) → LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₀) m₁ → False; this₁ = λ (x₁ : Nat) → λ (hm₂ : Eq {Nat} x₁ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → λ (hle₃ : LE:le {Nat} ⦃ instLENat ⦄ (Nat:succ n₀) x₁) → Nat:le:casesOn {Nat:succ n₀} {λ (m₄ : Nat) → λ (x₅ : Nat:le (Nat:succ n₀) m₄) → Eq {Nat} m₄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) → False} {x₁} hle₃ (λ (h₄ : Eq {Nat} (Nat:succ n₀) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → Nat:noConfusion {False} {Nat:succ n₀} {OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄} h₄) (λ {m₄ : Nat} → λ (x₅ : Nat:le (Nat:succ n₀) m₄) → λ (h₆ : Eq {Nat} (Nat:succ m₄) (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → Nat:noConfusion {False} {Nat:succ m₄} {OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄} h₆) hm₂ in this₁ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (rfl {Nat} {OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄})

data Nat:le:below {n₀ : Nat} {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} : {a₂ : Nat} → Nat:le n₀ a₂ → Set where
  Nat:le:below:refl : Nat:le:below {n₀} {motive₁} {n₀} (Nat:le:refl {n₀})
  Nat:le:below:step : {m₂ : Nat} → (a₃ : Nat:le n₀ m₂) → Nat:le:below {n₀} {motive₁} {m₂} a₃ → motive₁ m₂ a₃ → Nat:le:below {n₀} {motive₁} {Nat:succ m₂} (Nat:le:step {n₀} {m₂} a₃)

postulate Nat:le:below:rec : {n₀ : Nat} → {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} → {motive₂ : {a₂ : Nat} → (t₃ : Nat:le n₀ a₂) → Nat:le:below {n₀} {motive₁} {a₂} t₃ → Set} → motive₂ {n₀} (Nat:le:refl {n₀}) (Nat:le:below:refl {n₀} {motive₁}) → ({m₃ : Nat} → (a₄ : Nat:le n₀ m₃) → (ih₅ : Nat:le:below {n₀} {motive₁} {m₃} a₄) → (aih₆ : motive₁ m₃ a₄) → motive₂ {m₃} a₄ ih₅ → motive₂ {Nat:succ m₃} (Nat:le:step {n₀} {m₃} a₄) (Nat:le:below:step {n₀} {motive₁} {m₃} a₄ ih₅ aih₆)) → {a₃ : Nat} → {t₄ : Nat:le n₀ a₃} → (t₅ : Nat:le:below {n₀} {motive₁} {a₃} t₄) → motive₂ {a₃} t₄ t₅

-- theorem
opaque
  Nat:le:brecOn : {n₀ : Nat} → {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} → {a₂ : Nat} → (t₃ : Nat:le n₀ a₂) → ((a₄ : Nat) → (t₅ : Nat:le n₀ a₄) → Nat:le:below {n₀} {motive₁} {a₄} t₅ → motive₁ a₄ t₅) → motive₁ a₂ t₃
  Nat:le:brecOn {n₀} {motive₁} {a₂} t₃ F1₄ = F1₄ a₂ t₃ (Nat:le:rec {n₀} {Nat:le:below {n₀} {motive₁}} (Nat:le:below:refl {n₀} {motive₁}) (λ {m₅ : Nat} → λ (a₆ : Nat:le n₀ m₅) → λ (ih₇ : Nat:le:below {n₀} {motive₁} {m₅} a₆) → Nat:le:below:step {n₀} {motive₁} {m₅} a₆ ih₇ (F1₄ m₅ a₆ ih₇)) {a₂} t₃)

-- theorem
opaque
  Eq:symm : {α₀ : Set} → {a₁ : α₀} → {b₂ : α₀} → Eq {α₀} a₁ b₂ → Eq {α₀} b₂ a₁
  Eq:symm {α₀} {a₁} {b₂} h₃ = Eq:rec {α₀} {a₁} {λ (x₄ : α₀) → λ (h₅ : Eq {α₀} a₁ x₄) → Eq {α₀} x₄ a₁} (rfl {α₀} {a₁}) {b₂} h₃

data HEq {α₀ : Set} : α₀ → {β₁ : Set} → β₁ → Set where
  HEq:refl : (a₁ : α₀) → HEq {α₀} a₁ {α₀} a₁

postulate HEq:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : {β₂ : Set} → (a₃ : β₂) → HEq {α₀} a₁ {β₂} a₃ → Set} → motive₂ {α₀} a₁ (HEq:refl {α₀} a₁) → {β₃ : Set} → {a₄ : β₃} → (t₅ : HEq {α₀} a₁ {β₃} a₄) → motive₂ {β₃} a₄ t₅

Nat:le:below:casesOn : {n₀ : Nat} → {motive₁ : (a₁ : Nat) → Nat:le n₀ a₁ → Set} → {motive₂ : {a₂ : Nat} → (t₃ : Nat:le n₀ a₂) → Nat:le:below {n₀} {motive₁} {a₂} t₃ → Set} → {a₃ : Nat} → {t₄ : Nat:le n₀ a₃} → (t₅ : Nat:le:below {n₀} {motive₁} {a₃} t₄) → motive₂ {n₀} (Nat:le:refl {n₀}) (Nat:le:below:refl {n₀} {motive₁}) → ({m₆ : Nat} → (a₇ : Nat:le n₀ m₆) → (ih₈ : Nat:le:below {n₀} {motive₁} {m₆} a₇) → (aih₉ : motive₁ m₆ a₇) → motive₂ {Nat:succ m₆} (Nat:le:step {n₀} {m₆} a₇) (Nat:le:below:step {n₀} {motive₁} {m₆} a₇ ih₈ aih₉)) → motive₂ {a₃} t₄ t₅
Nat:le:below:casesOn {n₀} {motive₁} {motive₂} {a₃} {t₄} t₅ refl₆ step₇ = Nat:le:below:rec {n₀} {motive₁} {motive₂} refl₆ (λ {m₈ : Nat} → λ (a₉ : Nat:le n₀ m₈) → λ (ih₁₀ : Nat:le:below {n₀} {motive₁} {m₈} a₉) → λ (aih₁₁ : motive₁ m₈ a₉) → λ (ihih₁₂ : motive₂ {m₈} a₉ ih₁₀) → step₇ {m₈} a₉ ih₁₀ aih₁₁) {a₃} {t₄} t₅

cast : {α₀ : Set} → {β₁ : Set} → Eq {Set} α₀ β₁ → α₀ → β₁
cast {α₀} {β₁} h₂ a₃ = Eq:rec {Set} {α₀} {λ (x₄ : Set) → λ (x₅ : Eq {Set} α₀ x₄) → x₄} a₃ {β₁} h₂

-- theorem
opaque
  eq~uof~uheq : {α₀ : Set} → {a₁ : α₀} → {a₂ : α₀} → HEq {α₀} a₁ {α₀} a₂ → Eq {α₀} a₁ a₂
  eq~uof~uheq {α₀} {a₁} {a₂} h₃ = let this₄ : (α₄ : Set) → (β₅ : Set) → (a₆ : α₄) → (b₇ : β₅) → HEq {α₄} a₆ {β₅} b₇ → (h₈ : Eq {Set} α₄ β₅) → Eq {β₅} (cast {α₄} {β₅} h₈ a₆) b₇; this₄ = λ (x₄ : Set) → λ (x₅ : Set) → λ (x₆ : x₄) → λ (x₇ : x₅) → λ (h₈ : HEq {x₄} x₆ {x₅} x₇) → HEq:rec {x₄} {x₆} {λ {x₉ : Set} → λ (x₁₀ : x₉) → λ (x₁₁ : HEq {x₄} x₆ {x₉} x₁₀) → (h₁₂ : Eq {Set} x₄ x₉) → Eq {x₉} (cast {x₄} {x₉} h₁₂ x₆) x₁₀} (λ (x₉ : Eq {Set} x₄ x₄) → rfl {x₄} {cast {x₄} {x₄} x₉ x₆}) {x₅} {x₇} h₈ in this₄ α₀ α₀ a₁ a₂ h₃ (rfl {Set} {α₀})

~uprivate:Init:Prelude:~n0:Nat:succ~ule~usucc:match~u1~u7 : {n₀ : Nat} → (funType1₁ : {m₁ : Nat} → LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁ → Set) → (motive₂ : (m₂ : Nat) → (x₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₂) → Nat:le:below {n₀} {λ (m₄ : Nat) → λ (x₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₄) → funType1₁ {m₄} x₅} {m₂} x₃ → Set) → (m₃ : Nat) → (x₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₃) → (below₅ : Nat:le:below {n₀} {λ (m₅ : Nat) → λ (x₆ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₅) → funType1₁ {m₅} x₆} {m₃} x₄) → (Unit → motive₂ n₀ (Nat:le:refl {n₀}) (Nat:le:below:refl {n₀} {λ (m₆ : Nat) → λ (x₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₆) → funType1₁ {m₆} x₇})) → ((m₆ : Nat) → (h₇ : Nat:le n₀ m₆) → (ih₈ : Nat:le:below {n₀} {λ (m₈ : Nat) → λ (x₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₈) → funType1₁ {m₈} x₉} {m₆} h₇) → (aih₉ : funType1₁ {m₆} h₇) → motive₂ (Nat:succ m₆) (Nat:le:step {n₀} {m₆} h₇) (Nat:le:below:step {n₀} {λ (m₁₀ : Nat) → λ (x₁₁ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₀) → funType1₁ {m₁₀} x₁₁} {m₆} h₇ ih₈ aih₉)) → motive₂ m₃ x₄ below₅
~uprivate:Init:Prelude:~n0:Nat:succ~ule~usucc:match~u1~u7 {n₀} funType1₁ motive₂ m₃ x₄ below₅ h1₆ h2₇ = Nat:le:below:casesOn {n₀} {λ (m₈ : Nat) → λ (x₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₈) → funType1₁ {m₈} x₉} {λ {a₈ : Nat} → λ (t₉ : Nat:le n₀ a₈) → λ (x₁₀ : Nat:le:below {n₀} {λ (m₁₀ : Nat) → λ (x₁₁ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₀) → funType1₁ {m₁₀} x₁₁} {a₈} t₉) → Eq {Nat} m₃ a₈ → HEq {LE:le {Nat} ⦃ instLENat ⦄ n₀ m₃} x₄ {Nat:le n₀ a₈} t₉ → HEq {Nat:le:below {n₀} {λ (m₁₁ : Nat) → λ (x₁₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₁) → funType1₁ {m₁₁} x₁₂} {m₃} x₄} below₅ {Nat:le:below {n₀} {λ (m₁₁ : Nat) → λ (x₁₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₁) → funType1₁ {m₁₁} x₁₂} {a₈} t₉} x₁₀ → motive₂ m₃ x₄ below₅} {m₃} {x₄} below₅ (λ (h₈ : Eq {Nat} m₃ n₀) → Eq:ndrec {Nat} {n₀} {λ (m₉ : Nat) → (x₁₀ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₉) → (below₁₁ : Nat:le:below {n₀} {λ (m₁₁ : Nat) → λ (x₁₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₁) → funType1₁ {m₁₁} x₁₂} {m₉} x₁₀) → HEq {LE:le {Nat} ⦃ instLENat ⦄ n₀ m₉} x₁₀ {Nat:le n₀ n₀} (Nat:le:refl {n₀}) → HEq {Nat:le:below {n₀} {λ (m₁₂ : Nat) → λ (x₁₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₂) → funType1₁ {m₁₂} x₁₃} {m₉} x₁₀} below₁₁ {Nat:le:below {n₀} {λ (m₁₂ : Nat) → λ (x₁₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₂) → funType1₁ {m₁₂} x₁₃} {n₀} (Nat:le:refl {n₀})} (Nat:le:below:refl {n₀} {λ (m₁₂ : Nat) → λ (x₁₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₂) → funType1₁ {m₁₂} x₁₃}) → motive₂ m₉ x₁₀ below₁₁} (λ (x₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ n₀) → λ (below₁₀ : Nat:le:below {n₀} {λ (m₁₀ : Nat) → λ (x₁₁ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₀) → funType1₁ {m₁₀} x₁₁} {n₀} x₉) → λ (h₁₁ : HEq {LE:le {Nat} ⦃ instLENat ⦄ n₀ n₀} x₉ {Nat:le n₀ n₀} (Nat:le:refl {n₀})) → Eq:ndrec {LE:le {Nat} ⦃ instLENat ⦄ n₀ n₀} {Nat:le:refl {n₀}} {λ (x₁₂ : LE:le {Nat} ⦃ instLENat ⦄ n₀ n₀) → (below₁₃ : Nat:le:below {n₀} {λ (m₁₃ : Nat) → λ (x₁₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₃) → funType1₁ {m₁₃} x₁₄} {n₀} x₁₂) → HEq {Nat:le:below {n₀} {λ (m₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} x₁₅} {n₀} x₁₂} below₁₃ {Nat:le:below {n₀} {λ (m₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} x₁₅} {n₀} (Nat:le:refl {n₀})} (Nat:le:below:refl {n₀} {λ (m₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} x₁₅}) → motive₂ n₀ x₁₂ below₁₃} (λ (below₁₂ : Nat:le:below {n₀} {λ (m₁₂ : Nat) → λ (x₁₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₂) → funType1₁ {m₁₂} x₁₃} {n₀} (Nat:le:refl {n₀})) → λ (h₁₃ : HEq {Nat:le:below {n₀} {λ (m₁₃ : Nat) → λ (x₁₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₃) → funType1₁ {m₁₃} x₁₄} {n₀} (Nat:le:refl {n₀})} below₁₂ {Nat:le:below {n₀} {λ (m₁₃ : Nat) → λ (x₁₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₃) → funType1₁ {m₁₃} x₁₄} {n₀} (Nat:le:refl {n₀})} (Nat:le:below:refl {n₀} {λ (m₁₃ : Nat) → λ (x₁₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₃) → funType1₁ {m₁₃} x₁₄})) → Eq:ndrec {Nat:le:below {n₀} {λ (m₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} x₁₅} {n₀} (Nat:le:refl {n₀})} {Nat:le:below:refl {n₀} {λ (m₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} x₁₅}} {λ (below₁₄ : Nat:le:below {n₀} {λ (m₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} x₁₅} {n₀} (Nat:le:refl {n₀})) → motive₂ n₀ (Nat:le:refl {n₀}) below₁₄} (h1₆ Unit:unit) {below₁₂} (Eq:symm {Nat:le:below {n₀} {λ (m₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} x₁₅} {n₀} (Nat:le:refl {n₀})} {below₁₂} {Nat:le:below:refl {n₀} {λ (m₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} x₁₅}} (eq~uof~uheq {Nat:le:below {n₀} {λ (m₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} x₁₅} {n₀} (Nat:le:refl {n₀})} {below₁₂} {Nat:le:below:refl {n₀} {λ (m₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} x₁₅}} h₁₃))) {x₉} (Eq:symm {LE:le {Nat} ⦃ instLENat ⦄ n₀ n₀} {x₉} {Nat:le:refl {n₀}} (eq~uof~uheq {LE:le {Nat} ⦃ instLENat ⦄ n₀ n₀} {x₉} {Nat:le:refl {n₀}} h₁₁)) below₁₀) {m₃} (Eq:symm {Nat} {m₃} {n₀} h₈) x₄ below₅) (λ {m₈ : Nat} → λ (a₉ : Nat:le n₀ m₈) → λ (ih₁₀ : Nat:le:below {n₀} {λ (m₁₀ : Nat) → λ (x₁₁ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₀) → funType1₁ {m₁₀} x₁₁} {m₈} a₉) → λ (aih₁₁ : funType1₁ {m₈} a₉) → λ (h₁₂ : Eq {Nat} m₃ (Nat:succ m₈)) → Eq:ndrec {Nat} {Nat:succ m₈} {λ (m₁₃ : Nat) → (x₁₄ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₃) → (below₁₅ : Nat:le:below {n₀} {λ (m₁₅ : Nat) → λ (x₁₆ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₅) → funType1₁ {m₁₅} x₁₆} {m₁₃} x₁₄) → HEq {LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₃} x₁₄ {Nat:le n₀ (Nat:succ m₈)} (Nat:le:step {n₀} {m₈} a₉) → HEq {Nat:le:below {n₀} {λ (m₁₆ : Nat) → λ (x₁₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₆) → funType1₁ {m₁₆} x₁₇} {m₁₃} x₁₄} below₁₅ {Nat:le:below {n₀} {λ (m₁₆ : Nat) → λ (x₁₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₆) → funType1₁ {m₁₆} x₁₇} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)} (Nat:le:below:step {n₀} {λ (m₁₆ : Nat) → λ (x₁₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₆) → funType1₁ {m₁₆} x₁₇} {m₈} a₉ ih₁₀ aih₁₁) → motive₂ m₁₃ x₁₄ below₁₅} (λ (x₁₃ : LE:le {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₈)) → λ (below₁₄ : Nat:le:below {n₀} {λ (m₁₄ : Nat) → λ (x₁₅ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₄) → funType1₁ {m₁₄} x₁₅} {Nat:succ m₈} x₁₃) → λ (h₁₅ : HEq {LE:le {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₈)} x₁₃ {Nat:le n₀ (Nat:succ m₈)} (Nat:le:step {n₀} {m₈} a₉)) → Eq:ndrec {LE:le {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₈)} {Nat:le:step {n₀} {m₈} a₉} {λ (x₁₆ : LE:le {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₈)) → (below₁₇ : Nat:le:below {n₀} {λ (m₁₇ : Nat) → λ (x₁₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₇) → funType1₁ {m₁₇} x₁₈} {Nat:succ m₈} x₁₆) → HEq {Nat:le:below {n₀} {λ (m₁₈ : Nat) → λ (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} x₁₉} {Nat:succ m₈} x₁₆} below₁₇ {Nat:le:below {n₀} {λ (m₁₈ : Nat) → λ (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} x₁₉} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)} (Nat:le:below:step {n₀} {λ (m₁₈ : Nat) → λ (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} x₁₉} {m₈} a₉ ih₁₀ aih₁₁) → motive₂ (Nat:succ m₈) x₁₆ below₁₇} (λ (below₁₆ : Nat:le:below {n₀} {λ (m₁₆ : Nat) → λ (x₁₇ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₆) → funType1₁ {m₁₆} x₁₇} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)) → λ (h₁₇ : HEq {Nat:le:below {n₀} {λ (m₁₇ : Nat) → λ (x₁₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₇) → funType1₁ {m₁₇} x₁₈} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)} below₁₆ {Nat:le:below {n₀} {λ (m₁₇ : Nat) → λ (x₁₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₇) → funType1₁ {m₁₇} x₁₈} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)} (Nat:le:below:step {n₀} {λ (m₁₇ : Nat) → λ (x₁₈ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₇) → funType1₁ {m₁₇} x₁₈} {m₈} a₉ ih₁₀ aih₁₁)) → Eq:ndrec {Nat:le:below {n₀} {λ (m₁₈ : Nat) → λ (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} x₁₉} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)} {Nat:le:below:step {n₀} {λ (m₁₈ : Nat) → λ (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} x₁₉} {m₈} a₉ ih₁₀ aih₁₁} {λ (below₁₈ : Nat:le:below {n₀} {λ (m₁₈ : Nat) → λ (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} x₁₉} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)) → motive₂ (Nat:succ m₈) (Nat:le:step {n₀} {m₈} a₉) below₁₈} (h2₇ m₈ a₉ ih₁₀ aih₁₁) {below₁₆} (Eq:symm {Nat:le:below {n₀} {λ (m₁₈ : Nat) → λ (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} x₁₉} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)} {below₁₆} {Nat:le:below:step {n₀} {λ (m₁₈ : Nat) → λ (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} x₁₉} {m₈} a₉ ih₁₀ aih₁₁} (eq~uof~uheq {Nat:le:below {n₀} {λ (m₁₈ : Nat) → λ (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} x₁₉} {Nat:succ m₈} (Nat:le:step {n₀} {m₈} a₉)} {below₁₆} {Nat:le:below:step {n₀} {λ (m₁₈ : Nat) → λ (x₁₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₁₈) → funType1₁ {m₁₈} x₁₉} {m₈} a₉ ih₁₀ aih₁₁} h₁₇))) {x₁₃} (Eq:symm {LE:le {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₈)} {x₁₃} {Nat:le:step {n₀} {m₈} a₉} (eq~uof~uheq {LE:le {Nat} ⦃ instLENat ⦄ n₀ (Nat:succ m₈)} {x₁₃} {Nat:le:step {n₀} {m₈} a₉} h₁₅)) below₁₄) {m₃} (Eq:symm {Nat} {m₃} {Nat:succ m₈} h₁₂) x₄ below₅) (Eq:refl {Nat} m₃) (HEq:refl {LE:le {Nat} ⦃ instLENat ⦄ n₀ m₃} x₄) (HEq:refl {Nat:le:below {n₀} {λ (m₈ : Nat) → λ (x₉ : LE:le {Nat} ⦃ instLENat ⦄ n₀ m₈) → funType1₁ {m₈} x₉} {m₃} x₄} below₅)

instAddNat : Add Nat
instAddNat = Add:mk {Nat} Nat:add

instHAdd : {α₀ : Set} → ⦃ _ : Add α₀ ⦄ → HAdd α₀ α₀ α₀
instHAdd {α₀} ⦃ inst₁ ⦄ = HAdd:mk {α₀} {α₀} {α₀} (λ (a₂ : α₀) → λ (b₃ : α₀) → Add:add {α₀} ⦃ inst₁ ⦄ a₂ b₃)

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

-- theorem
opaque
  Nat:zero~ult~usucc : (n₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₀)
  Nat:zero~ult~usucc n₀ = Nat:succ~ule~usucc {OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄} {n₀} (Nat:zero~ule n₀)

~uprivate:Init:Prelude:~n0:Nat:add~upos~uright:match~u1~u1 : (motive₀ : (x₀ : Nat) → Nat → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₀ → Set) → (x₁ : Nat) → (x₂ : Nat) → (x₃ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₁) → ((x₄ : Nat) → (h₅ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) Nat:zero) → motive₀ Nat:zero x₄ h₅) → ((n₄ : Nat) → (x₅ : Nat) → (x₆ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₄)) → motive₀ (Nat:succ n₄) x₅ x₆) → motive₀ x₁ x₂ x₃
~uprivate:Init:Prelude:~n0:Nat:add~upos~uright:match~u1~u1 motive₀ x₁ x₂ x₃ h1₄ h2₅ = Nat:casesOn {λ (x₆ : Nat) → (x₇ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₆) → motive₀ x₆ x₂ x₇} x₁ (λ (x₆ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) Nat:zero) → h1₄ x₂ x₆) (λ (n₆ : Nat) → λ (x₇ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₆)) → h2₅ n₆ x₂ x₇) x₃

-- theorem
opaque
  Nat:add~upos~uright : {b₀ : Nat} → (a₁ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) b₀ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ a₁ b₀)
  Nat:add~upos~uright {x₀} x₁ x₂ = ~uprivate:Init:Prelude:~n0:Nat:add~upos~uright:match~u1~u1 (λ (x₃ : Nat) → λ (x₄ : Nat) → λ (x₅ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₃) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ x₄ x₃)) x₀ x₁ x₂ (λ (x₃ : Nat) → λ (h₄ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) Nat:zero) → False:elim {LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ x₃ Nat:zero)} (Nat:not~usucc~ule~uzero (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) h₄)) (λ (n₃ : Nat) → λ (x₄ : Nat) → λ (x₅ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₃)) → Nat:zero~ult~usucc (Nat:add x₄ n₃))

~uprivate:Init:Prelude:~n0:Nat:mul~upos:match~u1~u1:~ushare:~n1 : Set
~uprivate:Init:Prelude:~n0:Nat:mul~upos:match~u1~u1:~ushare:~n1 = (x₀ : Nat) → (x₁ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₀ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₁ → Set

~uprivate:Init:Prelude:~n0:Nat:mul~upos:match~u1~u1 : (motive₀ : ~uprivate:Init:Prelude:~n0:Nat:mul~upos:match~u1~u1:~ushare:~n1) → (x₁ : Nat) → (x₂ : Nat) → (x₃ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₁) → (x₄ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₂) → ((x₅ : Nat) → (x₆ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₅) → (hb₇ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) Nat:zero) → motive₀ x₅ Nat:zero x₆ hb₇) → ((x₅ : Nat) → (n₆ : Nat) → (ha₇ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₅) → (x₈ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₆)) → motive₀ x₅ (Nat:succ n₆) ha₇ x₈) → motive₀ x₁ x₂ x₃ x₄
~uprivate:Init:Prelude:~n0:Nat:mul~upos:match~u1~u1 motive₀ x₁ x₂ x₃ x₄ h1₅ h2₆ = Nat:casesOn {λ (x₇ : Nat) → (x₈ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₇) → motive₀ x₁ x₇ x₃ x₈} x₂ (λ (x₇ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) Nat:zero) → h1₅ x₁ x₃ x₇) (λ (n₇ : Nat) → λ (x₈ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₇)) → h2₆ x₁ n₇ x₃ x₈) x₄

record Mul (α₀ : Set) : Set where
  constructor Mul:mk
  field
    mul₁ : α₀ → α₀ → α₀

postulate Mul:rec : {α₀ : Set} → {motive₁ : Mul α₀ → Set} → ((mul₂ : α₀ → α₀ → α₀) → motive₁ (Mul:mk {α₀} mul₂)) → (t₂ : Mul α₀) → motive₁ t₂

Mul:mul : {α₀ : Set} → ⦃ _ : Mul α₀ ⦄ → α₀ → α₀ → α₀
Mul:mul {α₀} ⦃ self₁ ⦄ = Mul.mul₁ {α₀} self₁

instHMul : {α₀ : Set} → ⦃ _ : Mul α₀ ⦄ → HMul α₀ α₀ α₀
instHMul {α₀} ⦃ inst₁ ⦄ = HMul:mk {α₀} {α₀} {α₀} (λ (a₂ : α₀) → λ (b₃ : α₀) → Mul:mul {α₀} ⦃ inst₁ ⦄ a₂ b₃)

instMulNat : Mul Nat
instMulNat = Mul:mk {Nat} Nat:mul

-- theorem
opaque
  Nat:mul~upos : {n₀ : Nat} → {m₁ : Nat} → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) n₀ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) m₁ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HMul:hMul {Nat} {Nat} {Nat} ⦃ instHMul {Nat} ⦃ instMulNat ⦄ ⦄ n₀ m₁)
  Nat:mul~upos {x₀} {x₁} x₂ x₃ = ~uprivate:Init:Prelude:~n0:Nat:mul~upos:match~u1~u1 (λ (x₄ : Nat) → λ (x₅ : Nat) → λ (x₆ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₄) → λ (x₇ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₅) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HMul:hMul {Nat} {Nat} {Nat} ⦃ instHMul {Nat} ⦃ instMulNat ⦄ ⦄ x₄ x₅)) x₀ x₁ x₂ x₃ (λ (x₄ : Nat) → λ (x₅ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₄) → λ (hb₆ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) Nat:zero) → False:elim {LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HMul:hMul {Nat} {Nat} {Nat} ⦃ instHMul {Nat} ⦃ instMulNat ⦄ ⦄ x₄ Nat:zero)} (Nat:not~usucc~ule~uzero (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) hb₆)) (λ (x₄ : Nat) → λ (n₅ : Nat) → λ (ha₆ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) x₄) → λ (x₇ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (Nat:succ n₅)) → Nat:add~upos~uright {x₄} (Nat:mul x₄ n₅) ha₆)

~uprivate:Init:Prelude:~n0:Nat:pow~upos:match~u1~u1 : {a₀ : Nat} → (motive₁ : Nat → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) a₀ → Set) → (x₂ : Nat) → (x₃ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) a₀) → ((x₄ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) a₀) → motive₁ Nat:zero x₄) → ((n₄ : Nat) → (h₅ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) a₀) → motive₁ (Nat:succ n₄) h₅) → motive₁ x₂ x₃
~uprivate:Init:Prelude:~n0:Nat:pow~upos:match~u1~u1 {a₀} motive₁ x₂ x₃ h1₄ h2₅ = Nat:casesOn {λ (x₆ : Nat) → motive₁ x₆ x₃} x₂ (h1₄ x₃) (λ (n₆ : Nat) → h2₅ n₆ x₃)

Nat:pow~upos:~uf : {a₀ : Nat} → (x₁ : Nat) → Nat:below {λ (x₂ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) a₀ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HPow:hPow {Nat} {Nat} {Nat} ⦃ instHPow {Nat} {Nat} ⦃ instPowNat {Nat} ⦃ instNatPowNat ⦄ ⦄ ⦄ a₀ x₂)} x₁ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) a₀ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HPow:hPow {Nat} {Nat} {Nat} ⦃ instHPow {Nat} {Nat} ⦃ instPowNat {Nat} ⦃ instNatPowNat ⦄ ⦄ ⦄ a₀ x₁)
Nat:pow~upos:~uf {a₀} x₁ f₂ x₃ = ~uprivate:Init:Prelude:~n0:Nat:pow~upos:match~u1~u1 {a₀} (λ (x₄ : Nat) → λ (x₅ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) a₀) → Nat:below {λ (x₆ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) a₀ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HPow:hPow {Nat} {Nat} {Nat} ⦃ instHPow {Nat} {Nat} ⦃ instPowNat {Nat} ⦃ instNatPowNat ⦄ ⦄ ⦄ a₀ x₆)} x₄ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HPow:hPow {Nat} {Nat} {Nat} ⦃ instHPow {Nat} {Nat} ⦃ instPowNat {Nat} ⦃ instNatPowNat ⦄ ⦄ ⦄ a₀ x₄)) x₁ x₃ (λ (x₄ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) a₀) → λ (x₅ : Nat:below {λ (x₅ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) a₀ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HPow:hPow {Nat} {Nat} {Nat} ⦃ instHPow {Nat} {Nat} ⦃ instPowNat {Nat} ⦃ instNatPowNat ⦄ ⦄ ⦄ a₀ x₅)} Nat:zero) → Nat:zero~ult~usucc (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) (λ (n₄ : Nat) → λ (h₅ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) a₀) → λ (x₆ : Nat:below {λ (x₆ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) a₀ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HPow:hPow {Nat} {Nat} {Nat} ⦃ instHPow {Nat} {Nat} ⦃ instPowNat {Nat} ⦃ instNatPowNat ⦄ ⦄ ⦄ a₀ x₆)} (Nat:succ n₄)) → Nat:mul~upos {Nat:pow a₀ n₄} {a₀} (PProd.fst₂ {(λ (x₇ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) a₀ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HPow:hPow {Nat} {Nat} {Nat} ⦃ instHPow {Nat} {Nat} ⦃ instPowNat {Nat} ⦃ instNatPowNat ⦄ ⦄ ⦄ a₀ x₇)) n₄} {Nat:rec {λ (t₇ : Nat) → Set} PUnit (λ (n₇ : Nat) → λ (nih₈ : Set) → PProd ((λ (x₉ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) a₀ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HPow:hPow {Nat} {Nat} {Nat} ⦃ instHPow {Nat} {Nat} ⦃ instPowNat {Nat} ⦃ instNatPowNat ⦄ ⦄ ⦄ a₀ x₉)) n₇) nih₈) n₄} x₆ h₅) h₅) f₂

-- theorem
opaque
  Nat:pow~upos : {a₀ : Nat} → {n₁ : Nat} → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) a₀ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HPow:hPow {Nat} {Nat} {Nat} ⦃ instHPow {Nat} {Nat} ⦃ instPowNat {Nat} ⦃ instNatPowNat ⦄ ⦄ ⦄ a₀ n₁)
  Nat:pow~upos {a₀} {x₁} x₂ = Nat:brecOn {λ (x₃ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) a₀ → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HPow:hPow {Nat} {Nat} {Nat} ⦃ instHPow {Nat} {Nat} ⦃ instPowNat {Nat} ⦃ instNatPowNat ⦄ ⦄ ⦄ a₀ x₃)} x₁ (Nat:pow~upos:~uf {a₀}) x₂

-- theorem
opaque
  BitVec:ofNat:~uproof~u1 : (n₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (HPow:hPow {Nat} {Nat} {Nat} ⦃ instHPow {Nat} {Nat} ⦃ instPowNat {Nat} ⦃ instNatPowNat ⦄ ⦄ ⦄ (OfNat:ofNat {Nat} 2 ⦃ instOfNatNat 2 ⦄) n₀)
  BitVec:ofNat:~uproof~u1 n₀ = Nat:pow~upos {OfNat:ofNat {Nat} 2 ⦃ instOfNatNat 2 ⦄} {n₀} (Nat:zero~ult~usucc (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))

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

Nat:ble:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → ((x₃ : Nat) → motive₀ Nat:zero x₃) → ((n₃ : Nat) → motive₀ (Nat:succ n₃) Nat:zero) → ((n₃ : Nat) → (m₄ : Nat) → motive₀ (Nat:succ n₃) (Nat:succ m₄)) → motive₀ x₁ x₂
Nat:ble:match~u1 motive₀ x₁ x₂ h1₃ h2₄ h3₅ = Nat:casesOn {λ (x₆ : Nat) → motive₀ x₆ x₂} x₁ (h1₃ x₂) (λ (n₆ : Nat) → Nat:casesOn {λ (x₇ : Nat) → motive₀ (Nat:succ n₆) x₇} x₂ (h2₄ n₆) (λ (n₇ : Nat) → h3₅ n₆ n₇))

Nat:ble:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Nat → Bool} x₀ → Nat → Bool
Nat:ble:~uf x₀ f₁ x₂ = Nat:ble:match~u1 (λ (x₃ : Nat) → λ (x₄ : Nat) → Nat:below {λ (x₅ : Nat) → Nat → Bool} x₃ → Bool) x₀ x₂ (λ (x₃ : Nat) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Bool} Nat:zero) → Bool:true) (λ (n₃ : Nat) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Bool} (Nat:succ n₃)) → Bool:false) (λ (n₃ : Nat) → λ (m₄ : Nat) → λ (x₅ : Nat:below {λ (x₅ : Nat) → Nat → Bool} (Nat:succ n₃)) → PProd.fst₂ {(λ (x₆ : Nat) → Nat → Bool) n₃} {Nat:rec {λ (t₆ : Nat) → Set} PUnit (λ (n₆ : Nat) → λ (nih₇ : Set) → PProd ((λ (x₈ : Nat) → Nat → Bool) n₆) nih₇) n₃} x₅ m₄) f₁

Nat:ble : Nat → Nat → Bool
Nat:ble x₀ x₁ = Nat:brecOn {λ (x₂ : Nat) → Nat → Bool} x₀ Nat:ble:~uf x₁

Bool:casesOn : {motive₀ : Bool → Set} → (t₁ : Bool) → motive₀ Bool:false → motive₀ Bool:true → motive₀ t₁
Bool:casesOn {motive₀} t₁ false₂ true₃ = Bool:rec {motive₀} false₂ true₃ t₁

Bool:ctorIdx : Bool → Nat
Bool:ctorIdx x₀ = Bool:casesOn {λ (x₁ : Bool) → Nat} x₀ 0 1

Eq:casesOn : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → Eq {α₀} a₁ a₂ → Set} → {a₃ : α₀} → (t₄ : Eq {α₀} a₁ a₃) → motive₂ a₁ (Eq:refl {α₀} a₁) → motive₂ a₃ t₄
Eq:casesOn {α₀} {a₁} {motive₂} {a₃} t₄ refl₅ = Eq:rec {α₀} {a₁} {motive₂} refl₅ {a₃} t₄

Nat:beq:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → (Unit → motive₀ Nat:zero Nat:zero) → ((n₃ : Nat) → motive₀ Nat:zero (Nat:succ n₃)) → ((n₃ : Nat) → motive₀ (Nat:succ n₃) Nat:zero) → ((n₃ : Nat) → (m₄ : Nat) → motive₀ (Nat:succ n₃) (Nat:succ m₄)) → motive₀ x₁ x₂
Nat:beq:match~u1 motive₀ x₁ x₂ h1₃ h2₄ h3₅ h4₆ = Nat:casesOn {λ (x₇ : Nat) → motive₀ x₇ x₂} x₁ (Nat:casesOn {λ (x₇ : Nat) → motive₀ Nat:zero x₇} x₂ (h1₃ Unit:unit) (λ (n₇ : Nat) → h2₄ n₇)) (λ (n₇ : Nat) → Nat:casesOn {λ (x₈ : Nat) → motive₀ (Nat:succ n₇) x₈} x₂ (h3₅ n₇) (λ (n₈ : Nat) → h4₆ n₇ n₈))

Nat:beq:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Nat → Bool} x₀ → Nat → Bool
Nat:beq:~uf x₀ f₁ x₂ = Nat:beq:match~u1 (λ (x₃ : Nat) → λ (x₄ : Nat) → Nat:below {λ (x₅ : Nat) → Nat → Bool} x₃ → Bool) x₀ x₂ (λ (x₃ : Unit) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Bool} Nat:zero) → Bool:true) (λ (n₃ : Nat) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Bool} Nat:zero) → Bool:false) (λ (n₃ : Nat) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Bool} (Nat:succ n₃)) → Bool:false) (λ (n₃ : Nat) → λ (m₄ : Nat) → λ (x₅ : Nat:below {λ (x₅ : Nat) → Nat → Bool} (Nat:succ n₃)) → PProd.fst₂ {(λ (x₆ : Nat) → Nat → Bool) n₃} {Nat:rec {λ (t₆ : Nat) → Set} PUnit (λ (n₆ : Nat) → λ (nih₇ : Set) → PProd ((λ (x₈ : Nat) → Nat → Bool) n₆) nih₇) n₃} x₅ m₄) f₁

Nat:beq : Nat → Nat → Bool
Nat:beq x₀ x₁ = Nat:brecOn {λ (x₂ : Nat) → Nat → Bool} x₀ Nat:beq:~uf x₁

record True : Set where
  constructor True:intro

postulate True:rec : {motive₀ : True → Set} → motive₀ True:intro → (t₁ : True) → motive₀ t₁

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
  Nat:le~uof~uble~ueq~utrue {n₀} {m₁} h₂ = Nat:brecOn {λ (n₃ : Nat) → {m₄ : Nat} → Eq {Bool} (Nat:ble n₃ m₄) Bool:true → LE:le {Nat} ⦃ instLENat ⦄ n₃ m₄} n₀ Nat:le~uof~uble~ueq~utrue:~uf {m₁} h₂

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

Decidable:casesOn : {p₀ : Set} → {motive₁ : Decidable p₀ → Set} → (t₂ : Decidable p₀) → ((h₃ : Not p₀) → motive₁ (Decidable:isFalse {p₀} h₃)) → ((h₃ : p₀) → motive₁ (Decidable:isTrue {p₀} h₃)) → motive₁ t₂
Decidable:casesOn {p₀} {motive₁} t₂ isFalse₃ isTrue₄ = Decidable:rec {p₀} {motive₁} (λ (h₅ : Not p₀) → isFalse₃ h₅) (λ (h₅ : p₀) → isTrue₄ h₅) t₂

dite : {α₀ : Set} → (c₁ : Set) → ⦃ _ : Decidable c₁ ⦄ → (c₁ → α₀) → (Not c₁ → α₀) → α₀
dite {α₀} c₁ ⦃ h₂ ⦄ t₃ e₄ = Decidable:casesOn {c₁} {λ (x₅ : Decidable c₁) → α₀} h₂ e₄ t₃

Bool:decEq:match~u1 : (motive₀ : Bool → Bool → Set) → (a₁ : Bool) → (b₂ : Bool) → (Unit → motive₀ Bool:false Bool:false) → (Unit → motive₀ Bool:false Bool:true) → (Unit → motive₀ Bool:true Bool:false) → (Unit → motive₀ Bool:true Bool:true) → motive₀ a₁ b₂
Bool:decEq:match~u1 motive₀ a₁ b₂ h1₃ h2₄ h3₅ h4₆ = Bool:casesOn {λ (x₇ : Bool) → motive₀ x₇ b₂} a₁ (Bool:casesOn {λ (x₇ : Bool) → motive₀ Bool:false x₇} b₂ (h1₃ Unit:unit) (h2₄ Unit:unit)) (Bool:casesOn {λ (x₇ : Bool) → motive₀ Bool:true x₇} b₂ (h3₅ Unit:unit) (h4₆ Unit:unit))

Bool:noConfusionType : Set → Bool → Bool → Set
Bool:noConfusionType P₀ t₁ t₂ = Bool:casesOn {λ (t₃ : Bool) → Set} t₁ (Bool:casesOn {λ (t₃ : Bool) → Set} t₂ (P₀ → P₀) P₀) (Bool:casesOn {λ (t₃ : Bool) → Set} t₂ P₀ (P₀ → P₀))

Bool:noConfusion : {P₀ : Set} → {t₁ : Bool} → {t₂ : Bool} → Eq {Bool} t₁ t₂ → Bool:noConfusionType P₀ t₁ t₂
Bool:noConfusion {P₀} {t₁} {t₂} eq₃ = Eq:ndrec {Bool} {t₁} {λ (t₄ : Bool) → Bool:noConfusionType P₀ t₁ t₄} (Bool:casesOn {λ (t₄ : Bool) → Bool:noConfusionType P₀ t₄ t₄} t₁ (λ (k₄ : P₀) → k₄) (λ (k₄ : P₀) → k₄)) {t₂} eq₃

Bool:decEq : (a₀ : Bool) → (b₁ : Bool) → Decidable (Eq {Bool} a₀ b₁)
Bool:decEq a₀ b₁ = Bool:decEq:match~u1 (λ (a₂ : Bool) → λ (b₃ : Bool) → Decidable (Eq {Bool} a₂ b₃)) a₀ b₁ (λ (x₂ : Unit) → Decidable:isTrue {Eq {Bool} Bool:false Bool:false} (rfl {Bool} {Bool:false})) (λ (x₂ : Unit) → Decidable:isFalse {Eq {Bool} Bool:false Bool:true} (λ (h₃ : Eq {Bool} Bool:false Bool:true) → Bool:noConfusion {False} {Bool:false} {Bool:true} h₃)) (λ (x₂ : Unit) → Decidable:isFalse {Eq {Bool} Bool:true Bool:false} (λ (h₃ : Eq {Bool} Bool:true Bool:false) → Bool:noConfusion {False} {Bool:true} {Bool:false} h₃)) (λ (x₂ : Unit) → Decidable:isTrue {Eq {Bool} Bool:true Bool:true} (rfl {Bool} {Bool:true}))

DecidableEq : Set → Set
DecidableEq α₀ = (a₁ : α₀) → (b₂ : α₀) → Decidable (Eq {α₀} a₁ b₂)

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

postulate HSub:rec : {α₀ : Set} → {β₁ : Set} → {γ₂ : Set} → {motive₃ : HSub α₀ β₁ γ₂ → Set} → ((hSub₄ : α₀ → β₁ → γ₂) → motive₃ (HSub:mk {α₀} {β₁} {γ₂} hSub₄)) → (t₄ : HSub α₀ β₁ γ₂) → motive₃ t₄

HSub:hSub : {α₀ : Set} → {β₁ : Set} → {γ₂ : outParam Set} → ⦃ _ : HSub α₀ β₁ γ₂ ⦄ → α₀ → β₁ → γ₂
HSub:hSub {α₀} {β₁} {γ₂} ⦃ self₃ ⦄ = HSub.hSub₃ {α₀} {β₁} {γ₂} self₃

Nat:ctorIdx : Nat → Nat
Nat:ctorIdx x₀ = Nat:casesOn {λ (x₁ : Nat) → Nat} x₀ 0 (λ (n₁ : Nat) → 1)

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

Nat:sub:~uf : (x₀ : Nat) → Nat:below {λ (x₁ : Nat) → Nat → Nat} x₀ → Nat → Nat
Nat:sub:~uf x₀ f₁ x₂ = Nat:mul:match~u1 (λ (x₃ : Nat) → λ (x₄ : Nat) → Nat:below {λ (x₅ : Nat) → Nat → Nat} x₄ → Nat) x₂ x₀ (λ (a₃ : Nat) → λ (x₄ : Nat:below {λ (x₄ : Nat) → Nat → Nat} (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) → a₃) (λ (a₃ : Nat) → λ (b₄ : Nat) → λ (x₅ : Nat:below {λ (x₅ : Nat) → Nat → Nat} (Nat:succ b₄)) → Nat:pred (PProd.fst₂ {(λ (x₆ : Nat) → Nat → Nat) b₄} {Nat:rec {λ (t₆ : Nat) → Set} PUnit (λ (n₆ : Nat) → λ (nih₇ : Set) → PProd ((λ (x₈ : Nat) → Nat → Nat) n₆) nih₇) b₄} x₅ a₃)) f₁

Nat:sub : Nat → Nat → Nat
Nat:sub x₀ x₁ = Nat:brecOn {λ (x₂ : Nat) → Nat → Nat} x₁ Nat:sub:~uf x₀

record Sub (α₀ : Set) : Set where
  constructor Sub:mk
  field
    sub₁ : α₀ → α₀ → α₀

postulate Sub:rec : {α₀ : Set} → {motive₁ : Sub α₀ → Set} → ((sub₂ : α₀ → α₀ → α₀) → motive₁ (Sub:mk {α₀} sub₂)) → (t₂ : Sub α₀) → motive₁ t₂

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

postulate Or:rec : {a₀ : Set} → {b₁ : Set} → {motive₂ : Or a₀ b₁ → Set} → ((h₃ : a₀) → motive₂ (Or:inl {a₀} {b₁} h₃)) → ((h₃ : b₁) → motive₂ (Or:inr {a₀} {b₁} h₃)) → (t₃ : Or a₀ b₁) → motive₂ t₃

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

Fin:Internal:ofNat : (n₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) n₀ → Nat → Fin n₀
Fin:Internal:ofNat n₀ hn₁ a₂ = Fin:mk {n₀} (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ a₂ n₀) (Nat:mod~ult a₂ {n₀} hn₁)

BitVec:ofNat : (n₀ : Nat) → Nat → BitVec n₀
BitVec:ofNat n₀ i₁ = BitVec:ofFin {n₀} (Fin:Internal:ofNat (HPow:hPow {Nat} {Nat} {Nat} ⦃ instHPow {Nat} {Nat} ⦃ instPowNat {Nat} ⦃ instNatPowNat ⦄ ⦄ ⦄ (OfNat:ofNat {Nat} 2 ⦃ instOfNatNat 2 ⦄) n₀) (BitVec:ofNat:~uproof~u1 n₀) i₁)

BitVec:toFin : {w₀ : Nat} → BitVec w₀ → Fin (HPow:hPow {Nat} {Nat} {Nat} ⦃ instHPow {Nat} {Nat} ⦃ instPowNat {Nat} ⦃ instNatPowNat ⦄ ⦄ ⦄ (OfNat:ofNat {Nat} 2 ⦃ instOfNatNat 2 ⦄) w₀)
BitVec:toFin {w₀} self₁ = BitVec.toFin₁ {w₀} self₁

Fin:val : {n₀ : Nat} → Fin n₀ → Nat
Fin:val {n₀} self₁ = Fin.val₁ {n₀} self₁

BitVec:toNat : {w₀ : Nat} → BitVec w₀ → Nat
BitVec:toNat {w₀} x₁ = Fin:val {HPow:hPow {Nat} {Nat} {Nat} ⦃ instHPow {Nat} {Nat} ⦃ instPowNat {Nat} ⦃ instNatPowNat ⦄ ⦄ ⦄ (OfNat:ofNat {Nat} 2 ⦃ instOfNatNat 2 ⦄) w₀} (BitVec:toFin {w₀} x₁)

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

Nat:isValidChar : Nat → Set
Nat:isValidChar n₀ = Or (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ (OfNat:ofNat {Nat} 55296 ⦃ instOfNatNat 55296 ⦄)) (And (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 57343 ⦃ instOfNatNat 57343 ⦄) n₀) (LT:lt {Nat} ⦃ instLTNat ⦄ n₀ (OfNat:ofNat {Nat} 1114112 ⦃ instOfNatNat 1114112 ⦄)))

UInt32:toBitVec : UInt32 → BitVec (OfNat:ofNat {Nat} 32 ⦃ instOfNatNat 32 ⦄)
UInt32:toBitVec self₀ = UInt32.toBitVec₀ self₀

UInt32:toNat : UInt32 → Nat
UInt32:toNat n₀ = BitVec:toNat {OfNat:ofNat {Nat} 32 ⦃ instOfNatNat 32 ⦄} (UInt32:toBitVec n₀)

UInt32:isValidChar : UInt32 → Set
UInt32:isValidChar n₀ = Nat:isValidChar (UInt32:toNat n₀)

record Char : Set where
  constructor Char:mk
  field
    val₀ : UInt32
    valid₁ : UInt32:isValidChar val₀

postulate Char:rec : {motive₀ : Char → Set} → ((val₁ : UInt32) → (valid₂ : UInt32:isValidChar val₁) → motive₀ (Char:mk val₁ valid₂)) → (t₁ : Char) → motive₀ t₁

List:append:match~u1 : {α₀ : Set} → (motive₁ : List α₀ → List α₀ → Set) → (x₂ : List α₀) → (x₃ : List α₀) → ((bs₄ : List α₀) → motive₁ (List:nil {α₀}) bs₄) → ((a₄ : α₀) → (as₅ : List α₀) → (bs₆ : List α₀) → motive₁ (List:cons {α₀} a₄ as₅) bs₆) → motive₁ x₂ x₃
List:append:match~u1 {α₀} motive₁ x₂ x₃ h1₄ h2₅ = List:casesOn {α₀} {λ (x₆ : List α₀) → motive₁ x₆ x₃} x₂ (h1₄ x₃) (λ (head₆ : α₀) → λ (tail₇ : List α₀) → h2₅ head₆ tail₇ x₃)

List:append:~uf : {α₀ : Set} → (x₁ : List α₀) → List:below {α₀} {λ (x₂ : List α₀) → List α₀ → List α₀} x₁ → List α₀ → List α₀
List:append:~uf {α₀} x₁ f₂ x₃ = List:append:match~u1 {α₀} (λ (x₄ : List α₀) → λ (x₅ : List α₀) → List:below {α₀} {λ (x₆ : List α₀) → List α₀ → List α₀} x₄ → List α₀) x₁ x₃ (λ (bs₄ : List α₀) → λ (x₅ : List:below {α₀} {λ (x₅ : List α₀) → List α₀ → List α₀} (List:nil {α₀})) → bs₄) (λ (a₄ : α₀) → λ (as₅ : List α₀) → λ (bs₆ : List α₀) → λ (x₇ : List:below {α₀} {λ (x₇ : List α₀) → List α₀ → List α₀} (List:cons {α₀} a₄ as₅)) → List:cons {α₀} a₄ (PProd.fst₂ {(λ (x₈ : List α₀) → List α₀ → List α₀) as₅} {List:rec {α₀} {λ (t₈ : List α₀) → Set} PUnit (λ (head₈ : α₀) → λ (tail₉ : List α₀) → λ (tailih₁₀ : Set) → PProd ((λ (x₁₁ : List α₀) → List α₀ → List α₀) tail₉) tailih₁₀) as₅} x₇ bs₆)) f₂

List:append : {α₀ : Set} → List α₀ → List α₀ → List α₀
List:append {α₀} x₁ x₂ = List:brecOn {α₀} {λ (x₃ : List α₀) → List α₀ → List α₀} x₁ (List:append:~uf {α₀}) x₂

List:flatten:match~u1 : {α₀ : Set} → (motive₁ : List (List α₀) → Set) → (x₂ : List (List α₀)) → (Unit → motive₁ (List:nil {List α₀})) → ((l₃ : List α₀) → (L₄ : List (List α₀)) → motive₁ (List:cons {List α₀} l₃ L₄)) → motive₁ x₂
List:flatten:match~u1 {α₀} motive₁ x₂ h1₃ h2₄ = List:casesOn {List α₀} {λ (x₅ : List (List α₀)) → motive₁ x₅} x₂ (h1₃ Unit:unit) (λ (head₅ : List α₀) → λ (tail₆ : List (List α₀)) → h2₄ head₅ tail₆)

List:flatten:~uf : {α₀ : Set} → (x₁ : List (List α₀)) → List:below {List α₀} {λ (x₂ : List (List α₀)) → List α₀} x₁ → List α₀
List:flatten:~uf {α₀} x₁ f₂ = List:flatten:match~u1 {α₀} (λ (x₃ : List (List α₀)) → List:below {List α₀} {λ (x₄ : List (List α₀)) → List α₀} x₃ → List α₀) x₁ (λ (x₃ : Unit) → λ (x₄ : List:below {List α₀} {λ (x₄ : List (List α₀)) → List α₀} (List:nil {List α₀})) → List:nil {α₀}) (λ (l₃ : List α₀) → λ (L₄ : List (List α₀)) → λ (x₅ : List:below {List α₀} {λ (x₅ : List (List α₀)) → List α₀} (List:cons {List α₀} l₃ L₄)) → List:append {α₀} l₃ (PProd.fst₂ {(λ (x₆ : List (List α₀)) → List α₀) L₄} {List:rec {List α₀} {λ (t₆ : List (List α₀)) → Set} PUnit (λ (head₆ : List α₀) → λ (tail₇ : List (List α₀)) → λ (tailih₈ : Set) → PProd ((λ (x₉ : List (List α₀)) → List α₀) tail₇) tailih₈) L₄} x₅)) f₂

List:flatten : {α₀ : Set} → List (List α₀) → List α₀
List:flatten {α₀} x₁ = List:brecOn {List α₀} {λ (x₂ : List (List α₀)) → List α₀} x₁ (List:flatten:~uf {α₀})

instDecidableEqList:match~u1 : {α₀ : Set} → (motive₁ : List α₀ → Set) → (ys₂ : List α₀) → (Unit → motive₁ (List:nil {α₀})) → ((head₃ : α₀) → (tail₄ : List α₀) → motive₁ (List:cons {α₀} head₃ tail₄)) → motive₁ ys₂
instDecidableEqList:match~u1 {α₀} motive₁ ys₂ h1₃ h2₄ = List:casesOn {α₀} {λ (x₅ : List α₀) → motive₁ x₅} ys₂ (h1₃ Unit:unit) (λ (head₅ : α₀) → λ (tail₆ : List α₀) → h2₄ head₅ tail₆)

List:map:~uf : {α₀ : Set} → {β₁ : Set} → (α₀ → β₁) → (x₂ : List α₀) → List:below {α₀} {λ (x₃ : List α₀) → List β₁} x₂ → List β₁
List:map:~uf {α₀} {β₁} f₂ x₃ f₄ = instDecidableEqList:match~u1 {α₀} (λ (x₅ : List α₀) → List:below {α₀} {λ (x₆ : List α₀) → List β₁} x₅ → List β₁) x₃ (λ (x₅ : Unit) → λ (x₆ : List:below {α₀} {λ (x₆ : List α₀) → List β₁} (List:nil {α₀})) → List:nil {β₁}) (λ (a₅ : α₀) → λ (as₆ : List α₀) → λ (x₇ : List:below {α₀} {λ (x₇ : List α₀) → List β₁} (List:cons {α₀} a₅ as₆)) → List:cons {β₁} (f₂ a₅) (PProd.fst₂ {(λ (x₈ : List α₀) → List β₁) as₆} {List:rec {α₀} {λ (t₈ : List α₀) → Set} PUnit (λ (head₈ : α₀) → λ (tail₉ : List α₀) → λ (tailih₁₀ : Set) → PProd ((λ (x₁₁ : List α₀) → List β₁) tail₉) tailih₁₀) as₆} x₇)) f₄

List:map : {α₀ : Set} → {β₁ : Set} → (α₀ → β₁) → List α₀ → List β₁
List:map {α₀} {β₁} f₂ x₃ = List:brecOn {α₀} {λ (x₄ : List α₀) → List β₁} x₃ (List:map:~uf {α₀} {β₁} f₂)

List:flatMap : {α₀ : Set} → {β₁ : Set} → (α₀ → List β₁) → List α₀ → List β₁
List:flatMap {α₀} {β₁} b₂ as₃ = List:flatten {β₁} (List:map {α₀} {List β₁} b₂ as₃)

ByteArray:emptyWithCapacity : Nat → ByteArray
ByteArray:emptyWithCapacity c₀ = ByteArray:mk (Array:empty {UInt8})

ByteArray:empty : ByteArray
ByteArray:empty = ByteArray:emptyWithCapacity (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)

ByteArray:casesOn : {motive₀ : ByteArray → Set} → (t₁ : ByteArray) → ((data₂ : Array UInt8) → motive₀ (ByteArray:mk data₂)) → motive₀ t₁
ByteArray:casesOn {motive₀} t₁ mk₂ = ByteArray:rec {motive₀} (λ (data₃ : Array UInt8) → mk₂ data₃) t₁

ByteArray:push:match~u1 : (motive₀ : ByteArray → UInt8 → Set) → (x₁ : ByteArray) → (x₂ : UInt8) → ((bs₃ : Array UInt8) → (b₄ : UInt8) → motive₀ (ByteArray:mk bs₃) b₄) → motive₀ x₁ x₂
ByteArray:push:match~u1 motive₀ x₁ x₂ h1₃ = ByteArray:casesOn {λ (x₄ : ByteArray) → motive₀ x₄ x₂} x₁ (λ (data₄ : Array UInt8) → h1₃ data₄ x₂)

ByteArray:push : ByteArray → UInt8 → ByteArray
ByteArray:push x₀ x₁ = ByteArray:push:match~u1 (λ (x₂ : ByteArray) → λ (x₃ : UInt8) → ByteArray) x₀ x₁ (λ (bs₂ : Array UInt8) → λ (b₃ : UInt8) → ByteArray:mk (Array:push {UInt8} bs₂ b₃))

List:toByteArray:match~u1 : (motive₀ : List UInt8 → ByteArray → Set) → (x₁ : List UInt8) → (x₂ : ByteArray) → ((r₃ : ByteArray) → motive₀ (List:nil {UInt8}) r₃) → ((b₃ : UInt8) → (bs₄ : List UInt8) → (r₅ : ByteArray) → motive₀ (List:cons {UInt8} b₃ bs₄) r₅) → motive₀ x₁ x₂
List:toByteArray:match~u1 motive₀ x₁ x₂ h1₃ h2₄ = List:casesOn {UInt8} {λ (x₅ : List UInt8) → motive₀ x₅ x₂} x₁ (h1₃ x₂) (λ (head₅ : UInt8) → λ (tail₆ : List UInt8) → h2₄ head₅ tail₆ x₂)

List:toByteArray:loop:~uf : (x₀ : List UInt8) → List:below {UInt8} {λ (x₁ : List UInt8) → ByteArray → ByteArray} x₀ → ByteArray → ByteArray
List:toByteArray:loop:~uf x₀ f₁ x₂ = List:toByteArray:match~u1 (λ (x₃ : List UInt8) → λ (x₄ : ByteArray) → List:below {UInt8} {λ (x₅ : List UInt8) → ByteArray → ByteArray} x₃ → ByteArray) x₀ x₂ (λ (r₃ : ByteArray) → λ (x₄ : List:below {UInt8} {λ (x₄ : List UInt8) → ByteArray → ByteArray} (List:nil {UInt8})) → r₃) (λ (b₃ : UInt8) → λ (bs₄ : List UInt8) → λ (r₅ : ByteArray) → λ (x₆ : List:below {UInt8} {λ (x₆ : List UInt8) → ByteArray → ByteArray} (List:cons {UInt8} b₃ bs₄)) → PProd.fst₂ {(λ (x₇ : List UInt8) → ByteArray → ByteArray) bs₄} {List:rec {UInt8} {λ (t₇ : List UInt8) → Set} PUnit (λ (head₇ : UInt8) → λ (tail₈ : List UInt8) → λ (tailih₉ : Set) → PProd ((λ (x₁₀ : List UInt8) → ByteArray → ByteArray) tail₈) tailih₉) bs₄} x₆ (ByteArray:push r₅ b₃)) f₁

List:toByteArray:loop : List UInt8 → ByteArray → ByteArray
List:toByteArray:loop x₀ x₁ = List:brecOn {UInt8} {λ (x₂ : List UInt8) → ByteArray → ByteArray} x₀ List:toByteArray:loop:~uf x₁

List:toByteArray : List UInt8 → ByteArray
List:toByteArray bs₀ = List:toByteArray:loop bs₀ ByteArray:empty

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

Nat:div:go:~uf : (y₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀ → (fuel₁ : Nat) → Nat:below {λ (fuel₂ : Nat) → (x₃ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₃ fuel₂ → Nat} fuel₁ → (x₂ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₂ fuel₁ → Nat
Nat:div:go:~uf y₀ hy₁ fuel₂ f₃ x₄ hfuel₅ = Nat:div:go:match~u1 x₄ (λ (fuel₆ : Nat) → λ (hfuel₇ : LT:lt {Nat} ⦃ instLTNat ⦄ x₄ fuel₆) → Nat:below {λ (fuel₈ : Nat) → (x₉ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₉ fuel₈ → Nat} fuel₆ → Nat) fuel₂ hfuel₅ (λ (fuel₆ : Nat) → λ (hfuel₇ : LT:lt {Nat} ⦃ instLTNat ⦄ x₄ (Nat:succ fuel₆)) → λ (x₈ : Nat:below {λ (fuel₈ : Nat) → (x₉ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₉ fuel₈ → Nat} (Nat:succ fuel₆)) → dite {Nat} (LE:le {Nat} ⦃ instLENat ⦄ y₀ x₄) ⦃ Nat:decLe y₀ x₄ ⦄ (λ (h₉ : LE:le {Nat} ⦃ instLENat ⦄ y₀ x₄) → HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (PProd.fst₂ {(λ (fuel₁₀ : Nat) → (x₁₁ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₁₁ fuel₁₀ → Nat) fuel₆} {Nat:rec {λ (t₁₀ : Nat) → Set} PUnit (λ (n₁₀ : Nat) → λ (nih₁₁ : Set) → PProd ((λ (fuel₁₂ : Nat) → (x₁₃ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₁₃ fuel₁₂ → Nat) n₁₀) nih₁₁) fuel₆} x₈ (HSub:hSub {Nat} {Nat} {Nat} ⦃ instHSub {Nat} ⦃ instSubNat ⦄ ⦄ x₄ y₀) (Nat:div~urec~ufuel~ulemma {x₄} {y₀} {fuel₆} hy₁ h₉ hfuel₇)) (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (λ (x₉ : Not (LE:le {Nat} ⦃ instLENat ⦄ y₀ x₄)) → OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)) f₃

Nat:div:go : (y₀ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₀ → (fuel₁ : Nat) → (x₂ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₂ fuel₁ → Nat
Nat:div:go y₀ hy₁ fuel₂ x₃ hfuel₄ = Nat:brecOn {λ (fuel₅ : Nat) → (x₆ : Nat) → LT:lt {Nat} ⦃ instLTNat ⦄ x₆ fuel₅ → Nat} fuel₂ (Nat:div:go:~uf y₀ hy₁) x₃ hfuel₄

Nat:div : Nat → Nat → Nat
Nat:div x₀ y₁ = dite {Nat} (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) ⦃ Nat:decLt (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁ ⦄ (λ (hy₂ : LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁) → Nat:div:go y₁ hy₂ (Nat:succ x₀) x₀ (Nat:lt~usucc~uself x₀)) (λ (x₂ : Not (LT:lt {Nat} ⦃ instLTNat ⦄ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) y₁)) → OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)

Nat:instDiv : Div Nat
Nat:instDiv = Div:mk {Nat} Nat:div

UInt8:ofNat : Nat → UInt8
UInt8:ofNat n₀ = UInt8:ofBitVec (BitVec:ofNat (OfNat:ofNat {Nat} 8 ⦃ instOfNatNat 8 ⦄) n₀)

Div:div : {α₀ : Set} → ⦃ _ : Div α₀ ⦄ → α₀ → α₀ → α₀
Div:div {α₀} ⦃ self₁ ⦄ = Div.div₁ {α₀} self₁

instHDiv : {α₀ : Set} → ⦃ _ : Div α₀ ⦄ → HDiv α₀ α₀ α₀
instHDiv {α₀} ⦃ inst₁ ⦄ = HDiv:mk {α₀} {α₀} {α₀} (λ (a₂ : α₀) → λ (b₃ : α₀) → Div:div {α₀} ⦃ inst₁ ⦄ a₂ b₃)

String:utf8EncodeChar : Char → List UInt8
String:utf8EncodeChar c₀ = let v₁ : Nat; v₁ = UInt32:toNat (Char:val c₀) in ite {List UInt8} (LE:le {Nat} ⦃ instLENat ⦄ v₁ (OfNat:ofNat {Nat} 127 ⦃ instOfNatNat 127 ⦄)) ⦃ Nat:decLe v₁ (OfNat:ofNat {Nat} 127 ⦃ instOfNatNat 127 ⦄) ⦄ (List:cons {UInt8} (UInt8:ofNat v₁) (List:nil {UInt8})) (ite {List UInt8} (LE:le {Nat} ⦃ instLENat ⦄ v₁ (OfNat:ofNat {Nat} 2047 ⦃ instOfNatNat 2047 ⦄)) ⦃ Nat:decLe v₁ (OfNat:ofNat {Nat} 2047 ⦃ instOfNatNat 2047 ⦄) ⦄ (List:cons {UInt8} (UInt8:ofNat (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ (HDiv:hDiv {Nat} {Nat} {Nat} ⦃ instHDiv {Nat} ⦃ Nat:instDiv ⦄ ⦄ v₁ (OfNat:ofNat {Nat} 64 ⦃ instOfNatNat 64 ⦄)) (OfNat:ofNat {Nat} 32 ⦃ instOfNatNat 32 ⦄)) (OfNat:ofNat {Nat} 192 ⦃ instOfNatNat 192 ⦄))) (List:cons {UInt8} (UInt8:ofNat (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ v₁ (OfNat:ofNat {Nat} 64 ⦃ instOfNatNat 64 ⦄)) (OfNat:ofNat {Nat} 128 ⦃ instOfNatNat 128 ⦄))) (List:nil {UInt8}))) (ite {List UInt8} (LE:le {Nat} ⦃ instLENat ⦄ v₁ (OfNat:ofNat {Nat} 65535 ⦃ instOfNatNat 65535 ⦄)) ⦃ Nat:decLe v₁ (OfNat:ofNat {Nat} 65535 ⦃ instOfNatNat 65535 ⦄) ⦄ (List:cons {UInt8} (UInt8:ofNat (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ (HDiv:hDiv {Nat} {Nat} {Nat} ⦃ instHDiv {Nat} ⦃ Nat:instDiv ⦄ ⦄ v₁ (OfNat:ofNat {Nat} 4096 ⦃ instOfNatNat 4096 ⦄)) (OfNat:ofNat {Nat} 16 ⦃ instOfNatNat 16 ⦄)) (OfNat:ofNat {Nat} 224 ⦃ instOfNatNat 224 ⦄))) (List:cons {UInt8} (UInt8:ofNat (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ (HDiv:hDiv {Nat} {Nat} {Nat} ⦃ instHDiv {Nat} ⦃ Nat:instDiv ⦄ ⦄ v₁ (OfNat:ofNat {Nat} 64 ⦃ instOfNatNat 64 ⦄)) (OfNat:ofNat {Nat} 64 ⦃ instOfNatNat 64 ⦄)) (OfNat:ofNat {Nat} 128 ⦃ instOfNatNat 128 ⦄))) (List:cons {UInt8} (UInt8:ofNat (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ v₁ (OfNat:ofNat {Nat} 64 ⦃ instOfNatNat 64 ⦄)) (OfNat:ofNat {Nat} 128 ⦃ instOfNatNat 128 ⦄))) (List:nil {UInt8})))) (List:cons {UInt8} (UInt8:ofNat (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ (HDiv:hDiv {Nat} {Nat} {Nat} ⦃ instHDiv {Nat} ⦃ Nat:instDiv ⦄ ⦄ v₁ (OfNat:ofNat {Nat} 262144 ⦃ instOfNatNat 262144 ⦄)) (OfNat:ofNat {Nat} 8 ⦃ instOfNatNat 8 ⦄)) (OfNat:ofNat {Nat} 240 ⦃ instOfNatNat 240 ⦄))) (List:cons {UInt8} (UInt8:ofNat (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ (HDiv:hDiv {Nat} {Nat} {Nat} ⦃ instHDiv {Nat} ⦃ Nat:instDiv ⦄ ⦄ v₁ (OfNat:ofNat {Nat} 4096 ⦃ instOfNatNat 4096 ⦄)) (OfNat:ofNat {Nat} 64 ⦃ instOfNatNat 64 ⦄)) (OfNat:ofNat {Nat} 128 ⦃ instOfNatNat 128 ⦄))) (List:cons {UInt8} (UInt8:ofNat (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ (HDiv:hDiv {Nat} {Nat} {Nat} ⦃ instHDiv {Nat} ⦃ Nat:instDiv ⦄ ⦄ v₁ (OfNat:ofNat {Nat} 64 ⦃ instOfNatNat 64 ⦄)) (OfNat:ofNat {Nat} 64 ⦃ instOfNatNat 64 ⦄)) (OfNat:ofNat {Nat} 128 ⦃ instOfNatNat 128 ⦄))) (List:cons {UInt8} (UInt8:ofNat (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ (HMod:hMod {Nat} {Nat} {Nat} ⦃ instHMod {Nat} ⦃ Nat:instMod ⦄ ⦄ v₁ (OfNat:ofNat {Nat} 64 ⦃ instOfNatNat 64 ⦄)) (OfNat:ofNat {Nat} 128 ⦃ instOfNatNat 128 ⦄))) (List:nil {UInt8})))))))

List:utf8Encode : List Char → ByteArray
List:utf8Encode l₀ = List:toByteArray (List:flatMap {Char} {UInt8} String:utf8EncodeChar l₀)

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

PrintFixtures:applyImplicit : ({α₀ : Set} → α₀ → α₀) → Nat
PrintFixtures:applyImplicit f₀ = f₀ {Nat} (OfNat:ofNat {Nat} 3 ⦃ instOfNatNat 3 ⦄)

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
