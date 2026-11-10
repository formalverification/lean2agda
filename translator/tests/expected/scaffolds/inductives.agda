-- File: translator/tests/expected/scaffolds/inductives.agda
{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of InductiveFixtures:Bad InductiveFixtures:Packed InductiveFixtures:Packed:fits InductiveFixtures:Packed:measured InductiveFixtures:Packed:value and 12 more
-- refused 3 declarations; refusals.txt names each with its reason
module U.TranslatorTests.Input.Inductives where

record Add (α₀ : Set) : Set where
  constructor Add:mk
  field
    add₁ : α₀ → α₀ → α₀

-- recursor
Add:rec : {α₀ : Set} → {motive₁ : Add α₀ → Set} → ((add₂ : α₀ → α₀ → α₀) → motive₁ (Add:mk {α₀} add₂)) → (t₂ : Add α₀) → motive₁ t₂
Add:rec {α₀} {motive₁} mk₂ (Add:mk add₃) = mk₂ add₃

Add:add : {α₀ : Set} → ⦃ _ : Add α₀ ⦄ → α₀ → α₀ → α₀
Add:add {α₀} ⦃ self₁ ⦄ = Add.add₁ {α₀} self₁

data Bool : Set where
  Bool:false : Bool
  Bool:true : Bool

-- recursor
Bool:rec : {motive₀ : Bool → Set} → motive₀ Bool:false → motive₀ Bool:true → (t₁ : Bool) → motive₀ t₁
Bool:rec {motive₀} false₁ true₂ Bool:false = false₁
Bool:rec {motive₀} false₁ true₂ Bool:true = true₂

record BEq (α₀ : Set) : Set where
  constructor BEq:mk
  field
    beq₁ : α₀ → α₀ → Bool

-- recursor
BEq:rec : {α₀ : Set} → {motive₁ : BEq α₀ → Set} → ((beq₂ : α₀ → α₀ → Bool) → motive₁ (BEq:mk {α₀} beq₂)) → (t₂ : BEq α₀) → motive₁ t₂
BEq:rec {α₀} {motive₁} mk₂ (BEq:mk beq₃) = mk₂ beq₃

record LT (α₀ : Set) : Set where
  constructor LT:mk
  field
    lt₁ : α₀ → α₀ → Set

-- recursor
LT:rec : {α₀ : Set} → {motive₁ : LT α₀ → Set} → ((lt₂ : α₀ → α₀ → Set) → motive₁ (LT:mk {α₀} lt₂)) → (t₂ : LT α₀) → motive₁ t₂
LT:rec {α₀} {motive₁} mk₂ (LT:mk lt₃) = mk₂ lt₃

LT:lt : {α₀ : Set} → ⦃ _ : LT α₀ ⦄ → α₀ → α₀ → Set
LT:lt {α₀} ⦃ self₁ ⦄ = LT.lt₁ {α₀} self₁

data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

-- recursor
Nat:rec : {motive₀ : Nat → Set} → motive₀ Nat:zero → ((n₁ : Nat) → motive₀ n₁ → motive₀ (Nat:succ n₁)) → (t₁ : Nat) → motive₀ t₁
Nat:rec {motive₀} zero₁ succ₂ Nat:zero = zero₁
Nat:rec {motive₀} zero₁ succ₂ (Nat:succ n₃) = succ₂ n₃ (Nat:rec {motive₀} zero₁ succ₂ n₃)

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

record InductiveFixtures:Measure (α₀ : Set) : Set where
  constructor InductiveFixtures:Measure:mk
  field
    measure₁ : α₀ → Nat

-- recursor
InductiveFixtures:Measure:rec : {α₀ : Set} → {motive₁ : InductiveFixtures:Measure α₀ → Set} → ((measure₂ : α₀ → Nat) → motive₁ (InductiveFixtures:Measure:mk {α₀} measure₂)) → (t₂ : InductiveFixtures:Measure α₀) → motive₁ t₂
InductiveFixtures:Measure:rec {α₀} {motive₁} mk₂ (InductiveFixtures:Measure:mk measure₃) = mk₂ measure₃

InductiveFixtures:Measure:measure : {α₀ : Set} → ⦃ _ : InductiveFixtures:Measure α₀ ⦄ → α₀ → Nat
InductiveFixtures:Measure:measure {α₀} ⦃ self₁ ⦄ = InductiveFixtures:Measure.measure₁ {α₀} self₁

record LE (α₀ : Set) : Set where
  constructor LE:mk
  field
    le₁ : α₀ → α₀ → Set

-- recursor
LE:rec : {α₀ : Set} → {motive₁ : LE α₀ → Set} → ((le₂ : α₀ → α₀ → Set) → motive₁ (LE:mk {α₀} le₂)) → (t₂ : LE α₀) → motive₁ t₂
LE:rec {α₀} {motive₁} mk₂ (LE:mk le₃) = mk₂ le₃

LE:le : {α₀ : Set} → ⦃ _ : LE α₀ ⦄ → α₀ → α₀ → Set
LE:le {α₀} ⦃ self₁ ⦄ = LE.le₁ {α₀} self₁

instLENat : LE Nat
instLENat = LE:mk {Nat} Nat:le

record InductiveFixtures:Packed (α₀ : Set) ⦃ inst₁ : BEq α₀ ⦄ : Set where
  constructor InductiveFixtures:Packed:mk
  field
    {width₂} : Nat
    ⦃ measured₃ ⦄ : InductiveFixtures:Measure α₀
    value₄ : α₀
    fits₅ : LE:le {Nat} ⦃ instLENat ⦄ (InductiveFixtures:Measure:measure {α₀} ⦃ measured₃ ⦄ value₄) width₂

-- recursor
InductiveFixtures:Packed:rec : {α₀ : Set} → ⦃ inst₁ : BEq α₀ ⦄ → {motive₂ : InductiveFixtures:Packed α₀ ⦃ inst₁ ⦄ → Set} → ({width₃ : Nat} → ⦃ measured₄ : InductiveFixtures:Measure α₀ ⦄ → (value₅ : α₀) → (fits₆ : LE:le {Nat} ⦃ instLENat ⦄ (InductiveFixtures:Measure:measure {α₀} ⦃ measured₄ ⦄ value₅) width₃) → motive₂ (InductiveFixtures:Packed:mk {α₀} ⦃ inst₁ ⦄ {width₃} ⦃ measured₄ ⦄ value₅ fits₆)) → (t₃ : InductiveFixtures:Packed α₀ ⦃ inst₁ ⦄) → motive₂ t₃
InductiveFixtures:Packed:rec {α₀} ⦃ inst₁ ⦄ {motive₂} mk₃ (InductiveFixtures:Packed:mk {width₄} ⦃ measured₅ ⦄ value₆ fits₇) = mk₃ {width₄} ⦃ measured₅ ⦄ value₆ fits₇

InductiveFixtures:Packed:measured : {α₀ : Set} → ⦃ inst₁ : BEq α₀ ⦄ → InductiveFixtures:Packed α₀ ⦃ inst₁ ⦄ → InductiveFixtures:Measure α₀
InductiveFixtures:Packed:measured {α₀} ⦃ inst₁ ⦄ self₂ = InductiveFixtures:Packed.measured₃ {α₀} ⦃ inst₁ ⦄ self₂

InductiveFixtures:Packed:value : {α₀ : Set} → ⦃ inst₁ : BEq α₀ ⦄ → InductiveFixtures:Packed α₀ ⦃ inst₁ ⦄ → α₀
InductiveFixtures:Packed:value {α₀} ⦃ inst₁ ⦄ self₂ = InductiveFixtures:Packed.value₄ {α₀} ⦃ inst₁ ⦄ self₂

InductiveFixtures:Packed:width : {α₀ : Set} → ⦃ inst₁ : BEq α₀ ⦄ → InductiveFixtures:Packed α₀ ⦃ inst₁ ⦄ → Nat
InductiveFixtures:Packed:width {α₀} ⦃ inst₁ ⦄ self₂ = InductiveFixtures:Packed.width₂ {α₀} ⦃ inst₁ ⦄ self₂

-- theorem
opaque
  InductiveFixtures:Packed:fits : {α₀ : Set} → ⦃ inst₁ : BEq α₀ ⦄ → (self₂ : InductiveFixtures:Packed α₀ ⦃ inst₁ ⦄) → LE:le {Nat} ⦃ instLENat ⦄ (InductiveFixtures:Measure:measure {α₀} ⦃ InductiveFixtures:Packed:measured {α₀} ⦃ inst₁ ⦄ self₂ ⦄ (InductiveFixtures:Packed:value {α₀} ⦃ inst₁ ⦄ self₂)) (InductiveFixtures:Packed:width {α₀} ⦃ inst₁ ⦄ self₂)
  InductiveFixtures:Packed:fits {α₀} ⦃ inst₁ ⦄ self₂ = InductiveFixtures:Packed.fits₅ {α₀} ⦃ inst₁ ⦄ self₂

mutual
  data InductiveFixtures:Term : Set where
    InductiveFixtures:Term:lit : Nat → InductiveFixtures:Term
    InductiveFixtures:Term:pair : InductiveFixtures:Pair → InductiveFixtures:Term
  record InductiveFixtures:Pair : Set where
    inductive
    no-eta-equality
    pattern
    constructor InductiveFixtures:Pair:mk
    field
      left₀ : InductiveFixtures:Term
      right₁ : InductiveFixtures:Term

-- recursor
mutual
  InductiveFixtures:Term:rec : {motive1₀ : InductiveFixtures:Term → Set} → {motive2₁ : InductiveFixtures:Pair → Set} → ((a₂ : Nat) → motive1₀ (InductiveFixtures:Term:lit a₂)) → ((a₂ : InductiveFixtures:Pair) → motive2₁ a₂ → motive1₀ (InductiveFixtures:Term:pair a₂)) → ((left₂ : InductiveFixtures:Term) → (right₃ : InductiveFixtures:Term) → motive1₀ left₂ → motive1₀ right₃ → motive2₁ (InductiveFixtures:Pair:mk left₂ right₃)) → (t₂ : InductiveFixtures:Term) → motive1₀ t₂
  InductiveFixtures:Pair:rec : {motive1₀ : InductiveFixtures:Term → Set} → {motive2₁ : InductiveFixtures:Pair → Set} → ((a₂ : Nat) → motive1₀ (InductiveFixtures:Term:lit a₂)) → ((a₂ : InductiveFixtures:Pair) → motive2₁ a₂ → motive1₀ (InductiveFixtures:Term:pair a₂)) → ((left₂ : InductiveFixtures:Term) → (right₃ : InductiveFixtures:Term) → motive1₀ left₂ → motive1₀ right₃ → motive2₁ (InductiveFixtures:Pair:mk left₂ right₃)) → (t₂ : InductiveFixtures:Pair) → motive2₁ t₂
  InductiveFixtures:Term:rec {motive1₀} {motive2₁} lit₂ pair₃ mk₄ (InductiveFixtures:Term:lit a₅) = lit₂ a₅
  InductiveFixtures:Term:rec {motive1₀} {motive2₁} lit₂ pair₃ mk₄ (InductiveFixtures:Term:pair a₅) = pair₃ a₅ (InductiveFixtures:Pair:rec {motive1₀} {motive2₁} lit₂ pair₃ mk₄ a₅)
  InductiveFixtures:Pair:rec {motive1₀} {motive2₁} lit₂ pair₃ mk₄ (InductiveFixtures:Pair:mk left₅ right₆) = mk₄ left₅ right₆ (InductiveFixtures:Term:rec {motive1₀} {motive2₁} lit₂ pair₃ mk₄ left₅) (InductiveFixtures:Term:rec {motive1₀} {motive2₁} lit₂ pair₃ mk₄ right₆)

data List (α₀ : Set) : Set where
  List:nil : List α₀
  List:cons : α₀ → List α₀ → List α₀

-- recursor
List:rec : {α₀ : Set} → {motive₁ : List α₀ → Set} → motive₁ (List:nil {α₀}) → ((head₂ : α₀) → (tail₃ : List α₀) → motive₁ tail₃ → motive₁ (List:cons {α₀} head₂ tail₃)) → (t₂ : List α₀) → motive₁ t₂
List:rec {α₀} {motive₁} nil₂ cons₃ List:nil = nil₂
List:rec {α₀} {motive₁} nil₂ cons₃ (List:cons head₄ tail₅) = cons₃ head₄ tail₅ (List:rec {α₀} {motive₁} nil₂ cons₃ tail₅)

record InductiveFixtures:Rose : Set where
  inductive
  no-eta-equality
  pattern
  constructor InductiveFixtures:Rose:mk
  field
    label₀ : Nat
    children₁ : List InductiveFixtures:Rose

-- recursor
mutual
  InductiveFixtures:Rose:rec : {motive1₀ : InductiveFixtures:Rose → Set} → {motive2₁ : List InductiveFixtures:Rose → Set} → ((label₂ : Nat) → (children₃ : List InductiveFixtures:Rose) → motive2₁ children₃ → motive1₀ (InductiveFixtures:Rose:mk label₂ children₃)) → motive2₁ (List:nil {InductiveFixtures:Rose}) → ((head₂ : InductiveFixtures:Rose) → (tail₃ : List InductiveFixtures:Rose) → motive1₀ head₂ → motive2₁ tail₃ → motive2₁ (List:cons {InductiveFixtures:Rose} head₂ tail₃)) → (t₂ : InductiveFixtures:Rose) → motive1₀ t₂
  InductiveFixtures:Rose:rec~u1 : {motive1₀ : InductiveFixtures:Rose → Set} → {motive2₁ : List InductiveFixtures:Rose → Set} → ((label₂ : Nat) → (children₃ : List InductiveFixtures:Rose) → motive2₁ children₃ → motive1₀ (InductiveFixtures:Rose:mk label₂ children₃)) → motive2₁ (List:nil {InductiveFixtures:Rose}) → ((head₂ : InductiveFixtures:Rose) → (tail₃ : List InductiveFixtures:Rose) → motive1₀ head₂ → motive2₁ tail₃ → motive2₁ (List:cons {InductiveFixtures:Rose} head₂ tail₃)) → (t₂ : List InductiveFixtures:Rose) → motive2₁ t₂
  InductiveFixtures:Rose:rec {motive1₀} {motive2₁} mk₂ nil₃ cons₄ (InductiveFixtures:Rose:mk label₅ children₆) = mk₂ label₅ children₆ (InductiveFixtures:Rose:rec~u1 {motive1₀} {motive2₁} mk₂ nil₃ cons₄ children₆)
  InductiveFixtures:Rose:rec~u1 {motive1₀} {motive2₁} mk₂ nil₃ cons₄ List:nil = nil₃
  InductiveFixtures:Rose:rec~u1 {motive1₀} {motive2₁} mk₂ nil₃ cons₄ (List:cons head₅ tail₆) = cons₄ head₅ tail₆ (InductiveFixtures:Rose:rec {motive1₀} {motive2₁} mk₂ nil₃ cons₄ head₅) (InductiveFixtures:Rose:rec~u1 {motive1₀} {motive2₁} mk₂ nil₃ cons₄ tail₆)

InductiveFixtures:Rose:children : InductiveFixtures:Rose → List InductiveFixtures:Rose
InductiveFixtures:Rose:children self₀ = InductiveFixtures:Rose.children₁ self₀

InductiveFixtures:Rose:label : InductiveFixtures:Rose → Nat
InductiveFixtures:Rose:label self₀ = InductiveFixtures:Rose.label₀ self₀

data InductiveFixtures:Same {α₀ : Set} : α₀ → α₀ → Set where
  InductiveFixtures:Same:refl : (a₁ : α₀) → InductiveFixtures:Same {α₀} a₁ a₁

-- recursor
InductiveFixtures:Same:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → InductiveFixtures:Same {α₀} a₁ a₂ → Set} → motive₂ a₁ (InductiveFixtures:Same:refl {α₀} a₁) → {a₃ : α₀} → (t₄ : InductiveFixtures:Same {α₀} a₁ a₃) → motive₂ a₃ t₄
InductiveFixtures:Same:rec {α₀} {a₁} {motive₂} refl₃ {_} (InductiveFixtures:Same:refl _) = refl₃

data InductiveFixtures:Sized : Nat → Set where
  InductiveFixtures:Sized:mk : (n₀ : Nat) → Fin n₀ → InductiveFixtures:Sized n₀

-- recursor
InductiveFixtures:Sized:rec : {a₀ : Nat} → {motive₁ : InductiveFixtures:Sized a₀ → Set} → ((value₂ : Fin a₀) → motive₁ (InductiveFixtures:Sized:mk a₀ value₂)) → (t₂ : InductiveFixtures:Sized a₀) → motive₁ t₂
InductiveFixtures:Sized:rec {a₀} {motive₁} mk₂ (InductiveFixtures:Sized:mk _ value₃) = mk₂ value₃

record InductiveFixtures:Stream~x27~ : Set where
  inductive
  no-eta-equality
  pattern
  constructor InductiveFixtures:Stream~x27~:mk
  field
    head₀ : Nat
    tail₁ : Nat → InductiveFixtures:Stream~x27~

-- recursor
InductiveFixtures:Stream~x27~:rec : {motive₀ : InductiveFixtures:Stream~x27~ → Set} → ((head₁ : Nat) → (tail₂ : Nat → InductiveFixtures:Stream~x27~) → ((a₃ : Nat) → motive₀ (tail₂ a₃)) → motive₀ (InductiveFixtures:Stream~x27~:mk head₁ tail₂)) → (t₁ : InductiveFixtures:Stream~x27~) → motive₀ t₁
InductiveFixtures:Stream~x27~:rec {motive₀} mk₁ (InductiveFixtures:Stream~x27~:mk head₂ tail₃) = mk₁ head₂ tail₃ (λ (a₄ : Nat) → InductiveFixtures:Stream~x27~:rec {motive₀} mk₁ (tail₃ a₄))

record InductiveFixtures:Token : Set where
  constructor InductiveFixtures:Token:mk

-- recursor
InductiveFixtures:Token:rec : {motive₀ : InductiveFixtures:Token → Set} → motive₀ InductiveFixtures:Token:mk → (t₁ : InductiveFixtures:Token) → motive₀ t₁
InductiveFixtures:Token:rec {motive₀} mk₁ InductiveFixtures:Token:mk = mk₁

record OfNat (α₀ : Set) (x₁ : Nat) : Set where
  constructor OfNat:mk
  field
    ofNat₂ : α₀

-- recursor
OfNat:rec : {α₀ : Set} → {x₁ : Nat} → {motive₂ : OfNat α₀ x₁ → Set} → ((ofNat₃ : α₀) → motive₂ (OfNat:mk {α₀} {x₁} ofNat₃)) → (t₃ : OfNat α₀ x₁) → motive₂ t₃
OfNat:rec {α₀} {x₁} {motive₂} mk₃ (OfNat:mk ofNat₄) = mk₃ ofNat₄

OfNat:ofNat : {α₀ : Set} → (x₁ : Nat) → ⦃ _ : OfNat α₀ x₁ ⦄ → α₀
OfNat:ofNat {α₀} x₁ ⦃ self₂ ⦄ = OfNat.ofNat₂ {α₀} {x₁} self₂

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

data InductiveFixtures:Vec (α₀ : Set) : Nat → Set where
  InductiveFixtures:Vec:nil : InductiveFixtures:Vec α₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)
  InductiveFixtures:Vec:cons : {n₁ : Nat} → α₀ → InductiveFixtures:Vec α₀ n₁ → InductiveFixtures:Vec α₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))

-- recursor
InductiveFixtures:Vec:rec : {α₀ : Set} → {motive₁ : (a₁ : Nat) → InductiveFixtures:Vec α₀ a₁ → Set} → motive₁ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄) (InductiveFixtures:Vec:nil {α₀}) → ({n₂ : Nat} → (head₃ : α₀) → (tail₄ : InductiveFixtures:Vec α₀ n₂) → motive₁ n₂ tail₄ → motive₁ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₂ (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)) (InductiveFixtures:Vec:cons {α₀} {n₂} head₃ tail₄)) → {a₂ : Nat} → (t₃ : InductiveFixtures:Vec α₀ a₂) → motive₁ a₂ t₃
InductiveFixtures:Vec:rec {α₀} {motive₁} nil₂ cons₃ {_} InductiveFixtures:Vec:nil = nil₂
InductiveFixtures:Vec:rec {α₀} {motive₁} nil₂ cons₃ {_} (InductiveFixtures:Vec:cons {n₅} head₆ tail₇) = cons₃ {n₅} head₆ tail₇ (InductiveFixtures:Vec:rec {α₀} {motive₁} nil₂ cons₃ {n₅} tail₇)

InductiveFixtures:Wide:node:~ushare:~n1 : Set
InductiveFixtures:Wide:node:~ushare:~n1 = Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat

InductiveFixtures:Wide:rec:~ushare:~n2 : Set
InductiveFixtures:Wide:rec:~ushare:~n2 = Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat

data InductiveFixtures:Wide : Set where
  InductiveFixtures:Wide:leaf : InductiveFixtures:Wide
  InductiveFixtures:Wide:node : (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → InductiveFixtures:Wide) → (Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → InductiveFixtures:Wide) → InductiveFixtures:Wide:node:~ushare:~n1 → InductiveFixtures:Wide:node:~ushare:~n1 → InductiveFixtures:Wide

InductiveFixtures:Wide:rec:~ushare:~n1 : Set
InductiveFixtures:Wide:rec:~ushare:~n1 = Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → InductiveFixtures:Wide

-- recursor
InductiveFixtures:Wide:rec : {motive₀ : InductiveFixtures:Wide → Set} → motive₀ InductiveFixtures:Wide:leaf → ((f₁ : InductiveFixtures:Wide:rec:~ushare:~n1) → (g₂ : InductiveFixtures:Wide:rec:~ushare:~n1) → (h₃ : InductiveFixtures:Wide:rec:~ushare:~n2) → (k₄ : InductiveFixtures:Wide:rec:~ushare:~n2) → ((a₅ : Nat) → (a₆ : Nat) → (a₇ : Nat) → (a₈ : Nat) → (a₉ : Nat) → (a₁₀ : Nat) → (a₁₁ : Nat) → (a₁₂ : Nat) → (a₁₃ : Nat) → (a₁₄ : Nat) → (a₁₅ : Nat) → (a₁₆ : Nat) → (a₁₇ : Nat) → (a₁₈ : Nat) → (a₁₉ : Nat) → (a₂₀ : Nat) → motive₀ (f₁ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀)) → ((a₅ : Nat) → (a₆ : Nat) → (a₇ : Nat) → (a₈ : Nat) → (a₉ : Nat) → (a₁₀ : Nat) → (a₁₁ : Nat) → (a₁₂ : Nat) → (a₁₃ : Nat) → (a₁₄ : Nat) → (a₁₅ : Nat) → (a₁₆ : Nat) → (a₁₇ : Nat) → (a₁₈ : Nat) → (a₁₉ : Nat) → (a₂₀ : Nat) → motive₀ (g₂ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀)) → motive₀ (InductiveFixtures:Wide:node f₁ g₂ h₃ k₄)) → (t₁ : InductiveFixtures:Wide) → motive₀ t₁
InductiveFixtures:Wide:rec {motive₀} leaf₁ node₂ InductiveFixtures:Wide:leaf = leaf₁
InductiveFixtures:Wide:rec {motive₀} leaf₁ node₂ (InductiveFixtures:Wide:node f₃ g₄ h₅ k₆) = node₂ f₃ g₄ h₅ k₆ (λ (a₇ : Nat) → λ (a₈ : Nat) → λ (a₉ : Nat) → λ (a₁₀ : Nat) → λ (a₁₁ : Nat) → λ (a₁₂ : Nat) → λ (a₁₃ : Nat) → λ (a₁₄ : Nat) → λ (a₁₅ : Nat) → λ (a₁₆ : Nat) → λ (a₁₇ : Nat) → λ (a₁₈ : Nat) → λ (a₁₉ : Nat) → λ (a₂₀ : Nat) → λ (a₂₁ : Nat) → λ (a₂₂ : Nat) → InductiveFixtures:Wide:rec {motive₀} leaf₁ node₂ (f₃ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁ a₂₂)) (λ (a₇ : Nat) → λ (a₈ : Nat) → λ (a₉ : Nat) → λ (a₁₀ : Nat) → λ (a₁₁ : Nat) → λ (a₁₂ : Nat) → λ (a₁₃ : Nat) → λ (a₁₄ : Nat) → λ (a₁₅ : Nat) → λ (a₁₆ : Nat) → λ (a₁₇ : Nat) → λ (a₁₈ : Nat) → λ (a₁₉ : Nat) → λ (a₂₀ : Nat) → λ (a₂₁ : Nat) → λ (a₂₂ : Nat) → InductiveFixtures:Wide:rec {motive₀} leaf₁ node₂ (g₄ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁ a₂₂))
