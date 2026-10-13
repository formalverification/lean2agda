-- File: translator/tests/expected/scaffolds/selected.agda
{-# OPTIONS --type-in-type #-}
-- lean2agda, profile U: the scaffold of the closure of Fixtures:selected
module U.TranslatorTests.Input.Consumer where

record Add (α₀ : Set) : Set where
  constructor Add:mk
  field
    add₁ : α₀ → α₀ → α₀

postulate Add:rec : {α₀ : Set} → {motive₁ : Add α₀ → Set} → ((add₂ : α₀ → α₀ → α₀) → motive₁ (Add:mk {α₀} add₂)) → (t₂ : Add α₀) → motive₁ t₂

Add:add : {α₀ : Set} → ⦃ _ : Add α₀ ⦄ → α₀ → α₀ → α₀
Add:add {α₀} ⦃ self₁ ⦄ = Add.add₁ {α₀} self₁

data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

postulate Nat:rec : {motive₀ : Nat → Set} → motive₀ Nat:zero → ((n₁ : Nat) → motive₀ n₁ → motive₀ (Nat:succ n₁)) → (t₁ : Nat) → motive₀ t₁

record OfNat (α₀ : Set) (x₁ : Nat) : Set where
  constructor OfNat:mk
  field
    ofNat₂ : α₀

postulate OfNat:rec : {α₀ : Set} → {x₁ : Nat} → {motive₂ : OfNat α₀ x₁ → Set} → ((ofNat₃ : α₀) → motive₂ (OfNat:mk {α₀} {x₁} ofNat₃)) → (t₃ : OfNat α₀ x₁) → motive₂ t₃

OfNat:ofNat : {α₀ : Set} → (x₁ : Nat) → ⦃ _ : OfNat α₀ x₁ ⦄ → α₀
OfNat:ofNat {α₀} x₁ ⦃ self₂ ⦄ = OfNat.ofNat₂ {α₀} {x₁} self₂

instOfNatNat : (n₀ : Nat) → OfNat Nat n₀
instOfNatNat n₀ = OfNat:mk {Nat} {n₀} n₀

Fixtures:token : Nat
Fixtures:token = OfNat:ofNat {Nat} 17 ⦃ instOfNatNat 17 ⦄

outParam : Set → Set
outParam α₀ = α₀

record HAdd (α₀ : Set) (β₁ : Set) (γ₂ : outParam Set) : Set where
  constructor HAdd:mk
  field
    hAdd₃ : α₀ → β₁ → γ₂

postulate HAdd:rec : {α₀ : Set} → {β₁ : Set} → {γ₂ : Set} → {motive₃ : HAdd α₀ β₁ γ₂ → Set} → ((hAdd₄ : α₀ → β₁ → γ₂) → motive₃ (HAdd:mk {α₀} {β₁} {γ₂} hAdd₄)) → (t₄ : HAdd α₀ β₁ γ₂) → motive₃ t₄

HAdd:hAdd : {α₀ : Set} → {β₁ : Set} → {γ₂ : outParam Set} → ⦃ _ : HAdd α₀ β₁ γ₂ ⦄ → α₀ → β₁ → γ₂
HAdd:hAdd {α₀} {β₁} {γ₂} ⦃ self₃ ⦄ = HAdd.hAdd₃ {α₀} {β₁} {γ₂} self₃

Nat:casesOn : {motive₀ : Nat → Set} → (t₁ : Nat) → motive₀ Nat:zero → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ t₁
Nat:casesOn {motive₀} t₁ zero₂ succ₃ = Nat:rec {motive₀} zero₂ (λ (n₄ : Nat) → λ (nih₅ : motive₀ n₄) → succ₃ n₄) t₁

Nat:add:match~u1 : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → ((a₃ : Nat) → motive₀ a₃ Nat:zero) → ((a₃ : Nat) → (b₄ : Nat) → motive₀ a₃ (Nat:succ b₄)) → motive₀ x₁ x₂
Nat:add:match~u1 motive₀ x₁ x₂ h1₃ h2₄ = Nat:casesOn {λ (x₅ : Nat) → motive₀ x₁ x₅} x₂ (h1₃ x₁) (λ (n₅ : Nat) → h2₄ x₁ n₅)

record PProd (α₀ : Set) (β₁ : Set) : Set where
  constructor PProd:mk
  field
    fst₂ : α₀
    snd₃ : β₁

postulate PProd:rec : {α₀ : Set} → {β₁ : Set} → {motive₂ : PProd α₀ β₁ → Set} → ((fst₃ : α₀) → (snd₄ : β₁) → motive₂ (PProd:mk {α₀} {β₁} fst₃ snd₄)) → (t₃ : PProd α₀ β₁) → motive₂ t₃

record PUnit : Set where
  constructor PUnit:unit

postulate PUnit:rec : {motive₀ : PUnit → Set} → motive₀ PUnit:unit → (t₁ : PUnit) → motive₀ t₁

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

~uprivate:TranslatorTests:Input:Consumer:~n0:Fixtures:secret : Nat
~uprivate:TranslatorTests:Input:Consumer:~n0:Fixtures:secret = HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ Fixtures:token (OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄)

Fixtures:selected : Nat
Fixtures:selected = ~uprivate:TranslatorTests:Input:Consumer:~n0:Fixtures:secret
