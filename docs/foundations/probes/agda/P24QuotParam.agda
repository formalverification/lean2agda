-- Outcome on 2026-10-07 with Agda 2.8.0: rejected, [UnequalTerms] lift f h (mk R a) != f a of type A
{-# OPTIONS --safe --cubical-compatible #-}
module P24QuotParam where
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Level using (Level; suc; _⊔_)
-- Lean's quotient primitives as a record, the module-parameter strategy for profiles K and CC;
-- the computation rule is a field, since a parameter cannot compute
record Quotients : Set₁ where
  field
    Quot : (A : Set) → (A → A → Set) → Set
    mk : {A : Set} (R : A → A → Set) → A → Quot A R
    lift : {A : Set} {R : A → A → Set} {B : Set} (f : A → B)
         → (∀ a b → R a b → f a ≡ f b) → Quot A R → B
    ind : {A : Set} {R : A → A → Set} {P : Quot A R → Set}
        → (∀ a → P (mk R a)) → ∀ q → P q
    sound : {A : Set} {R : A → A → Set} {a b : A} → R a b → mk R a ≡ mk R b
    lift-β : {A : Set} {R : A → A → Set} {B : Set} (f : A → B)
           → (h : ∀ a b → R a b → f a ≡ f b) (a : A) → lift f h (mk R a) ≡ f a
module _ (Q : Quotients) where
  open Quotients Q
  -- what Lean checks by computation needs the field here: refl is rejected
  _ : {A : Set} {R : A → A → Set} (f : A → A) (h : ∀ a b → R a b → f a ≡ f b) (a : A)
    → lift f h (mk R a) ≡ f a
  _ = λ f h a → refl
