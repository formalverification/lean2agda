-- Outcome on 2026-10-07 with Agda 2.8.0: rejected, [SplitInProp] Cannot split on datatype in Prop unless target is in Prop
{-# OPTIONS --safe --prop #-}
module P02bAccProp where
data AccP {A : Set} (R : A → A → Set) (x : A) : Prop where
  acc : (∀ y → R y x → AccP R y) → AccP R x
-- Lean's Acc.rec into Sort u; Agda rejects the Set-valued motive
wfRec : {A : Set} (R : A → A → Set) (P : A → Set)
      → (∀ x → (∀ y → R y x → P y) → P x) → ∀ x → AccP R x → P x
wfRec R P step x (acc h) = step x (λ y r → wfRec R P step y (h y r))
