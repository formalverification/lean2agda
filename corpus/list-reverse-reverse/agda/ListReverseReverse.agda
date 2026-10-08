{-# OPTIONS --safe --cubical-compatible #-}

-- File: corpus/list-reverse-reverse/agda/ListReverseReverse.agda
--
-- Lean's List.reverse_reverse (Init.Data.List.Lemmas, Lean v4.33.1):
--
--     theorem reverse_reverse (as : List α) : as.reverse.reverse = as
--
-- stated over agda-stdlib's List and reverse, and proved twice: by
-- agda-stdlib's reverse-involutive, the idiomatic proof, and by a direct
-- induction that follows the structure of Lean's kernel term, for
-- comparison (see ../notes.md).

module ListReverseReverse where

open import Level using (Level)
open import Data.List.Base using (List; []; _∷_; reverse; reverseAcc)
open import Data.List.Properties using (reverse-involutive)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

private
  variable
    a : Level
    A : Set a

-- The idiomatic translation.  Lean's universe variable u_1 becomes the
-- level a, and Lean's binder `as` becomes xs, the usual Agda name.

reverse-reverse : (xs : List A) → reverse (reverse xs) ≡ xs
reverse-reverse = reverse-involutive

-- The direct proof.  Lean defines reverse as reverseAux as [], where
-- reverseAux takes the list first and the accumulator second; agda-stdlib
-- defines reverse as reverseAcc [], with the accumulator first.  The two
-- auxiliaries agree clause by clause, so Lean's lemma
--
--     theorem reverseAux_reverseAux_nil :
--       reverseAux (reverseAux as bs) [] = reverseAux bs as
--
-- reads as follows with the arguments swapped.  Lean proves its step case
-- with simp, which closes the goal through eq_self and so brings in
-- propext; here the step case is the induction hypothesis, by computation.

reverseAcc-reverseAcc-nil : (xs ys : List A)
                          → reverseAcc [] (reverseAcc ys xs) ≡ reverseAcc xs ys
reverseAcc-reverseAcc-nil []       ys = refl
reverseAcc-reverseAcc-nil (x ∷ xs) ys = reverseAcc-reverseAcc-nil xs (x ∷ ys)

reverse-reverse-direct : (xs : List A) → reverse (reverse xs) ≡ xs
reverse-reverse-direct xs = reverseAcc-reverseAcc-nil xs []
