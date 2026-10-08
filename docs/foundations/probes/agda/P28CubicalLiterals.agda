-- Outcome on 2026-10-07 with Agda 2.8.0: accepted
{-# OPTIONS --safe --cubical --guardedness #-}
module P28CubicalLiterals where
open import Cubical.Foundations.Prelude
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String; primStringAppend)
_ : 18446744073709551616 + 1 ≡ 18446744073709551617
_ = refl
_ : 4294967296 * 4294967296 ≡ 18446744073709551616
_ = refl
_ : primStringAppend "ab" "c" ≡ "abc"
_ = refl
