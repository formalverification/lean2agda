-- Outcome on 2026-10-07 with Agda 2.8.0: accepted
{-# OPTIONS --safe --cubical-compatible #-}
module P11Literals where
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; _+_; _*_; _^_; _/_; _%_)
open import Data.Nat.GCD using (gcd)
open import Data.String using (String; _++_; toList)
open import Data.Char using (Char)
open import Data.List using (List; _∷_; [])
open import Agda.Builtin.String using (primStringFromList)
-- Nat literals and arithmetic are the builtin ones: closed terms compute at machine speed
_ : 18446744073709551616 + 1 ≡ 18446744073709551617
_ = refl
_ : 2 ^ 64 ≡ 18446744073709551616
_ = refl
_ : 1000000007 * 998244353 ≡ 998244359987710471
_ = refl
_ : 998244359987710471 / 1000000007 ≡ 998244353
_ = refl
_ : 998244359987710471 % 1000000007 ≡ 0
_ = refl
-- gcd is a library function by well-founded recursion, not a builtin; closed terms still compute
_ : gcd 12 18 ≡ 6
_ = refl
_ : gcd 1000000007 998244353 ≡ 1
_ = refl
-- String literals are primitive, not a structure over List Char; the conversions compute
_ : "ab" ++ "c" ≡ "abc"
_ = refl
_ : primStringFromList ('a' ∷ 'b' ∷ []) ≡ "ab"
_ = refl
_ : toList "ab" ≡ 'a' ∷ 'b' ∷ []
_ = refl
