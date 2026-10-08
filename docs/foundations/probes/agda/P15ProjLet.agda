-- Outcome on 2026-10-07 with Agda 2.8.0: accepted
{-# OPTIONS --safe --cubical-compatible #-}
module P15ProjLet where
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; _+_)
p : ℕ × ℕ
p = (1 , 2)
-- projections compute on constructors
_ : proj₁ p ≡ 1
_ = refl
-- let is non-recursive sugar, substituted away; a record pattern is allowed in it
_ : (let x = 1 in x + x) ≡ 2
_ = refl
_ : (let (a , b) = p in a + b) ≡ 3
_ = refl
