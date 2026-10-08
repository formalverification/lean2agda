-- Outcome on 2026-10-07 with Agda 2.8.0: accepted
{-# OPTIONS --safe --cubical --guardedness #-}
module P27CubicalInductives where
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_)
data Rose (A : Type) : Type where
  node : A → List (Rose A) → Rose A
mutual
  data Lists' : Type where
    atom : ℕ → Lists'
    cons : Lists' → Lists → Lists'
  data Lists : Type where
    nil : Lists
    of : Lists' → Lists
mutual
  data U : Type where
    nat : U
    pi : (a : U) → (El a → U) → U
  El : U → Type
  El nat = ℕ
  El (pi a b) = (x : El a) → El (b x)
