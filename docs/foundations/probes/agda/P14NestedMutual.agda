-- Outcome on 2026-10-07 with Agda 2.8.0: accepted
{-# OPTIONS --safe --cubical-compatible #-}
module P14NestedMutual where
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
-- nested: Rose trees through List
data Rose (A : Set) : Set where
  node : A → List (Rose A) → Rose A
-- mutual: two types that refer to each other, Lists'-style
mutual
  data Lists' : Set where
    atom : ℕ → Lists'
    cons : Lists' → Lists → Lists'
  data Lists : Set where
    nil : Lists
    of : Lists' → Lists
-- mutual predicates, with an interleaved function
mutual
  data Even : ℕ → Set where
    zero : Even zero
    suc : ∀ {n} → Odd n → Even (suc n)
  data Odd : ℕ → Set where
    suc : ∀ {n} → Even n → Odd (suc n)
-- induction-recursion, which Lean's kernel does not have
mutual
  data U : Set where
    nat : U
    pi : (a : U) → (El a → U) → U
  El : U → Set
  El nat = ℕ
  El (pi a b) = (x : El a) → El (b x)
