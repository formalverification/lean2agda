-- Outcome on 2026-11-10 with Agda 2.8.0: accepted
{-# OPTIONS --type-in-type --rewriting --local-confluence-check #-}
module P31NatSubRewrite where
-- Profile U's options, with Agda's local confluence check.  Nat.sub's equation at a successor,
-- which the builtin monus loses (probe P30), proved by induction and declared a rewrite rule, as
-- the operation table emits it under profile U, with two more rules that make the set confluent
-- with the monus's own clauses 0 - suc m = 0 and suc n - suc m = n - m.  Nat.pred is Lean's two
-- clauses, so that a rule headed by it can fire.  The check accepts the three declared by one
-- pragma; declared alone, the first is refused (RewriteNonConfluent, the pair at suc n - suc m).
-- The equation then holds by conversion on variables, so do the two critical pairs, and Agda still
-- computes the monus of two numerals with the host's integers.  --safe refuses --rewriting, so
-- profiles K and CC cannot state the rules.
data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

data Eq {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl : (a₁ : α₀) → Eq {α₀} a₁ a₁
{-# BUILTIN REWRITE Eq #-}

Nat:sub-builtin : Nat → Nat → Nat
Nat:sub-builtin n₀ Nat:zero = n₀
Nat:sub-builtin Nat:zero (Nat:succ m₁) = Nat:zero
Nat:sub-builtin (Nat:succ n₀) (Nat:succ m₁) = Nat:sub-builtin n₀ m₁
{-# BUILTIN NATMINUS Nat:sub-builtin #-}

Nat:pred : Nat → Nat
Nat:pred Nat:zero = Nat:zero
Nat:pred (Nat:succ n₀) = n₀

Nat:sub-builtin-succ : (n₀ : Nat) → (m₁ : Nat) → Eq {Nat} (Nat:sub-builtin n₀ (Nat:succ m₁)) (Nat:pred (Nat:sub-builtin n₀ m₁))
Nat:sub-builtin-succ Nat:zero Nat:zero = Eq:refl Nat:zero
Nat:sub-builtin-succ Nat:zero (Nat:succ m₁) = Eq:refl Nat:zero
Nat:sub-builtin-succ (Nat:succ n₀) Nat:zero = Eq:refl n₀
Nat:sub-builtin-succ (Nat:succ n₀) (Nat:succ m₁) = Nat:sub-builtin-succ n₀ m₁

Nat:sub-builtin-pred-zero : (m₁ : Nat) → Eq {Nat} (Nat:pred (Nat:sub-builtin Nat:zero m₁)) Nat:zero
Nat:sub-builtin-pred-zero Nat:zero = Eq:refl Nat:zero
Nat:sub-builtin-pred-zero (Nat:succ m₁) = Eq:refl Nat:zero

Nat:sub-builtin-pred-succ : (n₀ : Nat) → (m₁ : Nat) → Eq {Nat} (Nat:pred (Nat:sub-builtin (Nat:succ n₀) m₁)) (Nat:sub-builtin n₀ m₁)
Nat:sub-builtin-pred-succ n₀ Nat:zero = Eq:refl n₀
Nat:sub-builtin-pred-succ Nat:zero (Nat:succ m₁) = Nat:sub-builtin-pred-zero m₁
Nat:sub-builtin-pred-succ (Nat:succ n₀) (Nat:succ m₁) = Nat:sub-builtin-pred-succ n₀ m₁

{-# REWRITE Nat:sub-builtin-succ Nat:sub-builtin-pred-zero Nat:sub-builtin-pred-succ #-}

-- Lean's equation on variables
_ : (n m : Nat) → Eq (Nat:sub-builtin n (Nat:succ m)) (Nat:pred (Nat:sub-builtin n m))
_ = λ n m → Eq:refl _
-- the critical pairs with the monus's own clauses
_ : (m : Nat) → Eq (Nat:sub-builtin Nat:zero (Nat:succ m)) (Nat:pred (Nat:sub-builtin Nat:zero m))
_ = λ m → Eq:refl _
_ : (n m : Nat) → Eq (Nat:sub-builtin (Nat:succ n) (Nat:succ m)) (Nat:pred (Nat:sub-builtin (Nat:succ n) m))
_ = λ n m → Eq:refl _
-- numerals still compute at once
_ : Eq (Nat:sub-builtin 340282366920938463463374607431768211456 18446744073709551616) 340282366920938463444927863358058659840
_ = Eq:refl _
_ : Eq (Nat:pred (Nat:sub-builtin 18446744073709551616 340282366920938463463374607431768211456)) 0
_ = Eq:refl _
