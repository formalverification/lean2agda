{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of ArithmeticFixtures:add~uone ArithmeticFixtures:add~usucc ArithmeticFixtures:add~uzero ArithmeticFixtures:beq~usucc~usucc ArithmeticFixtures:beq~usucc~uzero and 49 more
-- Lean module Init.Data.Nat.Coprime
module U.Init.Data.Nat.Coprime where
import U.Init.Data.Nat.Gcd
import U.Init.Prelude

Nat:Coprime : U.Init.Prelude.Nat → U.Init.Prelude.Nat → Set
Nat:Coprime m₀ n₁ = U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Data.Nat.Gcd.Nat:gcd m₀ n₁) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄)

Nat:instDecidableCoprime : (m₀ : U.Init.Prelude.Nat) → (n₁ : U.Init.Prelude.Nat) → U.Init.Prelude.Decidable (Nat:Coprime m₀ n₁)
Nat:instDecidableCoprime m₀ n₁ = U.Init.Prelude.instDecidableEqNat (U.Init.Data.Nat.Gcd.Nat:gcd m₀ n₁) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄)
