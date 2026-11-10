{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of RecursorFixtures:Doc RecursorFixtures:Doc:~usizeOf~u1 RecursorFixtures:Doc:~usizeOf~u2 RecursorFixtures:Doc:~usizeOf~u2~ueq RecursorFixtures:Doc:~usizeOf~u3 and 251 more
-- Lean module Init.Data.Fin.Basic
module U.Init.Data.Fin.Basic where
import U.Init.Data.Nat.Basic
import U.Init.Data.NeZero
import U.Init.Data.Zero
import U.Init.Prelude

-- theorem
opaque
  Fin:ofNat:~uproof~u1 : (n₀ : U.Init.Prelude.Nat) → ⦃ _ : U.Init.Data.NeZero.NeZero {U.Init.Prelude.Nat} ⦃ U.Init.Data.Zero.Zero:ofOfNat0 {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instOfNatNat 0 ⦄ ⦄ n₀ ⦄ → (a₁ : U.Init.Prelude.Nat) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ (U.Init.Prelude.HMod:hMod {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHMod {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.Nat:instMod ⦄ ⦄ a₁ n₀) n₀
  Fin:ofNat:~uproof~u1 n₀ ⦃ inst₁ ⦄ a₂ = U.Init.Prelude.Nat:mod~ult a₂ {n₀} (U.Init.Data.Nat.Basic.Nat:pos~uof~uneZero n₀ ⦃ inst₁ ⦄)

Fin:ofNat : (n₀ : U.Init.Prelude.Nat) → ⦃ _ : U.Init.Data.NeZero.NeZero {U.Init.Prelude.Nat} ⦃ U.Init.Data.Zero.Zero:ofOfNat0 {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instOfNatNat 0 ⦄ ⦄ n₀ ⦄ → U.Init.Prelude.Nat → U.Init.Prelude.Fin n₀
Fin:ofNat n₀ ⦃ inst₁ ⦄ a₂ = U.Init.Prelude.Fin:mk {n₀} (U.Init.Prelude.HMod:hMod {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHMod {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.Nat:instMod ⦄ ⦄ a₂ n₀) (Fin:ofNat:~uproof~u1 n₀ ⦃ inst₁ ⦄ a₂)

Fin:instOfNat : {n₀ : U.Init.Prelude.Nat} → ⦃ _ : U.Init.Data.NeZero.NeZero {U.Init.Prelude.Nat} ⦃ U.Init.Data.Zero.Zero:ofOfNat0 {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instOfNatNat 0 ⦄ ⦄ n₀ ⦄ → {i₁ : U.Init.Prelude.Nat} → U.Init.Prelude.OfNat (U.Init.Prelude.Fin n₀) i₁
Fin:instOfNat {n₀} ⦃ inst₁ ⦄ {i₂} = U.Init.Prelude.OfNat:mk {U.Init.Prelude.Fin n₀} {i₂} (Fin:ofNat n₀ ⦃ inst₁ ⦄ i₂)
