{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of RecursorFixtures:Doc RecursorFixtures:Doc:~usizeOf~u1 RecursorFixtures:Doc:~usizeOf~u2 RecursorFixtures:Doc:~usizeOf~u2~ueq RecursorFixtures:Doc:~usizeOf~u3 and 251 more
-- Lean module Init.Data.Zero
module U.Init.Data.Zero where
import U.Init.Prelude

Zero:toOfNat0 : {α₀ : Set} → ⦃ _ : U.Init.Prelude.Zero α₀ ⦄ → U.Init.Prelude.OfNat α₀ 0
Zero:toOfNat0 {α₀} ⦃ inst₁ ⦄ = U.Init.Prelude.OfNat:mk {α₀} {0} (U.Init.Prelude.Zero:zero {α₀} ⦃ inst₁ ⦄)

Zero:ofOfNat0 : {α₀ : Set} → ⦃ _ : U.Init.Prelude.OfNat α₀ 0 ⦄ → U.Init.Prelude.Zero α₀
Zero:ofOfNat0 {α₀} ⦃ inst₁ ⦄ = U.Init.Prelude.Zero:mk {α₀} (U.Init.Prelude.OfNat:ofNat {α₀} 0 ⦃ inst₁ ⦄)
