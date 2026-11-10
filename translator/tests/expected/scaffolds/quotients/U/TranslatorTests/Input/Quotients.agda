{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of QuotFixtures:eta~umk QuotFixtures:ind~umk QuotFixtures:over~umk QuotFixtures:succ QuotFixtures:succ~umk
-- Lean module TranslatorTests.Input.Quotients
module U.TranslatorTests.Input.Quotients where
import U.Init.Prelude

-- theorem
opaque
  QuotFixtures:eta~umk : (f₀ : U.Init.Prelude.Nat → U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat → U.Init.Prelude.Nat} (λ (x₁ : U.Init.Prelude.Nat) → U.Init.Prelude.Quot:lift {U.Init.Prelude.Nat → U.Init.Prelude.Nat} {U.Init.Prelude.Eq {U.Init.Prelude.Nat → U.Init.Prelude.Nat}} {U.Init.Prelude.Nat} (λ (g₂ : U.Init.Prelude.Nat → U.Init.Prelude.Nat) → g₂ x₁) (λ (x₂ : U.Init.Prelude.Nat → U.Init.Prelude.Nat) → λ (x₃ : U.Init.Prelude.Nat → U.Init.Prelude.Nat) → λ (h₄ : U.Init.Prelude.Eq {U.Init.Prelude.Nat → U.Init.Prelude.Nat} x₂ x₃) → U.Init.Prelude.congrArg {U.Init.Prelude.Nat → U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {x₂} {x₃} (λ (g₅ : U.Init.Prelude.Nat → U.Init.Prelude.Nat) → g₅ x₁) h₄) (U.Init.Prelude.Quot:mk {U.Init.Prelude.Nat → U.Init.Prelude.Nat} (U.Init.Prelude.Eq {U.Init.Prelude.Nat → U.Init.Prelude.Nat}) f₀)) f₀
  QuotFixtures:eta~umk f₀ = U.Init.Prelude.rfl {U.Init.Prelude.Nat → U.Init.Prelude.Nat} {λ (x₁ : U.Init.Prelude.Nat) → U.Init.Prelude.Quot:lift {U.Init.Prelude.Nat → U.Init.Prelude.Nat} {U.Init.Prelude.Eq {U.Init.Prelude.Nat → U.Init.Prelude.Nat}} {U.Init.Prelude.Nat} (λ (g₂ : U.Init.Prelude.Nat → U.Init.Prelude.Nat) → g₂ x₁) (λ (x₂ : U.Init.Prelude.Nat → U.Init.Prelude.Nat) → λ (x₃ : U.Init.Prelude.Nat → U.Init.Prelude.Nat) → λ (h₄ : U.Init.Prelude.Eq {U.Init.Prelude.Nat → U.Init.Prelude.Nat} x₂ x₃) → U.Init.Prelude.congrArg {U.Init.Prelude.Nat → U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {x₂} {x₃} (λ (g₅ : U.Init.Prelude.Nat → U.Init.Prelude.Nat) → g₅ x₁) h₄) (U.Init.Prelude.Quot:mk {U.Init.Prelude.Nat → U.Init.Prelude.Nat} (U.Init.Prelude.Eq {U.Init.Prelude.Nat → U.Init.Prelude.Nat}) f₀)}

-- theorem
opaque
  QuotFixtures:ind~umk : (n₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Eq {U.Init.Prelude.Nat} n₀ n₀} (U.Init.Prelude.Quot:ind {U.Init.Prelude.Nat} {U.Init.Prelude.Eq {U.Init.Prelude.Nat}} {λ (x₁ : U.Init.Prelude.Quot {U.Init.Prelude.Nat} (U.Init.Prelude.Eq {U.Init.Prelude.Nat})) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} n₀ n₀} (λ (x₁ : U.Init.Prelude.Nat) → U.Init.Prelude.rfl {U.Init.Prelude.Nat} {n₀}) (U.Init.Prelude.Quot:mk {U.Init.Prelude.Nat} (U.Init.Prelude.Eq {U.Init.Prelude.Nat}) n₀)) (U.Init.Prelude.rfl {U.Init.Prelude.Nat} {n₀})
  QuotFixtures:ind~umk n₀ = U.Init.Prelude.rfl {U.Init.Prelude.Eq {U.Init.Prelude.Nat} n₀ n₀} {U.Init.Prelude.Quot:ind {U.Init.Prelude.Nat} {U.Init.Prelude.Eq {U.Init.Prelude.Nat}} {λ (x₁ : U.Init.Prelude.Quot {U.Init.Prelude.Nat} (U.Init.Prelude.Eq {U.Init.Prelude.Nat})) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} n₀ n₀} (λ (x₁ : U.Init.Prelude.Nat) → U.Init.Prelude.rfl {U.Init.Prelude.Nat} {n₀}) (U.Init.Prelude.Quot:mk {U.Init.Prelude.Nat} (U.Init.Prelude.Eq {U.Init.Prelude.Nat}) n₀)}

QuotFixtures:over~umk:~ushare:~n1 : U.Init.Prelude.Quot {U.Init.Prelude.Nat} (U.Init.Prelude.Eq {U.Init.Prelude.Nat}) → U.Init.Prelude.Nat → U.Init.Prelude.Nat
QuotFixtures:over~umk:~ushare:~n1 = U.Init.Prelude.Quot:lift {U.Init.Prelude.Nat} {U.Init.Prelude.Eq {U.Init.Prelude.Nat}} {U.Init.Prelude.Nat → U.Init.Prelude.Nat} (λ (a₀ : U.Init.Prelude.Nat) → λ (x₁ : U.Init.Prelude.Nat) → a₀) (λ (x₀ : U.Init.Prelude.Nat) → λ (x₁ : U.Init.Prelude.Nat) → λ (h₂ : U.Init.Prelude.Eq {U.Init.Prelude.Nat} x₀ x₁) → U.Init.Prelude.congrArg {U.Init.Prelude.Nat} {U.Init.Prelude.Nat → U.Init.Prelude.Nat} {x₀} {x₁} (λ (a₃ : U.Init.Prelude.Nat) → λ (x₄ : U.Init.Prelude.Nat) → a₃) h₂)

-- theorem
opaque
  QuotFixtures:over~umk : (n₀ : U.Init.Prelude.Nat) → (m₁ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (QuotFixtures:over~umk:~ushare:~n1 (U.Init.Prelude.Quot:mk {U.Init.Prelude.Nat} (U.Init.Prelude.Eq {U.Init.Prelude.Nat}) n₀) m₁) n₀
  QuotFixtures:over~umk n₀ m₁ = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {QuotFixtures:over~umk:~ushare:~n1 (U.Init.Prelude.Quot:mk {U.Init.Prelude.Nat} (U.Init.Prelude.Eq {U.Init.Prelude.Nat}) n₀) m₁}

QuotFixtures:succ : U.Init.Prelude.Quot {U.Init.Prelude.Nat} (U.Init.Prelude.Eq {U.Init.Prelude.Nat}) → U.Init.Prelude.Nat
QuotFixtures:succ q₀ = U.Init.Prelude.Quot:lift {U.Init.Prelude.Nat} {U.Init.Prelude.Eq {U.Init.Prelude.Nat}} {U.Init.Prelude.Nat} U.Init.Prelude.Nat:succ (λ (x₁ : U.Init.Prelude.Nat) → λ (x₂ : U.Init.Prelude.Nat) → λ (h₃ : U.Init.Prelude.Eq {U.Init.Prelude.Nat} x₁ x₂) → U.Init.Prelude.congrArg {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {x₁} {x₂} U.Init.Prelude.Nat:succ h₃) q₀

-- theorem
opaque
  QuotFixtures:succ~umk : (n₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (QuotFixtures:succ (U.Init.Prelude.Quot:mk {U.Init.Prelude.Nat} (U.Init.Prelude.Eq {U.Init.Prelude.Nat}) n₀)) (U.Init.Prelude.Nat:succ n₀)
  QuotFixtures:succ~umk n₀ = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {QuotFixtures:succ (U.Init.Prelude.Quot:mk {U.Init.Prelude.Nat} (U.Init.Prelude.Eq {U.Init.Prelude.Nat}) n₀)}
