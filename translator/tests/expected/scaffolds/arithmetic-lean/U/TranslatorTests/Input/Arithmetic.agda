{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of ArithmeticFixtures:add~uone ArithmeticFixtures:add~usucc ArithmeticFixtures:add~uzero ArithmeticFixtures:beq~usucc~usucc ArithmeticFixtures:beq~usucc~uzero and 32 more
-- Lean module TranslatorTests.Input.Arithmetic
module U.TranslatorTests.Input.Arithmetic where
import U.Init.Data.Nat.Bitwise.Basic
import U.Init.Data.Nat.Gcd
import U.Init.Prelude

-- theorem
opaque
  ArithmeticFixtures:add~uone : (n₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ n₀ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄)) (U.Init.Prelude.Nat:succ n₀)
  ArithmeticFixtures:add~uone n₀ = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ n₀ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄)}

-- theorem
opaque
  ArithmeticFixtures:add~usucc : (n₀ : U.Init.Prelude.Nat) → (m₁ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Prelude.Nat:add n₀ (U.Init.Prelude.Nat:succ m₁)) (U.Init.Prelude.Nat:succ (U.Init.Prelude.Nat:add n₀ m₁))
  ArithmeticFixtures:add~usucc n₀ m₁ = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {U.Init.Prelude.Nat:add n₀ (U.Init.Prelude.Nat:succ m₁)}

-- theorem
opaque
  ArithmeticFixtures:add~uzero : (n₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Prelude.Nat:add n₀ U.Init.Prelude.Nat:zero) n₀
  ArithmeticFixtures:add~uzero n₀ = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {U.Init.Prelude.Nat:add n₀ U.Init.Prelude.Nat:zero}

-- theorem
opaque
  ArithmeticFixtures:beq~usucc~usucc : (n₀ : U.Init.Prelude.Nat) → (m₁ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Bool} (U.Init.Prelude.Nat:beq (U.Init.Prelude.Nat:succ n₀) (U.Init.Prelude.Nat:succ m₁)) (U.Init.Prelude.Nat:beq n₀ m₁)
  ArithmeticFixtures:beq~usucc~usucc n₀ m₁ = U.Init.Prelude.rfl {U.Init.Prelude.Bool} {U.Init.Prelude.Nat:beq (U.Init.Prelude.Nat:succ n₀) (U.Init.Prelude.Nat:succ m₁)}

-- theorem
opaque
  ArithmeticFixtures:beq~usucc~uzero : (n₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Bool} (U.Init.Prelude.Nat:beq (U.Init.Prelude.Nat:succ n₀) U.Init.Prelude.Nat:zero) U.Init.Prelude.Bool:false
  ArithmeticFixtures:beq~usucc~uzero n₀ = U.Init.Prelude.rfl {U.Init.Prelude.Bool} {U.Init.Prelude.Nat:beq (U.Init.Prelude.Nat:succ n₀) U.Init.Prelude.Nat:zero}

-- theorem
opaque
  ArithmeticFixtures:beq~uzero~usucc : (m₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Bool} (U.Init.Prelude.Nat:beq U.Init.Prelude.Nat:zero (U.Init.Prelude.Nat:succ m₀)) U.Init.Prelude.Bool:false
  ArithmeticFixtures:beq~uzero~usucc m₀ = U.Init.Prelude.rfl {U.Init.Prelude.Bool} {U.Init.Prelude.Nat:beq U.Init.Prelude.Nat:zero (U.Init.Prelude.Nat:succ m₀)}

-- theorem
opaque
  ArithmeticFixtures:beq~uzero~uzero : U.Init.Prelude.Eq {U.Init.Prelude.Bool} (U.Init.Prelude.Nat:beq U.Init.Prelude.Nat:zero U.Init.Prelude.Nat:zero) U.Init.Prelude.Bool:true
  ArithmeticFixtures:beq~uzero~uzero = U.Init.Prelude.rfl {U.Init.Prelude.Bool} {U.Init.Prelude.Nat:beq U.Init.Prelude.Nat:zero U.Init.Prelude.Nat:zero}

-- theorem
opaque
  ArithmeticFixtures:bitwise~uzero~uleft : (f₀ : U.Init.Prelude.Bool → U.Init.Prelude.Bool → U.Init.Prelude.Bool) → (m₁ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Data.Nat.Bitwise.Basic.Nat:bitwise f₀ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄) m₁) (U.Init.Prelude.ite {U.Init.Prelude.Nat} (U.Init.Prelude.Eq {U.Init.Prelude.Bool} (f₀ U.Init.Prelude.Bool:false U.Init.Prelude.Bool:true) U.Init.Prelude.Bool:true) ⦃ U.Init.Prelude.instDecidableEqBool (f₀ U.Init.Prelude.Bool:false U.Init.Prelude.Bool:true) U.Init.Prelude.Bool:true ⦄ m₁ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄))
  ArithmeticFixtures:bitwise~uzero~uleft f₀ m₁ = U.Init.Prelude.Eq:refl {U.Init.Prelude.Nat} (U.Init.Data.Nat.Bitwise.Basic.Nat:bitwise f₀ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄) m₁)

-- theorem
opaque
  ArithmeticFixtures:ble~uoffset : (m₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Bool} (U.Init.Prelude.Nat:ble (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 3 ⦃ U.Init.Prelude.instOfNatNat 3 ⦄) (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ m₀ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 4 ⦃ U.Init.Prelude.instOfNatNat 4 ⦄))) U.Init.Prelude.Bool:true
  ArithmeticFixtures:ble~uoffset m₀ = U.Init.Prelude.rfl {U.Init.Prelude.Bool} {U.Init.Prelude.Nat:ble (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 3 ⦃ U.Init.Prelude.instOfNatNat 3 ⦄) (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ m₀ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 4 ⦃ U.Init.Prelude.instOfNatNat 4 ⦄))}

-- theorem
opaque
  ArithmeticFixtures:ble~usucc~usucc : (n₀ : U.Init.Prelude.Nat) → (m₁ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Bool} (U.Init.Prelude.Nat:ble (U.Init.Prelude.Nat:succ n₀) (U.Init.Prelude.Nat:succ m₁)) (U.Init.Prelude.Nat:ble n₀ m₁)
  ArithmeticFixtures:ble~usucc~usucc n₀ m₁ = U.Init.Prelude.rfl {U.Init.Prelude.Bool} {U.Init.Prelude.Nat:ble (U.Init.Prelude.Nat:succ n₀) (U.Init.Prelude.Nat:succ m₁)}

-- theorem
opaque
  ArithmeticFixtures:ble~usucc~uzero : (n₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Bool} (U.Init.Prelude.Nat:ble (U.Init.Prelude.Nat:succ n₀) U.Init.Prelude.Nat:zero) U.Init.Prelude.Bool:false
  ArithmeticFixtures:ble~usucc~uzero n₀ = U.Init.Prelude.rfl {U.Init.Prelude.Bool} {U.Init.Prelude.Nat:ble (U.Init.Prelude.Nat:succ n₀) U.Init.Prelude.Nat:zero}

-- theorem
opaque
  ArithmeticFixtures:ble~uzero : (m₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Bool} (U.Init.Prelude.Nat:ble U.Init.Prelude.Nat:zero m₀) U.Init.Prelude.Bool:true
  ArithmeticFixtures:ble~uzero m₀ = U.Init.Prelude.rfl {U.Init.Prelude.Bool} {U.Init.Prelude.Nat:ble U.Init.Prelude.Nat:zero m₀}

-- theorem
opaque
  ArithmeticFixtures:div~uoffset : (m₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Prelude.HDiv:hDiv {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHDiv {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.Nat:instDiv ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 3 ⦃ U.Init.Prelude.instOfNatNat 3 ⦄) (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ m₀ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 4 ⦃ U.Init.Prelude.instOfNatNat 4 ⦄))) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄)
  ArithmeticFixtures:div~uoffset m₀ = U.Init.Prelude.Eq:refl {U.Init.Prelude.Nat} (U.Init.Prelude.HDiv:hDiv {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHDiv {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.Nat:instDiv ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 3 ⦃ U.Init.Prelude.instOfNatNat 3 ⦄) (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ m₀ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 4 ⦃ U.Init.Prelude.instOfNatNat 4 ⦄)))

-- theorem
opaque
  ArithmeticFixtures:div~uzero : (n₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Prelude.HDiv:hDiv {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHDiv {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.Nat:instDiv ⦄ ⦄ n₀ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄)) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄)
  ArithmeticFixtures:div~uzero n₀ = U.Init.Prelude.Eq:refl {U.Init.Prelude.Nat} (U.Init.Prelude.HDiv:hDiv {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHDiv {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.Nat:instDiv ⦄ ⦄ n₀ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄))

-- theorem
opaque
  ArithmeticFixtures:gcd~uzero~uleft : (n₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Data.Nat.Gcd.Nat:gcd (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄) n₀) n₀
  ArithmeticFixtures:gcd~uzero~uleft n₀ = U.Init.Prelude.Eq:refl {U.Init.Prelude.Nat} (U.Init.Data.Nat.Gcd.Nat:gcd (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄) n₀)

-- theorem
opaque
  ArithmeticFixtures:land~uzero~uleft : (m₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Data.Nat.Bitwise.Basic.Nat:land (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄) m₀) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄)
  ArithmeticFixtures:land~uzero~uleft m₀ = U.Init.Prelude.Eq:refl {U.Init.Prelude.Nat} (U.Init.Data.Nat.Bitwise.Basic.Nat:land (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄) m₀)

-- theorem
opaque
  ArithmeticFixtures:lor~uzero~uleft : (m₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Data.Nat.Bitwise.Basic.Nat:lor (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄) m₀) m₀
  ArithmeticFixtures:lor~uzero~uleft m₀ = U.Init.Prelude.Eq:refl {U.Init.Prelude.Nat} (U.Init.Data.Nat.Bitwise.Basic.Nat:lor (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄) m₀)

-- theorem
opaque
  ArithmeticFixtures:mod~uoffset : (m₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Prelude.HMod:hMod {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHMod {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.Nat:instMod ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 3 ⦃ U.Init.Prelude.instOfNatNat 3 ⦄) (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ m₀ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 4 ⦃ U.Init.Prelude.instOfNatNat 4 ⦄))) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 3 ⦃ U.Init.Prelude.instOfNatNat 3 ⦄)
  ArithmeticFixtures:mod~uoffset m₀ = U.Init.Prelude.Eq:refl {U.Init.Prelude.Nat} (U.Init.Prelude.HMod:hMod {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHMod {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.Nat:instMod ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 3 ⦃ U.Init.Prelude.instOfNatNat 3 ⦄) (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ m₀ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 4 ⦃ U.Init.Prelude.instOfNatNat 4 ⦄)))

-- theorem
opaque
  ArithmeticFixtures:mul~usucc : (n₀ : U.Init.Prelude.Nat) → (m₁ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Prelude.Nat:mul n₀ (U.Init.Prelude.Nat:succ m₁)) (U.Init.Prelude.Nat:add (U.Init.Prelude.Nat:mul n₀ m₁) n₀)
  ArithmeticFixtures:mul~usucc n₀ m₁ = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {U.Init.Prelude.Nat:mul n₀ (U.Init.Prelude.Nat:succ m₁)}

-- theorem
opaque
  ArithmeticFixtures:mul~uzero : (n₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Prelude.Nat:mul n₀ U.Init.Prelude.Nat:zero) U.Init.Prelude.Nat:zero
  ArithmeticFixtures:mul~uzero n₀ = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {U.Init.Prelude.Nat:mul n₀ U.Init.Prelude.Nat:zero}

-- theorem
opaque
  ArithmeticFixtures:pow~usucc : (n₀ : U.Init.Prelude.Nat) → (m₁ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Prelude.Nat:pow n₀ (U.Init.Prelude.Nat:succ m₁)) (U.Init.Prelude.Nat:mul (U.Init.Prelude.Nat:pow n₀ m₁) n₀)
  ArithmeticFixtures:pow~usucc n₀ m₁ = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {U.Init.Prelude.Nat:pow n₀ (U.Init.Prelude.Nat:succ m₁)}

-- theorem
opaque
  ArithmeticFixtures:pow~uzero : (n₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Prelude.Nat:pow n₀ U.Init.Prelude.Nat:zero) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄)
  ArithmeticFixtures:pow~uzero n₀ = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {U.Init.Prelude.Nat:pow n₀ U.Init.Prelude.Nat:zero}

-- theorem
opaque
  ArithmeticFixtures:pred~usucc : (n₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Prelude.Nat:pred (U.Init.Prelude.Nat:succ n₀)) n₀
  ArithmeticFixtures:pred~usucc n₀ = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {U.Init.Prelude.Nat:pred (U.Init.Prelude.Nat:succ n₀)}

-- theorem
opaque
  ArithmeticFixtures:pred~uzero : U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Prelude.Nat:pred (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄)) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄)
  ArithmeticFixtures:pred~uzero = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {U.Init.Prelude.Nat:pred (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄)}

-- theorem
opaque
  ArithmeticFixtures:shiftLeft~usucc : (n₀ : U.Init.Prelude.Nat) → (m₁ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Data.Nat.Bitwise.Basic.Nat:shiftLeft n₀ (U.Init.Prelude.Nat:succ m₁)) (U.Init.Data.Nat.Bitwise.Basic.Nat:shiftLeft (U.Init.Prelude.HMul:hMul {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHMul {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instMulNat ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 2 ⦃ U.Init.Prelude.instOfNatNat 2 ⦄) n₀) m₁)
  ArithmeticFixtures:shiftLeft~usucc n₀ m₁ = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {U.Init.Data.Nat.Bitwise.Basic.Nat:shiftLeft n₀ (U.Init.Prelude.Nat:succ m₁)}

-- theorem
opaque
  ArithmeticFixtures:shiftLeft~uzero : (n₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Data.Nat.Bitwise.Basic.Nat:shiftLeft n₀ U.Init.Prelude.Nat:zero) n₀
  ArithmeticFixtures:shiftLeft~uzero n₀ = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {U.Init.Data.Nat.Bitwise.Basic.Nat:shiftLeft n₀ U.Init.Prelude.Nat:zero}

-- theorem
opaque
  ArithmeticFixtures:shiftRight~usucc : (n₀ : U.Init.Prelude.Nat) → (m₁ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Data.Nat.Bitwise.Basic.Nat:shiftRight n₀ (U.Init.Prelude.Nat:succ m₁)) (U.Init.Prelude.HDiv:hDiv {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHDiv {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.Nat:instDiv ⦄ ⦄ (U.Init.Data.Nat.Bitwise.Basic.Nat:shiftRight n₀ m₁) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 2 ⦃ U.Init.Prelude.instOfNatNat 2 ⦄))
  ArithmeticFixtures:shiftRight~usucc n₀ m₁ = U.Init.Prelude.Eq:refl {U.Init.Prelude.Nat} (U.Init.Data.Nat.Bitwise.Basic.Nat:shiftRight n₀ (U.Init.Prelude.Nat:succ m₁))

-- theorem
opaque
  ArithmeticFixtures:shiftRight~uzero : (n₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Data.Nat.Bitwise.Basic.Nat:shiftRight n₀ U.Init.Prelude.Nat:zero) n₀
  ArithmeticFixtures:shiftRight~uzero n₀ = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {U.Init.Data.Nat.Bitwise.Basic.Nat:shiftRight n₀ U.Init.Prelude.Nat:zero}

-- theorem
opaque
  ArithmeticFixtures:sub~usucc : (n₀ : U.Init.Prelude.Nat) → (m₁ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Prelude.Nat:sub n₀ (U.Init.Prelude.Nat:succ m₁)) (U.Init.Prelude.Nat:pred (U.Init.Prelude.Nat:sub n₀ m₁))
  ArithmeticFixtures:sub~usucc n₀ m₁ = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {U.Init.Prelude.Nat:sub n₀ (U.Init.Prelude.Nat:succ m₁)}

-- theorem
opaque
  ArithmeticFixtures:sub~uzero : (n₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Prelude.Nat:sub n₀ U.Init.Prelude.Nat:zero) n₀
  ArithmeticFixtures:sub~uzero n₀ = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {U.Init.Prelude.Nat:sub n₀ U.Init.Prelude.Nat:zero}

-- theorem
opaque
  ArithmeticFixtures:succ~umod : (n₀ : U.Init.Prelude.Nat) → (m₁ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Prelude.HMod:hMod {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHMod {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.Nat:instMod ⦄ ⦄ (U.Init.Prelude.Nat:succ n₀) m₁) (U.Init.Prelude.ite {U.Init.Prelude.Nat} (U.Init.Prelude.LE:le {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLENat ⦄ m₁ (U.Init.Prelude.Nat:succ n₀)) ⦃ U.Init.Prelude.Nat:decLe m₁ (U.Init.Prelude.Nat:succ n₀) ⦄ (U.Init.Prelude.Nat:modCore (U.Init.Prelude.Nat:succ n₀) m₁) (U.Init.Prelude.Nat:succ n₀))
  ArithmeticFixtures:succ~umod n₀ m₁ = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {U.Init.Prelude.HMod:hMod {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHMod {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.Nat:instMod ⦄ ⦄ (U.Init.Prelude.Nat:succ n₀) m₁}

-- theorem
opaque
  ArithmeticFixtures:succ~umod~uzero : (n₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Prelude.HMod:hMod {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHMod {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.Nat:instMod ⦄ ⦄ (U.Init.Prelude.Nat:succ n₀) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄)) (U.Init.Prelude.Nat:succ n₀)
  ArithmeticFixtures:succ~umod~uzero n₀ = U.Init.Prelude.Eq:refl {U.Init.Prelude.Nat} (U.Init.Prelude.HMod:hMod {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHMod {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.Nat:instMod ⦄ ⦄ (U.Init.Prelude.Nat:succ n₀) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄))

-- theorem
opaque
  ArithmeticFixtures:succ~usub~usucc : (n₀ : U.Init.Prelude.Nat) → (m₁ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Prelude.Nat:sub (U.Init.Prelude.Nat:succ n₀) (U.Init.Prelude.Nat:succ m₁)) (U.Init.Prelude.Nat:pred (U.Init.Prelude.Nat:sub (U.Init.Prelude.Nat:succ n₀) m₁))
  ArithmeticFixtures:succ~usub~usucc n₀ m₁ = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {U.Init.Prelude.Nat:sub (U.Init.Prelude.Nat:succ n₀) (U.Init.Prelude.Nat:succ m₁)}

-- theorem
opaque
  ArithmeticFixtures:xor~uzero~uleft : (m₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Data.Nat.Bitwise.Basic.Nat:xor (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄) m₀) m₀
  ArithmeticFixtures:xor~uzero~uleft m₀ = U.Init.Prelude.Eq:refl {U.Init.Prelude.Nat} (U.Init.Data.Nat.Bitwise.Basic.Nat:xor (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄) m₀)

-- theorem
opaque
  ArithmeticFixtures:zero~udiv~usucc : (m₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Prelude.HDiv:hDiv {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHDiv {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.Nat:instDiv ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄) (U.Init.Prelude.Nat:succ m₀)) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄)
  ArithmeticFixtures:zero~udiv~usucc m₀ = U.Init.Prelude.Eq:refl {U.Init.Prelude.Nat} (U.Init.Prelude.HDiv:hDiv {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHDiv {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.Nat:instDiv ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄) (U.Init.Prelude.Nat:succ m₀))

-- theorem
opaque
  ArithmeticFixtures:zero~umod : (m₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Prelude.HMod:hMod {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHMod {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.Nat:instMod ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄) m₀) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄)
  ArithmeticFixtures:zero~umod m₀ = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {U.Init.Prelude.HMod:hMod {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHMod {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.Nat:instMod ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄) m₀}

-- theorem
opaque
  ArithmeticFixtures:zero~usub~usucc : (n₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Prelude.Nat:sub (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄) (U.Init.Prelude.Nat:succ n₀)) (U.Init.Prelude.Nat:pred (U.Init.Prelude.Nat:sub (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄) n₀))
  ArithmeticFixtures:zero~usub~usucc n₀ = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {U.Init.Prelude.Nat:sub (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄) (U.Init.Prelude.Nat:succ n₀)}
