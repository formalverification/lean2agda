{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of ArithmeticFixtures:add~uone ArithmeticFixtures:add~usucc ArithmeticFixtures:add~uzero ArithmeticFixtures:beq~usucc~usucc ArithmeticFixtures:beq~usucc~uzero and 49 more
-- Lean module TranslatorTests.Input.Numerals
module U.TranslatorTests.Input.Numerals where
import U.Init.Data.Nat.Bitwise.Basic
import U.Init.Data.Nat.Coprime
import U.Init.Data.Nat.Gcd
import U.Init.Prelude

NumeralFixtures:add~ubig:~ushare:~n1 : U.Init.Prelude.Nat
NumeralFixtures:add~ubig:~ushare:~n1 = U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551616 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551616 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄)

-- theorem
opaque
  NumeralFixtures:add~ubig : U.Init.Prelude.Eq {U.Init.Prelude.Nat} NumeralFixtures:add~ubig:~ushare:~n1 (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551617 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551617 ⦄)
  NumeralFixtures:add~ubig = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {NumeralFixtures:add~ubig:~ushare:~n1}

-- theorem
opaque
  NumeralFixtures:beq~ubig : U.Init.Prelude.Eq {U.Init.Prelude.Bool} (U.Init.Prelude.Nat:beq (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551616 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551616 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551616 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551616 ⦄)) U.Init.Prelude.Bool:true
  NumeralFixtures:beq~ubig = U.Init.Prelude.rfl {U.Init.Prelude.Bool} {U.Init.Prelude.Nat:beq (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551616 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551616 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551616 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551616 ⦄)}

-- theorem
opaque
  NumeralFixtures:ble~ubig : U.Init.Prelude.Eq {U.Init.Prelude.Bool} (U.Init.Prelude.Nat:ble (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551617 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551617 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551616 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551616 ⦄)) U.Init.Prelude.Bool:false
  NumeralFixtures:ble~ubig = U.Init.Prelude.rfl {U.Init.Prelude.Bool} {U.Init.Prelude.Nat:ble (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551617 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551617 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551616 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551616 ⦄)}

NumeralFixtures:div~ubig:~ushare:~n1 : U.Init.Prelude.Nat
NumeralFixtures:div~ubig:~ushare:~n1 = U.Init.Prelude.HDiv:hDiv {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHDiv {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.Nat:instDiv ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 998244359987710471 ⦃ U.Init.Prelude.instOfNatNat 998244359987710471 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1000000007 ⦃ U.Init.Prelude.instOfNatNat 1000000007 ⦄)

-- theorem
opaque
  NumeralFixtures:div~ubig : U.Init.Prelude.Eq {U.Init.Prelude.Nat} NumeralFixtures:div~ubig:~ushare:~n1 (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 998244353 ⦃ U.Init.Prelude.instOfNatNat 998244353 ⦄)
  NumeralFixtures:div~ubig = U.Init.Prelude.Eq:refl {U.Init.Prelude.Nat} NumeralFixtures:div~ubig:~ushare:~n1

NumeralFixtures:gcd~uprimes:~ushare:~n1 : Set
NumeralFixtures:gcd~uprimes:~ushare:~n1 = U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Data.Nat.Gcd.Nat:gcd (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1000000007 ⦃ U.Init.Prelude.instOfNatNat 1000000007 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 998244353 ⦃ U.Init.Prelude.instOfNatNat 998244353 ⦄)) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄)

-- theorem
opaque
  NumeralFixtures:gcd~uprimes : NumeralFixtures:gcd~uprimes:~ushare:~n1
  NumeralFixtures:gcd~uprimes = U.Init.Prelude.of~udecide~ueq~utrue {NumeralFixtures:gcd~uprimes:~ushare:~n1} ⦃ U.Init.Data.Nat.Coprime.Nat:instDecidableCoprime (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1000000007 ⦃ U.Init.Prelude.instOfNatNat 1000000007 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 998244353 ⦃ U.Init.Prelude.instOfNatNat 998244353 ⦄) ⦄ (U.Init.Prelude.id {U.Init.Prelude.Eq {U.Init.Prelude.Bool} (U.Init.Prelude.Decidable:decide NumeralFixtures:gcd~uprimes:~ushare:~n1 ⦃ U.Init.Data.Nat.Coprime.Nat:instDecidableCoprime (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1000000007 ⦃ U.Init.Prelude.instOfNatNat 1000000007 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 998244353 ⦃ U.Init.Prelude.instOfNatNat 998244353 ⦄) ⦄) U.Init.Prelude.Bool:true} (U.Init.Prelude.Eq:refl {U.Init.Prelude.Bool} U.Init.Prelude.Bool:true))

-- theorem
opaque
  NumeralFixtures:gcd~usmall : U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Data.Nat.Gcd.Nat:gcd (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 12 ⦃ U.Init.Prelude.instOfNatNat 12 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18 ⦃ U.Init.Prelude.instOfNatNat 18 ⦄)) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 6 ⦃ U.Init.Prelude.instOfNatNat 6 ⦄)
  NumeralFixtures:gcd~usmall = U.Init.Prelude.Eq:refl {U.Init.Prelude.Nat} (U.Init.Data.Nat.Gcd.Nat:gcd (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 12 ⦃ U.Init.Prelude.instOfNatNat 12 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18 ⦃ U.Init.Prelude.instOfNatNat 18 ⦄))

-- theorem
opaque
  NumeralFixtures:land~ubig : U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Data.Nat.Bitwise.Basic.Nat:land (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551615 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551615 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 9223372036854788153 ⦃ U.Init.Prelude.instOfNatNat 9223372036854788153 ⦄)) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 9223372036854788153 ⦃ U.Init.Prelude.instOfNatNat 9223372036854788153 ⦄)
  NumeralFixtures:land~ubig = U.Init.Prelude.Eq:refl {U.Init.Prelude.Nat} (U.Init.Data.Nat.Bitwise.Basic.Nat:land (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551615 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551615 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 9223372036854788153 ⦃ U.Init.Prelude.instOfNatNat 9223372036854788153 ⦄))

-- theorem
opaque
  NumeralFixtures:lor~ubig : U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Data.Nat.Bitwise.Basic.Nat:lor (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551615 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551615 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 9223372036854788153 ⦃ U.Init.Prelude.instOfNatNat 9223372036854788153 ⦄)) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551615 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551615 ⦄)
  NumeralFixtures:lor~ubig = U.Init.Prelude.Eq:refl {U.Init.Prelude.Nat} (U.Init.Data.Nat.Bitwise.Basic.Nat:lor (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551615 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551615 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 9223372036854788153 ⦃ U.Init.Prelude.instOfNatNat 9223372036854788153 ⦄))

NumeralFixtures:mod~ubig:~ushare:~n1 : U.Init.Prelude.Nat
NumeralFixtures:mod~ubig:~ushare:~n1 = U.Init.Prelude.HMod:hMod {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHMod {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.Nat:instMod ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 998244359987710471 ⦃ U.Init.Prelude.instOfNatNat 998244359987710471 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1000000007 ⦃ U.Init.Prelude.instOfNatNat 1000000007 ⦄)

-- theorem
opaque
  NumeralFixtures:mod~ubig : U.Init.Prelude.Eq {U.Init.Prelude.Nat} NumeralFixtures:mod~ubig:~ushare:~n1 (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄)
  NumeralFixtures:mod~ubig = U.Init.Prelude.Eq:refl {U.Init.Prelude.Nat} NumeralFixtures:mod~ubig:~ushare:~n1

NumeralFixtures:mul~ubig:~ushare:~n1 : U.Init.Prelude.Nat
NumeralFixtures:mul~ubig:~ushare:~n1 = U.Init.Prelude.HMul:hMul {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHMul {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instMulNat ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1000000007 ⦃ U.Init.Prelude.instOfNatNat 1000000007 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 998244353 ⦃ U.Init.Prelude.instOfNatNat 998244353 ⦄)

-- theorem
opaque
  NumeralFixtures:mul~ubig : U.Init.Prelude.Eq {U.Init.Prelude.Nat} NumeralFixtures:mul~ubig:~ushare:~n1 (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 998244359987710471 ⦃ U.Init.Prelude.instOfNatNat 998244359987710471 ⦄)
  NumeralFixtures:mul~ubig = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {NumeralFixtures:mul~ubig:~ushare:~n1}

NumeralFixtures:pow~ubig:~ushare:~n1 : U.Init.Prelude.Nat
NumeralFixtures:pow~ubig:~ushare:~n1 = U.Init.Prelude.HPow:hPow {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHPow {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instPowNat {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instNatPowNat ⦄ ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 2 ⦃ U.Init.Prelude.instOfNatNat 2 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 128 ⦃ U.Init.Prelude.instOfNatNat 128 ⦄)

-- theorem
opaque
  NumeralFixtures:pow~ubig : U.Init.Prelude.Eq {U.Init.Prelude.Nat} NumeralFixtures:pow~ubig:~ushare:~n1 (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 340282366920938463463374607431768211456 ⦃ U.Init.Prelude.instOfNatNat 340282366920938463463374607431768211456 ⦄)
  NumeralFixtures:pow~ubig = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {NumeralFixtures:pow~ubig:~ushare:~n1}

NumeralFixtures:pow~utwo:~ushare:~n1 : U.Init.Prelude.Nat
NumeralFixtures:pow~utwo:~ushare:~n1 = U.Init.Prelude.HPow:hPow {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHPow {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instPowNat {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instNatPowNat ⦄ ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 2 ⦃ U.Init.Prelude.instOfNatNat 2 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 64 ⦃ U.Init.Prelude.instOfNatNat 64 ⦄)

NumeralFixtures:pow~utwo:~ushare:~n2 : Set
NumeralFixtures:pow~utwo:~ushare:~n2 = U.Init.Prelude.Eq {U.Init.Prelude.Nat} NumeralFixtures:pow~utwo:~ushare:~n1 (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551616 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551616 ⦄)

NumeralFixtures:pow~utwo:~ushare:~n3 : U.Init.Prelude.Decidable (U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Prelude.HPow:hPow {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHPow {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instPowNat {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instNatPowNat ⦄ ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 2 ⦃ U.Init.Prelude.instOfNatNat 2 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 64 ⦃ U.Init.Prelude.instOfNatNat 64 ⦄)) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551616 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551616 ⦄))
NumeralFixtures:pow~utwo:~ushare:~n3 = U.Init.Prelude.instDecidableEqNat NumeralFixtures:pow~utwo:~ushare:~n1 (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551616 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551616 ⦄)

-- theorem
opaque
  NumeralFixtures:pow~utwo : NumeralFixtures:pow~utwo:~ushare:~n2
  NumeralFixtures:pow~utwo = U.Init.Prelude.of~udecide~ueq~utrue {NumeralFixtures:pow~utwo:~ushare:~n2} ⦃ NumeralFixtures:pow~utwo:~ushare:~n3 ⦄ (U.Init.Prelude.id {U.Init.Prelude.Eq {U.Init.Prelude.Bool} (U.Init.Prelude.Decidable:decide NumeralFixtures:pow~utwo:~ushare:~n2 ⦃ NumeralFixtures:pow~utwo:~ushare:~n3 ⦄) U.Init.Prelude.Bool:true} (U.Init.Prelude.Eq:refl {U.Init.Prelude.Bool} U.Init.Prelude.Bool:true))

-- theorem
opaque
  NumeralFixtures:shiftLeft~ubig : U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Data.Nat.Bitwise.Basic.Nat:shiftLeft (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 64 ⦃ U.Init.Prelude.instOfNatNat 64 ⦄)) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551616 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551616 ⦄)
  NumeralFixtures:shiftLeft~ubig = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {U.Init.Data.Nat.Bitwise.Basic.Nat:shiftLeft (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 64 ⦃ U.Init.Prelude.instOfNatNat 64 ⦄)}

-- theorem
opaque
  NumeralFixtures:shiftRight~ubig : U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Data.Nat.Bitwise.Basic.Nat:shiftRight (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551616 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551616 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 60 ⦃ U.Init.Prelude.instOfNatNat 60 ⦄)) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 16 ⦃ U.Init.Prelude.instOfNatNat 16 ⦄)
  NumeralFixtures:shiftRight~ubig = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {U.Init.Data.Nat.Bitwise.Basic.Nat:shiftRight (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551616 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551616 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 60 ⦃ U.Init.Prelude.instOfNatNat 60 ⦄)}

NumeralFixtures:sub~ubig:~ushare:~n1 : U.Init.Prelude.Nat
NumeralFixtures:sub~ubig:~ushare:~n1 = U.Init.Prelude.HSub:hSub {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHSub {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instSubNat ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 340282366920938463463374607431768211456 ⦃ U.Init.Prelude.instOfNatNat 340282366920938463463374607431768211456 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551616 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551616 ⦄)

-- theorem
opaque
  NumeralFixtures:sub~ubig : U.Init.Prelude.Eq {U.Init.Prelude.Nat} NumeralFixtures:sub~ubig:~ushare:~n1 (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 340282366920938463444927863358058659840 ⦃ U.Init.Prelude.instOfNatNat 340282366920938463444927863358058659840 ⦄)
  NumeralFixtures:sub~ubig = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {NumeralFixtures:sub~ubig:~ushare:~n1}

-- theorem
opaque
  NumeralFixtures:succ~ubig : U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Prelude.Nat:succ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551615 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551615 ⦄)) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551616 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551616 ⦄)
  NumeralFixtures:succ~ubig = U.Init.Prelude.rfl {U.Init.Prelude.Nat} {U.Init.Prelude.Nat:succ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551615 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551615 ⦄)}

-- theorem
opaque
  NumeralFixtures:xor~ubig : U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Data.Nat.Bitwise.Basic.Nat:xor (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551615 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551615 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 9223372036854788153 ⦃ U.Init.Prelude.instOfNatNat 9223372036854788153 ⦄)) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 9223372036854763462 ⦃ U.Init.Prelude.instOfNatNat 9223372036854763462 ⦄)
  NumeralFixtures:xor~ubig = U.Init.Prelude.Eq:refl {U.Init.Prelude.Nat} (U.Init.Data.Nat.Bitwise.Basic.Nat:xor (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551615 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551615 ⦄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 9223372036854788153 ⦃ U.Init.Prelude.instOfNatNat 9223372036854788153 ⦄))
