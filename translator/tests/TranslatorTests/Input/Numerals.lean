/-
File: translator/tests/TranslatorTests/Input/Numerals.lean
-/

/-!
Lean's accelerated operations on numerals past 2^64, each a theorem
Lean's kernel checks with its arbitrary-precision library, by `rfl` or
by `decide`, for the operation table of the profile U scaffold (the
golden tree `numerals` of `tests/run.sh`).  Under the table Agda computes
every one with its builtins; under `--arithmetic lean` each would be
computed in unary, which no heap bound survives, so the harness checks
this module under the table only (the null results of the other setting
are in `docs/foundations/nat-operations.md`).  `gcd_primes` and
`pow_two` are the gap catalog's examples by `decide`.
-/

namespace NumeralFixtures

theorem succ_big : Nat.succ 18446744073709551615 = 18446744073709551616 := rfl
theorem add_big : 18446744073709551616 + 1 = 18446744073709551617 := rfl
theorem sub_big : 340282366920938463463374607431768211456 - 18446744073709551616 =
    340282366920938463444927863358058659840 := rfl
theorem mul_big : 1000000007 * 998244353 = 998244359987710471 := rfl
theorem pow_big : 2 ^ 128 = 340282366920938463463374607431768211456 := rfl
theorem beq_big : Nat.beq 18446744073709551616 18446744073709551616 = true := rfl
theorem ble_big : Nat.ble 18446744073709551617 18446744073709551616 = false := rfl
theorem div_big : 998244359987710471 / 1000000007 = 998244353 := by with_unfolding_all rfl
theorem mod_big : 998244359987710471 % 1000000007 = 0 := by with_unfolding_all rfl
theorem gcd_small : Nat.gcd 12 18 = 6 := by with_unfolding_all rfl
theorem gcd_primes : Nat.gcd 1000000007 998244353 = 1 := by decide
theorem pow_two : 2 ^ 64 = 18446744073709551616 := by decide
theorem land_big : Nat.land 18446744073709551615 9223372036854788153 = 9223372036854788153 :=
  by with_unfolding_all rfl
theorem lor_big : Nat.lor 18446744073709551615 9223372036854788153 = 18446744073709551615 :=
  by with_unfolding_all rfl
theorem xor_big : Nat.xor 18446744073709551615 9223372036854788153 = 9223372036854763462 :=
  by with_unfolding_all rfl
theorem shiftLeft_big : Nat.shiftLeft 1 64 = 18446744073709551616 := rfl
theorem shiftRight_big : Nat.shiftRight 18446744073709551616 60 = 16 := rfl

end NumeralFixtures
