/-
File: translator/tests/TranslatorTests/Input/Arithmetic.lean
-/

/-!
Lean's equations for the operations its kernel accelerates on numerals,
each one that the kernel accepts on variables at the pin, as a theorem
by `rfl` (`docs/foundations/probes/lean/NatOps.lean`), for the operation
table of the profile U scaffold (`tests/Scaffold.lean`, and the golden
trees `arithmetic` and `arithmetic-lean` of `tests/run.sh`).  Under
`--arithmetic lean` every theorem checks, since the scaffold emits
Lean's own definitions; under the table every one checks but
`bitwise_zero_left`, the equation of `Nat.bitwise` for an unknown `f`,
which the table's definition gives up.  `sub_succ` checks through the
rewrite rules the table states for `Nat.sub`, and `zero_sub_succ` and
`succ_sub_succ`, the instances where the builtin monus's own clauses fire
first, through the two that make the rules confluent.  `Nat.div`, `Nat.gcd` and
`Nat.bitwise` are irreducible to the elaborator, so their theorems unfold
everything first; the kernel checks the same `Eq.refl`.
-/

namespace ArithmeticFixtures

theorem add_zero (n : Nat) : Nat.add n Nat.zero = n := rfl
theorem add_succ (n m : Nat) : Nat.add n (Nat.succ m) = Nat.succ (Nat.add n m) := rfl
theorem add_one (n : Nat) : n + 1 = Nat.succ n := rfl
theorem sub_zero (n : Nat) : Nat.sub n Nat.zero = n := rfl
theorem sub_succ (n m : Nat) : Nat.sub n (Nat.succ m) = Nat.pred (Nat.sub n m) := rfl
theorem zero_sub_succ (n : Nat) : Nat.sub 0 (Nat.succ n) = Nat.pred (Nat.sub 0 n) := rfl
theorem succ_sub_succ (n m : Nat) :
    Nat.sub (Nat.succ n) (Nat.succ m) = Nat.pred (Nat.sub (Nat.succ n) m) := rfl
theorem pred_zero : Nat.pred 0 = 0 := rfl
theorem pred_succ (n : Nat) : Nat.pred (Nat.succ n) = n := rfl
theorem mul_zero (n : Nat) : Nat.mul n Nat.zero = Nat.zero := rfl
theorem mul_succ (n m : Nat) : Nat.mul n (Nat.succ m) = Nat.add (Nat.mul n m) n := rfl
theorem pow_zero (n : Nat) : Nat.pow n Nat.zero = 1 := rfl
theorem pow_succ (n m : Nat) : Nat.pow n (Nat.succ m) = Nat.mul (Nat.pow n m) n := rfl
theorem beq_zero_zero : Nat.beq Nat.zero Nat.zero = true := rfl
theorem beq_zero_succ (m : Nat) : Nat.beq Nat.zero (Nat.succ m) = false := rfl
theorem beq_succ_zero (n : Nat) : Nat.beq (Nat.succ n) Nat.zero = false := rfl
theorem beq_succ_succ (n m : Nat) : Nat.beq (Nat.succ n) (Nat.succ m) = Nat.beq n m := rfl
theorem ble_zero (m : Nat) : Nat.ble Nat.zero m = true := rfl
theorem ble_succ_zero (n : Nat) : Nat.ble (Nat.succ n) Nat.zero = false := rfl
theorem ble_succ_succ (n m : Nat) : Nat.ble (Nat.succ n) (Nat.succ m) = Nat.ble n m := rfl
theorem ble_offset (m : Nat) : Nat.ble 3 (m + 4) = true := rfl
theorem div_zero (n : Nat) : n / 0 = 0 := by with_unfolding_all rfl
theorem zero_div_succ (m : Nat) : 0 / Nat.succ m = 0 := by with_unfolding_all rfl
theorem div_offset (m : Nat) : 3 / (m + 4) = 0 := by with_unfolding_all rfl
theorem zero_mod (m : Nat) : 0 % m = 0 := rfl
theorem succ_mod_zero (n : Nat) : Nat.succ n % 0 = Nat.succ n := by with_unfolding_all rfl
theorem mod_offset (m : Nat) : 3 % (m + 4) = 3 := by with_unfolding_all rfl
theorem succ_mod (n m : Nat) :
    Nat.succ n % m = if m ≤ Nat.succ n then Nat.modCore (Nat.succ n) m else Nat.succ n := rfl
theorem gcd_zero_left (n : Nat) : Nat.gcd 0 n = n := by with_unfolding_all rfl
theorem land_zero_left (m : Nat) : Nat.land 0 m = 0 := by with_unfolding_all rfl
theorem lor_zero_left (m : Nat) : Nat.lor 0 m = m := by with_unfolding_all rfl
theorem xor_zero_left (m : Nat) : Nat.xor 0 m = m := by with_unfolding_all rfl
theorem bitwise_zero_left (f : Bool → Bool → Bool) (m : Nat) :
    Nat.bitwise f 0 m = if f false true then m else 0 := by with_unfolding_all rfl
theorem shiftLeft_zero (n : Nat) : Nat.shiftLeft n Nat.zero = n := rfl
theorem shiftLeft_succ (n m : Nat) : Nat.shiftLeft n (Nat.succ m) = Nat.shiftLeft (2 * n) m := rfl
theorem shiftRight_zero (n : Nat) : Nat.shiftRight n Nat.zero = n := rfl
theorem shiftRight_succ (n m : Nat) : Nat.shiftRight n (Nat.succ m) = Nat.shiftRight n m / 2 :=
  by with_unfolding_all rfl

end ArithmeticFixtures
