/-
File: corpus/nat-gcd-succ/lean/Statement.lean

The definition of `Nat.gcd` and its equation at a successor,
`Nat.gcd_succ`, quoted from Lean v4.33.1, `src/Init/Data/Nat/Gcd.lean`,
lines 34 to 41 and 46 to 47:

    @[extern "lean_nat_gcd"]
    def gcd (m n : @& Nat) : Nat :=
      if m = 0 then
        n
      else
        gcd (n % m) m
      termination_by m
      decreasing_by simp_wf; apply mod_lt _ (zero_lt_of_ne_zero _); assumption

    theorem gcd_succ (x y : Nat) : gcd (succ x) y = gcd (y % succ x) (succ x) := by
      rw [gcd]; rfl

Run from `translator/` as

    lake env lean ../corpus/nat-gcd-succ/lean/Statement.lean

it prints the following:

    Nat.gcd_succ : ∀ (x y : Nat), x.succ.gcd y = (y % x.succ).gcd x.succ
    'Nat.gcd_succ' depends on axioms: [Quot.sound]
    'Nat.gcd' does not depend on any axioms

The module is in Lean's core library, so the import needs no Mathlib.
The export of `Nat.gcd_succ` contains `Nat.gcd`, so the entry's
`lean_name` is the equation.
-/
import Init.Data.Nat.Gcd

#check @Nat.gcd_succ
#print axioms Nat.gcd_succ
#print axioms Nat.gcd
