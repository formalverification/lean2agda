/-
File: corpus/nat-gcd-self/lean/Statement.lean

The statement of `Nat.gcd_self`, quoted from Lean v4.33.1,
`src/Init/Data/Nat/Gcd.lean`, lines 70 to 71:

    @[simp] theorem gcd_self (n : Nat) : gcd n n = n := by
      cases n <;> simp [gcd_succ]

Run from `translator/` as

    lake env lean ../corpus/nat-gcd-self/lean/Statement.lean

it prints the following:

    Nat.gcd_self : ∀ (n : Nat), n.gcd n = n
    'Nat.gcd_self' depends on axioms: [propext, Quot.sound]

The module is in Lean's core library, so the import needs no Mathlib.
-/
import Init.Data.Nat.Gcd

#check @Nat.gcd_self
#print axioms Nat.gcd_self
