-- File: docs/foundations/probes/lean/NatOps.lean
-- Lean's definitions of the operations its kernel accelerates, and which of their equations the kernel accepts on variables.
-- Run from translator/ as: lake env lean ../docs/foundations/probes/lean/NatOps.lean
import Lean
open Lean Meta Elab Command Term

/-- Whether Lean's kernel identifies the two sides of an equation, its
variables bound in the local context, by `Lean.Kernel.isDefEq`: the
kernel's own answer, which the elaborator's `rfl` can miss, since
`Nat.div`, `Nat.gcd` and `Nat.bitwise` are irreducible to it. -/
elab "#kernel_rfl " t:term : command => liftTermElabM do
  let e ← instantiateMVars (← elabTerm t none)
  let verdict ← forallTelescope e fun _ body => do
    let some (_, lhs, rhs) := body.eq? | throwError "not an equation"
    return match Lean.Kernel.isDefEq (← getEnv) (← getLCtx) lhs rhs with
      | .ok true => "holds"
      | .ok false => "fails"
      | .error _ => "kernel error"
  logInfo m!"{verdict}: {t}"

#print Nat.add
#print Nat.sub
#print Nat.mul
#print Nat.pow
#print Nat.div
#print Nat.div.go
#print Nat.mod
#print Nat.modCore
#print Nat.modCore.go
#print Nat.beq
#print Nat.ble
#print Nat.land
#print Nat.bitwise
#print Nat.bitwise._unary
#print Nat.shiftLeft
#print Nat.shiftRight
#print Nat.gcd
#print Nat.log2
#print WellFounded.Nat.eager

-- add
#kernel_rfl ∀ n : Nat, Nat.add n Nat.zero = n
#kernel_rfl ∀ n m : Nat, Nat.add n (Nat.succ m) = Nat.succ (Nat.add n m)
#kernel_rfl ∀ n : Nat, Nat.add Nat.zero n = n
#kernel_rfl ∀ n m : Nat, Nat.add (Nat.succ n) m = Nat.succ (Nat.add n m)
-- sub
#kernel_rfl ∀ n : Nat, Nat.sub n Nat.zero = n
#kernel_rfl ∀ n m : Nat, Nat.sub n (Nat.succ m) = Nat.pred (Nat.sub n m)
#kernel_rfl ∀ n : Nat, Nat.sub Nat.zero n = Nat.zero
#kernel_rfl ∀ n m : Nat, Nat.sub (Nat.succ n) (Nat.succ m) = Nat.sub n m
-- mul
#kernel_rfl ∀ n : Nat, Nat.mul n Nat.zero = Nat.zero
#kernel_rfl ∀ n m : Nat, Nat.mul n (Nat.succ m) = Nat.add (Nat.mul n m) n
#kernel_rfl ∀ n : Nat, Nat.mul Nat.zero n = Nat.zero
-- pow
#kernel_rfl ∀ n : Nat, Nat.pow n Nat.zero = Nat.succ Nat.zero
#kernel_rfl ∀ n m : Nat, Nat.pow n (Nat.succ m) = Nat.mul (Nat.pow n m) n
-- beq
#kernel_rfl Nat.beq Nat.zero Nat.zero = true
#kernel_rfl ∀ m : Nat, Nat.beq Nat.zero (Nat.succ m) = false
#kernel_rfl ∀ n : Nat, Nat.beq (Nat.succ n) Nat.zero = false
#kernel_rfl ∀ n m : Nat, Nat.beq (Nat.succ n) (Nat.succ m) = Nat.beq n m
#kernel_rfl ∀ n : Nat, Nat.beq n n = true
-- ble
#kernel_rfl ∀ m : Nat, Nat.ble Nat.zero m = true
#kernel_rfl ∀ n : Nat, Nat.ble (Nat.succ n) Nat.zero = false
#kernel_rfl ∀ n m : Nat, Nat.ble (Nat.succ n) (Nat.succ m) = Nat.ble n m
#kernel_rfl ∀ m : Nat, Nat.ble 3 (Nat.add m 4) = true
-- div
#kernel_rfl ∀ n : Nat, Nat.div n Nat.zero = Nat.zero
#kernel_rfl ∀ m : Nat, Nat.div Nat.zero (Nat.succ m) = Nat.zero
#kernel_rfl ∀ m : Nat, Nat.div Nat.zero m = Nat.zero
#kernel_rfl ∀ n : Nat, Nat.div n 1 = n
#kernel_rfl ∀ n m : Nat, Nat.div n m = if 0 < m ∧ m ≤ n then Nat.div (n - m) m + 1 else 0
#kernel_rfl ∀ m : Nat, Nat.div 3 (Nat.add m 4) = 0
-- mod
#kernel_rfl ∀ m : Nat, Nat.mod Nat.zero m = Nat.zero
#kernel_rfl ∀ n m : Nat, Nat.mod (Nat.succ n) m = if m ≤ Nat.succ n then Nat.modCore (Nat.succ n) m else Nat.succ n
#kernel_rfl ∀ n : Nat, Nat.mod (Nat.succ n) Nat.zero = Nat.succ n
#kernel_rfl ∀ n : Nat, Nat.mod n Nat.zero = n
#kernel_rfl ∀ m : Nat, Nat.mod 3 (Nat.add m 4) = 3
#kernel_rfl ∀ n : Nat, Nat.mod n 1 = 0
#kernel_rfl ∀ n m : Nat, Nat.mod n m = if 0 < m ∧ m ≤ n then Nat.mod (n - m) m else n
-- gcd
#kernel_rfl ∀ n : Nat, Nat.gcd Nat.zero n = n
#kernel_rfl ∀ m : Nat, Nat.gcd (Nat.succ m) Nat.zero = Nat.succ m
#kernel_rfl ∀ n : Nat, Nat.gcd n Nat.zero = n
#kernel_rfl ∀ m n : Nat, Nat.gcd (Nat.succ m) n = Nat.gcd (n % Nat.succ m) (Nat.succ m)
#kernel_rfl ∀ n : Nat, Nat.gcd 1 n = 1
-- land, lor, xor
#kernel_rfl ∀ m : Nat, Nat.land Nat.zero m = Nat.zero
#kernel_rfl ∀ n : Nat, Nat.land n Nat.zero = Nat.zero
#kernel_rfl ∀ m : Nat, Nat.lor Nat.zero m = m
#kernel_rfl ∀ n : Nat, Nat.lor n Nat.zero = n
#kernel_rfl ∀ m : Nat, Nat.xor Nat.zero m = m
#kernel_rfl ∀ n : Nat, Nat.xor n Nat.zero = n
#kernel_rfl ∀ f : Bool → Bool → Bool, ∀ m : Nat, Nat.bitwise f Nat.zero m = if f false true then m else 0
-- shiftLeft, shiftRight
#kernel_rfl ∀ n : Nat, Nat.shiftLeft n Nat.zero = n
#kernel_rfl ∀ n m : Nat, Nat.shiftLeft n (Nat.succ m) = Nat.shiftLeft (2 * n) m
#kernel_rfl ∀ n : Nat, Nat.shiftRight n Nat.zero = n
#kernel_rfl ∀ n m : Nat, Nat.shiftRight n (Nat.succ m) = Nat.shiftRight n m / 2
-- succ and literals
#kernel_rfl ∀ n : Nat, Nat.add n 1 = Nat.succ n
#kernel_rfl Nat.succ 18446744073709551615 = 18446744073709551616
#kernel_rfl ∀ n : Nat, n + 3 = Nat.succ (Nat.succ (Nat.succ n))

/- Output on 2026-11-10 (Lean v4.33.1), from translator/ as
   lake env lean ../docs/foundations/probes/lean/NatOps.lean  (exit status 0, 2 s):
@[instance_reducible] protected def Nat.add : Nat → Nat → Nat :=
fun x x_1 => Nat.brecOn (motive := fun x => Nat → Nat) x_1 Nat.add._f x
@[instance_reducible] protected def Nat.sub : Nat → Nat → Nat :=
fun x x_1 => Nat.brecOn (motive := fun x => Nat → Nat) x_1 Nat.sub._f x
@[instance_reducible] protected def Nat.mul : Nat → Nat → Nat :=
fun x x_1 => Nat.brecOn (motive := fun x => Nat → Nat) x_1 Nat.mul._f x
protected def Nat.pow : Nat → Nat → Nat :=
fun m x => Nat.brecOn x (Nat.pow._f m)
@[irreducible] protected def Nat.div : Nat → Nat → Nat :=
fun x y => if hy : 0 < y then Nat.div.go y hy x.succ x ⋯ else 0
def Nat.div.go : (y : Nat) → 0 < y → (fuel x : Nat) → x < fuel → Nat :=
fun y hy fuel x hfuel => Nat.brecOn (motive := fun fuel => (x : Nat) → x < fuel → Nat) fuel (Nat.div.go._f y hy) x hfuel
protected def Nat.mod : Nat → Nat → Nat :=
fun x x_1 =>
  match x, x_1 with
  | 0, x => 0
  | n@h:n_1.succ, m => if m ≤ n then n.modCore m else n
@[irreducible] protected def Nat.modCore : Nat → Nat → Nat :=
fun x y => if hy : 0 < y then Nat.modCore.go y hy x.succ x ⋯ else x
def Nat.modCore.go : (y : Nat) → 0 < y → (fuel x : Nat) → x < fuel → Nat :=
fun y hy fuel x hfuel =>
  Nat.brecOn (motive := fun fuel => (x : Nat) → x < fuel → Nat) fuel (Nat.modCore.go._f y hy) x hfuel
def Nat.beq : Nat → Nat → Bool :=
fun x x_1 => Nat.brecOn (motive := fun x => Nat → Bool) x Nat.beq._f x_1
def Nat.ble : Nat → Nat → Bool :=
fun x x_1 => Nat.brecOn (motive := fun x => Nat → Bool) x Nat.ble._f x_1
def Nat.land : Nat → Nat → Nat :=
Nat.bitwise and
@[irreducible] def Nat.bitwise : (Bool → Bool → Bool) → Nat → Nat → Nat :=
fun f n m => Nat.bitwise._unary f ⟨n, m⟩
def Nat.bitwise._unary : (Bool → Bool → Bool) → (_ : Nat) ×' Nat → Nat :=
fun f =>
  WellFounded.Nat.fix (fun x => PSigma.casesOn x fun n m => n) fun _x a =>
    PSigma.casesOn (motive := fun _x =>
      ((y : (_ : Nat) ×' Nat) → InvImage (fun x1 x2 => x1 < x2) (fun x => PSigma.casesOn x fun n m => n) y _x → Nat) →
        Nat)
      _x
      (fun n m a =>
        if h : n = 0 then if h : f false true = true then m else 0
        else
          if h : m = 0 then if h : f true false = true then n else 0
          else
            let n' := n / 2;
            let m' := m / 2;
            let b₁ := n % 2 = 1;
            let b₂ := m % 2 = 1;
            let r := a ⟨n', m'⟩ ⋯;
            if h : f (decide b₁) (decide b₂) = true then r + r + 1 else r + r)
      a
@[implicit_reducible] def Nat.shiftLeft : Nat → Nat → Nat :=
fun x x_1 => Nat.brecOn (motive := fun x => Nat → Nat) x_1 Nat.shiftLeft._f x
@[implicit_reducible] def Nat.shiftRight : Nat → Nat → Nat :=
fun x x_1 => Nat.brecOn (motive := fun x => Nat → Nat) x_1 Nat.shiftRight._f x
@[irreducible] def Nat.gcd : Nat → Nat → Nat :=
fun m n => Nat.gcd._unary ⟨m, n⟩
def Nat.log2 : Nat → Nat :=
fun n =>
  Nat.rec (motive := fun x => Nat → Nat) (fun x => 0) (fun x ih n => Bool.rec 0 (ih (n.div 2)).succ (Nat.ble 2 n)) n n
@[implicit_reducible] def WellFounded.Nat.eager : Nat → Nat :=
fun n => if n.beq n = true then n else n
holds: ∀ n : Nat, Nat.add n Nat.zero = n
holds: ∀ n m : Nat, Nat.add n (Nat.succ m) = Nat.succ (Nat.add n m)
fails: ∀ n : Nat, Nat.add Nat.zero n = n
fails: ∀ n m : Nat, Nat.add (Nat.succ n) m = Nat.succ (Nat.add n m)
holds: ∀ n : Nat, Nat.sub n Nat.zero = n
holds: ∀ n m : Nat, Nat.sub n (Nat.succ m) = Nat.pred (Nat.sub n m)
fails: ∀ n : Nat, Nat.sub Nat.zero n = Nat.zero
fails: ∀ n m : Nat, Nat.sub (Nat.succ n) (Nat.succ m) = Nat.sub n m
holds: ∀ n : Nat, Nat.mul n Nat.zero = Nat.zero
holds: ∀ n m : Nat, Nat.mul n (Nat.succ m) = Nat.add (Nat.mul n m) n
fails: ∀ n : Nat, Nat.mul Nat.zero n = Nat.zero
holds: ∀ n : Nat, Nat.pow n Nat.zero = Nat.succ Nat.zero
holds: ∀ n m : Nat, Nat.pow n (Nat.succ m) = Nat.mul (Nat.pow n m) n
holds: Nat.beq Nat.zero Nat.zero = true
holds: ∀ m : Nat, Nat.beq Nat.zero (Nat.succ m) = false
holds: ∀ n : Nat, Nat.beq (Nat.succ n) Nat.zero = false
holds: ∀ n m : Nat, Nat.beq (Nat.succ n) (Nat.succ m) = Nat.beq n m
fails: ∀ n : Nat, Nat.beq n n = true
holds: ∀ m : Nat, Nat.ble Nat.zero m = true
holds: ∀ n : Nat, Nat.ble (Nat.succ n) Nat.zero = false
holds: ∀ n m : Nat, Nat.ble (Nat.succ n) (Nat.succ m) = Nat.ble n m
holds: ∀ m : Nat, Nat.ble 3 (Nat.add m 4) = true
holds: ∀ n : Nat, Nat.div n Nat.zero = Nat.zero
holds: ∀ m : Nat, Nat.div Nat.zero (Nat.succ m) = Nat.zero
fails: ∀ m : Nat, Nat.div Nat.zero m = Nat.zero
fails: ∀ n : Nat, Nat.div n 1 = n
fails: ∀ n m : Nat, Nat.div n m = if 0 < m ∧ m ≤ n then Nat.div (n - m) m + 1 else 0
holds: ∀ m : Nat, Nat.div 3 (Nat.add m 4) = 0
holds: ∀ m : Nat, Nat.mod Nat.zero m = Nat.zero
holds: ∀ n m : Nat, Nat.mod (Nat.succ n) m = if m ≤ Nat.succ n then Nat.modCore (Nat.succ n) m else Nat.succ n
holds: ∀ n : Nat, Nat.mod (Nat.succ n) Nat.zero = Nat.succ n
fails: ∀ n : Nat, Nat.mod n Nat.zero = n
holds: ∀ m : Nat, Nat.mod 3 (Nat.add m 4) = 3
fails: ∀ n : Nat, Nat.mod n 1 = 0
fails: ∀ n m : Nat, Nat.mod n m = if 0 < m ∧ m ≤ n then Nat.mod (n - m) m else n
holds: ∀ n : Nat, Nat.gcd Nat.zero n = n
fails: ∀ m : Nat, Nat.gcd (Nat.succ m) Nat.zero = Nat.succ m
fails: ∀ n : Nat, Nat.gcd n Nat.zero = n
fails: ∀ m n : Nat, Nat.gcd (Nat.succ m) n = Nat.gcd (n % Nat.succ m) (Nat.succ m)
fails: ∀ n : Nat, Nat.gcd 1 n = 1
holds: ∀ m : Nat, Nat.land Nat.zero m = Nat.zero
fails: ∀ n : Nat, Nat.land n Nat.zero = Nat.zero
holds: ∀ m : Nat, Nat.lor Nat.zero m = m
fails: ∀ n : Nat, Nat.lor n Nat.zero = n
holds: ∀ m : Nat, Nat.xor Nat.zero m = m
fails: ∀ n : Nat, Nat.xor n Nat.zero = n
holds: ∀ f : Bool → Bool → Bool, ∀ m : Nat, Nat.bitwise f Nat.zero m = if f false true then m else 0
holds: ∀ n : Nat, Nat.shiftLeft n Nat.zero = n
holds: ∀ n m : Nat, Nat.shiftLeft n (Nat.succ m) = Nat.shiftLeft (2 * n) m
holds: ∀ n : Nat, Nat.shiftRight n Nat.zero = n
holds: ∀ n m : Nat, Nat.shiftRight n (Nat.succ m) = Nat.shiftRight n m / 2
holds: ∀ n : Nat, Nat.add n 1 = Nat.succ n
holds: Nat.succ 18446744073709551615 = 18446744073709551616
holds: ∀ n : Nat, n + 3 = Nat.succ (Nat.succ (Nat.succ n))
-/
