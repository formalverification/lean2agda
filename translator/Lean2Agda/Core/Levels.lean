/-
File: translator/Lean2Agda/Core/Levels.lean
-/
import Lean.Level

/-!
# Levels without `imax`

Lean's universe levels are `0`, `ℓ + 1`, `max`, `imax` and parameters,
where `imax a b` is zero when `b` is and `max a b` otherwise.  Agda's
levels have no `imax`.  Once every parameter that an `imax` depends on is
fixed as zero or as a successor (`Specialize.lean`), the `imax` is one or
the other, and a level has a normal form: the maximum of a constant and
of parameters, each under a number of successors.  This file is that
normal form, read off a level under an assignment of its parameters, with
the questions the specialization asks of it: whether the level is zero,
whether it can never be zero, and whether it has a predecessor.
`docs/translator/levels.md` gives the rules.
-/

namespace Lean2Agda

open Lean

/-- The maximum of `constant` and of `p + k` for each atom `(p, k)`: a
level without `imax`.  The canonical form (`NormalLevel.canonical`) has
one atom per parameter, the atoms in the order of their names, and the
constant only when it exceeds every atom's offset, so two levels are
equal at every assignment of their parameters exactly when their
canonical forms are equal. -/
structure NormalLevel where
  constant : Nat := 0
  atoms : Array (Name × Nat) := #[]
  deriving BEq, Repr, Inhabited

/-- One atom per parameter, at its largest offset, in the order of the
names; the constant dropped when an atom's offset reaches it, since
`p + k` is at least `k`. -/
def NormalLevel.canonical (constant : Nat) (atoms : Array (Name × Nat)) : NormalLevel :=
  let merged := atoms.foldl (init := (#[] : Array (Name × Nat))) fun acc (p, k) =>
    match acc.findIdx? (·.1 == p) with
    | some i => acc.modify i fun (q, j) => (q, Nat.max j k)
    | none => acc.push (p, k)
  let sorted := merged.qsort fun a b => a.1.lt b.1
  { constant := if sorted.any (·.2 ≥ constant) then 0 else constant, atoms := sorted }

def NormalLevel.zero : NormalLevel := {}

def NormalLevel.param (p : Name) : NormalLevel := { atoms := #[(p, 0)] }

def NormalLevel.succ (n : NormalLevel) : NormalLevel :=
  .canonical (n.constant + 1) (n.atoms.map fun (p, k) => (p, k + 1))

def NormalLevel.max (a b : NormalLevel) : NormalLevel :=
  .canonical (Nat.max a.constant b.constant) (a.atoms ++ b.atoms)

/-- Zero at every assignment of the parameters. -/
def NormalLevel.isZero (n : NormalLevel) : Bool := n.constant == 0 && n.atoms.isEmpty

/-- Zero at no assignment of the parameters. -/
def NormalLevel.neverZero (n : NormalLevel) : Bool := n.constant > 0 || n.atoms.any (·.2 > 0)

/-- The parameters under no successor.  A level that is neither zero nor
never zero is the maximum of these alone, and is zero exactly when they
all are. -/
def NormalLevel.bare (n : NormalLevel) : Array Name :=
  n.atoms.filterMap fun (p, k) => if k == 0 then some p else none

/-- The level one below, when there is one at every assignment: a level
that is not zero and has no bare parameter.  `max 1 u` has none, since it
is one below `1` at `u = 0` and one below `u` elsewhere. -/
def NormalLevel.pred? (n : NormalLevel) : Option NormalLevel :=
  if n.isZero || !n.bare.isEmpty then none
  else some (.canonical (n.constant - 1) (n.atoms.map fun (p, k) => (p, k - 1)))

/-- The level as Lean writes it: the constant, when the form keeps one or
has no atom, then each atom, under `max` nested to the right. -/
def NormalLevel.toLevel (n : NormalLevel) : Level :=
  let atoms := n.atoms.map fun (p, k) => (Level.param p).addOffset k
  let terms := if n.constant > 0 || atoms.isEmpty then #[Level.ofNat n.constant] ++ atoms else atoms
  match terms.back? with
  | some last => terms.pop.foldr Level.max last
  | none => .zero

/-- Why a level has no normal form: an `imax` whose second argument is
the maximum of the given bare parameters, zero for some assignments of
them and not for others; or a metavariable, which no compiled constant
holds. -/
inductive LevelError where
  | undecided (params : Array Name)
  | metavariable
  deriving BEq, Repr, Inhabited

/-- The normal form of a level whose parameters stand for the levels
`assign` gives.  An `imax a b` is zero when `b` is, whatever `a` is, and
`max a b` when `b` is never zero. -/
def normalLevelWith (assign : Name → NormalLevel) : Level → Except LevelError NormalLevel
  | .zero => pure .zero
  | .succ l => return (← normalLevelWith assign l).succ
  | .max a b => return (← normalLevelWith assign a).max (← normalLevelWith assign b)
  | .imax a b => do
    let nb ← normalLevelWith assign b
    if nb.isZero then return .zero
    if nb.neverZero then return (← normalLevelWith assign a).max nb
    throw (.undecided nb.bare)
  | .param p => pure (assign p)
  | .mvar _ => throw .metavariable

/-- The normal form of a level in its own parameters. -/
def normalLevel (l : Level) : Except LevelError NormalLevel := normalLevelWith .param l

/-- Whether a level holds an `imax`. -/
def hasIMax : Level → Bool
  | .imax .. => true
  | .succ l => hasIMax l
  | .max a b => hasIMax a || hasIMax b
  | _ => false

end Lean2Agda
