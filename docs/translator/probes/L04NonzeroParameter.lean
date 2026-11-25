-- File: docs/translator/probes/L04NonzeroParameter.lean
-- What Lean's own level functions do with imax, and which form of an instance its kernel accepts.
-- Run from the repository's root as: nix develop .#lean --command lean docs/translator/probes/L04NonzeroParameter.lean
-- Outcome on 2026-11-24 with Lean 4.33.1: every line printed says "as expected".
import Lean
open Lean

def u : Level := .param `u
def v : Level := .param `v
def one : Level := .succ .zero

def expect (label : String) (condition : Bool) : IO Unit :=
  IO.println s!"{if condition then "as expected" else "NOT as expected"}: {label}"

-- `Level.normalize` decides an imax whose second argument is a successor
-- or zero, and leaves one whose second argument is another parameter.
#eval expect "normalize (imax u (v+1)) = max u (v+1)"
  ((Level.imax u (.succ v)).normalize == Level.max u (.succ v))
#eval expect "normalize (imax u 0) = 0" ((Level.imax u .zero).normalize == .zero)
#eval expect "normalize (imax u v) = imax u v" ((Level.imax u v).normalize == Level.imax u v)

-- Substituting zero for u and v+1 for v decides it, and the substitution
-- alone already simplifies.
#eval expect "(imax u v)[u := 0, v := v+1] = v+1"
  ((Level.imax u v).instantiateParams [`u, `v] [.zero, .succ v] == .succ v)
#eval expect "(imax u v)[v := 0] = 0" ((Level.imax u v).instantiateParams [`v] [.zero] == .zero)
#eval expect "(max 1 u)[u := u+1] normalizes to u+1"
  (((Level.max one u).instantiateParams [`u] [.succ u]).normalize == .succ u)

/-- Whether the kernel accepts a definition `name.{u} : type := value`. -/
def accepts (env : Environment) (name : Name) (type value : Expr) : Bool :=
  let decl : Declaration := .defnDecl {
    name, levelParams := [`u], type, value, hints := .abbrev, safety := .safe, all := [name] }
  (env.addDeclCore 0 0 decl none).toOption.isSome

/-- `fun (α : Sort a) => Nat → α`, a function into `Sort (imax 1 a)`. -/
def arrows (a : Level) : Expr := .lam `α (.sort a) (.forallE `n (.const ``Nat []) (.bvar 1) .default) .default

def typed (a result : Level) : Expr := .forallE `α (.sort a) (.sort result) .default

#eval show Lean.Elab.Command.CommandElabM Unit from do
  let env ← getEnv
  -- The constant itself: its sort is `imax 1 u`.
  expect "the kernel accepts f.{u} : Sort u → Sort (imax 1 u)" (accepts env `probe.f (typed u (.imax one u)) (arrows u))
  -- A nonzero parameter kept as `u`, with the imax rewritten to max by an
  -- assumption `u ≥ 1` that the kernel does not have: rejected, since the
  -- two levels differ at `u = 0`.
  expect "the kernel rejects f.{u} : Sort u → Sort (max 1 u)" (!accepts env `probe.g (typed u (.max one u)) (arrows u))
  -- A nonzero parameter written `u + 1`: an instantiation, accepted, with
  -- the level in normal form.
  expect "the kernel accepts f.{u} : Sort (u+1) → Sort (u+1)"
    (accepts env `probe.h (typed (.succ u) (.succ u)) (arrows (.succ u)))
  -- The parameter at zero: accepted, and the sort is Prop.
  expect "the kernel accepts f : Prop → Prop" (accepts env `probe.k (typed .zero .zero) (arrows .zero))
