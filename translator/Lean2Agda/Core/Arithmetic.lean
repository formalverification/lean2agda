/-
File: translator/Lean2Agda/Core/Arithmetic.lean
-/
import Lean2Agda.Core.Naming
import Lean.Expr

/-!
# The operation table

Lean's kernel computes `Nat.succ` and fourteen binary operations on
numerals with an arbitrary-precision library instead of unfolding them.
The scaffold emits Lean's compiled definitions of those operations, which
Agda would compute in unary, and whose normal forms, stuck on a variable,
Agda's positivity check expands until it exhausts its heap.  Under
`--arithmetic agda`, the default, the scaffold emits instead the table's
definition of each operation's recursive core, as follows, and keeps
Lean's non-recursive wrappers around them (`Nat.div`, `Nat.mod`,
`Nat.modCore`, `Nat.land`, `Nat.lor`, `Nat.xor`, `Nat.gcd`):

+  `Nat.add`, `Nat.mul` and `Nat.ble`, Agda's builtin `_+_`, `_*_` and
   `_<_` with their arguments swapped or shifted, which keeps every one
   of Lean's defining equations by conversion;
+  `Nat.beq`, Agda's builtin `_==_` itself, bound to `NATEQUALS`;
+  `Nat.sub`, Agda's builtin monus, which loses Lean's equation
   `Nat.sub n (succ m) = pred (Nat.sub n m)`; profile U restores it with
   two more that make the set confluent, rewrite rules proved by
   induction (`subRules`), which `--safe` refuses, and `Nat.pred` is
   Lean's two clauses, so that the rules can fire on it;
+  `Nat.div.go` and `Nat.modCore.go`, the fuel cores of `Nat.div` and
   `Nat.mod`, Agda's `div-helper` and `mod-helper`, the fuel and the
   proofs ignored, which loses their own equations on the fuel;
+  `Nat.pow`, `Nat.shiftLeft`, `Nat.shiftRight` and `Nat.bitwise`, Lean's
   equations as clauses over the builtins, which compute in as many steps
   as their recursion takes; `Nat.bitwise` by fuel, its recursive result
   used once, which loses only its equation for an unknown `f`.

`Bool` gets `BUILTIN BOOL`, `TRUE` and `FALSE`, which `NATEQUALS` and
`NATLESS` need.  The helpers' identifiers end in `-builtin`, `-succ` or
another suffix with a hyphen, which no `agdaIdent` produces.
`docs/foundations/nat-operations.md` is the table, with Lean's equations,
which of them each definition keeps, and the probes that settle them;
the clauses are written against Lean's definitions at the pin, and
`tableEntry?` refuses an operation whose type no longer has the arity
they bind.
-/

namespace Lean2Agda

open Lean

/-- Which definitions of Lean's accelerated operations the scaffold
emits: the operation table's (`agda`) or Lean's compiled ones (`lean`). -/
inductive Arithmetic where
  | agda
  | lean
  deriving BEq, Repr, Inhabited

def Arithmetic.label : Arithmetic → String
  | .agda => "agda"
  | .lean => "lean"

def Arithmetic.parse? : String → Option Arithmetic
  | "agda" => some .agda
  | "lean" => some .lean
  | _ => none

/-- How a module names what the table's text mentions: a Lean constant as
the printer names it there, and a helper by its identifier in its home
module and by the home's path and the identifier elsewhere. -/
structure TableNaming where
  constant : Name → String
  helper : String → String

def TableNaming.unqualified : TableNaming := ⟨agdaIdent, id⟩

/-- A definition the table adds: its identifier, the Lean constant whose
module is its home, its lines as a module names their references, the
helpers it uses, and the Lean constants it mentions. -/
structure Helper where
  name : String
  home : Name
  lines : TableNaming → Array String
  uses : Array String := #[]
  mentions : Array Name := #[]
  deriving Inhabited

/-- One row of the table: the Lean constant, how many arguments its type
takes (every one explicit), the clauses that replace its value given how
its module names things and its identifier, the helpers they use, and the
Lean constants they mention. -/
structure TableEntry where
  const : Name
  arity : Nat
  clauses : TableNaming → String → Array String
  uses : Array String := #[]
  mentions : Array Name := #[]
  deriving Inhabited

/-- What every helper over `Nat` mentions, a literal's type among them. -/
private def natNames : Array Name := #[``Nat, ``Nat.zero, ``Nat.succ]
private def boolNames : Array Name := #[``Bool, ``Bool.false, ``Bool.true]

def addBuiltin : String := agdaIdent ``Nat.add ++ "-builtin"
def subBuiltin : String := agdaIdent ``Nat.sub ++ "-builtin"
def mulBuiltin : String := agdaIdent ``Nat.mul ++ "-builtin"
def divBuiltin : String := agdaIdent ``Nat.div ++ "-builtin"
def modBuiltin : String := agdaIdent ``Nat.mod ++ "-builtin"
def bltBuiltin : String := agdaIdent ``Nat.blt ++ "-builtin"
def bitwisePick : String := agdaIdent ``Nat.bitwise ++ "-pick"
def bitwiseBit : String := agdaIdent ``Nat.bitwise ++ "-bit"
def bitwiseOdd : String := agdaIdent ``Nat.bitwise ++ "-odd"
def bitwiseGo : String := agdaIdent ``Nat.bitwise ++ "-go"
def subRuleName : String := agdaIdent ``Nat.sub ++ "-builtin-succ"
def subPredZeroName : String := agdaIdent ``Nat.sub ++ "-builtin-pred-zero"
def subPredSuccName : String := agdaIdent ``Nat.sub ++ "-builtin-pred-succ"

/-- The helpers, each defined as `Agda.Builtin.Nat` defines the builtin it
is bound to, or by Lean's equations over them.  The builtins live with
`Nat` (with `Bool` for `_<_`), `Nat.bitwise`'s helpers with it. -/
def helpers : Array Helper := #[
  { name := addBuiltin, home := ``Nat, mentions := natNames, lines := fun q =>
      let (nat, zero, succ, add) := (q.constant ``Nat, q.constant ``Nat.zero, q.constant ``Nat.succ, q.helper addBuiltin)
      #[s!"{add} : {nat} → {nat} → {nat}",
        s!"{add} {zero} m₁ = m₁",
        s!"{add} ({succ} n₀) m₁ = {succ} ({add} n₀ m₁)",
        s!"\{-# BUILTIN NATPLUS {add} #-}"] },
  { name := subBuiltin, home := ``Nat, mentions := natNames, lines := fun q =>
      let (nat, zero, succ, sub) := (q.constant ``Nat, q.constant ``Nat.zero, q.constant ``Nat.succ, q.helper subBuiltin)
      #[s!"{sub} : {nat} → {nat} → {nat}",
        s!"{sub} n₀ {zero} = n₀",
        s!"{sub} {zero} ({succ} m₁) = {zero}",
        s!"{sub} ({succ} n₀) ({succ} m₁) = {sub} n₀ m₁",
        s!"\{-# BUILTIN NATMINUS {sub} #-}"] },
  { name := mulBuiltin, home := ``Nat, mentions := natNames, uses := #[addBuiltin], lines := fun q =>
      let (nat, zero, succ, mul) := (q.constant ``Nat, q.constant ``Nat.zero, q.constant ``Nat.succ, q.helper mulBuiltin)
      #[s!"{mul} : {nat} → {nat} → {nat}",
        s!"{mul} {zero} m₁ = {zero}",
        s!"{mul} ({succ} n₀) m₁ = {q.helper addBuiltin} m₁ ({mul} n₀ m₁)",
        s!"\{-# BUILTIN NATTIMES {mul} #-}"] },
  { name := divBuiltin, home := ``Nat, mentions := natNames, lines := fun q =>
      let (nat, zero, succ, div) := (q.constant ``Nat, q.constant ``Nat.zero, q.constant ``Nat.succ, q.helper divBuiltin)
      #[s!"{div} : {nat} → {nat} → {nat} → {nat} → {nat}",
        s!"{div} k₀ m₁ {zero} j₃ = k₀",
        s!"{div} k₀ m₁ ({succ} n₂) {zero} = {div} ({succ} k₀) m₁ n₂ m₁",
        s!"{div} k₀ m₁ ({succ} n₂) ({succ} j₃) = {div} k₀ m₁ n₂ j₃",
        s!"\{-# BUILTIN NATDIVSUCAUX {div} #-}"] },
  { name := modBuiltin, home := ``Nat, mentions := natNames, lines := fun q =>
      let (nat, zero, succ, mod) := (q.constant ``Nat, q.constant ``Nat.zero, q.constant ``Nat.succ, q.helper modBuiltin)
      #[s!"{mod} : {nat} → {nat} → {nat} → {nat} → {nat}",
        s!"{mod} k₀ m₁ {zero} j₃ = k₀",
        s!"{mod} k₀ m₁ ({succ} n₂) {zero} = {mod} {zero} m₁ n₂ m₁",
        s!"{mod} k₀ m₁ ({succ} n₂) ({succ} j₃) = {mod} ({succ} k₀) m₁ n₂ j₃",
        s!"\{-# BUILTIN NATMODSUCAUX {mod} #-}"] },
  { name := bltBuiltin, home := ``Bool, mentions := natNames ++ boolNames, lines := fun q =>
      let (nat, zero, succ, blt) := (q.constant ``Nat, q.constant ``Nat.zero, q.constant ``Nat.succ, q.helper bltBuiltin)
      #[s!"{blt} : {nat} → {nat} → {q.constant ``Bool}",
        s!"{blt} n₀ {zero} = {q.constant ``Bool.false}",
        s!"{blt} {zero} ({succ} m₁) = {q.constant ``Bool.true}",
        s!"{blt} ({succ} n₀) ({succ} m₁) = {blt} n₀ m₁",
        s!"\{-# BUILTIN NATLESS {blt} #-}"] },
  { name := bitwisePick, home := ``Nat.bitwise, mentions := natNames ++ boolNames, lines := fun q =>
      let (nat, bool, pick) := (q.constant ``Nat, q.constant ``Bool, q.helper bitwisePick)
      #[s!"{pick} : {bool} → {nat} → {nat}",
        s!"{pick} {q.constant ``Bool.false} n₁ = {q.constant ``Nat.zero}",
        s!"{pick} {q.constant ``Bool.true} n₁ = n₁"] },
  { name := bitwiseBit, home := ``Nat.bitwise, mentions := natNames ++ boolNames, uses := #[mulBuiltin],
    lines := fun q =>
      let (nat, bool, bit, mul) := (q.constant ``Nat, q.constant ``Bool, q.helper bitwiseBit, q.helper mulBuiltin)
      #[s!"{bit} : {bool} → {nat} → {nat}",
        s!"{bit} {q.constant ``Bool.false} r₁ = {mul} r₁ 2",
        s!"{bit} {q.constant ``Bool.true} r₁ = {q.constant ``Nat.succ} ({mul} r₁ 2)"] },
  { name := bitwiseOdd, home := ``Nat.bitwise, mentions := natNames ++ boolNames, uses := #[bltBuiltin, modBuiltin],
    lines := fun q =>
      let odd := q.helper bitwiseOdd
      #[s!"{odd} : {q.constant ``Nat} → {q.constant ``Bool}",
        s!"{odd} n₀ = {q.helper bltBuiltin} {q.constant ``Nat.zero} ({q.helper modBuiltin} {q.constant ``Nat.zero} 1 n₀ 1)"] },
  { name := bitwiseGo, home := ``Nat.bitwise, mentions := natNames ++ boolNames,
    uses := #[bitwisePick, bitwiseBit, bitwiseOdd, divBuiltin], lines := fun q =>
      let (nat, bool, zero, succ) := (q.constant ``Nat, q.constant ``Bool, q.constant ``Nat.zero, q.constant ``Nat.succ)
      let (ff, tt, go, div) := (q.constant ``Bool.false, q.constant ``Bool.true, q.helper bitwiseGo, q.helper divBuiltin)
      let (pick, bit, odd) := (q.helper bitwisePick, q.helper bitwiseBit, q.helper bitwiseOdd)
      #[s!"{go} : {nat} → ({bool} → {bool} → {bool}) → {nat} → {nat} → {nat}",
        s!"{go} {zero} f₁ n₂ m₃ = {zero}",
        s!"{go} ({succ} k₀) f₁ {zero} m₃ = {pick} (f₁ {ff} {tt}) m₃",
        s!"{go} ({succ} k₀) f₁ ({succ} n₂) {zero} = {pick} (f₁ {tt} {ff}) ({succ} n₂)",
        s!"{go} ({succ} k₀) f₁ ({succ} n₂) ({succ} m₃) = {bit} (f₁ ({odd} ({succ} n₂)) ({odd} ({succ} m₃))) " ++
          s!"({go} k₀ f₁ ({div} {zero} 1 ({succ} n₂) 1) ({div} {zero} 1 ({succ} m₃) 1))"] }]

/-- The rows of the table whose clauses replace a Lean definition's value:
every recursive core of an accelerated operation. -/
def table : Array TableEntry := #[
  { const := ``Nat.add, arity := 2, uses := #[addBuiltin],
    clauses := fun q f => #[s!"{f} x₀ x₁ = {q.helper addBuiltin} x₁ x₀"] },
  { const := ``Nat.sub, arity := 2, uses := #[subBuiltin],
    clauses := fun q f => #[s!"{f} x₀ x₁ = {q.helper subBuiltin} x₀ x₁"] },
  { const := ``Nat.mul, arity := 2, uses := #[mulBuiltin],
    clauses := fun q f => #[s!"{f} x₀ x₁ = {q.helper mulBuiltin} x₁ x₀"] },
  { const := ``Nat.pow, arity := 2, uses := #[mulBuiltin], mentions := natNames,
    clauses := fun q f => #[s!"{f} m₀ {q.constant ``Nat.zero} = 1",
      s!"{f} m₀ ({q.constant ``Nat.succ} n₁) = {q.helper mulBuiltin} m₀ ({f} m₀ n₁)"] },
  { const := ``Nat.beq, arity := 2, mentions := natNames ++ boolNames,
    clauses := fun q f =>
      let (zero, succ, tt, ff) := (q.constant ``Nat.zero, q.constant ``Nat.succ, q.constant ``Bool.true, q.constant ``Bool.false)
      #[s!"{f} {zero} {zero} = {tt}", s!"{f} ({succ} n₀) ({succ} m₁) = {f} n₀ m₁",
        s!"{f} {zero} ({succ} m₁) = {ff}", s!"{f} ({succ} n₀) {zero} = {ff}",
        s!"\{-# BUILTIN NATEQUALS {f} #-}"] },
  { const := ``Nat.pred, arity := 1, mentions := natNames,
    clauses := fun q f => #[s!"{f} {q.constant ``Nat.zero} = {q.constant ``Nat.zero}",
      s!"{f} ({q.constant ``Nat.succ} n₀) = n₀"] },
  { const := ``Nat.ble, arity := 2, uses := #[bltBuiltin], mentions := natNames,
    clauses := fun q f => #[s!"{f} x₀ x₁ = {q.helper bltBuiltin} x₀ ({q.constant ``Nat.succ} x₁)"] },
  { const := ``Nat.div.go, arity := 5, uses := #[divBuiltin], mentions := natNames,
    clauses := fun q f =>
      let (zero, succ) := (q.constant ``Nat.zero, q.constant ``Nat.succ)
      #[s!"{f} {zero} hy₁ fuel₂ x₃ hfuel₄ = {zero}",
        s!"{f} ({succ} y₀) hy₁ fuel₂ x₃ hfuel₄ = {q.helper divBuiltin} {zero} y₀ x₃ y₀"] },
  { const := ``Nat.modCore.go, arity := 5, uses := #[modBuiltin], mentions := natNames,
    clauses := fun q f =>
      let (zero, succ) := (q.constant ``Nat.zero, q.constant ``Nat.succ)
      #[s!"{f} {zero} hy₁ fuel₂ x₃ hfuel₄ = x₃",
        s!"{f} ({succ} y₀) hy₁ fuel₂ x₃ hfuel₄ = {q.helper modBuiltin} {zero} y₀ x₃ y₀"] },
  { const := ``Nat.bitwise, arity := 3, uses := #[bitwiseGo], mentions := natNames,
    clauses := fun q f => #[s!"{f} f₀ n₁ m₂ = {q.helper bitwiseGo} ({q.constant ``Nat.succ} n₁) f₀ n₁ m₂"] },
  { const := ``Nat.shiftLeft, arity := 2, uses := #[mulBuiltin], mentions := natNames,
    clauses := fun q f => #[s!"{f} n₀ {q.constant ``Nat.zero} = n₀",
      s!"{f} n₀ ({q.constant ``Nat.succ} m₁) = {f} ({q.helper mulBuiltin} n₀ 2) m₁"] },
  { const := ``Nat.shiftRight, arity := 2, uses := #[divBuiltin], mentions := natNames,
    clauses := fun q f => #[s!"{f} n₀ {q.constant ``Nat.zero} = n₀",
      s!"{f} n₀ ({q.constant ``Nat.succ} m₁) = {q.helper divBuiltin} {q.constant ``Nat.zero} 1 ({f} n₀ m₁) 1"] }]

/-- The rewrite rules of `Nat.sub` under profile U, each proved by
induction: `Nat.sub n (succ m) = pred (Nat.sub n m)`, the equation of
Lean's `Nat.sub` that the builtin monus loses, and two that make the set
confluent with the monus's own clauses `0 - succ m = 0` and `succ n -
succ m = n - m`, `pred (0 - m) = 0` and `pred (succ n - m) = n - m`
(Agda's `--local-confluence-check` accepts the three, declared by one
pragma, and refuses the first alone; probe `P31NatSubRewrite`).  They
mention Lean's `Nat.pred`, the table's row by its clauses, so that a rule
headed by it can fire and the rewritten term is the one Lean's equation
has, and `Eq`, the rewrite relation.  They live with `Nat.sub`, the last
carrying the pragma, and `Nat.sub` refers to it, so that whatever uses
`Nat.sub` imports the rules. -/
def subRules : Array Helper :=
  let ruleMentions := natNames ++ #[``Nat.pred, ``Eq, ``Eq.refl]
  #[{ name := subRuleName, home := ``Nat.sub, uses := #[subBuiltin], mentions := ruleMentions, lines := fun q =>
      let (nat, zero, succ, sub) := (q.constant ``Nat, q.constant ``Nat.zero, q.constant ``Nat.succ, q.helper subBuiltin)
      let (refl, rule) := (q.constant ``Eq.refl, q.helper subRuleName)
      #[s!"{rule} : (n₀ : {nat}) → (m₁ : {nat}) → {q.constant ``Eq} \{{nat}} ({sub} n₀ ({succ} m₁)) " ++
          s!"({q.constant ``Nat.pred} ({sub} n₀ m₁))",
        s!"{rule} {zero} {zero} = {refl} {zero}",
        s!"{rule} {zero} ({succ} m₁) = {refl} {zero}",
        s!"{rule} ({succ} n₀) {zero} = {refl} n₀",
        s!"{rule} ({succ} n₀) ({succ} m₁) = {rule} n₀ m₁"] },
    { name := subPredZeroName, home := ``Nat.sub, uses := #[subBuiltin], mentions := ruleMentions, lines := fun q =>
      let (nat, zero, succ, sub) := (q.constant ``Nat, q.constant ``Nat.zero, q.constant ``Nat.succ, q.helper subBuiltin)
      let (refl, rule) := (q.constant ``Eq.refl, q.helper subPredZeroName)
      #[s!"{rule} : (m₁ : {nat}) → {q.constant ``Eq} \{{nat}} ({q.constant ``Nat.pred} ({sub} {zero} m₁)) {zero}",
        s!"{rule} {zero} = {refl} {zero}",
        s!"{rule} ({succ} m₁) = {refl} {zero}"] },
    { name := subPredSuccName, home := ``Nat.sub, uses := #[subBuiltin, subRuleName, subPredZeroName],
      mentions := ruleMentions, lines := fun q =>
      let (nat, zero, succ, sub) := (q.constant ``Nat, q.constant ``Nat.zero, q.constant ``Nat.succ, q.helper subBuiltin)
      let (refl, rule) := (q.constant ``Eq.refl, q.helper subPredSuccName)
      #[s!"{rule} : (n₀ : {nat}) → (m₁ : {nat}) → {q.constant ``Eq} \{{nat}} " ++
          s!"({q.constant ``Nat.pred} ({sub} ({succ} n₀) m₁)) ({sub} n₀ m₁)",
        s!"{rule} n₀ {zero} = {refl} n₀",
        s!"{rule} {zero} ({succ} m₁) = {q.helper subPredZeroName} m₁",
        s!"{rule} ({succ} n₀) ({succ} m₁) = {rule} n₀ m₁",
        s!"\{-# REWRITE {q.helper subRuleName} {q.helper subPredZeroName} {rule} #-}"] }]

/-- The pragmas that bind Lean's `Bool` to Agda's builtin booleans. -/
def boolPragmas : Array String :=
  #[s!"\{-# BUILTIN BOOL {agdaIdent ``Bool} #-}", s!"\{-# BUILTIN FALSE {agdaIdent ``Bool.false} #-}",
    s!"\{-# BUILTIN TRUE {agdaIdent ``Bool.true} #-}"]

/-- How many binders a type opens, every one explicit; none when one is
not explicit. -/
def explicitArity : Expr → Option Nat
  | .forallE _ _ b .default => (explicitArity b).map (· + 1)
  | .forallE .. => none
  | _ => some 0

/-- The row for a constant, when it has one and its type still opens the
binders the row's clauses bind; an error when the type no longer does,
since the clauses were written against Lean's definition at the pin. -/
def tableEntry? (name : Name) (type : Expr) : Except String (Option TableEntry) := do
  let some entry := table.find? (·.const == name) | return none
  unless explicitArity type == some entry.arity do
    throw s!"the operation table expects {name} to take {entry.arity} explicit arguments"
  return some entry

/-- The helpers the given ones use, directly or through each other, in
the table's order. -/
def helperClosure (start : Array String) : Array Helper := Id.run do
  let mut wanted := start
  let mut changed := true
  while changed do
    changed := false
    for h in helpers do
      if wanted.contains h.name then
        for u in h.uses do
          unless wanted.contains u do
            wanted := wanted.push u
            changed := true
  return helpers.filter (wanted.contains ·.name)

end Lean2Agda
