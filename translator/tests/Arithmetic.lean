/-
File: translator/tests/Arithmetic.lean
-/
import Lean2Agda.Main
import TranslatorTests

/-!
The operation table (issue M3-6), on the fixture
`TranslatorTests.Input.Arithmetic`.  Under `--arithmetic agda` each
accelerated operation's recursive core is its row of the table: the
builtins with their arguments swapped or shifted, `Nat.beq` bound to
`NATEQUALS`, the fuel cores matching on the divisor, Lean's clauses for
the others; each helper sits in its home module before its first user,
with its `BUILTIN` pragma, and a module elsewhere names it by its home's
path; `Bool` carries its builtins; and the rewrite rules of `Nat.sub`
come before `Nat.sub`, which refers to them.  Under `--arithmetic lean` none of that appears, and
the tree declares the same Lean constants.  `tableEntry?` refuses a
definition whose type no longer has its row's arity.  `tests/run.sh`
checks the fixture's trees under both settings with Agda, and the
numerals of `TranslatorTests.Input.Numerals` under the table.
-/

open Lean Lean2Agda

namespace ArithmeticTests

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def treeOf (env : Environment) (arithmetic : Arithmetic) : IO ScaffoldTree := do
  let roots ← IO.ofExcept <| selectRoots env #[`TranslatorTests.Input.Arithmetic] #[]
  let closure ← IO.ofExcept (dependencyClosure env roots)
  IO.ofExcept (scaffoldTree env `U (← IO.ofExcept (shareClosure env defaultShareThreshold closure))
    defaultSplitThreshold arithmetic)

def moduleOf (t : ScaffoldTree) (source : Name) : IO AgdaModule := do
  let some m := t.module? source | throw (IO.userError s!"no module for {source}")
  return m

def indexOf (m : AgdaModule) (ident : String) : IO Nat := do
  let some i := m.items.findIdx? (·.provides.contains ident) | throw (IO.userError s!"no item for {ident}")
  return i

def textOf (m : AgdaModule) (ident : String) : IO String :=
  return m.items[← indexOf m ident]!.text

def provided (t : ScaffoldTree) : Array String :=
  t.modules.foldl (fun acc m => m.items.foldl (· ++ ·.provides) acc) #[]

def isHelper (ident : String) : Bool := (ident.splitOn "-").length > 1

def checkTable (env : Environment) : IO Unit := do
  let t ← treeOf env .agda
  let prelude ← moduleOf t `Init.Prelude
  let bitwise ← moduleOf t `Init.Data.Nat.Bitwise.Basic
  -- A builtin with its arguments swapped, after its helper and the
  -- helper's pragma.
  require ((← textOf prelude "Nat:add") ==
    "-- operation table\nNat:add : Nat → Nat → Nat\nNat:add x₀ x₁ = Nat:add-builtin x₁ x₀\n")
    s!"Nat.add: {← textOf prelude "Nat:add"}"
  require ((← textOf prelude "Nat:add-builtin").endsWith "\n{-# BUILTIN NATPLUS Nat:add-builtin #-}\n")
    "the helper of Nat.add lost its pragma"
  require ((← indexOf prelude "Nat:add-builtin") < (← indexOf prelude "Nat:add")) "a helper after its user"
  require ((← textOf prelude "Nat:mul").endsWith "Nat:mul x₀ x₁ = Nat:mul-builtin x₁ x₀\n") "Nat.mul"
  require ((← textOf prelude "Nat:ble").endsWith "Nat:ble x₀ x₁ = Nat:blt-builtin x₀ (Nat:succ x₁)\n") "Nat.ble"
  -- `Nat.beq` is Agda's `_==_` itself.
  require ((← textOf prelude "Nat:beq").endsWith "\n{-# BUILTIN NATEQUALS Nat:beq #-}\n") "Nat.beq"
  -- Lean's clauses for `Nat.pow`, over the builtin product.
  require ((← textOf prelude "Nat:pow").endsWith
    "Nat:pow m₀ Nat:zero = 1\nNat:pow m₀ (Nat:succ n₁) = Nat:mul-builtin m₀ (Nat:pow m₀ n₁)\n") "Nat.pow"
  -- The fuel cores match on the divisor and ignore the fuel and the proofs.
  require ((← textOf prelude "Nat:div:go").endsWith
    "Nat:div:go (Nat:succ y₀) hy₁ fuel₂ x₃ hfuel₄ = Nat:div-builtin Nat:zero y₀ x₃ y₀\n") "Nat.div.go"
  require ((← textOf prelude "Nat:modCore:go").endsWith
    "Nat:modCore:go (Nat:succ y₀) hy₁ fuel₂ x₃ hfuel₄ = Nat:mod-builtin Nat:zero y₀ x₃ y₀\n") "Nat.modCore.go"
  -- Lean's wrappers stay Lean's.
  require (!(← textOf prelude "Nat:div").startsWith "-- operation table") "Nat.div is Lean's"
  -- `Bool` carries its builtins, which `NATEQUALS` and `NATLESS` need.
  require ((← textOf prelude "Bool").endsWith
    "{-# BUILTIN BOOL Bool #-}\n{-# BUILTIN FALSE Bool:false #-}\n{-# BUILTIN TRUE Bool:true #-}\n") "Bool"
  -- The rules of `Nat.sub` right before `Nat.sub`, which refers to the
  -- last, so that a part that uses `Nat.sub` imports them; one pragma
  -- declares the three, which Agda finds confluent only together.
  require ((← indexOf prelude "Nat:sub-builtin-pred-succ") + 1 == (← indexOf prelude "Nat:sub")) "the rules' place"
  require ((← indexOf prelude "Nat:sub-builtin-succ") < (← indexOf prelude "Nat:sub-builtin-pred-succ")
    && (← indexOf prelude "Nat:sub-builtin-pred-zero") < (← indexOf prelude "Nat:sub-builtin-pred-succ"))
    "a rule after the pragma that names it"
  let sub := prelude.items[← indexOf prelude "Nat:sub"]!
  require (sub.references.contains "Nat:sub-builtin-pred-succ") "Nat.sub does not refer to its rules"
  require ((← textOf prelude "Nat:sub-builtin-pred-succ").endsWith
    "\n{-# REWRITE Nat:sub-builtin-succ Nat:sub-builtin-pred-zero Nat:sub-builtin-pred-succ #-}\n")
    "the rules' pragma"
  require (!(← textOf prelude "Nat:sub-builtin-succ").contains "REWRITE") "a rule declared alone"
  -- `Nat.pred` by Lean's clauses, so that a rule headed by it can fire.
  require ((← textOf prelude "Nat:pred").endsWith "Nat:pred Nat:zero = Nat:zero\nNat:pred (Nat:succ n₀) = n₀\n")
    "Nat.pred"
  -- `Nat.bitwise`'s helpers sit in its module and are named bare there;
  -- the builtins of `Init.Prelude` are named by its path.
  require ((← textOf bitwise "Nat:bitwise").endsWith
    "Nat:bitwise f₀ n₁ m₂ = Nat:bitwise-go (U.Init.Prelude.Nat:succ n₁) f₀ n₁ m₂\n")
    s!"Nat.bitwise: {← textOf bitwise "Nat:bitwise"}"
  require (((← textOf bitwise "Nat:bitwise-go").splitOn "U.Init.Prelude.Nat:div-builtin").length == 3)
    "a helper of another module, unqualified"
  require ((← textOf bitwise "Nat:shiftRight").endsWith
    "Nat:shiftRight n₀ (U.Init.Prelude.Nat:succ m₁) = U.Init.Prelude.Nat:div-builtin U.Init.Prelude.Nat:zero 1 (Nat:shiftRight n₀ m₁) 1\n")
    "Nat.shiftRight"
  require (bitwise.imports.contains ["U", "Init", "Prelude"]) "the bitwise module does not import the builtins"
  -- The helpers are the table's.
  let helpers := (provided t).filter isHelper
  require (helpers.qsort (· < ·) == #["Nat:add-builtin", "Nat:bitwise-bit", "Nat:bitwise-go",
    "Nat:bitwise-odd", "Nat:bitwise-pick", "Nat:blt-builtin", "Nat:div-builtin", "Nat:mod-builtin",
    "Nat:mul-builtin", "Nat:sub-builtin", "Nat:sub-builtin-pred-succ", "Nat:sub-builtin-pred-zero",
    "Nat:sub-builtin-succ"]) s!"helpers: {helpers}"

def checkLean (env : Environment) : IO Unit := do
  let t ← treeOf env .lean
  let prelude ← moduleOf t `Init.Prelude
  require ((← textOf prelude "Nat:add").startsWith "Nat:add : Nat → Nat → Nat\nNat:add x₀ x₁ = Nat:brecOn")
    s!"Nat.add under --arithmetic lean: {← textOf prelude "Nat:add"}"
  require (!(← textOf prelude "Bool").contains "BUILTIN") "Bool's builtins under --arithmetic lean"
  require (!((provided t).any isHelper)) "a helper under --arithmetic lean"
  -- The same Lean constants either way.
  let table ← treeOf env .agda
  require (((provided table).filter (!isHelper ·)).qsort (· < ·) == (provided t).qsort (· < ·))
    "the two settings declare different constants"

def checkArity : IO Unit := do
  let nat : Expr := .const ``Nat []
  let two : Expr := .forallE `a nat (.forallE `b nat nat .default) .default
  let three : Expr := .forallE `c nat two .default
  let hidden : Expr := .forallE `a nat (.forallE `b nat nat .default) .implicit
  require ((tableEntry? ``Nat.add two).toOption.map (·.map (·.const)) == some (some ``Nat.add)) "the row of Nat.add"
  require ((tableEntry? ``Nat.add three) matches .error _) "a wrong arity accepted"
  require ((tableEntry? ``Nat.add hidden) matches .error _) "an implicit binder accepted"
  require ((tableEntry? ``Nat.modCore two) matches .ok none) "a row for Nat.modCore, a wrapper"

def run : IO Unit := do
  let env ← importEnvironment #[`TranslatorTests]
  checkTable env
  checkLean env
  checkArity
  IO.println "arithmetic checks: the table's rows and helpers, both settings, and the arity guard passed"

end ArithmeticTests
