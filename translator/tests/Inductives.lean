/-
File: translator/tests/Inductives.lean
-/
import Lean2Agda.Main
import TranslatorTests

/-!
Checks of the emitter of inductive types (issue M2-4): which types become
records, how many parameters stay parameters, the declarations of `Eq`,
`HEq`, `Acc`, `List`, `Nat.le`, `Nat` and `Lean.Syntax` and of the
fixtures in `TranslatorTests/Input/Inductives.lean`, projections printed
as field projections or, from a structure-like type that is not a record,
through its recursor, and the sharing pass's rule for constructor types.
Agda checks the same declarations in `run.sh`, in the fixture's scaffold
and in the scaffold of `Init.Core`'s inductive types.
-/

open Lean Lean2Agda

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def expectText (actual expected : String) (what : String) : IO Unit :=
  require (actual == expected) s!"{what}: expected\n{expected}\ngot\n{actual}"

def inductiveOf (env : Environment) (n : Name) : IO InductiveVal := do
  let some (.inductInfo v) := env.find? n | throw (IO.userError s!"no inductive type {n}")
  return v

/-- The declaration of a type's block, read from the environment. -/
def declarationText (env : Environment) (n : Name) : IO String := do
  let members ← IO.ofExcept (blockMembers env.find? (← inductiveOf env n))
  let d ← IO.ofExcept (inductiveDecl { env } members)
  return "\n".intercalate d.lines.toList

/-- Parameters kept, of the kernel's, and whether the type is a record. -/
def checkShapes (env : Environment) : IO Unit := do
  let cases : List (Name × Nat × Nat × Bool) := [
    (``Eq, 1, 2, false), (``HEq, 1, 2, false), (``Nat.le, 1, 1, false), (``Acc, 2, 2, false),
    (``List, 1, 1, false), (``Nat, 0, 0, false), (``String, 0, 0, false), (``Prod, 2, 2, true),
    (``PUnit, 0, 0, true), (``True, 0, 0, true), (``And, 2, 2, true), (``LawfulBEq, 2, 2, true),
    (``Relation.TransGen, 3, 3, false), (``Lean.Syntax, 0, 0, false),
    (``Lean.Meta.CheckTactic.CheckGoalType, 1, 2, false),
    (``InductiveFixtures.Vec, 1, 1, false), (``InductiveFixtures.Same, 1, 2, false),
    (``InductiveFixtures.Sized, 0, 1, false), (``InductiveFixtures.Packed, 2, 2, true),
    (``InductiveFixtures.Token, 0, 0, true), (``InductiveFixtures.Rose, 0, 0, true),
    (``InductiveFixtures.Stream', 0, 0, true), (``InductiveFixtures.Term, 0, 0, false),
    (``InductiveFixtures.Pair, 0, 0, true)]
  for (n, kept, params, record) in cases do
    let v ← inductiveOf env n
    require (v.numParams == params) s!"{n} has {v.numParams} parameters in the kernel"
    require (agdaParamCount env v == kept) s!"{n} keeps {agdaParamCount env v} parameters"
    require (isAgdaRecord env v == record) s!"{n} is a record: {isAgdaRecord env v}"
  for (n, expected) in [(``Prod.fst, true), (``Subtype.property, true), (``LE.le, true),
      (``InductiveFixtures.Packed.fits, true), (``InductiveFixtures.Rose.children, true),
      (``String.toByteArray, false), (``String.isValidUTF8, false), (``Nat.add, false)] do
    require (isRecordProjection env n == expected) s!"{n} is a record projection"

/-- The declarations, each as `run.sh` has Agda check it. -/
def checkDeclarations (env : Environment) : IO Unit := do
  let cases : List (Name × String) := [
    (``Eq, "data Eq {α₀ : Set} : α₀ → α₀ → Set where\n  Eq:refl : (a₁ : α₀) → Eq {α₀} a₁ a₁"),
    (``HEq, "data HEq {α₀ : Set} : α₀ → {β₁ : Set} → β₁ → Set where\n" ++
      "  HEq:refl : (a₁ : α₀) → HEq {α₀} a₁ {α₀} a₁"),
    (``Acc, "data Acc {α₀ : Set} (r₁ : α₀ → α₀ → Set) : α₀ → Set where\n" ++
      "  Acc:intro : (x₂ : α₀) → ((y₃ : α₀) → r₁ y₃ x₂ → Acc {α₀} r₁ y₃) → Acc {α₀} r₁ x₂"),
    (``List, "data List (α₀ : Set) : Set where\n  List:nil : List α₀\n  List:cons : α₀ → List α₀ → List α₀"),
    (``Nat.le, "data Nat:le (n₀ : Nat) : Nat → Set where\n  Nat:le:refl : Nat:le n₀ n₀\n" ++
      "  Nat:le:step : {m₁ : Nat} → Nat:le n₀ m₁ → Nat:le n₀ (Nat:succ m₁)"),
    (``Nat, "data Nat : Set where\n  Nat:zero : Nat\n  Nat:succ : Nat → Nat\n{-# BUILTIN NATURAL Nat #-}"),
    (``Prod, "record Prod (α₀ : Set) (β₁ : Set) : Set where\n  constructor Prod:mk\n  field\n" ++
      "    fst₂ : α₀\n    snd₃ : β₁"),
    (``PUnit, "record PUnit : Set where\n  constructor PUnit:unit"),
    (``LawfulBEq, "record LawfulBEq (α₀ : Set) ⦃ inst₁ : BEq α₀ ⦄ : Set where\n" ++
      "  constructor LawfulBEq:mk\n  field\n    ⦃ toReflBEq₂ ⦄ : ReflBEq α₀ ⦃ inst₁ ⦄\n" ++
      "    eqofbeq₃ : {a₃ : α₀} → {b₄ : α₀} → Eq {Bool} (BEq:beq {α₀} ⦃ inst₁ ⦄ a₃ b₄) Bool:true → Eq {α₀} a₃ b₄"),
    (``Lean.Syntax, "data Lean:Syntax : Set where\n  Lean:Syntax:missing : Lean:Syntax\n" ++
      "  Lean:Syntax:node : Lean:SourceInfo → Lean:SyntaxNodeKind → Array Lean:Syntax → Lean:Syntax\n" ++
      "  Lean:Syntax:atom : Lean:SourceInfo → String → Lean:Syntax\n" ++
      "  Lean:Syntax:ident : Lean:SourceInfo → Substring:Raw → Lean:Name → List Lean:Syntax:Preresolved → Lean:Syntax"),
    (``InductiveFixtures.Vec, "data InductiveFixtures:Vec (α₀ : Set) : Nat → Set where\n" ++
      "  InductiveFixtures:Vec:nil : InductiveFixtures:Vec α₀ (OfNat:ofNat {Nat} 0 ⦃ instOfNatNat 0 ⦄)\n" ++
      "  InductiveFixtures:Vec:cons : {n₁ : Nat} → α₀ → InductiveFixtures:Vec α₀ n₁ → " ++
      "InductiveFixtures:Vec α₀ (HAdd:hAdd {Nat} {Nat} {Nat} ⦃ instHAdd {Nat} ⦃ instAddNat ⦄ ⦄ n₁ " ++
      "(OfNat:ofNat {Nat} 1 ⦃ instOfNatNat 1 ⦄))"),
    (``InductiveFixtures.Same, "data InductiveFixtures:Same {α₀ : Set} : α₀ → α₀ → Set where\n" ++
      "  InductiveFixtures:Same:refl : (a₁ : α₀) → InductiveFixtures:Same {α₀} a₁ a₁"),
    (``InductiveFixtures.Sized, "data InductiveFixtures:Sized : Nat → Set where\n" ++
      "  InductiveFixtures:Sized:mk : (n₀ : Nat) → Fin n₀ → InductiveFixtures:Sized n₀"),
    (``InductiveFixtures.Packed, "record InductiveFixtures:Packed (α₀ : Set) ⦃ inst₁ : BEq α₀ ⦄ : Set where\n" ++
      "  constructor InductiveFixtures:Packed:mk\n  field\n    {width₂} : Nat\n" ++
      "    ⦃ measured₃ ⦄ : InductiveFixtures:Measure α₀\n    value₄ : α₀\n" ++
      "    fits₅ : LE:le {Nat} ⦃ instLENat ⦄ (InductiveFixtures:Measure:measure {α₀} ⦃ measured₃ ⦄ value₄) width₂"),
    (``InductiveFixtures.Token, "record InductiveFixtures:Token : Set where\n" ++
      "  constructor InductiveFixtures:Token:mk"),
    (``InductiveFixtures.Rose, "record InductiveFixtures:Rose : Set where\n  inductive\n" ++
      "  no-eta-equality\n  pattern\n  constructor InductiveFixtures:Rose:mk\n  field\n" ++
      "    label₀ : Nat\n    children₁ : List InductiveFixtures:Rose"),
    (``InductiveFixtures.Stream', "record InductiveFixtures:Stream~x27~ : Set where\n  inductive\n" ++
      "  no-eta-equality\n  pattern\n  constructor InductiveFixtures:Stream~x27~:mk\n  field\n" ++
      "    head₀ : Nat\n    tail₁ : Nat → InductiveFixtures:Stream~x27~"),
    (``InductiveFixtures.Bad, "{-# NO_POSITIVITY_CHECK #-}\nrecord InductiveFixtures:Bad : Set where\n" ++
      "  inductive\n  no-eta-equality\n  pattern\n  constructor InductiveFixtures:Bad:mk\n  field\n" ++
      "    a₀ : InductiveFixtures:Bad → Nat"),
    (``InductiveFixtures.Pair, "mutual\n  data InductiveFixtures:Term : Set where\n" ++
      "    InductiveFixtures:Term:lit : Nat → InductiveFixtures:Term\n" ++
      "    InductiveFixtures:Term:pair : InductiveFixtures:Pair → InductiveFixtures:Term\n" ++
      "  record InductiveFixtures:Pair : Set where\n    inductive\n    no-eta-equality\n    pattern\n" ++
      "    constructor InductiveFixtures:Pair:mk\n    field\n      left₀ : InductiveFixtures:Term\n" ++
      "      right₁ : InductiveFixtures:Term")]
  for (n, expected) in cases do
    expectText (← declarationText env n) expected s!"the declaration of {n}"
  -- A block declares its types and constructors and refers to nothing it declares.
  let members ← IO.ofExcept (blockMembers env.find? (← inductiveOf env ``InductiveFixtures.Term))
  let d ← IO.ofExcept (inductiveDecl { env } members)
  require (d.provides == #["InductiveFixtures:Term", "InductiveFixtures:Term:lit",
    "InductiveFixtures:Term:pair", "InductiveFixtures:Pair", "InductiveFixtures:Pair:mk"])
    s!"the mutual block provides {d.provides}"
  require (d.references == #["Nat"]) s!"the mutual block refers to {d.references}"

def printType (env : Environment) (e : Expr) : IO String := do
  let (t, _) ← IO.ofExcept (({ env } : Printer).type e)
  return t.render

/-- Projections: from a record, Agda's field projection, its parameters
implicit or instance arguments as Agda's projections take them; from a
structure-like type that is not a record, the recursor. -/
def checkProjections (env : Environment) : IO Unit := do
  let nat := mkConst ``Nat
  let prod := mkApp2 (.const ``Prod [.zero, .zero]) nat nat
  expectText (← printType env (.lam `p prod (.proj ``Prod 0 (.bvar 0)) .default))
    "λ (p₀ : Prod Nat Nat) → Prod.fst₂ {Nat} {Nat} p₀" "a record's projection"
  let beq := mkApp (.const ``BEq [.zero]) nat
  let packed := mkApp2 (mkConst ``InductiveFixtures.Packed) nat (.bvar 0)
  expectText (← printType env (.lam `b beq (.lam `p packed (.proj ``InductiveFixtures.Packed 3 (.bvar 0))
      .default) .instImplicit))
    ("λ ⦃ b₀ : BEq Nat ⦄ → λ (p₁ : InductiveFixtures:Packed Nat ⦃ b₀ ⦄) → " ++
     "InductiveFixtures:Packed.fits₅ {Nat} ⦃ b₀ ⦄ p₁") "a projection past an instance parameter"
  expectText (← printType env (.lam `t (mkConst ``InductiveFixtures.Rose)
      (.proj ``InductiveFixtures.Rose 1 (.bvar 0)) .default))
    "λ (t₀ : InductiveFixtures:Rose) → InductiveFixtures:Rose.children₁ t₀" "a recursive record's projection"
  expectText (← printType env (.lam `s (mkConst ``String) (.proj ``String 0 (.bvar 0)) .default))
    ("λ (s₀ : String) → String:rec {λ (self₁ : String) → ByteArray} " ++
     "(λ (toByteArray₁ : ByteArray) → λ (isValidUTF8₂ : ByteArray:IsValidUTF8 toByteArray₁) → toByteArray₁) s₀")
    "a projection from String, a postulate"
  let sized := mkApp (mkConst ``InductiveFixtures.Sized) (.lit (.natVal 3))
  expectText (← printType env (.lam `x sized (.proj ``InductiveFixtures.Sized 0 (.bvar 0)) .default))
    ("λ (x₀ : InductiveFixtures:Sized 3) → InductiveFixtures:Sized:rec {3} " ++
     "{λ (self₁ : InductiveFixtures:Sized 3) → Fin 3} (λ (value₁ : Fin 3) → value₁) x₀")
    "a projection from a structure-like data type"

/-- The sharing pass makes no auxiliary of a constructor's type that
mentions its block, and the scaffold puts every other one first. -/
def checkSharing (env : Environment) : IO Unit := do
  let some info := env.find? ``InductiveFixtures.Wide.node | throw (IO.userError "missing Wide.node")
  let decl : Lean2Agda.Declaration := {
    name := ``InductiveFixtures.Wide.node, info := info,
    sourceModule := some `TranslatorTests.Input.Inductives, dependencies := #[] }
  let shared ← IO.ofExcept (shareDeclaration env defaultShareThreshold decl)
  require (shared.auxiliaries.size == 1) s!"auxiliaries of Wide.node: {shared.auxiliaries.size}"
  require (shared.auxiliaries.all fun a => (a.info.value!.find? (·.isConstOf ``InductiveFixtures.Wide)).isNone)
    "an auxiliary of Wide.node mentions Wide"
  -- A subterm mentions a block's type through a constant or a projection.
  let x := mkConst ``Nat.zero
  require (!outsideBlock [`T] (mkApp (mkConst `T) x) && !outsideBlock [`T] (.proj `T 0 x) &&
    outsideBlock [`T] (.proj `U 0 x) && outsideBlock [] (.proj `T 0 x)) "outsideBlock"
  let closure ← IO.ofExcept (dependencyClosure env #[``InductiveFixtures.Wide])
  let s ← IO.ofExcept (scaffold env `U (← IO.ofExcept (shareClosure env defaultShareThreshold closure)))
  let position (n : String) : IO Nat := do
    let some i := s.items.findIdx? (·.provides.contains n) | throw (IO.userError s!"no item {n}")
    return i
  require ((← position "InductiveFixtures:Wide:node:~ushare:~n1") < (← position "InductiveFixtures:Wide"))
    "the auxiliary follows the type that uses it"

#eval show IO Unit from do
  let env ← importEnvironment #[`Init, `TranslatorTests.Input.Inductives]
  checkShapes env
  checkDeclarations env
  checkProjections env
  checkSharing env
  IO.println "inductive checks: shapes, declarations, projections, and sharing passed"
