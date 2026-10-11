/-
File: translator/tests/Check.lean
-/
import Lean2Agda.Main
import TranslatorTests
import Atlas.Graph

open Lean Lean2Agda

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def checkOrder (closure : Closure) : IO Unit := do
  let mut positions : Std.HashMap Name Nat := {}
  for i in [:closure.groups.size] do
    for decl in closure.groups[i]! do
      require (!positions.contains decl.name) s!"duplicate {decl.name}"
      positions := positions.insert decl.name i
  for i in [:closure.groups.size] do
    for decl in closure.groups[i]! do
      for dep in decl.dependencies do
        let some j := positions[dep]? | throw (IO.userError s!"missing {dep}")
        require (j ≤ i) s!"dependency {dep} follows {decl.name}"
  require (positions.size == closure.size) "closure size disagrees with groups"
  let s := closure.stats
  require (s.constants == s.axioms + s.definitions + s.theorems + s.opaques +
    s.inductives + s.constructors + s.recursors + s.quotients) "statistics do not sum to size"

def namesOf (closure : Closure) : Array Name := closure.declarations.map (·.name)

def closureFor (env : Environment) (roots : Array Name) : IO Closure := do
  let closure ← IO.ofExcept (dependencyClosure env roots)
  checkOrder closure
  return closure

def checkArgs : IO Unit := do
  let args ← IO.ofExcept <| parseArgs ["--profile", "U", "--out", "a b", "--stats",
    "Init.Data.Nat.Gcd", "--", "Nat.gcd_self", "Nat.gcd_self"]
  require (args.profile == "U" && args.stats && args.out == some "a b" &&
    args.modules == #[`Init.Data.Nat.Gcd] && args.declarations.size == 2) "argument parsing"
  require ((← IO.ofExcept <| parseName "A.«b.c».2") == .num (.str `A "b.c") 2) "quoted name"
  for argv in [[], ["--wat"], ["--profile"], ["--out"], ["--profile", "K", "Init"],
    ["--out", "--stats", "Init"], ["Init", "--", "--stats"], ["A..B"]] do
    require ((parseArgs argv).toOption.isNone) s!"accepted malformed command {argv}"
  require ((← IO.ofExcept <| parseArgs ["--help"]).help) "help requires a module"

def checkFixtures : IO Unit := do
  let moduleName := `TranslatorTests.Input.Consumer
  let env ← importEnvironment #[moduleName]
  require ((← Fixtures.marker.get) == 23) "imported initializer did not execute"
  let roots ← IO.ofExcept <| selectRoots env #[moduleName] #[]
  require (roots.contains ``Fixtures.selected && roots.contains ``Fixtures.concealed) "module roots"
  require (!roots.contains ``Fixtures.token && !roots.contains ``Nat) "selected imported roots"
  require (roots.any isPrivateName) "private module root omitted"
  let all ← closureFor env roots
  require ((namesOf all).contains ``Fixtures.token) "cross-module dependency omitted"
  let selected ← closureFor env #[``Fixtures.selected]
  require (selected.declarations.any (isPrivateName ∘ (·.name))) "private dependency omitted"
  require (selected.declarations.any fun d =>
    d.name == ``Fixtures.token && d.sourceModule == some `TranslatorTests.Input.Base) "module ownership"
  let ctor ← closureFor env #[``Fixtures.Envelope.wrap]
  for n in [``Fixtures.Envelope, ``Fixtures.Envelope.wrap, ``Fixtures.Envelope.rec, ``Fixtures.Marker] do
    require ((namesOf ctor).contains n) s!"constructor closure misses {n}"
  require (ctor.groups.any fun g => g.any (·.name == ``Fixtures.Envelope) &&
    g.any (·.name == ``Fixtures.Envelope.wrap)) "inductive cycle split"
  let mutualClosure ← closureFor env #[``Fixtures.Tree]
  for n in [``Fixtures.Forest, ``Fixtures.Forest.cons, ``Fixtures.Tree.rec, ``Fixtures.Forest.rec] do
    require ((namesOf mutualClosure).contains n) s!"mutual closure misses {n}"
  let opaqueClosure ← closureFor env #[``Fixtures.concealed]
  require ((namesOf opaqueClosure).contains ``Fixtures.token && opaqueClosure.stats.opaques == 1)
    "opaque value omitted"
  let matcher ← closureFor env #[``Fixtures.mixed]
  require (matcher.declarations.any fun d =>
    (toString d.name).startsWith "Fixtures.mixed.match_") "matcher omitted"
  require ((expressionDependencies (.proj ``Fixtures.Box 0 (.bvar 0))).contains ``Fixtures.Box)
    "projection structure omitted"
  require ((expressionDependencies (.lit (.natVal 3))).contains ``Nat) "literal Nat omitted"
  require ((expressionDependencies (.lit (.strVal "x"))).contains ``String) "literal String omitted"
  let info : ConstantInfo := .recInfo {
    name := `syntheticRec, levelParams := [], type := .sort .zero, all := [],
    numParams := 0, numIndices := 0, numMotives := 0, numMinors := 0,
    rules := [{ ctor := ``Fixtures.Envelope.wrap, nfields := 1, rhs := mkConst ``Fixtures.token }],
    k := false, isUnsafe := false }
  require ((directDependencies {} info).contains ``Fixtures.token) "recursor rhs omitted"
  require ((dependencyClosure env #[`DoesNotExist]).toOption.isNone) "missing root accepted"
  require ((selectRoots env #[moduleName] #[`DoesNotExist]).toOption.isNone) "unknown selection accepted"
  require ((← closureFor env #[]).size == 0) "empty closure"
  let reversed ← closureFor env roots.reverse
  require (renderClosure "U" all == renderClosure "U" reversed) "root-order-dependent output"

/-- Compare the closure's axiom projection with the atlas, which records
axioms rather than the full declaration closure.  Also recompute through
the atlas's independently implemented graph on this closure. -/
def checkAtlas : IO Unit := do
  let env ← importEnvironment #[`Init.Data.Nat.Gcd]
  let closure ← closureFor env #[``Nat.gcd_self]
  let axioms := sortNames <| closure.declarations.filterMap fun d =>
    if d.kind == .axiom then some d.name else none
  let fixture ← IO.ofExcept <| Json.parse (← IO.FS.readFile "tests/atlas-gcd-self.json")
  let record ← IO.ofExcept <| fixture.getObjVal? "record"
  let expected ← IO.ofExcept <| record.getObjValAs? (Array String) "axioms"
  require (axioms.map toString == expected) "closure disagrees with atlas axiom record"
  let constants := closure.declarations.map fun d => (d.name, d.info)
  let sets := Atlas.axiomSets constants
  let some index := constants.findIdx? (·.1 == ``Nat.gcd_self)
    | throw (IO.userError "root missing")
  require (sortNames sets[index]! == axioms) "closure disagrees with atlas graph"
  let duplicate ← closureFor env #[``Nat.gcd_self, ``Nat.gcd_self]
  require (renderClosure "U" duplicate == renderClosure "U" closure) "duplicate roots change output"

def runChecks : IO Unit := do
  checkArgs
  checkFixtures
  checkAtlas
  IO.println "translator checks: parser, selection, dependencies, cycles, order, statistics, and atlas passed"

#eval runChecks
