/-
File: translator/tests/Levels.lean
-/
import Lean2Agda.Main
import TranslatorTests

/-!
The Prop-instantiation specialization (issue M3-3), on core Lean and the
fixture `TranslatorTests.Input.Levels`: the normal form of a level and
what the specialization asks of it; which level parameters each constant
is split on, under both rules; the instance a use selects, and that only
the instances something uses are made; an instance's expressions, with
every `imax` gone; an instance's identifier, which no Lean name's
encoding is, and its sidecar record; what the scaffold prints for a
closure of instances; and, over the closure of `Init.Core`'s
declarations, that no instance holds an `imax`, that every level is in
normal form with a predecessor where the predecessor rule promises one,
and that Lean's kernel accepts every instance.  `tests/run.sh` checks the
fixture's scaffold, printed with `--specialize`, against its golden tree
and listing, and the counts of `Init.Core`'s closure against their golden
file.
-/

open Lean Lean2Agda

namespace LevelTests

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def u : Level := .param `u
def v : Level := .param `v
def w : Level := .param `w
def one : Level := .succ .zero

def normal (l : Level) : IO NormalLevel :=
  match normalLevel l with
  | .ok n => pure n
  | .error _ => throw (IO.userError s!"no normal form for {l}")

/-- The parameters that leave a level's `imax` undecided, when some do. -/
def undecided (l : Level) : Option (Array Name) :=
  match normalLevel l with
  | .error (.undecided ps) => some ps
  | _ => none

def checkNormalForm : IO Unit := do
  -- An `imax` is zero when its second argument is, and a `max` when that
  -- is never zero; otherwise the bare parameters of the argument decide.
  require ((← normal (.imax u (.succ v))) == (← normal (.max u (.succ v)))) "imax u (v+1) is not max u (v+1)"
  require (← normal (.imax u .zero)).isZero "imax u 0 is not zero"
  require (← normal (.imax (.imax u v) .zero)).isZero "an undecided imax under one that is zero"
  require (undecided (.imax u v) == some #[`v]) s!"imax u v: {repr (undecided (.imax u v))}"
  require (undecided (.imax u (.max w v)) == some #[`v, `w]) "imax u (max w v)"
  require (undecided (.max (.imax u v) one) == some #[`v]) "an imax inside a max"
  require ((undecided (.imax u (.succ v))).isNone && (undecided u).isNone) "a decided level called undecided"
  -- Under an assignment of its parameters every `imax` of this one is decided.
  let under (zeros : Array Bool) : Option NormalLevel :=
    (normalLevelWith (assignment [`u, `v] #[true, true] zeros) (.imax u v)).toOption
  require (under #[true, false] == some (NormalLevel.param `v).succ) "imax u v at u zero"
  require (under #[false, true] == some .zero && under #[true, true] == some .zero) "imax u v at v zero"
  require (under #[false, false] == some ((NormalLevel.param `u).succ.max (NormalLevel.param `v).succ))
    "imax u v at neither zero"
  -- The canonical form: one atom per parameter, in the names' order, and
  -- the constant only where it exceeds every offset.
  require ((← normal (.max (.succ u) u)) == (← normal (.succ u))) "max (u+1) u"
  require ((← normal (.max u (.max v u))) == (← normal (.max v u))) "max u (max v u)"
  require ((← normal (.max one (.succ u))) == (← normal (.succ u))) "max 1 (u+1)"
  require ((← normal (.succ u)) == { constant := 0, atoms := #[(`u, 1)] }) "u+1 keeps a constant"
  require ((← normal (.max (.succ v) u)).atoms == #[(`u, 0), (`v, 1)]) "the atoms' order"
  let two := Level.succ one
  let kept ← normal (.max two (.succ u))
  require (kept != (← normal (.succ u)) && kept.constant == 2) "max 2 (u+1) lost its constant"
  -- Zero, never zero, bare parameters and predecessors.
  let m ← normal (.max one u)
  require (m.neverZero && !m.isZero && m.bare == #[`u] && m.pred?.isNone) "max 1 u"
  let bare ← normal (.max u v)
  require (!bare.neverZero && !bare.isZero && bare.bare == #[`u, `v] && bare.pred?.isNone) "max u v"
  require ((← normal (.succ u)).pred? == some (.param `u)) "the predecessor of u+1"
  require ((← normal (.max (.succ u) (.succ (.succ v)))).pred? == some (← normal (.max u (.succ v))))
    "the predecessor of max (u+1) (v+2)"
  require (kept.pred? == some (← normal (.max one u))) "the predecessor of max 2 (u+1)"
  require (NormalLevel.zero.pred?.isNone && (← normal one).pred? == some .zero) "the predecessors of 0 and 1"
  -- The level a normal form writes has that normal form, holds no `imax`,
  -- and is the level it came from, by Lean's own comparison of levels.
  for l in [Level.zero, one, u, .succ u, .max u v, .max (.succ u) v, .max two (.max (.succ u) (.succ (.succ w))),
      .max (.max one u) v, .imax u (.succ v), .imax (.succ u) (.max one v), .max (.succ (.max u v)) w] do
    let n ← normal l
    require ((← normal n.toLevel) == n) s!"{l}: its normal form's level has another normal form"
    require (!hasIMax n.toLevel) s!"{l}: an imax in a normal form"
    require (Level.isEquiv l n.toLevel) s!"{l}: Lean distinguishes it from {n.toLevel}"
  require (hasIMax (.max u (.succ (.imax u v))) && !hasIMax (.max u (.succ v))) "hasIMax"

/-- A closure's specialization under a rule: the fixture module's
declarations and the given constants as roots. -/
def specializationFor (env : Environment) (rule : SplitRule) (extra : Array Name) :
    IO (Closure × Splits × Array InstanceRecord × SpecializationStats) := do
  let roots ← IO.ofExcept (selectRoots env #[`TranslatorTests.Input.Levels] #[])
  let closure ← IO.ofExcept (dependencyClosure env (roots ++ extra))
  let (splits, instances, stats) ← IO.ofExcept (specializationOf env rule closure)
  return (closure, splits, instances, stats)

def coreNames : Array Name :=
  #[``Eq, ``Eq.rec, ``ULift, ``PUnit, ``Nat.rec, ``PProd, ``Prod, ``Quot.lift, ``Quot.ind, ``id]

def checkSplits (env : Environment) : IO Unit := do
  let (_, splits, _, _) ← specializationFor env .predecessor coreNames
  let expect (splits : Splits) (n : Name) (mask : Array Bool) : IO Unit :=
    require (splits.mask n == mask) s!"{n} under {splits.rule.label}: split {splits.mask n}, expected {mask}"
  -- A sort at the parameter itself: `Eq`'s `α : Sort u_1`, `PUnit : Sort u`,
  -- a recursor's motive.
  for (n, mask) in [(``Eq, #[true]), (``PUnit, #[true]), (``id, #[true]), (``Eq.rec, #[true, true]),
      (``Nat.rec, #[true]), (``PProd, #[true, true]), (``Quot.lift, #[true, true]), (``Quot.ind, #[true])] do
    expect splits n mask
  -- Never `Prop`: every sort of `ULift` and `Prod` is a `Type`.
  expect splits ``ULift #[false, false]
  expect splits ``Prod #[false, false]
  -- The fixtures: a sort; none; a parameter passed on, and a successor
  -- passed on; an `imax`.
  expect splits ``LevelFixtures.twice #[true]
  expect splits ``LevelFixtures.lifted #[false, false]
  expect splits ``LevelFixtures.passes #[true]
  expect splits ``LevelFixtures.passesSucc #[false]
  expect splits ``LevelFixtures.arrow #[true, true]
  expect splits ``LevelFixtures.atType #[]
  -- A block has one mask: a type's is its constructor's, and its
  -- recursor adds the motive's.
  for n in [``LevelFixtures.Box, ``LevelFixtures.Box.mk, ``LevelFixtures.Pick, ``LevelFixtures.Pick.left,
      ``LevelFixtures.Pick.right, ``LevelFixtures.Tagged, ``LevelFixtures.Tagged.mk] do
    expect splits n #[true]
  expect splits ``LevelFixtures.Box.rec #[true, true]
  expect splits ``LevelFixtures.Pick.rec #[true, true]
  -- `Holder : Type u` alone would not be split; its constructor's field
  -- `α : Sort u` splits the block.
  expect splits ``LevelFixtures.Holder #[true]
  expect splits ``LevelFixtures.Holder.mk #[true]
  -- `max 1 u` is never zero and has no predecessor: split under the
  -- predecessor rule only.
  expect splits ``LevelFixtures.wide #[true]
  let (_, byZero, _, _) ← specializationFor env .zeroness coreNames
  expect byZero ``LevelFixtures.wide #[false]
  expect byZero ``LevelFixtures.twice #[true]
  expect byZero ``LevelFixtures.passes #[true]
  expect byZero ``LevelFixtures.arrow #[true, true]

def checkUses (env : Environment) : IO Unit := do
  let (_, splits, instances, stats) ← specializationFor env .predecessor coreNames
  -- The instance a reference selects.
  let resolved (c : Name) (us : List Level) : Option Name := (splits.resolve c us).toOption
  require (resolved ``Eq [one] == some (instanceKey ``Eq "n")) "Eq at 1"
  require (resolved ``Eq [.zero] == some (instanceKey ``Eq "z")) "Eq at 0"
  require (resolved ``Eq [.max one u] == some (instanceKey ``Eq "n")) "Eq at max 1 u"
  require (resolved ``Eq.rec [.zero, .succ u] == some (instanceKey ``Eq.rec "zn")) "Eq.rec at 0 and u+1"
  require (resolved ``Eq [.imax u .zero] == some (instanceKey ``Eq "z")) "Eq at imax u 0"
  require (resolved ``ULift [u, v] == some ``ULift) "ULift, which has no instance but itself"
  require (resolved `no.such.constant [u] == some `no.such.constant) "a name the analysis never saw"
  require ((resolved ``Eq [u]).isNone && (resolved ``Eq [.imax u v]).isNone) "an undecided level selected an instance"
  -- What each instance uses.
  let usesOf (key : Name) : IO (Array Name) := do
    let some r := instances.find? (·.key == key) | throw (IO.userError s!"no instance {key}")
    return r.uses
  let twice (letters : String) := instanceKey ``LevelFixtures.twice letters
  let unit (letters : String) := instanceKey ``PUnit letters
  let atType ← usesOf ``LevelFixtures.atType
  require (atType.contains (twice "n") && !atType.contains (twice "z")) s!"atType uses {atType}"
  let atProp ← usesOf ``LevelFixtures.atProp
  require (atProp.contains (twice "z") && !atProp.contains (twice "n")) s!"atProp uses {atProp}"
  require ((← usesOf (instanceKey ``LevelFixtures.passes "z")) == #[unit "z"]) "passes at zero"
  require ((← usesOf (instanceKey ``LevelFixtures.passes "n")) == #[unit "n"]) "passes at nonzero"
  require ((← usesOf ``LevelFixtures.passesSucc) == #[unit "n"]) "passesSucc"
  -- A projection uses its structure at the levels of the term projected
  -- from, which only the kernel's inference gives.
  let box (letters : String) := instanceKey ``LevelFixtures.Box letters
  let val ← usesOf (instanceKey ``LevelFixtures.Box.val "z")
  require (val.contains (box "z") && !val.contains (box "n")) s!"Box.val at zero uses {val}"
  -- A quotient primitive's rule names `Quot.mk` and an instance of `Eq`.
  let lift ← usesOf (instanceKey ``Quot.lift "zn")
  require (lift.contains (instanceKey ``Quot.mk "z") && lift.contains (instanceKey ``Eq "n")) s!"Quot.lift#zn uses {lift}"
  let liftProp ← usesOf (instanceKey ``Quot.lift "nz")
  require (liftProp.contains (instanceKey ``Quot.mk "n") && liftProp.contains (instanceKey ``Eq "z"))
    s!"Quot.lift#nz uses {liftProp}"
  let ind ← usesOf (instanceKey ``Quot.ind "n")
  require (ind.contains (instanceKey ``Eq "z")) s!"Quot.ind#n uses {ind}"
  -- A recursor's instance comes with its type's and its constructors',
  -- which its own type names; a type's instance with its constructors',
  -- which nothing in its type names.
  let pickRec ← usesOf (instanceKey ``LevelFixtures.Pick.rec "zn")
  require (pickRec.contains (instanceKey ``LevelFixtures.Pick "n") &&
    pickRec.contains (instanceKey ``LevelFixtures.Pick.left "n") &&
    pickRec.contains (instanceKey ``LevelFixtures.Pick.right "n")) s!"Pick.rec#zn uses {pickRec}"
  -- A type of a mutual declaration comes with the block's other types.
  let even ← usesOf (instanceKey ``LevelFixtures.Even "z")
  require (even.contains (instanceKey ``LevelFixtures.Odd "z") && !even.contains (instanceKey ``LevelFixtures.Odd "n"))
    s!"Even#z uses {even}"
  let pick ← usesOf (instanceKey ``LevelFixtures.Pick "z")
  require (pick.contains (instanceKey ``LevelFixtures.Pick.left "z") &&
    pick.contains (instanceKey ``LevelFixtures.Pick.right "z") &&
    !pick.any (·.getPrefix == ``LevelFixtures.Pick.rec)) s!"Pick#z uses {pick}"
  -- A root comes at every pattern.
  for letters in ["zz", "zn", "nz", "nn"] do
    require (instances.any (·.key == instanceKey ``LevelFixtures.arrow letters)) s!"no instance arrow#{letters}"
  require (stats.instances == instances.size && stats.rule == .predecessor) "the counted instances"
  -- Instances are made from uses: the closure of `atType` alone holds
  -- `twice` at a type and not at a proposition.
  let closure ← IO.ofExcept (dependencyClosure env #[``LevelFixtures.atType])
  let (_, lazy, lazyStats) ← IO.ofExcept (specializationOf env .predecessor closure)
  require (lazy.any (·.key == twice "n") && !lazy.any (·.key == twice "z")) "twice at zero made without a use"
  -- Its counts: `atType`, `twice`, and `Nat` with its constructors and
  -- recursor; `twice` and `Nat.rec` have a parameter each, both split,
  -- and one instance of each is made; the entries are the two definitions
  -- and the type.
  let expected : SpecializationStats := {
    rule := .predecessor, constants := 6, polymorphic := 2, parameters := 2, split := 2, splitConstants := 2,
    instances := 5, possibleBySplit := 8, possibleByParameters := 8, entries := 3, possibleByEntries := 4 }
  require (lazyStats == expected) s!"the counts of atType's closure: {repr lazyStats}"
  require ((lazyStats.render.splitOn "\n").take 3 ==
    ["# specialization, rule predecessor", "constants\t6", "with level parameters\t2"]) "the counts' text"

def declarationOf (closure : Closure) (key : Name) : IO Lean2Agda.Declaration := do
  let some d := closure.declarations.find? (·.name == key) | throw (IO.userError s!"no declaration {key}")
  return d

def checkInstances (env : Environment) : IO Unit := do
  let roots ← IO.ofExcept (selectRoots env #[`TranslatorTests.Input.Levels] #[])
  let closure ← IO.ofExcept (dependencyClosure env roots)
  let (made, _, stats) ← IO.ofExcept (specializeClosure env .predecessor closure)
  require (made.size == stats.instances) "one declaration per instance"
  let arrow (a b result : Level) : Expr :=
    .forallE `α (.sort a) (.forallE `β (.sort b) (.sort result) .default) .default
  -- `Sort (imax u v)` in each instance: zero where `v` is, `v + 1` where
  -- only `u` is zero, a `max` where neither is; `u` there is one below the
  -- constant's `u`.
  for (letters, params, type) in [
      ("zz", [], arrow .zero .zero .zero),
      ("nz", [`u], arrow (.succ u) .zero .zero),
      ("zn", [`v], arrow .zero (.succ v) (.succ v)),
      ("nn", [`u, `v], arrow (.succ u) (.succ v) (.max (.succ u) (.succ v)))] do
    let d ← declarationOf made (instanceKey ``LevelFixtures.arrow letters)
    require (d.info.type == type) s!"arrow#{letters} : {d.info.type}"
    require (d.info.levelParams == params) s!"arrow#{letters} keeps {d.info.levelParams}"
    require (d.pattern == letters && d.info.name == ``LevelFixtures.arrow) s!"arrow#{letters}: pattern and name"
  -- `max 1 u` is `1` at zero and `u + 1` elsewhere.
  let wideZ ← declarationOf made (instanceKey ``LevelFixtures.wide "z")
  require (wideZ.info.type == .forallE `α (.sort one) (.sort one) .default) s!"wide#z : {wideZ.info.type}"
  let wideN ← declarationOf made (instanceKey ``LevelFixtures.wide "n")
  require (wideN.info.type == .forallE `α (.sort (.succ u)) (.sort (.succ u)) .default) s!"wide#n : {wideN.info.type}"
  -- A constant without split parameters is its own one instance, as it was.
  let lifted ← declarationOf made ``LevelFixtures.lifted
  require (lifted.pattern == "" && lifted.info.levelParams == [`u, `v]) "lifted"
  -- Every dependency is an instance of the closure, and the roots are
  -- the patterns of the closure's roots.
  let keys : Std.HashSet Name := made.declarations.foldl (fun s d => s.insert d.name) {}
  for d in made.declarations do
    for dep in d.dependencies do
      require (keys.contains dep) s!"{d.name} depends on {dep}, which the closure does not hold"
  require (made.roots.contains (instanceKey ``LevelFixtures.twice "z") &&
    made.roots.contains (instanceKey ``LevelFixtures.twice "n") && !made.roots.contains ``LevelFixtures.twice)
    "the roots of the closure of instances"

def checkNames (env : Environment) : IO Unit := do
  require (isPatternComponent "#z" && isPatternComponent "#nzn" && !isPatternComponent "#" &&
    !isPatternComponent "z" && !isPatternComponent "#zx" && !isPatternComponent "") "isPatternComponent"
  require (instanceKey ``Eq "" == ``Eq) "the empty pattern's key"
  require (instanceIdent (instanceKey ``Eq.rec "zn") == "Eq:rec#zn") "Eq.rec#zn"
  require (instanceIdent (auxiliaryName (instanceKey `A.b_c "n") 1) == "A:b~uc#n:~ushare:~n1") "an instance's auxiliary"
  require (instanceIdent .anonymous == agdaIdent .anonymous) "the anonymous name"
  require (keyDisplay (instanceKey ``sorryAx "z") == "sorryAx#z" && keyDisplay ``Nat.gcd_self == "Nat.gcd_self" &&
    keyDisplay (auxiliaryName (instanceKey `A.b "n") 1) == "A.b#n._share.1") "keyDisplay"
  -- A Lean name with a component of a pattern's form is not an instance:
  -- its `agdaIdent` escapes the `#`, and the specialization refuses it.
  let impostor : Name := .str `A "#z"
  require (agdaIdent impostor == "A:~x23~z" && instanceIdent (instanceKey `A "z") == "A#z") "the impostor's identifier"
  require (hasPatternComponent impostor && hasPatternComponent (.num (.str impostor "b") 1) &&
    !hasPatternComponent `A.b) "hasPatternComponent"
  -- The same closure under another name is specialized, so the refusal
  -- is the name's and says so.
  let axiomNamed (n : Name) : Lean2Agda.Declaration := {
    name := n, sourceModule := none, dependencies := #[],
    info := .axiomInfo { name := n, levelParams := [], type := .sort .zero, isUnsafe := false } }
  let alone (n : Name) := specializationOf env .predecessor { roots := #[n], groups := #[#[axiomNamed n]] }
  require ((alone `A.b).toOption.isSome) "a closure of one axiom was not specialized"
  let refusal : String := match alone impostor with
    | .error e => e
    | .ok _ => "none"
  require ((refusal.splitOn "has a component an instance's key is made with").length == 2)
    s!"a closure with a pattern's component in a constant's name: its refusal is {refusal}"
  -- Over every constant of the environment: a name without a pattern has
  -- the identifier it had, and the identifiers of its instances are
  -- distinct from each other and from every constant's.
  let mut seen : Std.HashSet String := {}
  let mut count := 0
  let names := env.constants.fold (init := #[]) fun acc n _ => acc.push n
  for n in names do
    let plain := agdaIdent n
    require (instanceIdent n == plain) s!"{n}: instanceIdent differs from agdaIdent"
    require (!plain.contains '#') s!"{n}: an identifier with #"
    seen := seen.insert plain
    count := count + 1
  require (seen.size == count) "two constants with one identifier"
  for n in names do
    for letters in ["z", "n", "zn"] do
      let ident := instanceIdent (instanceKey n letters)
      require (!seen.contains ident) s!"{n}#{letters}: its identifier is taken"
      seen := seen.insert ident
      count := count + 1
  require (seen.size == count && count == 4 * names.size) "instance identifiers collide"

def checkSidecars (env : Environment) : IO Unit := do
  let roots ← IO.ofExcept (selectRoots env #[`TranslatorTests.Input.Levels] #[])
  let closure ← IO.ofExcept (dependencyClosure env roots)
  let (made, _, _) ← IO.ofExcept (specializeClosure env .predecessor closure)
  let shared ← IO.ofExcept (shareClosure env defaultShareThreshold made)
  let maps ← IO.ofExcept (moduleNameMaps `U shared true)
  let some map := maps.find? (·.source == `TranslatorTests.Input.Levels) | throw (IO.userError "no sidecar")
  let text := map.render
  -- Naming version 2: a key's pattern is a `levels` component after the
  -- constant's own.
  require ((text.splitOn "\"version\":2").length == 2) "the sidecar's version"
  require ((text.splitOn ("{\"agda\":\"LevelFixtures:arrow#zn\",\"lean\":[{\"str\":\"LevelFixtures\"}," ++
    "{\"str\":\"arrow\"},{\"levels\":\"zn\"}]}")).length == 2) "the record of arrow#zn"
  require ((text.splitOn "{\"agda\":\"LevelFixtures:lifted\",\"lean\":[{\"str\":\"LevelFixtures\"},{\"str\":\"lifted\"}]}").length == 2)
    "the record of lifted"
  let parsed ← IO.ofExcept (ModuleNames.parse text)
  require (parsed.render == text && parsed.instances) "the sidecar's round trip"
  require (parsed.reverse.lookup "LevelFixtures:arrow#zn" == some (instanceKey ``LevelFixtures.arrow "zn"))
    "the reverse lookup of an instance"
  -- Version 1 has no `levels` component, and version 2 no string
  -- component of a pattern's form.
  require ((ModuleNames.parse (text.replace "\"version\":2" "\"version\":1")).toOption.isNone)
    "a levels component under version 1"
  require ((ModuleNames.parse (text.replace "{\"levels\":\"zn\"}" "{\"str\":\"#zn\"}")).toOption.isNone)
    "a pattern as a string component under version 2"
  require ((ModuleNames.parse (text.replace "{\"levels\":\"zn\"}" "{\"levels\":\"zx\"}")).toOption.isNone)
    "letters other than z and n"
  let key := instanceKey ``Eq.rec "zn"
  require ((nameFromJson (nameToJson key true) true).toOption == some key) "a key's round trip"
  require ((nameFromJson (nameToJson key true)).toOption.isNone) "a levels component read without instances"
  require ((nameFromJson (nameToJson key)).toOption == some key) "a key written as a plain name"
  -- Without instances the sidecars are version 1, as before.
  let plain ← IO.ofExcept (moduleNameMaps `U closure)
  require (plain.all fun m => (m.render.splitOn "\"version\":1").length == 2 && !m.render.contains '#')
    "the sidecars of a closure without instances"

def treeOf (env : Environment) (specialize prop : Bool) : IO ScaffoldTree := do
  let roots ← IO.ofExcept (selectRoots env #[`TranslatorTests.Input.Levels] #[])
  let closure ← IO.ofExcept (dependencyClosure env roots)
  if specialize then
    let (made, splits, _) ← IO.ofExcept (specializeClosure env .predecessor closure)
    IO.ofExcept (scaffoldTree env `U (← IO.ofExcept (shareClosure env defaultShareThreshold made))
      defaultSplitThreshold .agda (some splits) prop)
  else
    IO.ofExcept (scaffoldTree env `U (← IO.ofExcept (shareClosure env defaultShareThreshold closure))
      defaultSplitThreshold .agda none prop)

def textOf (t : ScaffoldTree) (ident : String) : IO String := do
  let some item := t.items.find? (·.provides.contains ident) | throw (IO.userError s!"no item for {ident}")
  return item.text

def checkEmission (env : Environment) : IO Unit := do
  let t ← treeOf env true false
  let provided := t.items.foldl (· ++ ·.provides) #[]
  -- Each instance is a declaration of its own, and the constant is not one.
  for ident in ["LevelFixtures:twice#z", "LevelFixtures:twice#n", "LevelFixtures:arrow#zn", "Eq#z", "Eq#n",
      "Eq:refl#z", "Eq:refl#n", "LevelFixtures:lifted", "LevelFixtures:Box#z", "LevelFixtures:Box:mk#n",
      "Quot:lift#zn-β", "Quot:lift#nz-β"] do
    require (provided.contains ident) s!"no declaration {ident}"
  for ident in ["LevelFixtures:twice", "Eq", "Eq:refl", "Quot:lift-β", "LevelFixtures:lifted#nn"] do
    require (!provided.contains ident) s!"a declaration {ident}"
  require (provided.size == (provided.foldl (fun (s : Std.HashSet String) x => s.insert x) {}).size)
    "an identifier declared twice"
  -- Each use names its instance.
  require ((← textOf t "LevelFixtures:atType") ==
    "LevelFixtures:atType : U.Init.Prelude.Nat → U.Init.Prelude.Nat\n" ++
    "LevelFixtures:atType n₀ = LevelFixtures:twice#n {U.Init.Prelude.Nat} U.Init.Prelude.Nat:succ n₀\n")
    s!"atType: {← textOf t "LevelFixtures:atType"}"
  let atProp ← textOf t "LevelFixtures:atProp"
  require ((atProp.splitOn "LevelFixtures:twice#z {U.Init.Prelude.True}").length == 2) s!"atProp: {atProp}"
  require ((← textOf t "LevelFixtures:passesSucc") ==
    "LevelFixtures:passesSucc : U.Init.Prelude.PUnit#n → U.Init.Prelude.PUnit#n\nLevelFixtures:passesSucc x₀ = x₀\n")
    "passesSucc"
  -- A block's types and constructors carry the block's pattern, a
  -- recursor's clause matches the constructor's instance, and a record's
  -- field is projected from the record's instance.
  require ((← textOf t "LevelFixtures:Pick#z") ==
    "data LevelFixtures:Pick#z (α₀ : Set) : Set where\n  LevelFixtures:Pick:left#z : α₀ → LevelFixtures:Pick#z α₀\n" ++
    "  LevelFixtures:Pick:right#z : α₀ → LevelFixtures:Pick#z α₀\n") s!"Pick#z: {← textOf t "LevelFixtures:Pick#z"}"
  let pickRec ← textOf t "LevelFixtures:Pick:rec#nz"
  require ((pickRec.splitOn "(LevelFixtures:Pick:left#z a₄) = left₂ a₄").length == 2) s!"Pick.rec#nz: {pickRec}"
  -- A mutual declaration's types are one block per pattern.
  let evenOdd ← IO.ofExcept <| (t.items.find? (·.provides.contains "LevelFixtures:Even#z")).elim
    (.error "no item for Even#z") .ok
  require (evenOdd.provides == #["LevelFixtures:Even#z", "LevelFixtures:Even:zero#z", "LevelFixtures:Even:succ#z",
    "LevelFixtures:Odd#z", "LevelFixtures:Odd:succ#z"] && evenOdd.text.startsWith "mutual\n")
    s!"Even and Odd at z: {evenOdd.provides}"
  -- A nested type's recursors are one `mutual` definition per pattern.
  let treeRec ← IO.ofExcept <| (t.items.find? (·.provides.contains "LevelFixtures:Tree:rec#nn")).elim
    (.error "no item for Tree.rec#nn") .ok
  require (treeRec.provides == #["LevelFixtures:Tree:rec#nn", "LevelFixtures:Tree:rec~u1#nn"] &&
    treeRec.text.startsWith "-- recursor\nmutual\n") s!"Tree's recursors at nn: {treeRec.provides}"
  let unbox ← textOf t "LevelFixtures:unbox#z"
  require ((unbox.splitOn "LevelFixtures:Box:val#z {α₀} b₁").length == 2) s!"unbox#z: {unbox}"
  let val ← textOf t "LevelFixtures:Box:val#z"
  require ((val.splitOn "LevelFixtures:Box#z.val₁ {α₀} self₁").length == 2) s!"Box.val#z: {val}"
  -- A projection from a type that is no record goes through the
  -- recursor's instance at the level of the field's type.
  require ((← textOf t "LevelFixtures:Tagged:get#z") ==
    "LevelFixtures:Tagged:get#z : {α₀ : Set} → LevelFixtures:Tagged#z α₀ → α₀\n" ++
    "LevelFixtures:Tagged:get#z {α₀} t₁ = LevelFixtures:Tagged:rec#zz {α₀} " ++
    "{λ (self₂ : LevelFixtures:Tagged#z α₀) → α₀} (λ (a₂ : α₀) → a₂) t₁\n")
    s!"Tagged.get#z: {← textOf t "LevelFixtures:Tagged:get#z"}"
  let getN ← textOf t "LevelFixtures:Tagged:get#n"
  require ((getN.splitOn "LevelFixtures:Tagged:rec#nn {α₀}").length == 2) s!"Tagged.get#n: {getN}"
  -- Each instance of `Eq` is a rewrite relation, and each instance of
  -- `Quot.lift` has the rule of its own levels, over the instance of `Eq`
  -- at its result's level.
  require (((← textOf t "Eq#n").splitOn "{-# BUILTIN REWRITE Eq#n #-}").length == 2) "Eq#n is not a rewrite relation"
  require (((← textOf t "Eq#z").splitOn "{-# BUILTIN REWRITE Eq#z #-}").length == 2) "Eq#z is not a rewrite relation"
  let ruleZN ← textOf t "Quot:lift#zn-β"
  require (ruleZN.startsWith "-- computation rule\npostulate Quot:lift#zn-β : " &&
    (ruleZN.splitOn "Eq#n {β₂} (Quot:lift#zn {α₀} {r₁} {β₂} f₃ h₄ (Quot:mk#z {α₀} r₁ a₅)) (f₃ a₅)").length == 2 &&
    ruleZN.endsWith "{-# REWRITE Quot:lift#zn-β #-}\n") s!"the rule of Quot.lift#zn: {ruleZN}"
  let ruleNZ ← textOf t "Quot:lift#nz-β"
  require ((ruleNZ.splitOn "Eq#z {β₂} (Quot:lift#nz {α₀} {r₁} {β₂} f₃ h₄ (Quot:mk#n {α₀} r₁ a₅)) (f₃ a₅)").length == 2)
    s!"the rule of Quot.lift#nz: {ruleNZ}"
  require (t.options == profileUOptions) "the options of a specialized tree"
  -- Without the switch nothing changes: no instance, no `#`.
  let plain ← treeOf env false false
  require (plain.items.all fun i => !i.text.contains '#' || (i.text.splitOn "{-#").length > 1) "a # without the switch"
  require ((plain.items.foldl (· ++ ·.provides) #[]).all (!·.contains '#')) "an instance without the switch"
  require ((← textOf plain "LevelFixtures:atType") ==
    "LevelFixtures:atType : U.Init.Prelude.Nat → U.Init.Prelude.Nat\n" ++
    "LevelFixtures:atType n₀ = LevelFixtures:twice {U.Init.Prelude.Nat} U.Init.Prelude.Nat:succ n₀\n") "atType, unspecialized"
  -- The measurement's printing: a sort at level zero is `Prop`, which in
  -- an instance is decided for every sort.
  let prop ← treeOf env true true
  require (prop.options == profileUPropOptions) "the options under --prop"
  require ((← textOf prop "LevelFixtures:arrow#zn") ==
    "LevelFixtures:arrow#zn : Prop → Set → Set\nLevelFixtures:arrow#zn α₀ β₁ = α₀ → β₁\n")
    s!"arrow#zn under --prop: {← textOf prop "LevelFixtures:arrow#zn"}"
  require ((← textOf prop "LevelFixtures:arrow#nz") ==
    "LevelFixtures:arrow#nz : Set → Prop → Prop\nLevelFixtures:arrow#nz α₀ β₁ = α₀ → β₁\n") "arrow#nz under --prop"
  require (((← textOf prop "Eq#z").splitOn "data Eq#z {α₀ : Prop} : α₀ → α₀ → Prop where").length == 2) "Eq#z under --prop"
  require (((← textOf prop "Eq#n").splitOn "data Eq#n {α₀ : Set} : α₀ → α₀ → Prop where").length == 2) "Eq#n under --prop"
  require ((← textOf prop "LevelFixtures:Holder#z") ==
    "record LevelFixtures:Holder#z : Set where\n  constructor LevelFixtures:Holder:mk#z\n  field\n" ++
    "    α₀ : Prop\n    a₁ : α₀\n") s!"Holder#z under --prop: {← textOf prop "LevelFixtures:Holder#z"}"
  require (((← textOf prop "LevelFixtures:Holder#n").splitOn "    α₀ : Set\n").length == 2) "Holder#n under --prop"
  let control ← treeOf env false true
  require (((← textOf control "LevelFixtures:arrow").splitOn "LevelFixtures:arrow : Set → Set → Set").length == 2)
    "the unspecialized arrow under --prop"

def checkTable (env : Environment) : IO Unit := do
  -- The operation table's rewrite rules for `Nat.sub` are equations
  -- between numbers: in a closure of instances they are stated over the
  -- instance of `Eq` at `Nat`'s level, and proved by its constructor's.
  let closure ← IO.ofExcept (dependencyClosure env #[``Nat.succ_sub_succ_eq_sub])
  let (made, splits, _) ← IO.ofExcept (specializeClosure env .predecessor closure)
  let t ← IO.ofExcept (scaffoldTree env `U (← IO.ofExcept (shareClosure env defaultShareThreshold made))
    defaultSplitThreshold .agda (some splits))
  let rule ← textOf t "Nat:sub-builtin-succ"
  require ((rule.splitOn "Eq#n {Nat} (Nat:sub-builtin n₀ (Nat:succ m₁))").length == 2 &&
    (rule.splitOn "Eq:refl#n Nat:zero").length == 3) s!"Nat.sub's rule: {rule}"
  let last ← textOf t "Nat:sub-builtin-pred-succ"
  require ((last.splitOn "{-# REWRITE Nat:sub-builtin-succ Nat:sub-builtin-pred-zero Nat:sub-builtin-pred-succ #-}").length == 2)
    s!"the rules' pragma: {last}"

def checkUnsafe (env : Environment) : IO Unit := do
  -- The kernel types no term of an `unsafe` declaration, so the levels
  -- of what one projects from are not read: its instances use every
  -- pattern, and the scaffold refuses them by their constants' names.
  let roots ← IO.ofExcept (selectRoots env #[`TranslatorTests.Input.Kinds, `TranslatorTests.Input.Inductives] #[])
  let closure ← IO.ofExcept (dependencyClosure env roots)
  let (made, splits, _) ← IO.ofExcept (specializeClosure env .predecessor closure)
  let t ← IO.ofExcept (scaffoldTree env `U (← IO.ofExcept (shareClosure env defaultShareThreshold made))
    defaultSplitThreshold .agda (some splits))
  let lines := t.renderRefusals.splitOn "\n"
  require (lines.contains "axiom\tsorryAx#z\tsorryAx: a proof left to sorry") s!"sorryAx's refusal: {lines.take 12}"
  require (lines.contains "theorem\tKindFixtures.usesSorry\tdepends on sorryAx#z") "a refusal through an instance"
  require (lines.any (·.startsWith "recursor\tInductiveFixtures.Bad.rec#")) "an unsafe type's recursor"

def checkProjection (env : Environment) : IO Unit := do
  -- A projection from `Tagged`, which is no Agda record, goes through
  -- `Tagged.rec` at the motive's level: the level of the field's type,
  -- which the kernel infers and which selects the recursor's instance.
  let (_, splits, _, _) ← specializationFor env .predecessor #[]
  let projection (l : Level) : Expr :=
    .lam `α (.sort l) (.lam `t (.app (.const ``LevelFixtures.Tagged [l]) (.bvar 0))
      (.proj ``LevelFixtures.Tagged 0 (.bvar 0)) .default) .default
  let printed (p : Printer) (l : Level) : IO String := do
    let (t, _) ← IO.ofExcept (p.type (projection l))
    return t.render
  let p : Printer := { env, naming := { constant := instanceIdent, ident := instanceIdent },
                       resolve := splits.resolve, specialized := true }
  let atZero ← printed p .zero
  require ((atZero.splitOn "LevelFixtures:Tagged:rec#zz").length == 2) s!"a projection at zero: {atZero}"
  let atOne ← printed p one
  require ((atOne.splitOn "LevelFixtures:Tagged:rec#nn").length == 2) s!"a projection at a type: {atOne}"
  let plain ← printed { env } one
  require ((plain.splitOn "LevelFixtures:Tagged:rec {").length == 2) s!"a projection, unspecialized: {plain}"
  -- The instance closure demands both motives for such a projection.
  let value : DefinitionVal := {
    name := `projecting, levelParams := [], type := .sort .zero, value := projection one,
    hints := .abbrev, safety := .safe, all := [`projecting] }
  let info : ConstantInfo := .defnInfo value
  let sites ← IO.ofExcept (levelSites env info)
  require (sites.projected == #[(``LevelFixtures.Tagged, [one])]) s!"the projection's site: {sites.projected}"
  let d : Lean2Agda.Declaration := { name := `projecting, info, sourceModule := none, dependencies := #[] }
  let uses ← IO.ofExcept (instanceUses env splits sites d #[])
  for x in [(``LevelFixtures.Tagged, "n"), (``LevelFixtures.Tagged.rec, "zn"), (``LevelFixtures.Tagged.rec, "nn")] do
    require (uses.contains x) s!"the projection's uses lack {x}: {uses}"

/-- Every level an expression holds: its sorts' and its constants'
arguments, each constant's with the constant and the argument's place. -/
def levelsOf (e : Expr) : Array (Option (Name × Nat) × Level) :=
  runST fun s => do
    let out : ST.Ref s (Array (Option (Name × Nat) × Level)) ← ST.mkRef #[]
    e.forEach (ω := s) (m := ST s) fun sub => do
      match sub with
      | .sort l => out.modify (·.push (none, l))
      | .const n us => out.modify fun acc => us.zipIdx.foldl (fun acc (l, i) => acc.push (some (n, i), l)) acc
      | _ => pure ()
    out.get

/-- Every reference to a constant in an expression, with its levels. -/
def referencesOf (e : Expr) : Array (Name × List Level) :=
  runST fun s => do
    let out : ST.Ref s (Array (Name × List Level)) ← ST.mkRef #[]
    e.forEach (ω := s) (m := ST s) fun sub => do
      match sub with
      | .const n us => out.modify (·.push (n, us))
      | _ => pure ()
    out.get

/-- Every instance of the closure of the given modules' declarations:
no `imax`, levels in normal form, predecessors where the rule promises
them, references that select instances that were made, and the kernel's
acceptance.  `run` checks `Init.Core`'s closure; with
`LEVELS_MODULES` set to module names it checks theirs instead, which is
how the whole of `Init` was checked once (`docs/translator/levels.md`). -/
def checkModules (modules : Array Name) : IO Unit := do
  let env ← importEnvironment modules
  let roots ← IO.ofExcept (selectRoots env modules #[])
  let closure ← IO.ofExcept (dependencyClosure env roots)
  let (made, splits, stats) ← IO.ofExcept (specializeClosure env .predecessor closure)
  require (made.size == stats.instances && stats.instances > closure.size) "the closure's instances"
  let keys : Std.HashSet Name := made.declarations.foldl (fun s d => s.insert d.name) {}
  let mut accepted := 0
  for d in made.declarations do
    for e in levelExprs d.info do
      -- No instance holds an `imax`.
      require (!exprHasIMax e) s!"{d.name} holds an imax"
      for (site, l) in levelsOf e do
        -- Every level is in normal form.
        let n ← normal l
        require (n.toLevel == l) s!"{d.name}: the level {l} is not in normal form"
        -- A sort is `Prop` or the type at a level the instance writes,
        -- and a level passed to a split parameter is zero or a successor.
        let decides := match site with
          | none => true
          | some (c, i) => (splits.mask c).getD i false
        if decides then
          require (n.isZero || n.pred?.isSome) s!"{d.name}: the level {l} has no predecessor"
      -- Every reference selects an instance of the closure.
      for (c, us) in referencesOf e do
        match splits.resolve c us with
        | .ok key => require (keys.contains key) s!"{d.name}: its reference to {c} selects {key}, which was not made"
        | .error _ => throw (IO.userError s!"{d.name}: a reference to {c} selects no instance")
    -- Lean's kernel accepts the instance: as a declaration of its own
    -- for an axiom, a definition, a theorem and an opaque constant, and
    -- as a well-typed type for the others, which the kernel declares
    -- only in blocks.
    let name : Name := .str d.name "_instance_check"
    let checked : Except Kernel.Exception Unit := match d.info with
      | .axiomInfo v => (env.addDeclCore 0 0 (.axiomDecl { v with name }) none).map fun _ => ()
      | .defnInfo v =>
        if v.safety == .safe then (env.addDeclCore 0 0 (.defnDecl { v with name, all := [name] }) none).map fun _ => ()
        else pure ()
      | .thmInfo v => (env.addDeclCore 0 0 (.thmDecl { v with name, all := [name] }) none).map fun _ => ()
      | .opaqueInfo v =>
        if v.isUnsafe then pure ()
        else (env.addDeclCore 0 0 (.opaqueDecl { v with name, all := [name] }) none).map fun _ => ()
      | info => (levelExprs info).forM fun e => (Kernel.check env {} e).map fun _ => ()
    match checked with
    | .ok _ => accepted := accepted + 1
    | .error _ => throw (IO.userError s!"Lean's kernel rejects the instance {d.name}")
  require (accepted == made.size) "the instances the kernel accepted"
  IO.println s!"level checks: {made.size} instances of {closure.size} constants, none with an imax, each accepted by Lean's kernel"

def run : IO Unit := do
  checkNormalForm
  let env ← importEnvironment #[`Init, `TranslatorTests.Input.Levels, `TranslatorTests.Input.Kinds,
    `TranslatorTests.Input.Inductives]
  checkSplits env
  checkUses env
  checkInstances env
  checkNames env
  checkSidecars env
  checkEmission env
  checkTable env
  checkUnsafe env
  checkProjection env
  let modules := ((← IO.getEnv "LEVELS_MODULES").getD "Init.Core").splitOn " " |>.filter (!·.isEmpty)
  checkModules (modules.map String.toName).toArray
  IO.println ("level checks: normal forms, splits, uses, instances, names, sidecars, emission, " ++
    "projections, and the modules' instances (no imax, the kernel's acceptance) passed")

end LevelTests
