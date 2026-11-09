/-
File: translator/tests/Scaffold.lean
-/
import Lean2Agda.Main
import TranslatorTests

/-!
The scaffold's rules, on the fixture `TranslatorTests.Input.Kinds`: how
each kind of declaration is emitted, what is refused and why, that the
sharing pass leaves `unsafe` declarations alone, that cyclic definitions
are postulated, and that a `String` root keeps its builtin; and on the
fixture `TranslatorTests.Input.Quotients`, the quotient's computation
rules: Lean's own statements, printed with the visibilities of
`Quot.lift` and `Quot.mk`, after what they mention, and only in a
closure that holds `Quot`.  `tests/run.sh` checks the same fixtures'
scaffolds against their golden files and refusal listings, where the
fallback fires and where the rules are left out.
-/

open Lean Lean2Agda

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def scaffoldOf (env : Environment) (roots : Array Name) (threshold : Nat := defaultShareThreshold) :
    IO Scaffold := do
  let closure ← IO.ofExcept (dependencyClosure env roots)
  IO.ofExcept (scaffold env `U (← IO.ofExcept (shareClosure env threshold closure)))

def itemOf (s : Scaffold) (n : Name) : IO ScaffoldItem := do
  let some item := s.items.find? (·.provides.contains (agdaIdent n))
    | throw (IO.userError s!"no item for {n}")
  return item

def checkKinds (env : Environment) : IO Unit := do
  let roots ← IO.ofExcept <| selectRoots env #[`TranslatorTests.Input.Kinds] #[]
  let s ← scaffoldOf env roots
  -- A definition is transparent, an instance among them, with no
  -- `instance` keyword: the printer passes every instance argument itself.
  let plain ← itemOf s ``KindFixtures.plain
  require (plain.text.startsWith "KindFixtures:plain : Nat → Nat\nKindFixtures:plain n₀ = ")
    s!"a definition: {plain.text}"
  let inst ← itemOf s ``KindFixtures.instMarkerNat
  require (inst.text.startsWith "KindFixtures:instMarkerNat : KindFixtures:Marker Nat\nKindFixtures:instMarkerNat = ")
    s!"an instance: {inst.text}"
  -- A theorem sits in an opaque block of its own, under its label.
  let base ← itemOf s ``KindFixtures.base
  require (base.text == "-- theorem\nopaque\n  KindFixtures:base : Eq {Nat} Nat:zero Nat:zero\n  KindFixtures:base = rfl {Nat} {Nat:zero}\n")
    s!"a theorem: {base.text}"
  -- Lean's opaque constants, a `partial` definition among them, sit in
  -- opaque blocks with their values; the `_unsafe_rec` companion, which
  -- refers to itself, is postulated.
  let hidden ← itemOf s ``KindFixtures.hidden
  require (hidden.text.startsWith "-- opaque constant\nopaque\n  KindFixtures:hidden : Nat\n  KindFixtures:hidden = ")
    s!"an opaque constant: {hidden.text}"
  let loop ← itemOf s ``KindFixtures.loop
  require (loop.text.startsWith "-- opaque constant\nopaque\n  KindFixtures:loop : Nat → Nat\n  KindFixtures:loop n₀ = ")
    s!"a partial definition: {loop.text}"
  let companion ← itemOf s ``KindFixtures.loop._unsafe_rec
  require (companion.text == "-- cyclic definition, postulated\npostulate KindFixtures:loop:~uunsafe~urec : Nat → Nat\n")
    s!"a partial definition's companion: {companion.text}"
  -- An axiom and a recursor are postulates; the class is a record, which
  -- declares its constructor (`Inductive.lean`).
  for n in [``KindFixtures.Q, ``KindFixtures.Marker.rec] do
    require ((← itemOf s n).text.startsWith "postulate ") s!"{n} is not a postulate"
  for n in [``KindFixtures.Marker, ``KindFixtures.Marker.mk] do
    require ((← itemOf s n).text.startsWith "record KindFixtures:Marker ") s!"{n} is not the record"
  -- Refusals: sorryAx, what depends on it, and the unsafe definitions,
  -- each with its reason; none of them has an item.
  let reasons := s.refused.map fun r => (r.name, r.reason)
  let expected : Array (Name × String) := #[
    (``KindFixtures.danger, "unsafe: exempt from Lean's kernel"),
    (``KindFixtures.onDanger, "unsafe: exempt from Lean's kernel"),
    (``sorryAx, "sorryAx: a proof left to sorry"),
    (``KindFixtures.usesSorry, "depends on sorryAx"),
    (``KindFixtures.onSorry, "depends on KindFixtures.usesSorry, and through it on sorryAx"),
    (``KindFixtures.wide, "unsafe: exempt from Lean's kernel")]
  require (reasons == expected) s!"refusals: {reasons}"
  for (n, _) in expected do
    require (s.items.all fun i => !i.provides.contains (agdaIdent n)) s!"refused {n} has an item"
  require (s.renderRefusals.startsWith "definition\tKindFixtures.danger\tunsafe: exempt from Lean's kernel\n")
    s!"refusals.txt: {s.renderRefusals}"
  require ((s.render "c").startsWith s!"{profileUOptions}\n-- c\n-- refused 6 declarations; refusals.txt names each with its reason\nmodule ")
    "the module's header does not count the refusals"
  -- A closure with nothing to refuse writes no refusal and no such comment.
  let clean ← scaffoldOf env #[``KindFixtures.plain]
  require (clean.refused.isEmpty && clean.renderRefusals.isEmpty
    && ((clean.render "c").splitOn "refused").length == 1) "a clean closure reports refusals"
  -- The sharing pass leaves an unsafe declaration alone: at threshold 2,
  -- `wide`'s repeated `Nat.succ danger` would otherwise become an auxiliary
  -- definition that the kernel refuses as safe.
  let closure ← IO.ofExcept (dependencyClosure env #[``KindFixtures.wide, ``KindFixtures.useMark])
  let shared ← IO.ofExcept (shareClosure env 2 closure)
  require (shared.declarations.all fun d => !(toString d.name).startsWith "KindFixtures.wide._share")
    "an unsafe declaration was shared"
  let _ ← IO.ofExcept (scaffold env `U shared)

def checkCyclesAndBuiltins (env : Environment) : IO Unit := do
  -- Mutually recursive partial companions fall back to postulates, and a
  -- String root keeps its builtin.
  let s ← scaffoldOf env #[``PrintFixtures.evenP._unsafe_rec, ``PrintFixtures.oddP._unsafe_rec, ``String]
  for n in [``PrintFixtures.evenP._unsafe_rec, ``PrintFixtures.oddP._unsafe_rec] do
    require ((← itemOf s n).text.startsWith "-- cyclic definition, postulated\npostulate ")
      s!"cyclic {n} was not postulated"
  let string ← itemOf s ``String
  require ((string.text.splitOn "BUILTIN STRING").length == 2) "a String root lost its builtin"

/-- A closed type with its level parameters set to `1`, so that the
kernel can check it outside a declaration. -/
def atLevelOne (e : Expr) : Expr :=
  e.instantiateLevelParams [`u, `v] [Level.one, Level.one]

def checkQuotientRules (env : Environment) : IO Unit := do
  -- Each rule's type is well typed and is, up to definitional equality,
  -- the theorem `Init.Core` states and proves by `rfl`.
  for (rule, statement) in [(quotLiftRuleType, ``Quot.liftBeta), (quotIndRuleType, ``Quot.indBeta)] do
    let some info := env.find? statement | throw (IO.userError s!"no {statement}")
    require (info.levelParams.all ([`u, `v].contains ·)) s!"{statement}'s levels are {info.levelParams}"
    require (Kernel.check env {} (atLevelOne rule) matches .ok (.sort _)) s!"the rule for {statement} is ill-typed"
    require (Kernel.isDefEq env {} (atLevelOne rule) (atLevelOne info.type) matches .ok true)
      s!"the rule is not {statement}"
  -- Each rule follows its primitive, `Quot.mk` and `Eq`, which declares the
  -- rewrite relation, and states its left-hand side as the printer prints
  -- the primitive applied to `Quot.mk`.
  let roots ← IO.ofExcept <| selectRoots env #[`TranslatorTests.Input.Quotients] #[]
  let s ← scaffoldOf env roots
  let position (n : String) : IO Nat := do
    let some i := s.items.findIdx? (·.provides.contains n) | throw (IO.userError s!"no item for {n}")
    return i
  let some liftRule := s.items.find? (·.provides == #["Quot:lift-β"]) | throw (IO.userError "no rule for Quot.lift")
  require (liftRule.text == "-- computation rule\npostulate Quot:lift-β : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → " ++
      "{β₂ : Set} → (f₃ : α₀ → β₂) → (h₄ : (a₄ : α₀) → (b₅ : α₀) → r₁ a₄ b₅ → Eq {β₂} (f₃ a₄) (f₃ b₅)) → " ++
      "(a₅ : α₀) → Eq {β₂} (Quot:lift {α₀} {r₁} {β₂} f₃ h₄ (Quot:mk {α₀} r₁ a₅)) (f₃ a₅)\n" ++
      "{-# REWRITE Quot:lift-β #-}\n") s!"the rule for Quot.lift: {liftRule.text}"
  require ((← itemOf s ``Quot.lift).text.startsWith "postulate Quot:lift : ") "Quot.lift is not a postulate"
  let some indRule := s.items.find? (·.provides == #["Quot:ind-β"]) | throw (IO.userError "no rule for Quot.ind")
  require (indRule.text == "-- computation rule\npostulate Quot:ind-β : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → " ++
      "{β₂ : Quot {α₀} r₁ → Set} → (mk₃ : (a₃ : α₀) → β₂ (Quot:mk {α₀} r₁ a₃)) → (a₄ : α₀) → " ++
      "Eq {β₂ (Quot:mk {α₀} r₁ a₄)} (Quot:ind {α₀} {r₁} {β₂} mk₃ (Quot:mk {α₀} r₁ a₄)) (mk₃ a₄)\n" ++
      "{-# REWRITE Quot:ind-β #-}\n") s!"the rule for Quot.ind: {indRule.text}"
  for (rule, before) in [("Quot:lift-β", ["Quot:lift", "Quot:mk", "Eq"]), ("Quot:ind-β", ["Quot:ind", "Quot:mk", "Eq"])] do
    for n in before do
      require ((← position n) < (← position rule)) s!"{rule} comes before {n}"
  require (((← itemOf s ``Eq).text.splitOn "{-# BUILTIN REWRITE Eq #-}").length == 2) "Eq is not the rewrite relation"
  -- A closure without `Quot` has no rule.
  let plain ← scaffoldOf env #[``KindFixtures.plain]
  require (plain.items.all fun i => (i.text.splitOn "REWRITE Quot").length == 1) "a rule without Quot"

#eval show IO Unit from do
  let env ← importEnvironment #[`Init, `TranslatorTests.Input.Kinds, `TranslatorTests.Input.Printing,
    `TranslatorTests.Input.Quotients]
  checkKinds env
  checkCyclesAndBuiltins env
  checkQuotientRules env
  IO.println "scaffold checks: kinds, refusals, unsafe sharing, cycles, builtins, and quotient rules passed"
