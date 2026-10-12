/-
File: translator/tests/Printing.lean
-/
import Lean2Agda.Main
import TranslatorTests

open Lean Lean2Agda

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def expectText (actual expected : String) (what : String) : IO Unit :=
  require (actual == expected) s!"{what}: expected\n  {expected}\ngot\n  {actual}"

/-- The precedence table, one case per position: an application's head,
an explicit argument, an implicit or instance argument, an arrow's
domain, and the right of an arrow, against each kind of term. -/
def precedenceCases : List (AgdaTerm × String) :=
  let f := AgdaTerm.const "f"
  let g := AgdaTerm.const "g"
  let a := AgdaTerm.var "a₀"
  let A := AgdaTerm.const "A"
  let B := AgdaTerm.const "B"
  let lam := AgdaTerm.lam .explicit "x₀" A (.var "x₀")
  let arrow := AgdaTerm.pi .explicit none A B
  let letE := AgdaTerm.letE "y₀" A a (.var "y₀")
  [(.app (.app f .explicit a) .explicit a, "f a₀ a₀"),
   (.app f .explicit (.app g .explicit a), "f (g a₀)"),
   (.app f .implicit (.app g .explicit a), "f {g a₀}"),
   (.app f .instance (.app g .explicit a), "f ⦃ g a₀ ⦄"),
   (.app f .implicit lam, "f {λ (x₀ : A) → x₀}"),
   (.app f .implicit (.pi .implicit (some "x₀") A B), "f { {x₀ : A} → B }"),
   (.app f .implicit (.pi .implicit none A B), "f { {_ : A} → B }"),
   (.app f .implicit (.app g .implicit A), "f {g {A}}"),
   (.app f .explicit lam, "f (λ (x₀ : A) → x₀)"),
   (.app lam .explicit a, "(λ (x₀ : A) → x₀) a₀"),
   (.app f .explicit arrow, "f (A → B)"),
   (.app f .explicit letE, "f (let y₀ : A; y₀ = a₀ in y₀)"),
   (.app f .explicit .sort, "f Set"),
   (.app f .explicit (.nat 42), "f 42"),
   (.app f .explicit (.str "s"), "f \"s\""),
   (.pi .explicit none arrow B, "(A → B) → B"),
   (.pi .explicit none A arrow, "A → A → B"),
   (.pi .explicit none (.app f .explicit a) B, "f a₀ → B"),
   (.pi .explicit none letE B, "(let y₀ : A; y₀ = a₀ in y₀) → B"),
   (.pi .explicit (some "x₀") A (.app f .explicit (.var "x₀")), "(x₀ : A) → f x₀"),
   (.pi .implicit (some "x₀") arrow B, "{x₀ : A → B} → B"),
   (.pi .instance (some "x₀") A B, "⦃ x₀ : A ⦄ → B"),
   (.pi .implicit none A B, "{_ : A} → B"),
   (.pi .instance none A B, "⦃ _ : A ⦄ → B"),
   (.pi .explicit none A lam, "A → λ (x₀ : A) → x₀"),
   (.lam .implicit "x₀" arrow (.lam .instance "i₁" A a), "λ {x₀ : A → B} → λ ⦃ i₁ : A ⦄ → a₀"),
   (.letE "y₀" arrow lam (.app (.var "y₀") .explicit a),
     "let y₀ : A → B; y₀ = λ (x₀ : A) → x₀ in y₀ a₀"),
   (.app (.app (.app f .implicit A) .instance a) .explicit (.app (.app g .explicit a) .implicit A),
     "f {A} ⦃ a₀ ⦄ (g a₀ {A})")]

def checkLayout : IO Unit := do
  for (t, expected) in precedenceCases do expectText t.render expected "layout"
  expectText (agdaStringLiteral "a\"b\\c\nd") "\"a\\\"b\\\\c\\10\\&d\"" "string escapes"
  expectText (agdaStringLiteral "λ9✝") "\"\\955\\&9\\10013\\&\"" "non-ASCII escapes"
  expectText ((Clause.ofTerm (.lam .implicit "α₀" .sort (.lam .instance "i₁" .sort
    (.lam .explicit "a₂" .sort (.var "a₂"))))).render "c") "c {α₀} ⦃ i₁ ⦄ a₂ = a₂" "clause patterns"

/-- Binder names: the base keeps ASCII letters, digits and Greek letters
of the name with its macro scopes erased, and every name ends in the
subscript decimal of its depth. -/
def checkBinderNames : IO Unit := do
  let hygienic := addMacroScope `Init.Data.List.Basic `x 13
  let cases : List (Name × String) := [(hygienic, "x"), (Name.mkSimple "inst✝", "inst"),
      (`_x, "x"), (`Set, "x"), (`Prop, "x"), (`SSet, "x"), (Name.mkSimple "Setω", "x"), (Name.mkSimple "Propω", "x"),
      (Name.mkSimple "1a", "x"), (`α, "α"), (Name.mkSimple "λ", "x"),
      (Name.anonymous, "x"), (`h₁, "h"), (`a.b, "b"), (Name.mkNum `a 2, "x"), (`motive, "motive"),
      (Name.mkSimple "x''", "x")]
  for (n, base) in cases do
    expectText (binderBase n) base s!"binder base of {n}"
  expectText (binderName `n 1209) "n₁₂₀₉" "subscript depth"
  -- Every binder name differs from every constant identifier: those are ASCII.
  require ((binderName `Nat 0).any (fun (c : Char) => c.toNat > 127)) "binder names are not ASCII"

/-- An Agda file binding every Agda keyword and sort name as a binder
base, with Greek and digits, checked by the shell's Agda in run.sh. -/
def lexicalFile : String :=
  let words := agdaReserved ++ ["α", "Ω", "x1", "SSet", "Setω", "Propω", "SSetω", "Set1", "Prop1", "λ"]
  let binders := (List.range words.length).zip words |>.map fun (i, w) =>
    binderName (.mkSimple w) i
  let telescope := " ".intercalate (binders.map (s!"({·} : Set)"))
  "{-# OPTIONS --type-in-type #-}\nmodule PrintingLexical where\n\n" ++
  s!"names : {telescope} → Set\n" ++
  s!"names {" ".intercalate binders} = {binders.getLast!}\n"

def withEnv (modules : Array Name) : IO Environment := importEnvironment modules

def printType (env : Environment) (e : Expr) : Except String String :=
  ({ env } : Printer).type e |>.map (·.1.render)

def checkConstructors (env : Environment) : IO Unit := do
  let p : Printer := { env }
  let ok (e : Expr) (expected : String) (what : String) : IO Unit := do
    expectText (← IO.ofExcept (printType env e)) expected what
  let fails (e : Expr) (what : String) : IO Unit :=
    require (printType env e).toOption.isNone s!"printed {what}"
  ok (.sort .zero) "Set" "Prop under U"
  ok (.sort (.imax (.param `u) .zero)) "Set" "imax under U"
  ok (mkConst ``Nat) "Nat" "constant"
  ok (mkConst ``Nat.gcd_self) "Nat:gcd~uself" "escaped constant"
  ok (.lit (.natVal 18446744073709551616)) "18446744073709551616" "natural literal"
  ok (.lit (.strVal "x\"")) "\"x\\\"\"" "string literal"
  ok (.mdata {} (mkConst ``Nat)) "Nat" "mdata dropped"
  ok (mkApp2 (.const ``id [.succ .zero]) (mkConst ``Nat) (.lit (.natVal 3))) "id {Nat} 3"
    "implicit argument"
  ok (.forallE `n (mkConst ``Nat) (.forallE `m (mkConst ``Nat) (mkApp3 (.const ``Eq [.succ .zero])
      (mkConst ``Nat) (.bvar 1) (.bvar 0)) .implicit) .default)
    "(n₀ : Nat) → {m₁ : Nat} → Eq {Nat} n₀ m₁" "dependent Pi types"
  ok (.forallE `inst (mkApp (.const ``Inhabited [.succ .zero]) (mkConst ``Nat)) (mkConst ``Nat) .instImplicit)
    "⦃ _ : Inhabited Nat ⦄ → Nat" "non-dependent instance binder"
  ok (.lam `x (mkConst ``Nat) (.bvar 0) .default) "λ (x₀ : Nat) → x₀" "lambda"
  ok (.letE `y (mkConst ``Nat) (.lit (.natVal 1)) (.bvar 0) false) "let y₀ : Nat; y₀ = 1 in y₀" "let"
  -- An instance argument is passed explicitly, in instance braces.
  ok (mkApp2 (.const ``Inhabited.default [.succ .zero]) (mkConst ``Nat) (mkConst ``instInhabitedNat))
    "Inhabited:default {Nat} ⦃ instInhabitedNat ⦄" "instance argument"
  -- A projection prints through the structure's recursor.
  ok (.lam `p (mkApp2 (.const ``Prod [.zero, .zero]) (mkConst ``Nat) (mkConst ``Nat))
      (.proj ``Prod 0 (.bvar 0)) .default)
    ("λ (p₀ : Prod Nat Nat) → Prod:rec {Nat} {Nat} {λ (self₁ : Prod Nat Nat) → Nat} " ++
     "(λ (fst₁ : Nat) → λ (snd₂ : Nat) → fst₁) p₀") "projection"
  -- A telescope: the first binders, and the rest in their scope.
  let some cons := env.find? ``List.cons | throw (IO.userError "missing List.cons")
  let ((binders, rest), _) ← IO.ofExcept (p.telescope cons.type 1)
  expectText (renderTelescope binders ++ " : " ++ rest.render) "{α₀ : Set} : α₀ → List α₀ → List α₀"
    "telescope"
  require ((p.telescope (mkConst ``Nat) 1).toOption.isNone) "a telescope longer than its type"
  fails (.bvar 0) "a loose bound variable"
  fails (.fvar ⟨`x⟩) "a free variable"
  fails (.mvar ⟨`m⟩) "a metavariable"
  fails (.proj ``Nat 0 (.lit (.natVal 1))) "a projection from a type with two constructors"
  -- Repairs: the top-level and the deeper case of the fixture.
  for (n, top, deep) in [(``PrintFixtures.alignedTop, 1, 0), (``PrintFixtures.alignedDeep, 0, 1)] do
    let some info := env.find? n | throw (IO.userError s!"missing {n}")
    let (_, counts) ← IO.ofExcept (p.clause info.type info.value!)
    require (counts.topRepairs == top && counts.deepRepairs == deep) s!"repairs of {n}: {repr counts}"
  let some info := env.find? ``PrintFixtures.alignedTop | throw (IO.userError "missing")
  let (clause, _) ← IO.ofExcept (p.clause info.type info.value!)
  expectText (clause.render "c") "c {α₀} a₁ = a₁" "top-level repair"

def checkNaming : IO Unit := do
  let owner : Name → Option ModuleName := fun n =>
    if n == ``Nat.gcd_self then some `Init.Data.Nat.Gcd else none
  let naming := Naming.qualified `U owner
  expectText (naming.constant ``Nat.gcd_self) "U.Init.Data.Nat.Gcd.Nat:gcd~uself" "qualified reference"
  expectText (naming.constant ``Nat.gcd) "Nat:gcd" "a constant of the current module"

/-- `Nat.add` doubled `n` times, built with sharing. -/
def doubled : Nat → Expr
  | 0 => mkConst ``Nat.zero
  | n + 1 => let e := doubled n; mkApp2 (mkConst ``Nat.add) e e

def checkSharing (env : Environment) : IO Unit := do
  -- The pass's size accounting on a term of 2 ^ 20 leaves: 42 distinct
  -- subterms (`Nat.zero`, `Nat.add`, and two per doubling), a tree of
  -- 2 ^ 22 - 3 nodes, and 19 shared doublings of 5 nodes each plus a root
  -- of 5 once shared.
  let (roots, g) := ShareGraph.build #[doubled 20]
  require (g.nodes.size == 42) s!"distinct subterms: {g.nodes.size}"
  let tree := g.printedSize roots (.replicate g.nodes.size false)
  require (tree == 2 ^ 22 - 3) s!"unshared size {tree}"
  let chosen := g.choose roots 2
  require ((chosen.filter id).size == 19) s!"shared subterms: {(chosen.filter id).size}"
  require (g.printedSize roots chosen == 100) s!"shared size {g.printedSize roots chosen}"
  -- Below the threshold nothing is shared.
  require ((g.choose roots (2 ^ 23)).all (!·)) "a subterm below the threshold was shared"
  -- The pass on a declaration: auxiliaries checked by the kernel, owned
  -- by the declaration's module, and printed in linear size.
  let value : DefinitionVal := {
    name := `Synthetic.doubling, levelParams := [], type := mkConst ``Nat, value := doubled 20,
    hints := ReducibilityHints.opaque, safety := DefinitionSafety.safe, all := [`Synthetic.doubling] }
  let decl : Lean2Agda.Declaration := {
    name := `Synthetic.doubling, sourceModule := some `Synthetic, dependencies := #[``Nat.add],
    info := .defnInfo value }
  let result ← IO.ofExcept (shareDeclaration env 2 decl)
  require (result.auxiliaries.size == 19) s!"auxiliaries: {result.auxiliaries.size}"
  require (result.auxiliaries.all fun a => a.auxiliary && a.sourceModule == some `Synthetic)
    "auxiliary ownership"
  let closure : Closure := { roots := #[decl.name], groups := #[#[result.declaration], result.auxiliaries] }
  let env' ← IO.ofExcept (addAuxiliaries env closure)
  let p : Printer := { env := env' }
  let text := result.auxiliaries.foldl (fun out a =>
    out ++ ((p.clause a.info.type a.info.value!).toOption.map (·.1.render "a") |>.getD "")) ""
  require (text.length < 2000) s!"printed shared size {text.length}"
  let _ ← IO.ofExcept (moduleNameMaps `U closure)
  -- The fixture's doubling at the default threshold.
  let some fixture := env.find? ``PrintFixtures.doubling | throw (IO.userError "missing fixture")
  let fixtureDecl : Lean2Agda.Declaration := {
    name := ``PrintFixtures.doubling, info := fixture, sourceModule := some `TranslatorTests.Input.Printing,
    dependencies := #[] }
  let fixtureShared ← IO.ofExcept (shareDeclaration env defaultShareThreshold fixtureDecl)
  require (fixtureShared.auxiliaries.size == 6) s!"fixture auxiliaries: {fixtureShared.auxiliaries.size}"
  -- Lambdas stay in place.
  let lam := Expr.lam `x (mkConst ``Nat) (.bvar 0) .default
  let (lroots, lg) := ShareGraph.build #[mkApp2 (mkConst ``Nat.add) lam lam]
  let lchosen := lg.choose lroots 1
  require ((List.range lg.nodes.size).all fun i => !lchosen[i]! || !lg.nodes[i]!.expr.isLambda)
    "a lambda was shared"

def checkScaffoldRules (env : Environment) : IO Unit := do
  for (n, expected) in [(``outParam, true), (``optParam, true), (``DecidableEq, true),
      (``DecidablePred, true), (``Nat.add, false), (``id, false), (``Nat.le, false)] do
    let some info := env.find? n | throw (IO.userError s!"missing {n}")
    require (isTypeAbbreviation info == expected) s!"type abbreviation {n}"
  -- Mutually recursive unsafe roots fall back to postulates, and a String
  -- root keeps its builtin.
  let roots := #[``PrintFixtures.evenP._unsafe_rec, ``PrintFixtures.oddP._unsafe_rec, ``String]
  let closure ← IO.ofExcept (dependencyClosure env roots)
  let s ← IO.ofExcept (scaffold env `U (← IO.ofExcept (shareClosure env defaultShareThreshold closure)))
  for n in [``PrintFixtures.evenP._unsafe_rec, ``PrintFixtures.oddP._unsafe_rec] do
    let some item := s.items.find? (·.provides.contains (agdaIdent n))
      | throw (IO.userError s!"missing item {n}")
    require (item.text.startsWith "postulate ") s!"cyclic {n} was not postulated"
  let some string := s.items.find? (·.provides.contains (agdaIdent ``String))
    | throw (IO.userError "missing item String")
  require ((string.text.splitOn "BUILTIN STRING").length == 2) "a String root lost its builtin"

#eval show IO Unit from do
  checkLayout
  checkBinderNames
  checkNaming
  let env ← withEnv #[`Init, `TranslatorTests.Input.Printing]
  checkConstructors env
  checkSharing env
  checkScaffoldRules env
  if let some dir ← IO.getEnv "PRINTING_AGDA_TEST_DIR" then
    IO.FS.writeFile (System.FilePath.mk dir / "PrintingLexical.agda") lexicalFile
  IO.println s!"printer checks: {precedenceCases.length} layout cases, binder names, constructors, telescopes, repairs, sharing, and scaffold rules passed"
