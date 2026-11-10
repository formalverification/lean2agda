/-
File: translator/tests/Recursors.lean
-/
import Lean2Agda.Main
import TranslatorTests

/-!
The recursors' clauses (issue M2-5): the kernel's rules as clauses, with
the visibilities of each recursor's Lean type; `_` for indices and for a
parameter Agda keeps as an index; a recursive field's call; the absurd
clause of an empty type; a nested type's recursors and a mutual pair's
as one `mutual` block, in `recursorRank`'s order; `String`'s recursor
left a postulate; and `breakCycles` leaving a recursor's recursion alone.
`tests/run.sh` checks the fixture `TranslatorTests.Input.Recursors`'s
scaffold against its golden file and listing, where every recursor's
values compute.
-/

open Lean Lean2Agda

namespace RecursorTests

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def expectText (actual expected label : String) : IO Unit :=
  require (actual == expected) s!"{label}:\nexpected {expected}\nactual   {actual}"

def scaffoldOf (env : Environment) (roots : Array Name) : IO ScaffoldTree := do
  let closure ← IO.ofExcept (dependencyClosure env roots)
  IO.ofExcept (scaffoldTree env `U (← IO.ofExcept (shareClosure env defaultShareThreshold closure)))

def itemOf (s : ScaffoldTree) (n : Name) : IO ScaffoldItem := do
  let some item := s.items.find? (·.provides.contains (agdaIdent n))
    | throw (IO.userError s!"no item for {n}")
  return item

/-- The lines of a recursor item's text after its comment. -/
def clauseLines (item : ScaffoldItem) : List String :=
  (item.text.splitOn "\n").drop 1 |>.filter (· != "")

def checkPatterns : IO Unit := do
  let p : Pattern := .ctor "C" #[(.implicit, .wild), (.explicit, .var "x₁"), (.instance, .var "i₂")]
  expectText (p.renderArg .explicit) "(C {_} x₁ ⦃ i₂ ⦄)" "a constructor pattern"
  expectText ((Pattern.ctor "Z" #[]).renderArg .explicit) "Z" "a constructor pattern without arguments"
  expectText (Pattern.wild.renderArg .implicit) "{_}" "an implicit wildcard"
  expectText ({ patterns := #[(.explicit, .var "m₀"), (.explicit, .absurd)], body := none : PatternClause }.render "f")
    "f m₀ ()" "an absurd clause"

def checkCoreRecursors (env : Environment) : IO Unit := do
  let s ← scaffoldOf env #[``Nat.rec, ``Eq.rec, ``HEq.rec, ``Acc.rec, ``False.rec, ``Prod.rec, ``String]
  -- A recursive field's call is structural.
  expectText (← itemOf s ``Nat.rec).text ("-- recursor\n" ++
    "Nat:rec : {motive₀ : Nat → Set} → motive₀ Nat:zero → ((n₁ : Nat) → motive₀ n₁ → motive₀ (Nat:succ n₁)) → (t₁ : Nat) → motive₀ t₁\n" ++
    "Nat:rec {motive₀} zero₁ succ₂ Nat:zero = zero₁\n" ++
    "Nat:rec {motive₀} zero₁ succ₂ (Nat:succ n₃) = succ₂ n₃ (Nat:rec {motive₀} zero₁ succ₂ n₃)\n") "Nat.rec"
  -- `a` is Lean's parameter, Agda's index: a variable pattern for the
  -- parameter, `_` for the constructor's argument and for the index.
  expectText ((clauseLines (← itemOf s ``Eq.rec)).getD 1 "")
    "Eq:rec {α₀} {a₁} {motive₂} refl₃ {_} (Eq:refl _) = refl₃" "Eq.rec"
  expectText ((clauseLines (← itemOf s ``HEq.rec)).getD 1 "")
    "HEq:rec {α₀} {a₁} {motive₂} refl₃ {_} {_} (HEq:refl _) = refl₃" "HEq.rec"
  -- A recursive field of function type: the call is under a lambda.
  expectText ((clauseLines (← itemOf s ``Acc.rec)).getD 1 "")
    ("Acc:rec {α₀} {r₁} {motive₂} intro₃ {_} (Acc:intro x₅ h₆) = intro₃ x₅ h₆ " ++
     "(λ (y₇ : α₀) → λ (a₈ : r₁ y₇ x₅) → Acc:rec {α₀} {r₁} {motive₂} intro₃ {y₇} (h₆ y₇ a₈))") "Acc.rec"
  -- A type without constructors, and a record.
  expectText ((clauseLines (← itemOf s ``False.rec)).getD 1 "") "False:rec motive₀ ()" "False.rec"
  expectText ((clauseLines (← itemOf s ``Prod.rec)).getD 1 "")
    "Prod:rec {α₀} {β₁} {motive₂} mk₃ (Prod:mk fst₄ snd₅) = mk₃ fst₄ snd₅" "Prod.rec"
  -- `String` is a postulate, and its recursor stays one.
  require ((← itemOf s ``String.rec).text.startsWith "postulate String:rec : ") "String.rec"
  -- Every recursor item is structural, so `breakCycles` left it alone.
  for n in [``Nat.rec, ``Acc.rec] do
    let item ← itemOf s n
    require (item.structural && item.text.startsWith "-- recursor\n") s!"{n} is not a recursor item"

def checkBlocks (env : Environment) : IO Unit := do
  -- A nested type's three recursors are one mutual block, `rec` first.
  let s ← scaffoldOf env #[``Lean.Syntax.rec]
  let syntaxBlock ← itemOf s ``Lean.Syntax.rec_2
  require (syntaxBlock.provides == #["Lean:Syntax:rec", "Lean:Syntax:rec~u1", "Lean:Syntax:rec~u2"])
    s!"Lean.Syntax's block: {syntaxBlock.provides}"
  let lines := clauseLines syntaxBlock
  require (lines.head? == some "mutual" && (lines.getD 1 "").startsWith "  Lean:Syntax:rec : ")
    s!"Lean.Syntax's block: {lines.take 2}"
  require (lines.any (·.startsWith "  Lean:Syntax:rec~u1 {motive1₀} {motive2₁} {motive3₂} missing₃ node₄ atom₅ ident₆ mk₇ nil₈ cons₉ (Array:mk toList₁₀) = "))
    "Lean.Syntax.rec_1 matches Array.mk"
  require (syntaxBlock.references.contains "Array:mk" && syntaxBlock.references.contains "List:cons")
    "the block refers to the constructors it matches"
  -- A mutual pair, each type's recursor in the order of `all`.
  let f ← scaffoldOf env #[``RecursorFixtures.Even.rec]
  require ((← itemOf f ``RecursorFixtures.Odd.rec).provides ==
    #["RecursorFixtures:Even:rec", "RecursorFixtures:Odd:rec"]) "the mutual pair's block"
  -- The order of a block: `rec` by `all`, then `rec_N` by `N`.
  let all := [`A, `B]
  let names := #[`A.rec_10, `B.rec, `A.rec_2, `A.rec]
  let ranked := names.qsort fun a b => recursorRank all a < recursorRank all b
  require (ranked == #[`A.rec, `B.rec, `A.rec_2, `A.rec_10]) s!"recursorRank: {ranked}"

def checkCycles : IO Unit := do
  -- A structural item refers to itself and stays; an ordinary one is
  -- postulated.
  let item (n : String) (structural : Bool) : ScaffoldItem :=
    { provides := #[n], references := #[n], text := n, fallback := some (#[], "postulate " ++ n),
      structural }
  let result := breakCycles #[item "r" true, item "d" false]
  require (result.map (·.text) == #["r", "-- cyclic definition, postulated\npostulate d"])
    s!"breakCycles: {result.map (·.text)}"

def run : IO Unit := do
  let env ← importEnvironment #[`Init, `TranslatorTests.Input.Recursors]
  checkPatterns
  checkCoreRecursors env
  checkBlocks env
  checkCycles
  IO.println "recursor checks: patterns, clauses, promoted parameters, absurd clauses, blocks, and cycles passed"

end RecursorTests
