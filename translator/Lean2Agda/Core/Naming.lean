/-
File: translator/Lean2Agda/Core/Naming.lean
-/
import Lean.Data.Name

namespace Lean2Agda

open Lean

/-- The caller chooses profile and layer roots; naming assigns no layers. -/
abbrev Root := Name
abbrev ModuleName := Name

/-- Agda 2.8.0 keywords, directive words, and unindexed universe names.
The lexer also reserves the deprecated `codata`. -/
def agdaReserved : List String :=
  ["abstract", "as", "codata", "coinductive", "constructor", "data", "do",
   "eta-equality", "field", "forall", "hiding", "import", "in", "inductive",
   "infix", "infixl", "infixr", "instance", "interleaved", "let", "macro",
   "module", "mutual", "no-eta-equality", "opaque", "open", "overlap",
   "pattern", "postulate", "primitive", "private", "public", "quote",
   "quoteTerm", "record", "renaming", "rewrite", "syntax", "tactic", "to",
   "unfolding", "unquote", "unquoteDecl", "unquoteDef", "using", "variable",
   "where", "with", "Set", "Prop"]

def isAsciiLetter (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

/-- Scalar escapes have terminators; the escape marker itself is escaped. -/
def agdaStringComponent (s : String) : String :=
  if s.isEmpty then "~e" else
  let encoded := s.foldl (fun acc c =>
    acc ++ if isAsciiLetter c || c.isDigit then String.singleton c
           else if c == '_' then "~u"
           else "~x" ++ String.ofList (Nat.toDigits 16 c.toNat) ++ "~") ""
  if s.front.isDigit || agdaReserved.contains s then "~s" ++ encoded else encoded

/-- Walk constructors directly, retaining numeric components and macro scopes. -/
def agdaComponents : Name → List String
  | .anonymous => []
  | .str p s => agdaComponents p ++ [agdaStringComponent s]
  | .num p n => agdaComponents p ++ ["~n" ++ toString n]

/-- One prefix identifier, with namespaces flattened into colon-separated parts. -/
def agdaIdent (n : Name) : String :=
  if n == .anonymous then "~a" else ":".intercalate (agdaComponents n)

/-! ## Instances

An instance of a constant (`Specialize.lean`, issue M3-3) is the constant
with each of its split level parameters fixed as zero or as nonzero.  The
closure holds it under a key, the constant's name followed by one more
component, `#` and a letter per split parameter (`z` for zero, `n` for
nonzero), and its identifier is the constant's followed by that
component as it is: `Eq#z`, `Eq:rec#zn`.  No `agdaIdent` holds a `#`,
which it escapes, so an instance's identifier is no Lean name's, and two
instances have the same one only when they are the same.  A constant
without split parameters has one instance, the empty pattern, whose key
and identifier are the constant's own. -/

/-- Whether a name component is a pattern's: `#` and one or more of `z`
and `n`. -/
def isPatternComponent (s : String) : Bool :=
  match s.toList with
  | '#' :: letters => !letters.isEmpty && letters.all fun c => c == 'z' || c == 'n'
  | _ => false

/-- Whether a name has a pattern's component.  The specialization refuses
a closure holding a Lean constant with one, so that a key is never a
constant's name. -/
def hasPatternComponent : Name → Bool
  | .anonymous => false
  | .str p s => isPatternComponent s || hasPatternComponent p
  | .num p _ => hasPatternComponent p

/-- The key of the instance of `n` with the given pattern letters. -/
def instanceKey (n : Name) (letters : String) : Name :=
  if letters.isEmpty then n else .str n ("#" ++ letters)

/-- `agdaComponents` for a key: a pattern's component joins the component
before it, unescaped.  An auxiliary definition of an instance, whose name
continues the instance's key, keeps the pattern where the key has it. -/
def instanceComponents : Name → List String
  | .anonymous => []
  | .str p s =>
    if isPatternComponent s then
      match (instanceComponents p).reverse with
      | last :: before => before.reverse ++ [last ++ s]
      | [] => [s]
    else instanceComponents p ++ [agdaStringComponent s]
  | .num p n => instanceComponents p ++ ["~n" ++ toString n]

/-- The identifier of a key; `agdaIdent` on a name without a pattern's
component. -/
def instanceIdent (n : Name) : String :=
  if n == .anonymous then "~a" else ":".intercalate (instanceComponents n)

/-- A key as a reader sees it in a message or in `refusals.txt`: the
constant's name as Lean prints it, with the pattern's component joined to
it, `sorryAx#z`; `toString` on a name without one. -/
def keyDisplay (n : Name) : String :=
  if !hasPatternComponent n then toString n
  else match n with
    | .str p s =>
      if isPatternComponent s then keyDisplay p ++ s else keyDisplay p ++ "." ++ toString (Name.mkSimple s)
    | .num p k => keyDisplay p ++ "." ++ toString k
    | .anonymous => ""

/-- Path segments, safe both as Agda module names and as filenames. -/
def agdaModule (root : Root) (moduleName : ModuleName) : List String :=
  agdaComponents root ++
    if moduleName == .anonymous then ["~a"] else agdaComponents moduleName

/-- Whether any component needed a code or prefix beyond namespace flattening. -/
def needsNameEscape : Name → Bool
  | .anonymous => true
  | .str p s => agdaStringComponent s != s || needsPrefixEscape p
  | .num _ _ => true
where
  needsPrefixEscape : Name → Bool
    | .anonymous => false
    | .str p s => agdaStringComponent s != s || needsPrefixEscape p
    | .num _ _ => true

end Lean2Agda
