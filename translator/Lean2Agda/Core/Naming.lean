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
