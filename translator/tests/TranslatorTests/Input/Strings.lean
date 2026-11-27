/-
File: translator/tests/TranslatorTests/Input/Strings.lean
-/

/-!
String literals as Lean's kernel expands them (issue M3-11), for the
golden tree `strings` of `tests/run.sh`, which checks this module under
the default `--arithmetic agda` only: under `--arithmetic lean`,
`ByteArray.IsValidUTF8` and `Char.ofNat`'s proofs exhaust Agda's heap
(`docs/foundations/nat-operations.md`, "`String` and `Char`").  A literal
is a kernel term of its own, which the kernel expands to `String.ofList`
over `Char.ofNat` applications where a comparison or a projection needs
it; the translator gives each distinct literal one definition, that
expansion.  The two round trips are issue M3-11's acceptance criterion:
the first holds because both sides print as one term, the second because
`String.mk`, deprecated, has `String.ofList`'s body, once the checker
unfolds the two proofs of validity the elaborator abstracts from them
(LF-17 in `docs/lean-findings.md`).  The definitions cover an escape, the
empty string, a character of each UTF-8 length (`a`, `λ`, `✝` and `𝔸`,
one to four bytes), one literal in two declarations, which the scaffold
defines once, and a repeated closed subterm holding literals, which the
sharing pass shares after the literals' definitions are in the kernel's
environment.
-/

namespace StringFixtures

theorem ofList_ab : "ab" = String.ofList ['a', 'b'] := rfl

set_option linter.deprecated false in
theorem mk_a : "a" = String.mk ['a'] := rfl

/-- A projection from a literal, which the kernel expands to reduce. -/
theorem toByteArray_ab : "ab".toByteArray = List.utf8Encode ['a', 'b'] := rfl

def widths : String := "aλ✝𝔸"

def escaped : String := "a\"b\\c\n"

def empty : String := ""

def first : String := "shared"

def second : List String := ["shared", "ab"]

/-- A closed subterm holding literals, repeated, which the sharing pass
makes an auxiliary definition that names the literals' definitions. -/
def repeated : List (List String) := [["a", "b", "c", "d", "e", "f"], ["a", "b", "c", "d", "e", "f"]]

end StringFixtures
