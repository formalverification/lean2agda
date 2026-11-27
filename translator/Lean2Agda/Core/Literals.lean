/-
File: translator/Lean2Agda/Core/Literals.lean
-/
import Lean.Expr

/-!
# String literals as Lean's kernel expands them

A string literal is a kernel term of its own, `Expr.lit (.strVal s)`, of
type `String`, which Lean's kernel expands on demand: where a recursor or a
projection meets one, or a comparison meets one against an application of
`String.ofList` (`string_lit_to_constructor` in `src/kernel/inductive.cpp`
at the pinned Lean), it decodes the literal's UTF-8 into code points
`k₁ … kₙ` and builds

    String.ofList (List.cons.{0} Char (Char.ofNat k₁) (… (List.nil.{0} Char)))

with each `kᵢ` a natural number literal.  Agda has no such term, so the
translator emits the expansion itself: the closure counts what it names
(`Closure.lean`), the printer prints a literal as it (`Print.lean`), and
the sharing pass gives each distinct literal of a closure one definition
whose value it is (`Share.lean`).  A character literal needs nothing of
its own: Lean's elaborator already writes `'a'` as `Char.ofNat 97`.
`docs/translator/printing.md` gives the rules.
-/

namespace Lean2Agda

open Lean

/-- The constants a string literal names once it is expanded, `Nat`, the
type of its code points, and `String`, its own type. -/
def stringLiteralConstants : Array Name :=
  #[``String, ``String.ofList, ``List.cons, ``List.nil, ``Char, ``Char.ofNat, ``Nat]

/-- The kernel's expansion of the string literal `s`: `String.ofList`
applied to the list of `s`'s code points, each as `Char.ofNat` of a
natural number literal, `List.cons` and `List.nil` at universe level zero
over `Char`.  `String.toList` gives the code points that the kernel's
UTF-8 decoding gives, one `Char` per scalar value whatever its encoded
length. -/
def stringLiteralExpansion (s : String) : Expr :=
  let char := Expr.const ``Char []
  let cons := mkApp (.const ``List.cons [.zero]) char
  let nil := mkApp (.const ``List.nil [.zero]) char
  mkApp (.const ``String.ofList []) <| s.toList.foldr (init := nil) fun c rest =>
    mkApp2 cons (mkApp (.const ``Char.ofNat []) (.lit (.natVal c.toNat))) rest

end Lean2Agda
