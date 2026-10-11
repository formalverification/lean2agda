/-
File: translator/tests/TranslatorTests/Input/Consumer.lean
-/
import TranslatorTests.Input.Base

namespace Fixtures

private def secret : Nat := token + 1
def selected : Nat := secret
opaque concealed : Nat := token
def literal : String := "fixture"
def projection (b : Box) : Marker := b.element
def mixed (n : Nat) (e : Envelope) : Nat :=
  match n, e with
  | 0, _ => 0
  | n + 1, .wrap _ => n

initialize marker : IO.Ref Nat ← IO.mkRef 23

end Fixtures
