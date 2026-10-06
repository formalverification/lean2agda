/-
File: translator/scripts/Smoke.lean

A smoke test of the Lake package's environment, run from `translator/` as

    lake env lean scripts/Smoke.lean

or from the repository root as `make lean-smoke`.  It is a standalone
file, not part of any library, so `lake build` never compiles it.

The import loads Mathlib's prebuilt `.olean` files, so the file elaborates
only if `lake exe cache get` has fetched them; the first `#print axioms`
names a Mathlib declaration and proves that.  The second names a
declaration of Lean's core library, which would print without Mathlib, as
a control.
-/
import Mathlib.Data.Finset.Card

#print axioms Finset.card_image_of_injective
#print axioms Nat.gcd_self
