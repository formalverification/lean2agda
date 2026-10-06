/-
File: translator/Lean2Agda.lean
-/

/-!
# Lean2Agda

The root module of the translator's library.  It is empty until issue
M2-1 adds the pure translation core under `Lean2Agda/Core/` and the
command line in `Lean2Agda/Main.lean`.

It imports nothing, Mathlib included.  The translator reads Mathlib's
elaborated environment when it runs, from the `.olean` files that
`lake exe cache get` downloads, so building this library never needs
Mathlib's modules.  `scripts/Smoke.lean` checks that those files load.
-/
