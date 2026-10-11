/-
File: translator/Lean2Agda.lean
-/
import Lean2Agda.Core.Types

/-!
# Lean2Agda

The root module of the translator's pure core.  The command line lives
separately in `Lean2Agda/Main.lean`.

It imports Lean, while the translator reads Mathlib's
elaborated environment when it runs, from the `.olean` files that
`lake exe cache get` downloads, so building this library never needs
Mathlib's modules.  `scripts/Smoke.lean` checks that those files load.
-/

