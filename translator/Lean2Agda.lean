/-
File: translator/Lean2Agda.lean
-/
import Lean2Agda.Core.Types
import Lean2Agda.Core.Closure
import Lean2Agda.Core.CommandLine
import Lean2Agda.Core.Render
import Lean2Agda.Core.Stats
import Lean2Agda.Core.Naming
import Lean2Agda.Core.ReverseMap
import Lean2Agda.Core.Print

/-!
# Lean2Agda

The root module of the translator's pure core.  The command line lives
separately in `Lean2Agda/Main.lean`.

It imports Lean, while the translator reads Mathlib's
elaborated environment when it runs, from the `.olean` files that
`lake exe cache get` downloads, so building this library never needs
Mathlib's modules.  `scripts/Smoke.lean` checks that those files load.
-/

