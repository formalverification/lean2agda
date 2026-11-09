/-
File: translator/Main.lean
-/
import Lean2Agda.Main

/-!
# The executable

The root of `lake exe lean2agda`: it parses the arguments, prints the
usage or the version or runs the shell (`Lean2Agda/Main.lean`), and turns
the outcome into an exit status.  It is a module of its own, outside the
library, because the unit tests' executable (`tests/UnitTests.lean`)
imports the shell, and an executable cannot import a second `main`.

The version is the line of `VERSION`, read when this module is compiled.
Lake tracks no file that `include_str` reads, so the executable's `needs`
names the package's input file `version` (`lakefile.toml`), whose hash
enters this module's trace: a change to `VERSION` rebuilds it, and
`--version` follows.
-/

/-- The translator's version, the line of `translator/VERSION`. -/
def Lean2Agda.version : String := (include_str "VERSION").trimAscii.toString

def main (argv : List String) : IO UInt32 := do
  match Lean2Agda.parseArgs argv with
  | .error e =>
    IO.eprintln s!"lean2agda: {e}\n{Lean2Agda.usage}"
    return 2
  | .ok args =>
    if args.help then
      IO.println Lean2Agda.usage
      return 0
    if args.version then
      IO.println s!"lean2agda {Lean2Agda.version}"
      return 0
    try
      Lean2Agda.run args
      return 0
    catch e =>
      IO.eprintln s!"lean2agda: {e}"
      return 1
