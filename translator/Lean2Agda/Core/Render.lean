/-
File: translator/Lean2Agda/Core/Render.lean
-/
import Lean2Agda.Core.Types

namespace Lean2Agda

/-- The diagnostic closure listing, before the Agda printer is added.
Each tab-separated row gives the kind, source module, and original name. -/
def renderClosure (profile : String) (closure : Closure) : String := Id.run do
  let mut lines := #[s!"# profile {profile}"]
  for i in [:closure.groups.size] do
    lines := lines.push s!"# group {i}"
    for decl in closure.groups[i]! do
      let source := decl.sourceModule.map toString |>.getD "<local>"
      lines := lines.push s!"{decl.kind.label}\t{source}\t{decl.name}"
  return "\n".intercalate lines.toList ++ "\n"

end Lean2Agda
