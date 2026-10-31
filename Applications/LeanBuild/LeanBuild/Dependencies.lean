import LeanBuild.Model

namespace LeanBuild.Dependencies

abbrev Index := Std.HashMap String Module

def index (modules : Array Module) : Index :=
  modules.foldl (fun entries m => entries.insert m.name m) {}

/-- Visit only the requested ancestry. Prepared modules include their complete
ancestry, so traversal stops at them. Return missing inputs in dependency order.
The explicit stack also handles long chains without recursive calls. -/
def missing (modules : Index) (prepared : Std.HashSet String)
    (imports : Array String) : Except String (Array Module) := do
  let mut pending : List (String ⊕ Module) := imports.toList.map Sum.inl
  let mut seen : Std.HashSet String := {}
  let mut result := #[]
  while let entry :: rest := pending do
    pending := rest
    match entry with
    | .inr m => result := result.push m
    | .inl name =>
      if prepared.contains name || seen.contains name then continue
      let some m := modules[name]? | throw s!"Unknown prerequisite: {name}"
      seen := seen.insert name
      pending := m.imports.toList.map Sum.inl ++ .inr m :: pending
  return result

end LeanBuild.Dependencies
