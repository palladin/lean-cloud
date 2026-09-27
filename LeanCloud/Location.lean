import Init

namespace LeanCloud

/-- Each level records `(child index, command index)`. For example,
`#[(0, 2), (1, 5)]` means root's fork at command 2, child 1, command 5.
Delay is transparent; sequential effects and completed groups advance the command. -/
abbrev Location := Array (Nat × Nat)

namespace Location

def root : Location := #[(0, 0)]

def key (location : Location) : String :=
  String.intercalate "/" (location.toList.map fun (branch, command) => s!"{branch}:{command}")

def next (location : Location) : Location :=
  let (branch, command) := location[location.size - 1]!
  location.set! (location.size - 1) (branch, command + 1)

def child (location : Location) (index : Nat) : Location := location.push (index, 0)

def parent? (location : Location) : Option (Location × Nat) :=
  if location.size ≤ 1 then none
  else some (location.extract 0 (location.size - 1), location[location.size - 1]!.1)

/-- An earlier position that must be reconstructed using accepted results. -/
def before (current target : Location) : Bool :=
  current.size < target.size || current[current.size - 1]!.2 < target[current.size - 1]!.2

def entersChild (current target : Location) : Bool :=
  current.size < target.size && current == target.extract 0 current.size

end Location
end LeanCloud
