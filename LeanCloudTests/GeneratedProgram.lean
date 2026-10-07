import LeanCloud.Core

namespace LeanCloudTests
open LeanCloud

def nextSeed (seed : Nat) : Nat := (1664525 * seed + 1013904223) % 4294967296

/-- A finite AST for property-based generation; production programs are ordinary
Cloud computations with closures, never this test representation. -/
inductive Tree where
  | value (n : Nat)
  | effect (n : Nat)
  | blob (n : Nat)
  | fail (n : Nat)
  | delay (child : Tree)
  | bind (first next : Tree)
  | branch (even odd : Tree)
  | parallel (children : List Tree)
  deriving Repr

mutual
  def lower [Pure m] (tree : Tree) (input : Nat) : Cloud m Nat :=
    match tree with
    | .value n => pure (input + n)
    | .effect n => Cloud.pure (fun _ => input + n) s!"generated/{n}"
    | .blob n => do
      let blob ← CloudBlob.putText s!"{input}:{n}"
      return (← CloudBlob.readText blob).length
    | .fail n => Cloud.fail s!"generated-failure/{n}"
    | .delay child => Cloud.delay fun _ => lower child input
    | .bind first next => do
      let value ← lower first input
      lower next (value + input)
    | .branch even odd => if input % 2 == 0 then lower even input else lower odd input
    | .parallel children => do
      let values ← Cloud.parallel (lowerChildren children input).toArray
      -- An order-sensitive result exposes reordered children; summing hid them.
      Cloud.pure (fun _ => values.foldl (fun acc value => acc * 31 + value + 1) input) "generated/join"
  termination_by structural tree

  def lowerChildren [Pure m] (children : List Tree) (input : Nat) : List (Cloud m Nat) :=
    match children with
    | [] => []
    | child :: rest => lower child input :: lowerChildren rest input
  termination_by structural children
end

def generate (depth seed : Nat) : Tree × Nat :=
  let seed := nextSeed seed
  let n := seed / 256 % 23
  match depth with
  | 0 =>
    let tree := match seed / 16 % 5 with
      | 0 => Tree.value n
      | 1 | 2 => Tree.effect n
      | 3 => Tree.blob n
      | _ => Tree.fail n
    (tree, seed)
  | depth + 1 =>
    match seed / 16 % 7 with
    | 0 => (.value n, seed)
    | 1 => (.effect n, seed)
    | 2 =>
      let (child, seed) := generate depth seed
      (.delay child, seed)
    | 3 | 4 =>
      let tag := seed / 16 % 7
      let (first, seed) := generate depth seed
      let (next, seed) := generate depth seed
      (if tag == 3 then .bind first next else .branch first next, seed)
    | _ => Id.run do
      let mut children := []
      let mut seed := seed
      for _ in [:seed / 256 % 4] do
        let (child, next) := generate depth seed
        children := child :: children
        seed := next
      return (.parallel children.reverse, seed)

end LeanCloudTests
