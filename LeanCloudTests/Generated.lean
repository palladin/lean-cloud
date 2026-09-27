import LeanCloudTests.Support

namespace LeanCloudTests
open LeanCloud

/-- A finite description used only to generate varied well-typed Cloud programs. -/
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
  def lower (ref : Ref) (tree : Tree) (input : Nat) : Cloud IO Nat :=
    match tree with
    | .value n => pure (input + n)
    | .effect n => execValue ref s!"generated/{n}" (input + n)
    | .blob n => do
      let blob ← CloudBlob.putText s!"{input}:{n}"
      return (← CloudBlob.readText blob).length
    | .fail n => Cloud.fail s!"generated-failure/{n}"
    | .delay child => Cloud.delay fun _ => lower ref child input
    | .bind first next => do
      let value ← lower ref first input
      lower ref next (value + input)
    | .branch even odd =>
      if input % 2 == 0 then lower ref even input else lower ref odd input
    | .parallel children => do
      let values ← Cloud.parallel (lowerChildren ref children input).toArray
      execValue ref "generated/join" (values.foldl (· + ·) input)
  termination_by structural tree

  def lowerChildren (ref : Ref) (children : List Tree) (input : Nat) : List (Cloud IO Nat) :=
    match children with
    | [] => []
    | child :: rest => lower ref child input :: lowerChildren ref rest input
  termination_by structural children
end

def nextSeed (seed : Nat) : Nat := (1664525 * seed + 1013904223) % 4294967296

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

def generatedCases : Array TestCase := (List.range 256).toArray.map fun seed =>
  let tree := (generate (3 + seed % 3) seed).1
  ⟨s!"generated/seed/{seed}", do
    try
      let _ ← differential (fun ref => lower ref tree (seed % 17))
    catch error =>
      throw (IO.userError s!"seed={seed}, program={reprStr tree}\n{error}")⟩

def smallCompositions : Array TestCase := Id.run do
  let leaves := #[Tree.value 0, Tree.effect 2, Tree.blob 3, Tree.fail 4]
  let mut cases := #[]
  for (a, i) in leaves.toList.zipIdx do
    for (b, j) in leaves.toList.zipIdx do
      for (tree, tag) in [(Tree.parallel [a, b], "parallel"), (Tree.bind a b, "bind")] do
        cases := cases.push ⟨s!"generated/exhaustive/{tag}/{i}/{j}", do
          let _ ← differential (fun ref => lower ref tree 1)
          pure ()⟩
  return cases

end LeanCloudTests
