import LeanCloudTests.Generated

namespace LeanCloudTests
open Lean LeanCloud LeanCloud.Proofs.ReplayModel

/-- Keep the existing generator's control-flow variety within the pure fragment. -/
private def pureTree : Tree → Tree
  | .blob n => .effect n
  | .delay child => .delay (pureTree child)
  | .bind first next => .bind (pureTree first) (pureTree next)
  | .branch even odd => .branch (pureTree even) (pureTree odd)
  | .parallel children => .parallel (children.map pureTree)
  | tree => tree

private def sequentialDifferential [Codec α] [BEq α] [Repr α]
    (program : ι → Cloud M α) (input : ι) : IO Journal := do
  let (expected, directJournal) := (DirectInterpreter.interpret noBlobs program input).run []
  assertTrue directJournal.isEmpty "Direct evaluation touched replay storage"
  let (actual, journal) := (SequentialReplay.interpret store noBlobs 10000 program input).run []
  assertOutcome actual expected
  let some record := journal.lookup (ReplayStore.returnKey Location.root)
    | throw (IO.userError "Sequential replay returned without a durable root record")
  assertOutcome (ReplayInterpreter.result (m := Id) record.outcome).run expected
  let (warm, unchanged) := (SequentialReplay.interpret store noBlobs 1 program input).run journal
  assertOutcome warm expected
  assertEq unchanged journal "Completed replay changed its journal"
  return journal

private def nestedSequential (input : Nat) : Cloud M (Nat × String) := cloud {
  let captured ← Cloud.pure (fun _ => input * 2)
  Cloud.delay fun _ => cloud {
    let (total, label) ← cloud {
      let values ← Cloud.parallel #[
        Cloud.delay fun _ => cloud { return captured + 1 },
        cloud {
          let empty ← Cloud.parallel (#[] : Array (Cloud M Nat))
          let nested ← Cloud.parallel #[cloud { return captured + 2 }, cloud { return captured + 3 }]
          return nested.foldl (· + ·) empty.size
        }]
      return values.foldl (· + ·) 0
    } || cloud { return s!"input={input}" }
    let final ← Cloud.parallel #[cloud { return total }, cloud { return input }]
    return (final.foldl (· + ·) 0, label)
  }
}

def sequentialReplayCases : Array TestCase := #[
  ⟨"sequential/nested-captured-delays-empty-and-later-groups", do
    let journal ← sequentialDifferential nestedSequential 7
    let some record := journal.lookup (ReplayStore.returnKey Location.root)
      | throw (IO.userError "Missing result")
    assertEq record.outcome (.success (Codec.encode ((55 : Nat), "input=7")))⟩,
  ⟨"sequential/source-ordered-errors-and-all-child-results", do
    let program (_ : Unit) : Cloud M (Array Nat) :=
      Cloud.parallel #[Cloud.delay fun _ => Cloud.fail "first", Cloud.fail "second", cloud { return 42 }]
    let journal ← sequentialDifferential program ()
    let some record := journal.lookup (ReplayStore.returnKey Location.root)
      | throw (IO.userError "Missing failure")
    assertEq record.outcome (.failure ⟨.application, "first"⟩)
    for index in [:3] do
      assertTrue (journal.lookup (ReplayStore.returnKey (Location.root.child index))).isSome
        "An error skipped an unfinished sibling"⟩,
  ⟨"sequential/insufficient-fuel-is-not-completion", do
    let (result, journal) := (SequentialReplay.interpret store noBlobs 1 nestedSequential 7).run []
    assertError result .protocol
    assertTrue (journal.lookup (ReplayStore.returnKey Location.root)).isNone "Exhausted run published a root result"⟩
] ++ (Array.range 256).map fun seed =>
  ⟨s!"sequential/generated/{seed}", do
    let tree := pureTree (generate (3 + seed % 3) seed).1
    try
      let _ ← sequentialDifferential (lower tree (m := M)) (seed % 17)
    catch error =>
      throw (IO.userError s!"seed={seed}, program={reprStr tree}\n{error}")⟩

end LeanCloudTests
