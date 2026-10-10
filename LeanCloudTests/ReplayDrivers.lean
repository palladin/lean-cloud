import LeanCloudTests.Generated
import LeanCloud.ReplayModel
import LeanCloud.ParallelReplay

namespace LeanCloudTests
open Lean LeanCloud LeanCloud.ReplayModel

/-- Keep the existing generator's control-flow variety within the pure fragment. -/
private def pureTree : Tree → Tree
  | .blob n => .effect n
  | .delay child => .delay (pureTree child)
  | .bind first next => .bind (pureTree first) (pureTree next)
  | .branch even odd => .branch (pureTree even) (pureTree odd)
  | .parallel children => .parallel (children.map pureTree)
  | tree => tree

private def replayDifferential [Codec α] [BEq α] [Repr α]
    (program : ι → Cloud M α) (input : ι) : IO Journal := do
  let (expected, directJournal) := (DirectInterpreter.interpret noBlobs program input).run []
  assertTrue directJournal.isEmpty "Direct evaluation touched replay storage"
  let (sequential, journal) := (SequentialReplay.interpret store noBlobs 10000 program input).run []
  let (parallel, parallelJournal) := (ParallelReplay.interpret 10000 program input).run []
  assertOutcome sequential expected
  assertOutcome parallel expected
  for (key, record) in journal do
    assertEq (parallelJournal.lookup key) (some record) s!"Parallel replay lost or changed {key}"
  assertEq parallelJournal.length journal.length "Parallel replay duplicated or invented records"
  for (run, records) in [
      (fun fuel => SequentialReplay.interpret store noBlobs fuel program input, journal),
      (fun fuel => ParallelReplay.interpret fuel program input, parallelJournal)] do
    let some record := records.lookup (ReplayStore.returnKey Location.root)
      | throw (IO.userError "Replay returned without a root record")
    assertOutcome (ReplayInterpreter.result (m := Id) record.outcome).run expected
    let (warm, unchanged) := (run 1).run records
    assertOutcome warm expected
    assertEq unchanged records "Completed replay changed its journal"
  return journal

private def nestedReplay (input : Nat) : Cloud M (Nat × String) := cloud {
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

def replayDriverCases : Array TestCase := #[
  ⟨"replay-drivers/nested-captured-delays-empty-and-later-groups", do
    let journal ← replayDifferential nestedReplay 7
    let some record := journal.lookup (ReplayStore.returnKey Location.root)
      | throw (IO.userError "Missing result")
    assertEq record.outcome (.success (Codec.encode ((55 : Nat), "input=7")))⟩,
  ⟨"replay-drivers/source-ordered-errors-and-all-child-results", do
    let program (_ : Unit) : Cloud M (Array Nat) :=
      Cloud.parallel #[Cloud.delay fun _ => Cloud.fail "first", Cloud.fail "second", cloud { return 42 }]
    let journal ← replayDifferential program ()
    let some record := journal.lookup (ReplayStore.returnKey Location.root)
      | throw (IO.userError "Missing failure")
    assertEq record.outcome (.failure ⟨.application, "first"⟩)
    for index in [:3] do
      assertTrue (journal.lookup (ReplayStore.returnKey (Location.root.child index))).isSome
        "An error skipped an unfinished sibling"⟩,
  ⟨"replay-drivers/insufficient-fuel-is-not-completion", do
    for run in [SequentialReplay.interpret store noBlobs 1 nestedReplay 7,
        ParallelReplay.interpret 1 nestedReplay 7] do
      let (result, journal) := run.run []
      assertError result .protocol
      assertTrue (journal.lookup (ReplayStore.returnKey Location.root)).isNone "Exhausted run published a root result"⟩,
  ⟨"replay-drivers/parallel-partial-journal-resumes", do
    let slow : Cloud M Nat := (List.range 20).foldl (fun child _ => Cloud.delay fun _ => child) (pure 2)
    for (children, completedIndex, expected) in [
        (#[pure 1, slow], 0, #[1, 2]), (#[slow, pure 1], 1, #[2, 1])] do
      let program (_ : Unit) := Cloud.parallel children
      let (stopped, partialJournal) := (ParallelReplay.interpret 3 program ()).run []
      assertError stopped .protocol
      assertTrue (partialJournal.lookup (ReplayStore.returnKey (Location.root.child completedIndex))).isSome
        "Completed sibling records were lost on fuel exhaustion"
      assertTrue (partialJournal.lookup (ReplayStore.returnKey Location.root)).isNone
        "Incomplete parent was marked complete"
      let (finished, journal) := (ParallelReplay.interpret 100 program ()).run partialJournal
      assertOutcome finished (.ok expected)
      for (key, record) in partialJournal do
        assertEq (journal.lookup key) (some record) "Resumption changed a recorded value"⟩,
  ⟨"replay-drivers/workers-share-reads-and-return-only-new-records", do
    let seed : ReplayRecord := ⟨ReplayStore.returnRequest, .success (toJson (7 : Nat))⟩
    let snapshot : Journal := [("ancestor", seed)]
    let resume (assignment : Assignment) : ExceptT CloudError M Unit := do
      let before ← get
      let _ ← store.create (ReplayStore.returnKey assignment.branchStart)
        ⟨ReplayStore.returnRequest, .success (toJson before.length)⟩
      pure ()
    let assignments := (List.range 8).map fun index => Assignment.mk 0 (Location.root.child index)
    for assignment in assignments do
      let (outcome, additions) := ParallelReplay.worker resume snapshot assignment
      assertOutcome outcome (.ok ())
      assertEq additions.length 1 "Worker returned old records as new writes"
      assertTrue (additions.lookup "ancestor").isNone "Shared ancestor escaped into worker writes"
    let (finished, journal) := (ParallelReplay.children resume assignments).run snapshot
    assertOutcome finished (.ok ())
    assertEq journal.length 9 "Union lost or duplicated records"
    for assignment in assignments do
      let some record := journal.lookup (ReplayStore.returnKey assignment.branchStart)
        | throw (IO.userError "Missing child record")
      assertEq record.outcome (.success (toJson (1 : Nat))) "A child saw a sibling's updated state"⟩,
  ⟨"replay-drivers/merge-order-and-conflicts", do
    let record (n : Nat) : ReplayRecord := ⟨ReplayStore.returnRequest, .success (toJson n)⟩
    let base : Journal := [("ancestor", record 7)]
    let children : List (Except CloudError Unit × Journal) :=
      [(Except.ok (), [("left", record 1)]), (.ok (), [("right", record 2)])]
    let (forward, first) := (ParallelReplay.mergeChildren children).run base
    let (backward, last) := (ParallelReplay.mergeChildren children.reverse).run base
    assertOutcome forward (.ok ())
    assertOutcome backward (.ok ())
    assertEq first.length 3 "Union lost or duplicated records"
    assertEq last.length first.length
    for (key, value) in first do assertEq (last.lookup key) (some value)
    for value in [record 7, record 8] do
      assertError (ReplayModel.merge base [("ancestor", value)]) .divergence
    assertError (ReplayModel.merge [] [("duplicate", record 1), ("duplicate", record 1)]) .divergence
    let (collision, unchanged) := (ParallelReplay.mergeChildren [
      (.ok (), [("shared", record 1)]), (.ok (), [("shared", record 1)])]).run base
    assertError collision .divergence
    assertEq unchanged base "Invalid ownership partially changed the journal"⟩
] ++ (Array.range 256).map fun seed =>
  ⟨s!"replay-drivers/generated/{seed}", do
    let tree := pureTree (generate (3 + seed % 3) seed).1
    try
      let _ ← replayDifferential (lower tree (m := M)) (seed % 17)
    catch error =>
      throw (IO.userError s!"seed={seed}, program={reprStr tree}\n{error}")⟩

end LeanCloudTests
