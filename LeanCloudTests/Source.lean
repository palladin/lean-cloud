import LeanCloudTests.Support
import LeanCloud.ReplayModel
import LeanCloudCli.Watch

namespace LeanCloudTests.Source
open Lean LeanEff LeanCloud LeanCloud.ReplayModel

private def repeated [Monad m] : Cloud m Nat := cloud {
  let first ← Cloud.pure (fun _ => 10) "same"
  let second ← Cloud.pure (fun _ => 20) "same"
  return first + second
}

private def branching [Monad m] : Cloud m (Array Nat) := cloud {
  Cloud.parallel #[cloud { return 11 }, cloud { return 22 }]
}

private def loopAndReturn [Monad m] (stop : Nat) : Cloud m Nat := cloud {
  let mut total := 0
  for i in [:5] do
    let value ← Cloud.pure (fun _ => i)
    if i == stop then return total
    total := total + value
  return total
}

-- IO syntax inside a thunk must not be rewritten into Cloud operations.
private def nestedIO : Cloud IO Nat := cloud {
  Cloud.exec fun _ => do
    let ref ← IO.mkRef 7
    return ← ref.get
}

private def files : Cloud Id String := cloud {
  CloudBlob.readTextByName "log.txt"
}

private def sources : Array ProgramSource := cloud_sources%

private def site (id : Option SourceSiteId) : Option SourceSite := do
  let id ← id
  sources.findSome? fun source => source.sites.find? (·.id == id)

private def textAt (id : Option SourceSiteId) : String :=
  ((site id) >>= fun site =>
    (sources.findSome? fun source => if source.sites.any (·.id == site.id) then
      (source.text.splitOn "\n").toArray[site.line - 1]? else none)).getD ""

private def skipDelay (program : Cloud m α) : Cloud m α :=
  match program with
  | .impure _ .delay next => next.apply ()
  | program => program

private def nextExec (program : Cloud Id α) : Cloud Id α :=
  match program with
  | .impure _ (.command _ (.exec _ body)) next => next.apply (body ())
  | program => program

private def has (text fragment : String) : Bool := (text.splitOn fragment).length > 1

private def ioBlobs : BlobStorage IO where
  putBlob _ := throw ⟨.unsupported, "blob"⟩
  readBlob _ := throw ⟨.unsupported, "blob"⟩
  resolveBlob _ := throw ⟨.unsupported, "blob"⟩

private def observeReplay : IO Unit := do
  let saved ← IO.mkRef ([] : Journal)
  let observations ← IO.mkRef (#[] : Array (Location × Option SourceSiteId))
  let records : ReplayStore IO := {
    read := fun key => return (← saved.get).lookup key
    create := fun key proposed => saved.modifyGet fun records =>
      match records.lookup key with
      | some existing => (existing, records)
      | none => (proposed, (key, proposed) :: records) }
  let visit : ReplayInterpreter.Observer IO := fun location source =>
    observations.modify (·.push (location, source))
  let assignment : Assignment := ⟨0, Location.root⟩
  let run := (ReplayInterpreter.step records ioBlobs 20 (fun _ : Unit => repeated) () assignment (some visit)).run
  assertOutcome (← run) (.ok .done)
  let first ← observations.get
  assertTrue (first.any fun (_, id) => has (textAt id) "let first ←") "Execution site missing"
  assertTrue (first.any fun (_, id) => has (textAt id) "let second ←") "Continuation site missing"
  -- Preserve command records but replay before the branch return was saved.
  saved.modify (·.filter (·.1 != ReplayStore.returnKey Location.root))
  observations.set #[]
  assertOutcome (← run) (.ok .done)
  assertEq (← observations.get) first "Replay visits different source sites"

def cases : Array TestCase := #[
  ⟨"source.observer-replay", observeReplay⟩,
  ⟨"source.console-multiple-files-and-unknown-sites", do
    let a : ProgramSource := ⟨"A.lean", "first\nread a", #[⟨"a", 2, 0, 2, 6⟩]⟩
    let b : ProgramSource := ⟨"B.lean", "read b\nlast", #[⟨"b", 1, 0, 1, 6⟩]⟩
    let run : LeanCloudCli.Run := ⟨"run", "image", ⟨"app/v1", "unit", "nat", "", none, #[a, b]⟩, Json.null, 2⟩
    let first : LeanCloudCli.Trace.Step := {
      timestamp := "1", event := ⟨"boot", 0, 0, "worker1", some 0, "0:0", "execute", "readBlob", "run", some "a"⟩ }
    let second := { first with timestamp := "2", event := { first.event with worker := "worker2", source := some "b" } }
    assertEq (LeanCloudCli.Watch.sourcePosition run first |>.map (·.1.file)) (some "A.lean")
    assertEq (LeanCloudCli.Watch.sourcePosition run second |>.map (·.2.line)) (some 1)
    assertTrue (LeanCloudCli.Watch.sourcePosition run { first with event := { first.event with source := none } }).isNone
      "An operation label was used as a source position"
    assertTrue (LeanCloudCli.Watch.sourcePosition run { first with event := { first.event with source := some "unknown" } }).isNone
      "Unknown source site was guessed"
    let view := LeanCloudCli.Watch.frame ⟨"/work", "test"⟩ run #[first, second] #[] {} 160 40 "completed"
    assertTrue (view.any (has · "B.lean:1") && !view.any (has · "A.lean:2")) "Last view did not follow the latest source file"⟩,
  ⟨"source.repeated-operations-and-return", do
    let first := skipDelay (repeated (m := Id))
    let second := nextExec first
    let final := nextExec second
    assertTrue (has (textAt first.metadata) "let first ←") "First call has no precise source site"
    assertTrue (has (textAt second.metadata) "let second ←") "Repeated operation reused first site"
    assertTrue (first.metadata != second.metadata) "Repeated calls share a site"
    assertTrue (has (textAt final.metadata) "return first + second") "Final pure node lost return site"
    assertTrue ((site first.metadata).any fun s => s.column > 0 && s.endColumn > s.column) "Source span missing"⟩,
  ⟨"source.helper-and-parallel-children", do
    let program := skipDelay files
    assertTrue (has (textAt program.metadata) "CloudBlob.readTextByName") "Helper lacks caller source"
    match program with
    | .impure _ (.command _ (.resolveBlob _)) next =>
      assertEq (next.apply ⟨"log", 0, 0⟩).metadata program.metadata "Helper lost call site between operations"
    | _ => throw (IO.userError "Expected blob helper")
    match skipDelay (branching (m := Id)) with
    | .impure info (.parallel _ count branches) _ =>
      assertTrue (has (textAt info) "Cloud.parallel") "Fork source missing"
      if h : 0 < count then
        let child := skipDelay (branches ⟨0, h⟩)
        assertTrue (child.metadata != info) "Child annotation overwritten by parent"
        assertTrue (has (textAt child.metadata) "return 11") "Child return source missing"
      else throw (IO.userError "Empty test fork")
    | _ => throw (IO.userError "Expected fork")⟩,
  ⟨"source.control-flow-and-io-thunks", do
    let noBlobs : BlobStorage Id := {
      putBlob := fun _ => throw ⟨.unsupported, "blob"⟩
      readBlob := fun _ => throw ⟨.unsupported, "blob"⟩
      resolveBlob := fun _ => throw ⟨.unsupported, "blob"⟩ }
    assertOutcome (DirectInterpreter.interpret noBlobs loopAndReturn 3).run (.ok 3)
    assertOutcome (DirectInterpreter.interpret noBlobs loopAndReturn 9).run (.ok 10)
    let ioBlobs : BlobStorage IO := {
      putBlob := fun _ => throw ⟨.unsupported, "blob"⟩
      readBlob := fun _ => throw ⟨.unsupported, "blob"⟩
      resolveBlob := fun _ => throw ⟨.unsupported, "blob"⟩ }
    assertOutcome (← (DirectInterpreter.interpret ioBlobs (fun _ => nestedIO) ()).run) (.ok 7)⟩,
  ⟨"source.annotation-preserves-replay", do
    for fuel in [:18] do
      let plain (_ : Unit) : Cloud M Nat := do
        let a ← Cloud.pure (fun _ => 10) "same"
        let b ← Cloud.pure (fun _ => 20) "same"
        return a + b
      let annotated := fun input => Cloud.withSource "test" (plain input)
      let (before, recordsBefore) := (SequentialReplay.interpret store noBlobs fuel plain ()).run []
      let (after, recordsAfter) := (SequentialReplay.interpret store noBlobs fuel annotated ()).run []
      assertOutcome after before
      assertEq recordsAfter recordsBefore "Metadata changed replay records or the fuel boundary"⟩
]

end LeanCloudTests.Source
