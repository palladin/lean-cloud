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
  Cloud.parallel $ #[cloud { return 11 }, cloud { return 22 }]
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

private def files : Cloud IO String := cloud {
  Cloud.exec fun env => env.blobs.readTextByName "log.txt"
}

private def implementationDetail [Monad m] (n : Nat) : Cloud m Nat := cloud {
  Cloud.pure (fun _ => n + 1) "hidden helper detail"
}

private def helperImplementation [Monad m] (n : Nat) : Cloud m Nat := cloud {
  let first ← implementationDetail n
  implementationDetail first
}

@[cloud_func (descr := "Increment twice") (opaque := true)]
private def opaqueHelper [Monad m] (n : Nat) : Cloud m Nat := helperImplementation n

private def helperCaller : Cloud Id Nat := cloud {
  let answer ← opaqueHelper 10
  return answer + 1
}

@[cloud_func] private def constantHelper : Cloud Id Nat := cloud {
  Cloud.pure (fun _ => 42) "constant detail"
}

private def constantCaller : Cloud Id Nat := cloud {
  constantHelper
}

@[cloud_func (opaque := false) (descr := "Visible steps")]
private def visibleHelper [Monad m] (n : Nat) : Cloud m Nat := helperImplementation n

private def visibleCaller : Cloud Id Nat := cloud {
  let answer ← visibleHelper 10
  return answer + 2
}

private def plainCaller : Cloud Id Nat := cloud {
  helperImplementation 10
}

@[cloud_func] private partial def recursiveHelper (n : Nat) : Cloud Id Nat := cloud {
  if n == 0 then return 0
  let value ← Cloud.pure (fun _ => n - 1) "recursive detail"
  recursiveHelper value
}

private def recursiveCaller : Cloud Id Nat := cloud {
  recursiveHelper 2
}

@[cloud_func] private def opaqueBranches [Monad m] (branches : Array (Cloud m Nat)) :
    Cloud m (Array Nat) := cloud {
  let _ ← Cloud.pure (fun _ => 1) "helper setup"
  Cloud.parallel $ branches
}

private def suppliedBranch : Cloud Id Nat := cloud { return 123 }

private def branchCaller : Cloud Id (Array Nat) := cloud {
  opaqueBranches #[suppliedBranch, cloud { return 456 }]
}

private def plannedBranches : Cloud IO (Array Nat) := cloud {
  let workers ← Cloud.exec (fun env => pure env.workers) "plan"
  Cloud.parallel $ workers.map fun worker => cloud { return worker.cpus }
}

private abbrev Job := Cloud Id Nat

@[cloud_func (descr := "Aliased job")]
private def aliasHelper : Job := cloud { Cloud.pure (fun _ => 1) "alias detail" }

private def aliasCaller : Job := cloud { aliasHelper }

private abbrev Jobs := Array Job
private def internalBranches : Jobs := #[cloud { Cloud.pure (fun _ => 3) "internal branch" }]

@[cloud_func] private def containerHelper : Cloud Id (Array Nat) := cloud {
  Cloud.parallel $ internalBranches
}

private def containerCaller : Cloud Id (Array Nat) := cloud { containerHelper }

private def sharedDetail : Cloud Id Nat := cloud { Cloud.pure (fun _ => 5) "shared detail" }

@[cloud_func]
private def sharedBranches (user : Cloud Id Nat) : Cloud Id (Array Nat) := cloud {
  let _ ← sharedDetail
  Cloud.parallel $ #[user]
}

private def sharedCaller : Cloud Id (Array Nat) := cloud { sharedBranches sharedDetail }

@[cloud_func (descr := "Inner steps") (opaque := false)]
private def innerVisible : Cloud Id Nat := cloud { Cloud.pure (fun _ => 5) "nested detail" }

@[cloud_func (descr := "Outer opaque")]
private def outerOpaque : Cloud Id Nat := cloud { innerVisible }

@[cloud_func (descr := "Outer visible") (opaque := false)]
private def outerVisible : Cloud Id Nat := cloud { innerVisible }

private def nestedOpaqueCaller : Cloud Id Nat := cloud { outerOpaque }
private def nestedVisibleCaller : Cloud Id Nat := cloud { outerVisible }

/-- error: Cloud function opaque must be true or false -/
#guard_msgs in
@[cloud_func (opaque := maybe)] private def badOpaque : Cloud Id Nat := pure 1

/-- error: Duplicate cloud_func descr -/
#guard_msgs in
@[cloud_func (descr := "first") (descr := "second")]
private def badDescr : Cloud Id Nat := pure 1

/-- error: Cloud function description cannot be empty -/
#guard_msgs in
@[cloud_func (descr := "  ")] private def emptyDescr : Cloud Id Nat := pure 1

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

private def inspectNext (program : Cloud IO α) (context : ExecContext IO)
    (inspect : Cloud IO α → IO Unit) : IO Unit :=
  match program with
  | .impure _ (.command _ _ body) next => do
    match ← (body context).run with
    | .ok value => inspect (next.apply value)
    | .error error => inspect (Cloud.send (.fail error))
  | program => inspect program

private def nextExec (program : Cloud Id α) : Cloud Id α :=
  match program with
  | .impure _ (.command _ _ body) next =>
    let context : ExecContext Id := { cancellation := .never, progress := .ignore, queues := .unsupported, blobs := {
      putBlob := fun _ => throw ⟨.unsupported, "blob"⟩
      readBlob := fun _ => throw ⟨.unsupported, "blob"⟩
      resolveBlob := fun _ => throw ⟨.unsupported, "blob"⟩ } }
    match (body context).run with
    | .ok value => next.apply value
    | .error error => Cloud.send (.fail error)
  | program => program

private def has (text fragment : String) : Bool := (text.splitOn fragment).length > 1

private def ioBlobs : ExecContext IO where
  cancellation := .never
  progress := .ignore
  queues := .unsupported
  blobs := {
    putBlob _ := throw ⟨.unsupported, "blob"⟩
    readBlob _ := throw ⟨.unsupported, "blob"⟩
    resolveBlob _ := throw ⟨.unsupported, "blob"⟩ }

private def observeReplay : IO Unit := do
  let saved ← IO.mkRef ([] : Journal)
  let observations ← IO.mkRef (#[] : Array (Location × Option SourceSiteId))
  let records : ReplayStore IO := {
    read := fun key => return (← saved.get).lookup key
    create := fun key proposed => saved.modifyGet fun records =>
      match records.lookup key with
      | some existing => (existing, records)
      | none => (proposed, (key, proposed) :: records) }
  let visit : ReplayInterpreter.Observer IO := fun location source _ =>
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
  ⟨"source.helper-return-type-alias", do
    let command := skipDelay (skipDelay aliasCaller)
    assertTrue (has (textAt command.metadata) "cloud { aliasHelper }") "Type alias bypassed opacity"
    assertEq ((site command.metadata).bind (·.functionInfo) |>.map (·.descr)) (some "Aliased job")⟩,
  ⟨"source.helper-owns-internal-branch-container", do
    match nextExec (skipDelay (skipDelay containerCaller)) with
    | .impure _ (.parallel _ count branches _) _ =>
      if h : 0 < count then
        let command := skipDelay (branches ⟨0, h⟩)
        assertTrue (has (textAt command.metadata) "cloud { containerHelper }") "Internal container exposed implementation"
      else throw (IO.userError "Missing internal branch")
    | _ => throw (IO.userError "Expected internal fork")⟩,
  ⟨"source.shared-helper-keeps-user-branch-visible", do
    let setup := skipDelay (skipDelay (skipDelay sharedCaller))
    assertTrue (has (textAt setup.metadata) "sharedBranches sharedDetail") "Internal call was not hidden"
    match nextExec (nextExec setup) with
    | .impure _ (.parallel _ count branches _) _ =>
      if h : 0 < count then
        let command := skipDelay (branches ⟨0, h⟩)
        assertTrue (has (textAt command.metadata) "\"shared detail\"") "Shared user branch was hidden"
        assertTrue ((site command.metadata).bind (·.functionInfo)).isNone "User branch inherited helper metadata"
      else throw (IO.userError "Missing shared branch")
    | _ => throw (IO.userError "Expected shared fork")⟩,
  ⟨"source.nested-function-display-policy", do
    let opaqueCommand := skipDelay (skipDelay (skipDelay nestedOpaqueCaller))
    assertTrue (has (textAt opaqueCommand.metadata) "cloud { outerOpaque }") "Nested helper escaped opacity"
    assertEq ((site opaqueCommand.metadata).bind (·.functionInfo) |>.map (·.descr)) (some "Outer opaque")
    let visibleCommand := skipDelay (skipDelay (skipDelay nestedVisibleCaller))
    assertTrue (has (textAt visibleCommand.metadata) "\"nested detail\"") "Transparent nesting hid implementation"
    assertEq ((site visibleCommand.metadata).bind (·.functionInfo) |>.map (·.descr)) (some "Inner steps")⟩,
  ⟨"source.opaque-helper-without-arguments", do
    let command := skipDelay (skipDelay constantCaller)
    assertTrue (has (textAt command.metadata) "  constantHelper") "Nullary helper exposed its definition"
    let some info := (site command.metadata).bind (·.functionInfo)
      | throw (IO.userError "Default function metadata missing")
    assertTrue (info.name.endsWith "constantHelper" && info.descr == info.name && info.opaque)
      "Wrong cloud_func defaults"⟩,
  ⟨"source.opaque-recursive-helper", do
    let first := skipDelay (skipDelay recursiveCaller)
    assertTrue (has (textAt first.metadata) "recursiveHelper 2") "Recursive helper exposed its implementation"
    let second := skipDelay (nextExec first)
    assertEq second.metadata first.metadata "Recursion lost outer call site"⟩,
  ⟨"source.opaque-helper-keeps-call-site", do
    let first := skipDelay (skipDelay helperCaller)
    let first := skipDelay first
    assertTrue (has (textAt first.metadata) "opaqueHelper 10") "Helper exposed its implementation"
    assertEq ((site first.metadata).bind (·.functionInfo) |>.map (·.descr)) (some "Increment twice")
    let second := skipDelay (nextExec first)
    assertEq second.metadata first.metadata "Nested helper lost outer call site"
    let final := nextExec second
    assertTrue (has (textAt final.metadata) "return answer + 1") "Opacity leaked past helper return"
    assertTrue ((site final.metadata).bind (·.functionInfo)).isNone "Description leaked past helper return"⟩,
  ⟨"source.transparent-helper-preserves-implementation", do
    let first := skipDelay (skipDelay (skipDelay visibleCaller))
    assertTrue (has (textAt first.metadata) "hidden helper detail") "Transparent helper hid its implementation"
    let some info := (site first.metadata).bind (·.functionInfo)
      | throw (IO.userError "Transparent helper lost description")
    assertEq info.descr "Visible steps"
    assertTrue (!info.opaque) "Transparent metadata marked opaque"
    let second := skipDelay (nextExec first)
    assertEq ((site second.metadata).bind (·.functionInfo)) (some info)
    let final := nextExec second
    assertTrue (has (textAt final.metadata) "return answer + 2") "Transparent helper lost caller continuation"
    assertTrue ((site final.metadata).bind (·.functionInfo)).isNone "Description leaked after helper"
    let original := skipDelay (skipDelay (skipDelay plainCaller))
    assertTrue ((site original.metadata).bind (·.functionInfo)).isNone "Description leaked into another call"⟩,
  ⟨"source.function-metadata-wire-and-watch", do
    let legacy : SourceSite ← unwrap (Json.parse "{\"id\":\"old\",\"line\":2,\"column\":0,\"endLine\":2,\"endColumn\":5}" >>= fromJson?)
    assertTrue legacy.functionInfo.isNone "Old source map requires function metadata"
    let invalid := Json.mkObj [("id", toJson "bad"), ("line", toJson (2 : Nat)),
      ("column", toJson (0 : Nat)), ("endLine", toJson (2 : Nat)), ("endColumn", toJson (5 : Nat)),
      ("functionInfo", toJson false)]
    assertTrue (fromJson? (α := SourceSite) invalid).toOption.isNone "Malformed metadata was silently ignored"
    let decoded : Array ProgramSource ← unwrap (fromJson? (toJson sources))
    let run : LeanCloudCli.Run := ⟨"run", "image", ⟨"app/v1", "unit", "nat", "", none, decoded⟩, Json.null⟩
    for (program, descr) in [(helperCaller, "Increment twice"), (visibleCaller, "Visible steps")] do
      let command := skipDelay (skipDelay (skipDelay program))
      let observation : LeanCloudCli.Trace.Step := {
        timestamp := "1", event := ⟨"boot", 0, 0, "worker1", some 0, "0:0", "execute", "internal", "run", command.metadata⟩ }
      let view := LeanCloudCli.Watch.frame ⟨"/work", "test"⟩ run #[observation] #[] {} 160 40 "completed"
      assertTrue (view.any (has · s!"Source: {descr} ·")) "Watch did not display the function description"⟩,
  ⟨"source.opaque-helper-preserves-supplied-branches", do
    let setup := skipDelay (skipDelay branchCaller)
    let fork := nextExec (nextExec setup)
    assertTrue (has (textAt fork.metadata) "opaqueBranches #[") "Helper fork exposed its definition"
    match fork with
    | .impure _ (.parallel _ count branches _) _ =>
      if h : 1 < count then
        assertTrue (has (textAt (skipDelay (branches ⟨0, by omega⟩)).metadata) "return 123")
          "Named user branch was hidden"
        assertTrue (has (textAt (skipDelay (branches ⟨1, h⟩)).metadata) "return 456")
          "Inline user branch was hidden"
      else throw (IO.userError "Missing supplied branches")
    | _ => throw (IO.userError "Expected helper parallel")⟩,
  ⟨"source.explicit-planning-and-parallel-sites", do
    let setup := skipDelay plannedBranches
    inspectNext setup ioBlobs fun fork => do
      assertTrue (has (textAt setup.metadata) "let workers ← Cloud.exec") "Explicit planning source missing"
      assertTrue (has (textAt fork.metadata) "Cloud.parallel") "Fork source missing"
      assertTrue (fork.metadata != setup.metadata) "Planning and fork share a source site"
      match fork with
      | .impure _ (.parallel _ count branches _) _ =>
        if h : 0 < count then
          assertTrue (has (textAt (skipDelay (branches ⟨0, h⟩)).metadata) "return worker.cpus")
            "User callback source was hidden"
        else throw (IO.userError "Empty planning environment")
      | _ => throw (IO.userError "Expected planned parallel")⟩,
  ⟨"source.observer-replay", observeReplay⟩,
  ⟨"source.console-multiple-files-and-unknown-sites", do
    let a : ProgramSource := ⟨"A.lean", "first\nread a", #[{ id := "a", line := 2, endLine := 2, endColumn := 6 }]⟩
    let b : ProgramSource := ⟨"B.lean", "read b\nlast", #[{ id := "b", line := 1, endLine := 1, endColumn := 6 }]⟩
    let run : LeanCloudCli.Run := ⟨"run", "image", ⟨"app/v1", "unit", "nat", "", none, #[a, b]⟩, Json.null⟩
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
    assertTrue (has (textAt program.metadata) "Cloud.exec fun env") "Helper lacks caller source"
    match program with
    | .impure _ (.command _ _ _) _ => pure ()
    | _ => throw (IO.userError "Expected blob helper")
    match nextExec (skipDelay (branching (m := Id))) with
    | .impure info (.parallel _ count branches _) _ =>
      assertTrue (has (textAt info) "Cloud.parallel") "Fork source missing"
      if h : 0 < count then
        let child := skipDelay (branches ⟨0, h⟩)
        assertTrue (child.metadata != info) "Child annotation overwritten by parent"
        assertTrue (has (textAt child.metadata) "return 11") "Child return source missing"
      else throw (IO.userError "Empty test fork")
    | _ => throw (IO.userError "Expected fork")⟩,
  ⟨"source.control-flow-and-io-thunks", do
    let noBlobs : ExecContext Id := {
      cancellation := .never
      progress := .ignore
      queues := .unsupported
      blobs := {
        putBlob := fun _ => throw ⟨.unsupported, "blob"⟩
        readBlob := fun _ => throw ⟨.unsupported, "blob"⟩
        resolveBlob := fun _ => throw ⟨.unsupported, "blob"⟩ } }
    assertOutcome (DirectInterpreter.interpret noBlobs loopAndReturn 3).run (.ok 3)
    assertOutcome (DirectInterpreter.interpret noBlobs loopAndReturn 9).run (.ok 10)
    let ioBlobs : ExecContext IO := {
      cancellation := .never
      progress := .ignore
      queues := .unsupported
      blobs := {
        putBlob := fun _ => throw ⟨.unsupported, "blob"⟩
        readBlob := fun _ => throw ⟨.unsupported, "blob"⟩
        resolveBlob := fun _ => throw ⟨.unsupported, "blob"⟩ } }
    assertOutcome (← (DirectInterpreter.interpret ioBlobs (fun _ => nestedIO) ()).run) (.ok 7)⟩,
  ⟨"source.annotation-preserves-replay", do
    for fuel in [:18] do
      let plain (_ : Unit) : Cloud M Nat := do
        let a ← Cloud.pure (fun _ => 10) "same"
        let b ← Cloud.pure (fun _ => 20) "same"
        return a + b
      let annotated := fun input => Cloud.withSource "test" (plain input)
      let (before, recordsBefore) := (SequentialReplay.interpret store pureContext fuel plain ()).run []
      let (after, recordsAfter) := (SequentialReplay.interpret store pureContext fuel annotated ()).run []
      assertOutcome after before
      assertEq recordsAfter recordsBefore "Metadata changed replay records or the fuel boundary"
      let raw (_ : Unit) : Cloud M Nat := cloud { helperImplementation 10 }
      let opaqueProgram (_ : Unit) : Cloud M Nat := cloud { opaqueHelper 10 }
      let visibleProgram (_ : Unit) : Cloud M Nat := cloud { visibleHelper 10 }
      let expected := (SequentialReplay.interpret store pureContext fuel raw ()).run []
      for program in [opaqueProgram, visibleProgram] do
        let actual := (SequentialReplay.interpret store pureContext fuel program ()).run []
        assertOutcome actual.1 expected.1
        assertEq actual.2 expected.2 "cloud_func changed replay records or fuel"⟩
]

end LeanCloudTests.Source
