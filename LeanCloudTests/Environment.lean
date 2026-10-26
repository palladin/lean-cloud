import LeanCloudTests.Support
import LeanCloud.ReplayModel

namespace LeanCloudTests.Environment
open LeanCloud LeanCloud.ReplayModel

private def journalStore (journal : IO.Ref Journal) : ReplayStore IO := {
  read := fun key => return (← journal.get).lookup key
  create := fun key proposed => journal.modifyGet fun records =>
    match records.lookup key with
    | some existing => (existing, records)
    | none => (proposed, (key, proposed) :: records) }

private def noBlobs : ExecContext IO := {
  cancellation := .never
  progress := .ignore
  queues := .unsupported
  blobs := {
    putBlob := fun _ => throw ⟨.unsupported, "blob"⟩
    readBlob := fun _ => throw ⟨.unsupported, "blob"⟩
    resolveBlob := fun _ => throw ⟨.unsupported, "blob"⟩ } }

private def context (id : String) (cpus count : Nat) : ExecContext IO :=
  { noBlobs with
    currentWorker := { id, cpus, memoryMiB := some 8192 }
    workers := (Array.range count).map fun i => { id := s!"worker{i}", cpus } }

private def partitioned (_ : Unit) : Cloud IO (Array (String × (String × Nat))) := cloud {
  let workers ← Cloud.exec (fun env => pure env.workers) "plan"
  Cloud.parallel $ workers.map fun planned => cloud {
      Cloud.exec fun actual =>
        pure (planned.id, actual.currentWorker.id, actual.currentWorker.cpus)
    }
}

def cases : Array TestCase := #[
  ⟨"environment.exec-captures-typed-errors-and-underlying-io", do
    let context : ExecContext (ExceptT CloudError IO) := { cancellation := .never, progress := .ignore, queues := .unsupported, blobs := {
      putBlob := fun _ => throw ⟨.unsupported, "blob"⟩
      readBlob := fun _ => throw ⟨.unsupported, "blob"⟩
      resolveBlob := fun _ => throw ⟨.unsupported, "blob"⟩ } }
    for typed in [false, true] do
      let program (_ : Unit) : Cloud (ExceptT CloudError IO) Nat := Cloud.exec fun _ => do
        if typed then throw ⟨.integrity, "typed error"⟩
        liftM (m := IO) (throw (IO.userError "IO error") : IO Nat)
      let .ok result ← (DirectInterpreter.interpret context program ()).run.run
        | throw (IO.userError "User error escaped the exec boundary")
      assertOutcome result (.error (if typed then ⟨.integrity, "typed error"⟩ else ⟨.application, "IO error"⟩))⟩,

  ⟨"environment.typed-blob-failure-and-recovery-are-recorded", do
    let error : CloudError := ⟨.integrity, "Corrupt blob"⟩
    for recover in [false, true] do
      let calls ← IO.mkRef 0
      let context : ExecContext (ExceptT CloudError IO) := { cancellation := .never, progress := .ignore, queues := .unsupported, blobs := {
        putBlob := fun _ => throw ⟨.unsupported, "blob"⟩
        readBlob := fun _ => do
          calls.modify (· + 1)
          throw error
        resolveBlob := fun _ => throw ⟨.unsupported, "blob"⟩ } }
      let program (_ : Unit) : Cloud (ExceptT CloudError IO) Nat := Cloud.exec fun env => do
        try
          return (← env.blobs.readBlob ⟨"input", 0, 0⟩).size
        catch caught =>
          if recover && caught == error then return 7
          throw caught
      let expected : Except CloudError Nat := if recover then .ok 7 else .error error
      let .ok direct ← (DirectInterpreter.interpret context program ()).run.run
        | throw (IO.userError "Blob failure escaped the direct exec boundary")
      assertOutcome direct expected
      calls.set 0
      let saved ← IO.mkRef ([] : Journal)
      let ioStore := journalStore saved
      let store : ReplayStore (ExceptT CloudError IO) := {
        read := fun key => liftM (ioStore.read key)
        create := fun key record => liftM (ioStore.create key record) }
      for _ in [:2] do
        let .ok replay ← (SequentialReplay.interpret store context 100 program ()).run.run
          | throw (IO.userError "Blob failure escaped the replay exec boundary")
        assertOutcome replay expected
        -- Require replay of the command, rather than the cached root return.
        saved.modify (·.filter (·.1 != ReplayStore.returnKey Location.root))
      assertEq (← calls.get) 1 "Replay repeated the recorded blob failure/recovery"⟩,

  ⟨"environment.parallel-label-is-display-only", do
    let labels ← IO.mkRef (#[] : Array (Location × ParallelDisplay))
    let observe : ReplayInterpreter.Observer IO := fun location _ label =>
      if let some label := label then labels.modify (·.push (location, label)) else pure ()
    let program (label : String) (_ : Unit) : Cloud IO (Array Nat) := cloud {
      Cloud.parallel (label := label) (completedLabel := label ++ " done") $ #[pure 3, pure 5]
    }
    let saved ← IO.mkRef ([] : Journal)
    let store := journalStore saved
    let step (label : String) (branch : Location) :=
      (ReplayInterpreter.step store noBlobs 100 (program label) () ⟨0, branch⟩ (some observe)).run
    let .ok (.fork location 2) ← step "200/9,031 · 2%" Location.root
      | throw (IO.userError "Expected labeled parallel")
    for i in [:2] do
      assertOutcome (← step "renamed" (location.child i)) (.ok .done)
    assertOutcome (← step "renamed" Location.root) (.ok .done)
    let before ← saved.get
    saved.modify (·.filter (·.1 != ReplayStore.returnKey Location.root))
    assertOutcome (← step "final label" Location.root) (.ok .done)
    assertTrue ((← saved.get) == before) "Display label changed replay records"
    assertTrue ((← labels.get).contains (location, ⟨2, ⟨"200/9,031 · 2%", "200/9,031 · 2% done"⟩⟩))
      "Source annotation lost parallel labels or count"
    assertTrue ((← labels.get).contains (location, ⟨2, ⟨"final label", "final label done"⟩⟩))
      "Cached join lost its labels"
    let .ok (some outcome) ← store.outcome.run | throw (IO.userError "Missing root result")
    assertOutcome (ReplayInterpreter.result (m := Id) (α := Array Nat) outcome).run (.ok #[3, 5])
    assertOutcome (← (DirectInterpreter.interpret noBlobs (program "direct label") ()).run) (.ok #[3, 5])⟩,
  ⟨"environment.parallel-is-an-array-function", do
    let runParallel : Array (Cloud IO Nat) → Cloud IO (Array Nat) := Cloud.parallel
    for program in #[Cloud.parallel #[pure 6], LeanCloud.Cloud.parallel #[pure 6], runParallel #[pure 6]] do
      assertOutcome (← (DirectInterpreter.interpret (context "a" 6 4) (fun _ : Unit => program) ()).run) (.ok #[6])
    let saved ← IO.mkRef ([] : Journal)
    let source (_ : Unit) : Cloud IO (Array Nat) := runParallel #[pure 6]
    assertOutcome (← (ReplayInterpreter.step (journalStore saved) noBlobs 100 source () ⟨0, Location.root⟩).run)
      (.ok (.fork Location.root 1))
    assertEq (← saved.get).length 0 "Parallel recorded a hidden environment command"⟩,
  ⟨"environment.direct-execution", do
    let program (_ : Unit) : Cloud IO Nat := Cloud.exec fun env => pure env.currentWorker.cpus
    assertOutcome (← (DirectInterpreter.interpret (context "a" 6 4) program ()).run) (.ok 6)⟩,
  ⟨"environment.parallel-plan-survives-pool-changes", do
    let journal ← IO.mkRef ([] : Journal)
    let store := journalStore journal
    let step (branch : Location) (env : ExecContext IO) :=
      (ReplayInterpreter.step store env 100 partitioned () ⟨0, branch⟩).run
    let fork ← step Location.root (context "planner" 6 2)
    let .ok (.fork location count) := fork | throw (IO.userError "Expected parallel suspension")
    assertEq count 2 "Wrong original partition count"
    for i in [:count] do
      assertOutcome (← step (location.child i) (context "replacement" 3 5)) (.ok .done)
    assertOutcome (← step Location.root (context "joining" 8 7)) (.ok .done)
    let .ok (some outcome) ← store.outcome.run | throw (IO.userError "Missing root outcome")
    let actual := (ReplayInterpreter.result (m := Id) (α := Array (String × (String × Nat))) outcome).run
    assertOutcome actual (.ok #[("worker0", "replacement", 3), ("worker1", "replacement", 3)])⟩,
  ⟨"environment.crash-before-record-uses-replacement-capacity", do
    let journal ← IO.mkRef ([] : Journal)
    let store := journalStore journal
    let crash ← IO.mkRef true
    let calls ← IO.mkRef 0
    let faulting : ReplayStore IO := { store with create := fun key value => do
      if ← crash.get then
        crash.set false
        throw (IO.userError "Simulated worker interruption before commit")
      store.create key value }
    let program (_ : Unit) : Cloud IO Nat := Cloud.exec fun env => do
      calls.modify (· + 1)
      return env.currentWorker.cpus
    let run (env : ExecContext IO) :=
      (ReplayInterpreter.step faulting env 100 program () ⟨0, Location.root⟩).run
    let interrupted ← try discard (run (context "a" 6 2)); pure false catch _ => pure true
    assertTrue interrupted "Storage interruption became an application result"
    assertOutcome (← run (context "b" 3 1)) (.ok .done)
    assertEq (← calls.get) 2 "Uncommitted exec was not retried"
    journal.modify (·.filter (·.1 != ReplayStore.returnKey Location.root))
    assertOutcome (← run (context "c" 9 4)) (.ok .done)
    assertEq (← calls.get) 2 "Committed exec ran again on replay"
    let .ok (some outcome) ← store.outcome.run | throw (IO.userError "Missing outcome")
    assertOutcome (ReplayInterpreter.result (m := Id) (α := Nat) outcome).run (.ok 3)⟩
]

end LeanCloudTests.Environment
