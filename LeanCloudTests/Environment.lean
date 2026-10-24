import LeanCloudTests.Support
import LeanCloud.ReplayModel

namespace LeanCloudTests.Environment
open LeanCloud LeanCloud.ReplayModel

private def context (id : String) (cpus count : Nat) : LeanCloud.Environment :=
  { currentWorker := { id, cpus, memoryMiB := some 8192 }
    workers := (Array.range count).map fun i => { id := s!"worker{i}", cpus } }

private def journalStore (journal : IO.Ref Journal) : ReplayStore IO := {
  read := fun key => return (← journal.get).lookup key
  create := fun key proposed => journal.modifyGet fun records =>
    match records.lookup key with
    | some existing => (existing, records)
    | none => (proposed, (key, proposed) :: records) }

private def noBlobs : BlobStorage IO := {
  putBlob := fun _ => throw ⟨.unsupported, "blob"⟩
  readBlob := fun _ => throw ⟨.unsupported, "blob"⟩
  resolveBlob := fun _ => throw ⟨.unsupported, "blob"⟩ }

private def partitioned (_ : Unit) : Cloud IO (Array (String × (String × Nat))) := cloud {
  Cloud.parallel fun planning =>
    planning.workers.map fun planned => cloud {
      Cloud.exec fun actual =>
        pure (planned.id, actual.currentWorker.id, actual.currentWorker.cpus)
    }
}

private def plan (env : LeanCloud.Environment) : Array (Cloud IO Nat) :=
  #[pure env.currentWorker.cpus]

def cases : Array TestCase := #[
  ⟨"environment.parallel-label-is-display-only", do
    let labels ← IO.mkRef (#[] : Array (Location × String))
    let observe : ReplayInterpreter.Observer IO := fun location _ label =>
      if let some label := label then labels.modify (·.push (location, label)) else pure ()
    let program (label : String) (_ : Unit) : Cloud IO (Array Nat) := cloud {
      Cloud.parallel (label := label) fun _ => #[pure 3, pure 5]
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
    assertTrue ((← labels.get).contains (location, "200/9,031 · 2%")) "Source annotation lost parallel label"
    assertTrue ((← labels.get).contains (location, "final label")) "Cached join lost its label"
    let .ok (some outcome) ← store.outcome.run | throw (IO.userError "Missing root result")
    assertOutcome (ReplayInterpreter.result (m := Id) (α := Array Nat) outcome).run (.ok #[3, 5])
    assertOutcome (← (DirectInterpreter.interpret noBlobs (program "direct label") ()).run) (.ok #[3, 5])⟩,
  ⟨"environment.parallel-callback-syntax", do
    let runParallel : (LeanCloud.Environment → Array (Cloud IO Nat)) → Cloud IO (Array Nat) :=
      Cloud.parallel
    let programs : Array (Cloud IO (Array Nat)) := #[
      cloud { Cloud.parallel fun (env : LeanCloud.Environment) => #[pure env.currentWorker.cpus] },
      cloud { Cloud.parallel (fun (env : LeanCloud.Environment) => #[pure env.currentWorker.cpus]) },
      cloud { LeanCloud.Cloud.parallel fun env => #[pure env.currentWorker.cpus] },
      cloud { LeanCloud.Cloud.parallel (fun env => #[pure env.currentWorker.cpus]) },
      cloud { Cloud.parallel fun _ => #[pure 6] },
      cloud { Cloud.parallel plan },
      runParallel plan]
    for program in programs do
      assertOutcome (← (DirectInterpreter.interpret noBlobs (fun _ : Unit => program) () (context "a" 6 4)).run)
        (.ok #[6])⟩,
  ⟨"environment.direct-execution", do
    let program (_ : Unit) : Cloud IO Nat := Cloud.exec fun env => pure env.currentWorker.cpus
    assertOutcome (← (DirectInterpreter.interpret noBlobs program () (context "a" 6 4)).run) (.ok 6)⟩,
  ⟨"environment.parallel-plan-survives-pool-changes", do
    let journal ← IO.mkRef ([] : Journal)
    let store := journalStore journal
    let step (branch : Location) (env : LeanCloud.Environment) :=
      (ReplayInterpreter.step store noBlobs 100 partitioned () ⟨0, branch⟩ (environment := env)).run
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
    let run (env : LeanCloud.Environment) :=
      (ReplayInterpreter.step faulting noBlobs 100 program () ⟨0, Location.root⟩ (environment := env)).run
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
