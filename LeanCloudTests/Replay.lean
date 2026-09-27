import LeanCloudTests.Differential

namespace LeanCloudTests
open Lean LeanCloud

def checkpointSweep [Codec α] [BEq α] [Repr α] (program : Program α) : IO Unit := do
  let (expected, completed) ← differential program
  assertTrue (completed.recordPuts > 0) "Checkpoint fixture made no writes"
  for cut in [1:completed.recordPuts + 1] do
    try
      let ref ← IO.mkRef { initial with crashAfterPut := some cut }
      let crashed ← try
        let _ ← runReplay program ref
        pure false
      catch error => do
        assertEq error.toString "injected crash after journal commit"
        pure true
      assertTrue crashed s!"Checkpoint {cut} was not reached"
      assertOutcome (← runReplay program ref) expected
      assertObservations (← ref.get) completed
      assertEq (journal (← ref.get)) (journal completed) "Recovered journal differs"
    catch error => throw (IO.userError s!"after-write checkpoint {cut}: {error}")

def fuelSweep [Codec α] [BEq α] [Repr α] (program : Program α) : IO Unit := do
  let (expected, completed) ← differential program
  for fuel in [:80] do
    try
      let ref ← IO.mkRef initial
      let first ← runReplay program ref fuel
      match first with
      | .error error =>
        if error.message != "Interpreter fuel exhausted" then assertOutcome first expected
      | .ok _ => assertOutcome first expected
      assertOutcome (← runReplay program ref) expected
      assertObservations (← ref.get) completed
      assertEq (journal (← ref.get)) (journal completed)
    catch error => throw (IO.userError s!"fuel={fuel}: {error}")

def replayCases : Array TestCase := #[
  ⟨"replay/checkpoints/nested", checkpointSweep nested⟩,
  ⟨"replay/checkpoints/blobs", checkpointSweep blobWorkflow⟩,
  ⟨"replay/checkpoints/failure", checkpointSweep failingParallel⟩,
  ⟨"replay/checkpoints/empty-group", checkpointSweep (fun ref => do
    let _ ← Cloud.parallel (#[] : Array (Cloud IO Nat))
    execValue ref "after-empty" 5)⟩,
  ⟨"replay/fuel/nested", fuelSweep nested⟩,
  ⟨"replay/fuel/blobs", fuelSweep blobWorkflow⟩,
  ⟨"replay/fuel/failure", fuelSweep failingParallel⟩,
  ⟨"replay/uncommitted-effect-can-repeat", do
    let program : Program Nat := fun ref => execValue ref "uncommitted" 42
    let ref ← IO.mkRef { initial with crashBeforePut := some 1 }
    let crashed ← try
      let _ ← runReplay program ref
      pure false
    catch error => do
      assertEq error.toString "injected crash before journal commit"
      pure true
    assertTrue crashed "Pre-commit crash did not occur"
    assertEq (← ref.get).trace.size 1
    assertTrue (← ref.get).records.isEmpty "The interrupted effect was committed"
    assertOutcome (← runReplay program ref) (.ok 42)
    assertEq (← ref.get).trace.size 2 "An uncommitted effect must execute again on replay"⟩,
  ⟨"replay/cached-blobs-survive-backend-removal", do
    let ref ← IO.mkRef initial
    assertOutcome (← runReplay blobWorkflow ref) (.ok "hello/seed: λ 🌍")
    let before ← ref.get
    ref.modify fun world => { world with blobs := [], names := [] }
    assertOutcome (← runReplay blobWorkflow ref) (.ok "hello/seed: λ 🌍")
    assertEq (← ref.get).trace before.trace
    assertTrue (← ref.get).blobs.isEmpty "Replay wrote a new blob"⟩,
  ⟨"replay/cached-failure-survives-repair", do
    let program : Program BlobRef := fun _ => CloudBlob.resolve "later"
    let ref ← IO.mkRef initial
    let expected ← runReplay program ref
    assertError expected .missingBlob
    let before ← ref.get
    ref.modify fun world => { world with names := [("later", makeRef "fixed" "x".toUTF8)] }
    assertOutcome (← runReplay program ref) expected
    assertEq (← ref.get).trace before.trace⟩,
  ⟨"replay/rejected-journal-write", do
    let ref ← IO.mkRef { initial with rejectPuts := true }
    let program : Program Nat := fun _ => pure 7
    assertError (← runReplay program ref) .protocol
    assertTrue (← ref.get).records.isEmpty "Rejected write changed the journal"⟩,
  ⟨"replay/malformed-record", do
    let ref ← IO.mkRef { initial with records := [("0:0", Json.str "bad record")] }
    assertError (← runReplay (fun ref => execValue ref "must-not-run" 1) ref) .codec
    assertTrue (← ref.get).trace.isEmpty "Malformed record caused an effect"⟩,
  ⟨"replay/malformed-effect-value", do
    let ref ← IO.mkRef { initial with records := [
      ("0:0", toJson (Result.completed (.success (Json.str "not a Nat"))))] }
    assertError (← runReplay (fun ref => execValue ref "must-not-run" 1) ref) .codec
    assertTrue (← ref.get).trace.isEmpty "Bad recorded value caused an effect"⟩,
  ⟨"replay/changed-child-count", do
    let ref ← IO.mkRef { initial with records := [("0:0", toJson (Result.suspended #[none]))] }
    let program : Program (Array Nat) := fun _ => Cloud.parallel #[pure 1, pure 2]
    assertError (← runReplay program ref) .divergence⟩,
  ⟨"replay/changed-pure-completion", do
    let ref ← IO.mkRef initial
    assertOutcome (← runReplay (fun _ => pure (1 : Nat)) ref) (.ok 1)
    assertError (← runReplay (fun _ => pure (2 : Nat)) ref) .divergence⟩,
  ⟨"replay/distinct-forks-have-distinct-keys", do
    let ref ← IO.mkRef initial
    let program : Program Nat := fun _ => do
      let xs ← Cloud.parallel #[pure (1 : Nat), pure 2]
      let ys ← Cloud.parallel #[pure xs[0]!, pure xs[1]!]
      return ys.foldl (· + ·) 0
    assertOutcome (← runReplay program ref) (.ok 3)
    for key in ["0:0", "0:1", "0:2", "0:0/0:0", "0:0/1:0", "0:1/0:0", "0:1/1:0"] do
      assertTrue ((← ref.get).records.lookup key).isSome s!"Missing distinct location {key}"⟩
]

end LeanCloudTests
