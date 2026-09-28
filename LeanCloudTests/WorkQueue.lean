import LeanCloudTests.Generated
import LeanCloudTests.Backends
import LeanCloudTests.Differential

namespace LeanCloudTests.Queue
open Lean LeanCloud

structure Decision where
  ready : Array Location
  selected : Nat
  deriving Repr

def recording (log : IO.Ref (Array Decision)) (choose : Select) : Select :=
  fun ready nonempty => do
    let selected ← choose ready nonempty
    log.modify (·.push ⟨ready, selected.val⟩)
    return selected

def seeded (seed : IO.Ref Nat) : Select := fun ready nonempty => do
  let n := nextSeed (← seed.get)
  seed.set n
  -- Use upper bits: the low bits of this generator have a short period.
  return ⟨(n / 256) % ready.size, Nat.mod_lt _ nonempty⟩

def noChoice : Select := fun _ _ =>
  throw (IO.userError "A completed replay requested new work")

/-- Exercise a queue policy, then require a completed restart to do no work. -/
def runScheduled [Codec α] [BEq α] [Repr α] (program : Program α) (select : Select) :
    IO (Except CloudError α × World × Array Decision) := do
  let ref ← IO.mkRef initial
  let log ← IO.mkRef #[]
  let outcome ← runReplay program ref replayFuel (recording log select)
  let world ← ref.get
  assertTrue world.pending.isEmpty "Finished run retained pending work"
  assertTrue world.completed.isSome "Environment lost the final outcome"
  assertOutcome (← runReplay program ref replayFuel noChoice) outcome
  assertObservations (← ref.get) world
  assertEq (journal (← ref.get)) (journal world)
  return (outcome, world, ← log.get)

def scripted (keys : Array String) (cursor : IO.Ref Nat) : Select :=
  fun ready _ => do
    let index ← cursor.get
    let some key := keys[index]? | throw (IO.userError "Script ran out of choices")
    let some selected := ready.findIdx? (fun location => location.key == key)
      | throw (IO.userError s!"Script selected {key}, ready: {reprStr (ready.map Location.key)}")
    if inside : selected < ready.size then
      cursor.set (index + 1)
      return ⟨selected, inside⟩
    else throw (IO.userError "Invalid script index")

def twoSteps (ref : Ref) (label : String) : Cloud IO Nat := cloud {
  let a ← execValue ref s!"{label}/1" 1
  execValue ref s!"{label}/2" (a + 1)
}

def interleaved : Program (Array Nat) := fun ref =>
  Cloud.parallel #[twoSteps ref "left", twoSteps ref "right"]

def interleavingScript : Array String := #[
  "0:0", "0:0/0:0", "0:0/1:0", "0:0/0:1", "0:0/1:1",
  "0:0/1:2", "0:0/0:2", "0:0", "0:1"]

/-- Unique effect labels and schedule-independent values allow a different
schedule after restart without mistaking legitimate reordering for duplication. -/
def recoveryProgram : Program Nat := fun ref => cloud {
  let values ← Cloud.parallel #[cloud {
    let nested ← Cloud.parallel #[twoSteps ref "nested/0", twoSteps ref "nested/1"]
    execValue ref "nested/join" (nested.foldl (· + ·) 0)
  }, twoSteps ref "sibling", cloud {
    let _ ← Cloud.parallel (#[] : Array (Cloud IO Nat))
    execValue ref "empty/join" 3
  }]
  execValue ref "root/join" (values.foldl (· + ·) 0)
}

def sortedEvents (world : World) : List (String × Json) :=
  world.trace.toList.mergeSort (fun a b => a.1 ≤ b.1)

def recoverySweep (program : Program Nat) (startSeed : Nat) : IO Unit := do
  let baseline ← IO.mkRef initial
  let seed ← IO.mkRef startSeed
  let expected ← runReplay program baseline replayFuel (seeded seed)
  let completed ← baseline.get
  assertTrue (completed.recordPuts > 0) "Recovery fixture made no writes"
  for cut in [1:completed.recordPuts + 1] do
    try
      let ref ← IO.mkRef { initial with crashAfterPut := some cut }
      let seed ← IO.mkRef startSeed
      let crashed ← try
        let _ ← runReplay program ref replayFuel (seeded seed)
        pure false
      catch error => do
        assertEq error.toString "injected crash after journal commit"
        pure true
      assertTrue crashed "Checkpoint not reached"
      let resumeSeed ← IO.mkRef (startSeed + cut + 73)
      assertOutcome (← runReplay program ref replayFuel (seeded resumeSeed)) expected
      let recovered ← ref.get
      assertEq (sortedEvents recovered) (sortedEvents completed) "Effects lost or repeated"
      assertEq (externalState recovered) (externalState completed)
      assertEq (journal recovered) (journal completed)
      assertOutcome (← runReplay program ref replayFuel noChoice) expected
      assertObservations (← ref.get) recovered
    catch error => throw (IO.userError s!"seed={startSeed}, after-write checkpoint={cut}: {error}")

/-- Interrupt before and after each atomic queue update, retaining both journal
and pending work. This includes publication of forks, joins, and final outcomes. -/
def queueUpdateSweep [Codec α] [BEq α] [Repr α] (program : Program α) : IO Unit := do
  let (expected, completed, decisions) ← runScheduled program selectFirst
  for after in [false, true] do
    for cut in [1:decisions.size + 1] do
      try
        let ref ← IO.mkRef initial
        let updates ← IO.mkRef 0
        let base := workQueue
        let queue : WorkQueue Ref IO := { base with
          complete := fun location update state => do
            let n := (← updates.get) + 1
            updates.set n
            if n == cut && !after then throw (IO.userError "queue interrupted")
            let result ← base.complete location update state
            if n == cut && after then throw (IO.userError "queue interrupted")
            return result }
        let crashed ← try
          let _ ← (interpret db blobStorage queue replayFuel program ref).run ref
          pure false
        catch error => do
          assertEq error.toString "queue interrupted"
          pure true
        assertTrue crashed "Queue checkpoint not reached"
        assertOutcome (← runReplay program ref) expected
        assertObservations (← ref.get) completed
        assertEq (journal (← ref.get)) (journal completed)
        assertTrue (← ref.get).pending.isEmpty "Finished queue retained pending work"
        assertEq (← ref.get).completed completed.completed
      catch error => throw (IO.userError s!"queue update={cut}, after={after}: {error}")

def cases : Array TestCase := #[
  ⟨"queue/explicit-interleaving", do
    let cursor ← IO.mkRef 0
    let (outcome, world, _) ← runScheduled interleaved (scripted interleavingScript cursor)
    assertOutcome outcome (.ok #[2, 2])
    assertEq (← cursor.get) interleavingScript.size
    assertEq (world.trace.map Prod.fst)
      #["exec:left/1", "exec:right/1", "exec:left/2", "exec:right/2"]⟩,
  ⟨"queue/state-dependent-order", do
    let program : Program (Array Nat) := fun ref => Cloud.parallel #[tick ref, tick ref]
    let (first, _, _) ← runScheduled program selectFirst
    let (last, _, _) ← runScheduled program selectLast
    assertOutcome first (.ok #[0, 1])
    assertOutcome last (.ok #[1, 0])⟩,
  ⟨"queue/global-nested-frontier", do
    let seed ← IO.mkRef 19
    let (_, _, decisions) ← runScheduled recoveryProgram (seeded seed)
    assertTrue (decisions.any fun d =>
      d.ready.any (fun loc => loc.size == 3) && d.ready.any (fun loc => loc.size == 2))
      "Nested children were not runnable alongside their parent's siblings"⟩,
  ⟨"queue/error-order-is-branch-order", do
    let program : Program (Array Nat) := fun ref => Cloud.parallel #[cloud {
      let _ ← execValue ref "left" 1
      Cloud.fail "left failure"
    }, cloud {
      let _ ← execValue ref "right" 2
      Cloud.fail "right failure"
    }]
    let (outcome, world, _) ← runScheduled program selectLast
    assertOutcome outcome (.error ⟨.application, "left failure"⟩)
    assertEq (world.trace.map Prod.fst) #["exec:right", "exec:left"]⟩,
  ⟨"queue/heterogeneous-pair-and-blobs", do
    let program : Program (Nat × String) := fun ref =>
      cloud { execValue ref "number" 42 } || cloud {
        let blob ← CloudBlob.putText "hello"
        CloudBlob.readText blob
      }
    let (outcome, _, _) ← runScheduled program selectLast
    assertOutcome outcome (.ok (42, "hello"))⟩,
  ⟨"queue/empty-group-has-fork-and-join", do
    let (outcome, _, decisions) ← runScheduled
      (fun _ => Cloud.parallel (#[] : Array (Cloud IO Nat))) selectFirst
    assertOutcome outcome (.ok #[])
    assertEq (decisions.map fun d => d.ready[d.selected]!.key) #["0:0", "0:0", "0:1"]⟩,
  ⟨"queue/direct-keeps-function-values", do
    let program : Program (Nat → Nat) := fun ref => cloud {
      let values ← Cloud.parallel #[execValue ref "left" 2, execValue ref "right" 3]
      return fun n => n + values.foldl (· + ·) 0
    }
    let ref ← IO.mkRef initial
    match ← runDirect program ref with
    | .ok f => assertEq (f 7) 12
    | .error e => throw (IO.userError (reprStr e))⟩,
  ⟨"queue/numeric-branch-order", do
    let program : Program (Array Nat) := fun ref =>
      Cloud.parallel ((Array.range 12).map fun i => execValue ref s!"{i}" i)
    let (outcome, world, _) ← runScheduled program selectFirst
    assertOutcome outcome (.ok (Array.range 12))
    assertEq (world.trace.map Prod.fst) ((Array.range 12).map fun i => s!"exec:{i}")⟩,
  ⟨"queue/recovery/new-schedule", recoverySweep recoveryProgram 17⟩,
  ⟨"queue/recovery/failed-child", recoverySweep (fun ref => do
    let _ ← Cloud.parallel #[recoveryProgram ref, cloud {
      let _ ← execValue ref "failure" 0
      Cloud.fail "expected failure"
    }]
    execValue ref "must-not-run" 0) 91⟩,
  ⟨"queue/updates/nested", queueUpdateSweep recoveryProgram⟩,
  ⟨"queue/updates/blobs", queueUpdateSweep blobWorkflow⟩,
  ⟨"queue/updates/failure", queueUpdateSweep failingParallel⟩,
  ⟨"queue/updates/empty", queueUpdateSweep (fun _ => Cloud.parallel (#[] : Array (Cloud IO Nat)))⟩,
  ⟨"queue/idle-then-work", do
    let ref ← IO.mkRef initial
    let idle ← IO.mkRef true
    let base := workQueue
    let queue : WorkQueue Ref IO := { base with next := fun state => do
      if ← idle.get then
        idle.set false
        return (.idle, state)
      base.next state }
    let (outcome, _) ← (interpret db blobStorage queue 20 (fun _ : Unit => pure (7 : Nat)) ()).run ref
    assertOutcome outcome (.ok 7)⟩,
  ⟨"queue/empty-is-not-completed-or-reseeded", do
    let ref ← IO.mkRef { initial with pending := #[] }
    let outcome ← runReplay (fun ref => execValue ref "must-not-run" 7) ref 5
    assertOutcome outcome (.error ⟨.protocol, "Interpreter fuel exhausted"⟩)
    assertTrue (← ref.get).completed.isNone "Idle queue was marked completed"
    assertTrue (← ref.get).trace.isEmpty "Interpreter seeded work without the environment"⟩,
  ⟨"queue/completed-group-arity", do
    let ref ← IO.mkRef { initial with records := [
      ("0:0", toJson (Result.completed (.success (toJson (#[1] : Array Nat)))))] }
    let program : Program (Array Nat) := fun _ => Cloud.parallel #[pure 1, pure 2]
    assertError (← runReplay program ref) .divergence⟩
]

/-- Ignore allocation order, but compare every effect and the bytes it read. -/
def effectMultiset (world : World) : List String :=
  (world.trace.toList.map fun (name, payload) =>
    let payload := if name == "readBlob" then
      match fromJson? (α := BlobRef) payload with
      | .ok blob => encodeBytes ((world.blobs.lookup blob.key).getD ByteArray.empty)
      | .error _ => payload
    else payload
    s!"{name}:{payload.compress}").mergeSort (· ≤ ·)

def generatedCases : Array TestCase := (Array.range 128).map fun seed =>
  let tree := (generate (3 + seed % 3) seed).1
  ⟨s!"queue/generated/{seed}", do
    try
      for policy in [:3] do
        let state ← IO.mkRef (seed + 101)
        let choose := if policy == 0 then selectFirst
          else if policy == 1 then selectLast else seeded state
        let program : Program Nat := fun ref => lower ref tree (seed % 17)
        let direct ← IO.mkRef initial
        let expected ← runDirect program direct
        let (actual, world, _) ← runScheduled program choose
        -- Generated actions return schedule-independent values; shared mutable
        -- counters are covered separately and need not match a sequential run.
        assertOutcome actual expected
        assertEq (effectMultiset world) (effectMultiset (← direct.get))
    catch error => throw (IO.userError s!"seed={seed}, program={reprStr tree}\n{error}")⟩

end LeanCloudTests.Queue
