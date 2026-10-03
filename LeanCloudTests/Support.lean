import LeanCloud

namespace LeanCloudTests
open Lean LeanCloud

structure TestCase where
  name : String
  run : IO Unit

def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def assertEq [BEq α] [Repr α] (actual expected : α) (context : String := "Values differ") : IO Unit :=
  assertTrue (actual == expected) s!"{context}\nexpected: {reprStr expected}\nactual:   {reprStr actual}"

def assertOutcome [BEq α] [Repr α] (actual expected : Except CloudError α) : IO Unit :=
  match actual, expected with
  | .ok a, .ok b => assertEq a b "Results differ"
  | .error a, .error b => assertEq a b "Errors differ"
  | _, _ => throw (IO.userError s!"Outcomes differ\nexpected: {reprStr expected}\nactual: {reprStr actual}")

def assertError (actual : Except CloudError α) (kind : ErrorKind) : IO Unit :=
  match actual with
  | .error error => assertEq error.kind kind
  | .ok _ => throw (IO.userError s!"Expected {reprStr kind}, got success")

def makeRef (key : String) (bytes : ByteArray) : BlobRef :=
  ⟨key, bytes.size, modelChecksum bytes⟩

/-- A sequential evaluator for simulation effects, used only to run the direct
reference and inspect client results. It performs no scheduling or replay. -/
def evaluate (fuel : Nat) (program : SimM δ α) (world : δ) : Except String (α × δ) :=
  match fuel with
  | 0 => .error "Simulation evaluation fuel exhausted"
  | fuel + 1 =>
    match program with
    | LeanEff.EffF.pure value => .ok (value, world)
    | .impure (.step _ _ operation) next =>
      let (value, world) := operation world
      evaluate fuel (LeanEff.ArrsF.apply next value) world

def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

abbrev Machine := Simulation.State SimulationBackend.World Unit 4
abbrev Start := Simulation.Start SimulationBackend.World Unit 4

def tick (start : Start) (actor : Fin 4) (state : Machine) : Except String Machine := do
  let event := match state.actors actor with
    | .waiting .. => some (Simulation.Event.commit actor)
    | .responding .. => some (.resume actor)
    | .stopped => some (.restart actor)
    | .finished _ => none
  match event with
  | none => return state
  | some event =>
    match SimulationBackend.step start event state with
    | .ok state => return state
    | .error error => throw (reprStr error)

def event (start : Start) (event : Simulation.Event 4) (state : Machine) : Except String Machine :=
  match SimulationBackend.step start event state with
  | .ok state => pure state
  | .error error => throw (reprStr error)

def nextSeed (seed : Nat) : Nat := (1664525 * seed + 1013904223) % 4294967296

/-- Finite chaos followed by fair delivery and actor scheduling. Includes crashes
of the scheduler, lost or late remote requests, duplicate messages, redelivery, and expiry.
Only uncommitted orphan requests may be discarded, never confirmed messages. -/
def runSystem (start : Start) (initial : Machine) (seed : Nat) (chaos : Bool) : Except String Machine := do
  let mut state := initial
  let mut random := seed
  for step in [:if chaos then 1500 else 0] do
    random := nextSeed random
    -- The low two bits of this LCG cycle through the same four actors.
    let actor : Fin 4 := ⟨random / 65536 % 4, Nat.mod_lt _ (by decide)⟩
    let index := random / 16 % max 1 state.world.network.size
    let networkEvent := match random / 256 % 13 with
      | 0 => .hold
      | 1 => .duplicate index
      | _ => .deliver index
    state := { state with world := SimulationBackend.networkStep networkEvent state.world }
    if random / 65536 % 19 == 0 then
      match state.actors actor with
      | .waiting .. | .responding .. => state ← event start (.crash actor) state
      | _ => state ← tick start actor state
    else state ← tick start actor state
    if !state.orphans.isEmpty && random / 1048576 % 7 == 0 then
      let orphan := random / 4096 % state.orphans.size
      let action := if random / 8388608 % 2 == 0 then
        Simulation.Event.commitOrphan orphan else .discardOrphan orphan
      state ← event start action state
    if step % 97 == 0 then
      state := { state with world := SimulationBackend.networkStep (.tick 500) state.world }
  -- Expire abandoned assignments after faults stop. Retrying messages repairs
  -- scheduler saves whose replies were lost. Late commits remain deliverable.
  state := { state with world := SimulationBackend.networkStep (.tick 1000000) state.world }
  for round in [:200000] do
    if let some error := state.world.scheduler.error then
      throw s!"Scheduler error: {reprStr error}"
    if state.world.scheduler.finished then
      -- Completion must remain valid when old remote requests arrive later.
      let completed := state.world.records
      while !state.orphans.isEmpty do state ← event start (.commitOrphan 0) state
      unless completed.all (fun (key, record) => state.world.records.lookup key == some record) do
        throw "Late request changed a committed record"
      return state
    if !state.orphans.isEmpty then state ← event start (.commitOrphan 0) state
    if round % 5000 == 0 then
      state := { state with world := SimulationBackend.networkStep (.tick 1000) state.world }
    state := { state with world := SimulationBackend.networkStep (.deliver 0) state.world }
    for actor in Array.finRange 4 do state ← tick start actor state
  throw s!"System did not finish; jobs={reprStr state.world.scheduler.jobs}"

/-- The very same Cloud program runs directly and through the scheduler/worker
actors. Compare the durable final outcome, not just a worker's transient return. -/
def differential [Codec α] [BEq α] [Repr α]
    (program : Unit → Cloud (SimM SimulationBackend.World) α) (seed := 0) (chaos := false) : IO SimulationBackend.World := do
  let (expected, direct) ← unwrap (evaluate 1000000
    (DirectInterpreter.interpret SimulationBackend.blobs program ()).run {})
  assertEq direct.writes 0 "Direct interpreter wrote replay records"
  assertEq direct.reads 0 "Direct interpreter read replay records"
  let start := SimulationBackend.start (workers := 3) 100000 10000 1000 program ()
  let finished ← unwrap ((runSystem start (Simulation.State.initial {} start) seed chaos).map (·.world))
  let (recorded, _) ← unwrap (evaluate 100000 (SimulationBackend.records.outcome).run finished)
  let outcome ← match recorded with
    | .ok (some outcome) => pure outcome
    | .ok none => throw (IO.userError "Scheduler finished without a durable root result")
    | .error error => throw (IO.userError (reprStr error))
  let actual : Except CloudError α := (ReplayInterpreter.result (m := Id) outcome).run
  assertOutcome actual expected
  -- Reconstructing any completed branch must reuse its result without writes.
  for job in finished.scheduler.jobs do
    assertEq job.status .done "Scheduler finished with unfinished branches"
    let assignment : Assignment := ⟨9999999, job.branch, job.location, job.joining⟩
    let (repeated, after) ← unwrap (evaluate 100000
      (ReplayInterpreter.step SimulationBackend.records SimulationBackend.blobs 10000 program () assignment).run
      finished)
    match repeated with
    | .ok .done => pure ()
    | other => throw (IO.userError s!"Completed branch failed warm replay: {reprStr other}")
    assertEq after.writes finished.writes "Warm replay wrote a record"
    assertEq after.records finished.records "Warm replay changed recorded outcomes"
  return finished

end LeanCloudTests
