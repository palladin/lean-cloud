import LeanCloudTests.Simulation

namespace LeanCloudTests.ConcurrentRead
open Lean LeanCloud Simulation SimulationBackend Simulated

private def key := "0:0"
private def success (value : Nat) : Exit := .success (toJson value)
private def failed : Exit := .failure ⟨.application, "child failed"⟩

/-- Reader and actual publisher share storage, with independent continuations. -/
private def start (publication : Result) : Start (Option Json × Unit) := fun worker =>
  if worker == 0 then (JournalDb.get rawDb key).run ()
  else (do
    let accepted ← JournalDb.put rawDb key (toJson publication)
    return if accepted then none else some (Json.str "publication rejected")).run ()

private def initial : Durable := { records := [("unrelated", toJson "keep")] }

private def readResult (state : Machine (Option Json × Unit)) (expected : Option Json) : IO Unit := do
  assertEq (state.workers 0).outcome? (some (expected, ()))
  assertEq (state.durable.records.lookup "unrelated") (some (toJson "keep"))

private def seeded : Durable := { initial with records :=
  [(JournalDb.forkKey key, toJson (3 : Nat)),
   (JournalDb.childKey key 0, toJson (success 11))] ++ initial.records }

private def publication : Result := .suspended #[some (success 11), some (success 22), some failed]

/-- The first slot was present before the read. The other two can be observed
at different times, but can never contain anything other than their published values. -/
private def allowed : Array (Option Json) :=
  #[#[some (success 11), none, none], #[some (success 11), some (success 22), none],
    #[some (success 11), none, some failed], #[some (success 11), some (success 22), some failed]].map
    fun slots => some (toJson (Result.settle slots))

private def checkObservation (state : Machine (Option Json × Unit)) : IO Unit := do
  let some (answer, ()) := (state.workers 0).outcome?
    | throw (IO.userError "Reader did not finish")
  assertTrue (allowed.any (· == answer)) s!"Invented or omitted a known result: {reprStr answer}"
  assertEq (state.workers 1).outcome? (some (none, ())) "Publisher did not succeed"
  for (recordKey, value) in seeded.records do
    assertEq (state.durable.records.lookup recordKey) (some value)
  assertEq (state.durable.records.lookup (JournalDb.childKey key 1)) (some (toJson (success 22)))
  assertEq (state.durable.records.lookup (JournalDb.childKey key 2)) (some (toJson failed))

private def fixtures : Array TestCase := #[
  ⟨"simulation/read/cached-result-delayed-reply", do
    let outcome := success 44
    let initial := { initial with records := (JournalDb.resultKey key, toJson outcome) :: initial.records }
    let start := start (.suspended #[none, none])
    let .ok paused := applyEvent start (.commit 0) (Simulation.State.initial initial start)
      | throw (IO.userError "Could not pause cached read")
    let .ok written := runWorker 20 start 1 paused
      | throw (IO.userError "Late initializer did not finish")
    let .ok final := applyEvent start (.resume 0) written
      | throw (IO.userError "Could not deliver cached read")
    readResult final (some (toJson (Result.completed outcome)))
    assertEq final.durable written.durable "Read changed storage"⟩,
  ⟨"simulation/read/stale-absence-after-completion", do
    let start := start (.completed (success 44))
    let .ok paused := Simulation.run start advance [.commit 0, .resume 0, .commit 0]
        (Simulation.State.initial initial start)
      | throw (IO.userError "Could not pause absent descriptor reply")
    let .ok written := runWorker 20 start 1 paused
      | throw (IO.userError "Completion publisher did not finish")
    let .ok final := applyEvent start (.resume 0) written
      | throw (IO.userError "Could not deliver absent descriptor reply")
    readResult final none
    assertEq (final.durable.records.lookup (JournalDb.resultKey key)) (some (toJson (success 44)))
    assertEq final.durable written.durable⟩,
  ⟨"simulation/read/mixed-view-is-not-a-snapshot", do
    let initial := { initial with records := (JournalDb.forkKey key, toJson (2 : Nat)) :: initial.records }
    let start := start (.suspended #[some (success 11), some (success 22)])
    let .ok paused := Simulation.run start advance [.commit 0, .resume 0, .commit 0, .resume 0, .commit 0]
        (Simulation.State.initial initial start)
      | throw (IO.userError "Could not pause first child reply")
    let .ok cuts := prefixes 30 start 1 paused
      | throw (IO.userError "Could not inspect writer's storage states")
    -- The writer publishes child 0 before child 1. The combination absent/22
    -- never exists in shared storage, yet the reader can assemble that view.
    for state in cuts do
      let first := state.durable.records.lookup (JournalDb.childKey key 0)
      let second := state.durable.records.lookup (JournalDb.childKey key 1)
      assertTrue (!(first.isNone && second.isSome)) "Unexpected simultaneous mixed state"
    let .ok written := runWorker 30 start 1 paused
      | throw (IO.userError "Writer did not finish")
    let .ok final := runWorker 30 start 0 written
      | throw (IO.userError "Reader did not finish")
    readResult final (some (toJson (Result.suspended #[none, some (success 22)])))
    assertEq final.durable written.durable
    let .ok fresh := runWorker 30 start 0 (Simulation.State.initial final.durable start)
      | throw (IO.userError "Fresh read did not finish")
    readResult fresh (some (toJson (Result.completed (successArray #[11, 22]))))⟩,
  ⟨"simulation/read/crash-at-every-boundary", do
    let start := start publication
    let .ok cuts := prefixes 30 start 0 (Simulation.State.initial seeded start)
      | throw (IO.userError "Could not enumerate read boundaries")
    assertEq cuts.length 10
    for paused in cuts do
      let .ok crashed := applyEvent start (.crash 0) paused
        | throw (IO.userError "Could not crash reader")
      assertEq crashed.durable seeded "Read or crash changed storage"
      let .ok written := runWorker 30 start 1 crashed
        | throw (IO.userError "Writer did not finish while reader was crashed")
      let .ok restarted := applyEvent start (.restart 0) written
        | throw (IO.userError "Could not restart reader")
      let .ok final := runWorker 30 start 0 restarted
        | throw (IO.userError "Restarted reader did not finish")
      readResult final (some (toJson (Result.completed failed)))
      assertEq final.durable written.durable⟩,
  ⟨"simulation/read/all-eight-event-prefixes", do
    let start := start publication
    let .ok paused := frontiers 8 start (Simulation.State.initial seeded start)
      | throw (IO.userError "Could not enumerate read/write schedules")
    assertEq paused.length 256
    for state in paused do
      let .ok final := drive 100 start state 19
        | throw (IO.userError "Read/write schedule did not finish")
      checkObservation final⟩,
  ⟨"simulation/read/empty-fork", do
    let initial := { initial with records := (JournalDb.forkKey key, toJson (0 : Nat)) :: initial.records }
    let start := start (.suspended #[])
    let .ok final := drive 50 start (Simulation.State.initial initial start) 13 [3]
      | throw (IO.userError "Empty fork read did not recover")
    readResult final (some (toJson (Result.completed (successArray #[]))))⟩
]
where
  successArray (values : Array Nat) : Exit := .success (toJson values)

private def schedules : Array TestCase :=
  (Array.range 16).flatMap fun seed =>
    #[false, true].map fun crashes =>
      ⟨s!"simulation/read/seed/{seed}/crashes/{crashes}", do
        let start := start publication
        let .ok final := drive 200 start (Simulation.State.initial seeded start) seed
            (if crashes then [3, 9, 17, 23] else [])
          | throw (IO.userError s!"Read/write schedule failed for seed {seed}")
        checkObservation final⟩

def cases : Array TestCase := fixtures ++ schedules

end LeanCloudTests.ConcurrentRead
