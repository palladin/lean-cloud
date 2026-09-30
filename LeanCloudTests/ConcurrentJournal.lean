import LeanCloudTests.Simulation

namespace LeanCloudTests.ConcurrentJournal
open Lean LeanCloud Simulation SimulationBackend Simulated

/-- Both reads see absence. B finishes its write before A receives its old read
response, so A's eventual write must tolerate a record that now exists. -/
private def delayedRead : List (Event 2) :=
  [.commit 0, .commit 1, .resume 1, .commit 1, .resume 1, .resume 0, .commit 0, .resume 0]

private def start (keys : Fin 2 → String) (values : Fin 2 → Json) : Start (Bool × Unit) :=
  fun worker => (JournalDb.putSame rawDb (keys worker) (values worker)).run ()

private def initial : Durable := { records := [("unrelated", toJson "keep")] }

private def check (state : Machine (Bool × Unit)) (keys : Fin 2 → String)
    (values : Fin 2 → Json) : IO Unit := do
  for worker in [0, 1] do
    assertEq (state.workers worker).outcome? (some (true, ()))
    assertEq (state.durable.records.lookup (keys worker)) (some (values worker))
  assertEq (state.durable.records.lookup "unrelated") (some (toJson "keep"))

private def singleRecordCases : Array TestCase := #[
  ⟨"simulation/journal/duplicate-delayed-read", do
    let keys := fun _ : Fin 2 => "shared"
    let values := fun _ : Fin 2 => toJson (17 : Nat)
    let start := start keys values
    let .ok final := Simulation.run start advance delayedRead (Simulation.State.initial initial start)
      | throw (IO.userError "Invalid delayed-read schedule")
    check final keys values⟩,
  ⟨"simulation/journal/different-keys", do
    let keys := fun worker : Fin 2 => s!"child/{worker.val}"
    let values := fun worker : Fin 2 => toJson (worker.val + 17)
    let start := start keys values
    let .ok final := Simulation.run start advance delayedRead (Simulation.State.initial initial start)
      | throw (IO.userError "Invalid independent-write schedule")
    check final keys values⟩,
  ⟨"simulation/journal/crash-at-every-boundary", do
    let keys := fun _ : Fin 2 => "shared"
    let values := fun _ : Fin 2 => toJson (17 : Nat)
    let start := start keys values
    let .ok cuts := prefixes 10 start 0 (Simulation.State.initial initial start)
      | throw (IO.userError "Could not enumerate putSame boundaries")
    assertEq cuts.length 4
    for paused in cuts do
      let .ok crashed := Simulation.step start advance (.crash 0) paused
        | throw (IO.userError "Could not crash writer")
      assertEq crashed.durable paused.durable
      let .ok other := runWorker 10 start 1 crashed
        | throw (IO.userError "Other writer did not finish")
      let .ok restarted := Simulation.step start advance (.restart 0) other
        | throw (IO.userError "Could not restart writer")
      let .ok final := runWorker 10 start 0 restarted
        | throw (IO.userError "Restarted writer did not finish")
      check final keys values⟩,
  ⟨"simulation/journal/observed-conflict-is-rejected", do
    let initial := { initial with records := ("shared", toJson (11 : Nat)) :: initial.records }
    let start := start (fun _ => "shared") (fun _ => toJson (22 : Nat))
    let .ok final := runWorker 10 start 0 (Simulation.State.initial initial start)
      | throw (IO.userError "Writer did not finish")
    assertEq (final.workers 0).outcome? (some (false, ()))
    assertEq final.durable initial⟩,
  ⟨"simulation/journal/agreement-is-required", do
    -- putSame is not compare-and-set. Disagreeing writers that both read
    -- absence can both return true, and the later physical write wins.
    let start := start (fun _ => "shared") (fun worker => toJson (worker.val + 17))
    let .ok final := Simulation.run start advance delayedRead (Simulation.State.initial initial start)
      | throw (IO.userError "Invalid conflicting-write schedule")
    assertEq (final.workers 0).outcome? (some (true, ()))
    assertEq (final.workers 1).outcome? (some (true, ()))
    assertEq (final.durable.records.lookup "shared") (some (toJson (17 : Nat)))
    assertEq (final.durable.records.lookup "unrelated") (some (toJson "keep"))⟩
]

private def publish (results : Fin 2 → Result) : Start (Bool × Unit) :=
  fun worker => (JournalDb.put rawDb "0:0" (toJson (results worker))).run ()

private def success (value : Nat) : Exit := .success (toJson value)

private def partials (worker : Fin 2) : Result :=
  if worker == 0 then .suspended #[some (success 11), none, some (success 33)]
  else .suspended #[none, some (.failure ⟨.application, "child failed"⟩), none]

private def slots : List (String × Json) :=
  [(JournalDb.forkKey "0:0", toJson (3 : Nat)),
   (JournalDb.childKey "0:0" 0, toJson (success 11)),
   (JournalDb.childKey "0:0" 1, toJson (Exit.failure ⟨.application, "child failed"⟩)),
   (JournalDb.childKey "0:0" 2, toJson (success 33))]

private def checkRecords (state : Durable) (records : List (String × Json)) : IO Unit := do
  for (key, value) in records do
    assertEq (state.records.lookup key) (some value) s!"Missing or changed record: {key}"

private def checkPublished (state : Machine (Bool × Unit))
    (records : List (String × Json)) : IO Unit := do
  for worker in [0, 1] do
    assertEq (state.workers worker).outcome? (some (true, ()))
  checkRecords state.durable (initial.records ++ records)

private def publicationCases : Array TestCase := #[
  ⟨"simulation/journal/partial-publications-delayed-read", do
    let start := publish partials
    let .ok paused := Simulation.run start advance delayedRead (Simulation.State.initial initial start)
      | throw (IO.userError "Invalid overlapping descriptor schedule")
    let .ok final := drive 100 start paused 7
      | throw (IO.userError "Partial publications did not finish")
    checkPublished final slots
    assertEq (final.durable.records.lookup (JournalDb.resultKey "0:0")) none⟩,
  ⟨"simulation/journal/publication-crash-at-every-boundary", do
    let start := publish partials
    let .ok cuts := prefixes 30 start 0 (Simulation.State.initial initial start)
      | throw (IO.userError "Could not enumerate publication boundaries")
    -- Descriptor and two present children: each has read/response/write/response.
    assertEq cuts.length 12
    for paused in cuts do
      let .ok crashed := applyEvent start (.crash 0) paused
        | throw (IO.userError "Could not crash partial publisher")
      assertEq crashed.durable paused.durable
      let .ok other := runWorker 30 start 1 crashed
        | throw (IO.userError "Other publisher did not finish")
      let .ok restarted := applyEvent start (.restart 0) other
        | throw (IO.userError "Could not restart partial publisher")
      let .ok final := runWorker 30 start 0 restarted
        | throw (IO.userError "Restarted publisher did not finish")
      checkPublished final slots
      checkRecords final.durable paused.durable.records⟩,
  ⟨"simulation/journal/publication-all-eight-event-prefixes", do
    let start := publish partials
    let .ok paused := frontiers 8 start (Simulation.State.initial initial start)
      | throw (IO.userError "Could not enumerate publication schedules")
    assertEq paused.length 256
    for state in paused do
      let .ok final := drive 100 start state 19
        | throw (IO.userError "Publication did not finish after prefix")
      checkPublished final slots
      checkRecords final.durable state.durable.records⟩,
  ⟨"simulation/journal/completed-cache-survives-late-initialization", do
    let result := success 44
    let results := fun worker : Fin 2 =>
      if worker == 0 then Result.suspended #[none, none] else .completed result
    let start := publish results
    let .ok cuts := prefixes 10 start 0 (Simulation.State.initial initial start)
      | throw (IO.userError "Could not enumerate initialization boundaries")
    assertEq cuts.length 4
    for paused in cuts do
      let .ok completed := runWorker 10 start 1 paused
        | throw (IO.userError "Completed-result publisher did not finish")
      let .ok final := runWorker 10 start 0 completed
        | throw (IO.userError "Late initializer did not finish")
      checkPublished final [(JournalDb.resultKey "0:0", toJson result),
        (JournalDb.forkKey "0:0", toJson (2 : Nat))]
      checkRecords final.durable completed.durable.records⟩,
  ⟨"simulation/journal/empty-publication-and-duplicate-completion", do
    for result in [Result.suspended #[], .completed (success 44)] do
      let start := publish (fun _ => result)
      let .ok final := drive 100 start (Simulation.State.initial initial start) 13 [3, 9]
        | throw (IO.userError "Duplicate publication did not recover")
      let records := match result with
        | .suspended _ => [(JournalDb.forkKey "0:0", toJson (0 : Nat))]
        | .completed outcome => [(JournalDb.resultKey "0:0", toJson outcome)]
      checkPublished final records⟩,
  ⟨"simulation/journal/publication-rejects-malformed-result", do
    let start : Start (Bool × Unit) := fun _ =>
      (JournalDb.put rawDb "0:0" (Json.str "not a Result")).run ()
    let state := Simulation.State.initial initial start
    assertEq (state.workers 0).outcome? (some (false, ()))
    assertEq state.durable initial⟩
]

private def recoveryCases : Array TestCase :=
  (Array.range 16).map fun seed =>
    ⟨s!"simulation/journal/publication-recovery/{seed}", do
      let start := publish partials
      let .ok final := drive 200 start (Simulation.State.initial initial start) seed [3, 9, 17, 23]
        | throw (IO.userError s!"Publication failed with schedule seed {seed}")
      checkPublished final slots⟩

def cases : Array TestCase := singleRecordCases ++ publicationCases ++ recoveryCases

end LeanCloudTests.ConcurrentJournal
