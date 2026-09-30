import LeanCloudTests.Simulation

namespace LeanCloudTests.ConcurrentJoin
open Lean LeanCloud Simulation SimulationBackend Simulated

private def success (value : Nat) : Exit := .success (toJson value)
private def failure (message : String) : Exit := .failure ⟨.application, message⟩

private structure Fixture where
  parent : Location
  children : Array Exit
  child : Fin 2 → Fin children.size
  expected : Exit

private def pair (parent : Location) (left right expected : Exit) : Fixture :=
  ⟨parent, #[left, right], fun worker => ⟨worker.val, by simp⟩, expected⟩

private def fixtures : Array Fixture := #[
  pair .root (success 11) (success 22) (.success (toJson (#[11, 22] : Array Nat))),
  pair .root (failure "first failure") (failure "second failure") (failure "first failure"),
  pair ((Location.root.child 3).next) (success 11) (success 22) (.success (toJson (#[11, 22] : Array Nat))),
  ⟨.root, #[success 11], fun _ => ⟨0, by decide⟩, .success (toJson (#[11] : Array Nat))⟩
]

private def initial (fixture : Fixture) : Durable := { records :=
  [(JournalDb.forkKey fixture.parent.key, toJson fixture.children.size), ("unrelated", toJson "keep")] }

private abbrev Return := Except CloudError StepResult × Unit

private def start (fixture : Fixture) : Start Return := fun worker =>
  (ReplayInterpreter.Internal.finish (JournalDb.ofDb rawDb)
    (fixture.parent.child (fixture.child worker).val) fixture.children[fixture.child worker]).run ()

private def checkFinished (fixture : Fixture) (state : Machine Return) : IO Unit := do
  let mut requested := false
  for worker in [0, 1] do
    let some (.ok (.runnable locations), ()) := (state.workers worker).outcome?
      | throw (IO.userError "Child completion did not return runnable work")
    assertTrue (locations == #[] || locations == #[fixture.parent]) "Wrong parent was requested"
    requested := requested || locations.contains fixture.parent
  assertTrue requested "Both child completions omitted the parent wakeup"
  for index in List.finRange fixture.children.size do
    assertEq (state.durable.records.lookup (JournalDb.childKey fixture.parent.key index.val))
      (some (toJson fixture.children[index])) "A child result was lost"
  assertEq (state.durable.records.lookup "unrelated") (some (toJson "keep"))
  let read : Start (Option Json × Unit) := fun _ => (JournalDb.get rawDb fixture.parent.key).run ()
  let .ok observed := runWorker 50 read 0 (Simulation.State.initial state.durable read)
    | throw (IO.userError "Could not read completed parent")
  assertEq (observed.workers 0).outcome? (some (some (toJson (Result.completed fixture.expected)), ()))
  assertEq observed.durable state.durable "Checking the join changed storage"

private def crashSweep (initial : Durable) (start : Start Return)
    (check : Machine Return → IO Unit) : IO Unit := do
  let .ok cuts := prefixes 200 start 0 (Simulation.State.initial initial start)
    | throw (IO.userError "Could not enumerate completion boundaries")
  assertTrue (!cuts.isEmpty) "Completion had no backend boundaries"
  for paused in cuts do
    let .ok crashed := applyEvent start (.crash 0) paused
      | throw (IO.userError "Could not crash completion")
    assertEq crashed.durable paused.durable
    let .ok other := runWorker 200 start 1 crashed
      | throw (IO.userError "Other completion did not finish during crash")
    let .ok restarted := applyEvent start (.restart 0) other
      | throw (IO.userError "Could not restart completion")
    let .ok final := runWorker 200 start 0 restarted
      | throw (IO.userError "Restarted completion did not finish")
    check final
    for (key, value) in paused.durable.records do
      assertEq (final.durable.records.lookup key) (some value)

private def boundaryCases : Array TestCase := #[
  ⟨"simulation/join/crash-at-every-first-worker-boundary", do
    for fixture in fixtures do
      crashSweep (initial fixture) (start fixture) (checkFinished fixture)⟩,
  ⟨"simulation/join/root-completion-crash-boundaries", do
    for outcome in [success 11, failure "root failure"] do
      let start : Start Return := fun _ =>
        (ReplayInterpreter.Internal.finish (JournalDb.ofDb rawDb) .root outcome).run ()
      crashSweep { records := [("unrelated", toJson "keep")] } start fun final => do
        for worker in [0, 1] do
          let some (.ok (.done actual), ()) := (final.workers worker).outcome?
            | throw (IO.userError "Root completion did not return done")
          assertEq actual outcome
        assertEq (final.durable.records.lookup (JournalDb.resultKey Location.root.key)) (some (toJson outcome))
        assertEq (final.durable.records.lookup "unrelated") (some (toJson "keep"))⟩,
  ⟨"simulation/join/completed-child-without-own-cache", do
    let parent := Location.root
    let current := parent.child 0
    let outcome := Exit.success (toJson (#[3, 4] : Array Nat))
    let records := [
      (JournalDb.forkKey parent.key, toJson (2 : Nat)),
      (JournalDb.childKey parent.key 1, toJson (success 22)),
      (JournalDb.forkKey current.key, toJson (2 : Nat)),
      (JournalDb.childKey current.key 0, toJson (success 3)),
      (JournalDb.childKey current.key 1, toJson (success 4))]
    let start : Start Return := fun _ =>
      (ReplayInterpreter.Internal.finish (JournalDb.ofDb rawDb) current outcome).run ()
    crashSweep { records } start fun final => do
      for worker in [0, 1] do
        let some (.ok (.runnable locations), ()) := (final.workers worker).outcome?
          | throw (IO.userError "Completed child did not return runnable work")
        assertEq locations #[parent]
      assertEq (final.durable.records.lookup (JournalDb.childKey parent.key 0)) (some (toJson outcome))
      assertEq (final.durable.records.lookup (JournalDb.resultKey current.key)) none
        "A completed child group should be reused without requiring its own cache"
      for (key, value) in records do
        assertEq (final.durable.records.lookup key) (some value)⟩,
  ⟨"simulation/join/lost-last-slot-reply-without-cache", do
    let fixture := fixtures[0]
    let start := start fixture
    let .ok first := runWorker 200 start 0 (Simulation.State.initial (initial fixture) start)
      | throw (IO.userError "First child did not finish")
    let .ok cuts := prefixes 200 start 1 first
      | throw (IO.userError "Could not enumerate last child's publication")
    let some paused := cuts.find? fun state =>
        (state.workers 1).phase == .responding &&
        (state.durable.records.lookup (JournalDb.childKey fixture.parent.key 1)).isSome &&
        (state.durable.records.lookup (JournalDb.resultKey fixture.parent.key)).isNone
      | throw (IO.userError "Did not find the committed last slot before cache publication")
    let .ok crashed := applyEvent start (.crash 1) paused
      | throw (IO.userError "Could not lose last-slot reply")
    let .ok restarted := applyEvent start (.restart 1) crashed
      | throw (IO.userError "Could not retry last child")
    let .ok final := runWorker 200 start 1 restarted
      | throw (IO.userError "Retry did not finish")
    checkFinished fixture final
    assertEq (final.durable.records.lookup (JournalDb.resultKey fixture.parent.key)) none
      "Retry should recognize the full slots without needing a result cache"⟩,
  ⟨"simulation/join/all-ten-event-prefixes", do
    let fixture := fixtures[1]
    let start := start fixture
    let .ok cuts := frontiers 10 start (Simulation.State.initial (initial fixture) start)
      | throw (IO.userError "Could not enumerate join scheduling prefixes")
    assertEq cuts.length 1024
    for paused in cuts do
      let .ok final := drive 500 start paused 7
        | throw (IO.userError "Join did not finish after scheduling prefix")
      checkFinished fixture final⟩
]

private def scheduledCases : Array TestCase :=
  (fixtures.mapIdx fun variant fixture =>
    (Array.range 4).flatMap fun seed =>
      #[false, true].map fun crashes =>
        ⟨s!"simulation/join/{variant}/seed/{seed}/crashes/{crashes}", do
          let start := start fixture
          let .ok final := drive 500 start (Simulation.State.initial (initial fixture) start) seed
              (if crashes then [7, 19, 31, 47] else [])
            | throw (IO.userError s!"Join failed for fixture {variant}, seed {seed}")
          checkFinished fixture final⟩ : Array (Array TestCase)).flatten

def cases : Array TestCase := boundaryCases ++ scheduledCases

end LeanCloudTests.ConcurrentJoin
